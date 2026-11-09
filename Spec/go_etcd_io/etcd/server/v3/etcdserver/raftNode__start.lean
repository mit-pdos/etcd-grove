/-
`(*raftNode).start(rh)` (`raft.go:176-354`): the `Ready` loop, in a new goroutine: ticks, and for
each `Ready`: the soft state into the ready handler; the last read state to `readStateC`; the batch
(committed entries, a copy of the snapshot, `notifyc`, `raftAdvancedC`, the latest hard state's term)
to the apply thread; the leader sends first; the snapshot saved (`SaveSnap`), the hard state and
entries saved (`Save`), and with a snapshot synced, signalled (`notifyc`) and installed in the
`MemoryStorage`; the entries appended to it; a follower then sends; the apply thread signalled
(and, with a conf change, waited for); `Advance`; `raftAdvancedC` closed. `onStop` at `stopped`.

**Users**: `run` (`server.go:808`). Snippets `raftnode.go` (`ReqDriverLoop`, `ReqWriteBeforeSend`),
`restart.go` (`ReqCrashKeepsAnswered`).

**Proof sketch** (the loop carries `rnLoop r`: R1's `nodeDriver n γ.raft st`, `nodeRunning n ½`, the
WAL's write half, the delivered log `st.delivered`, the ready handler's `readyHandlerTok`):
1. `<-r.ticker.C`: `tick.spec`.
2. `<-r.Ready()`: R1's `readyChan_recv` gives `readyGot`: the batch `b`, `readyEnter`,
   `readyCheck`, `readyStor`, the messages' credits, `committedLb`/`deliveredLb` of the delivered
   log `dl`, the snapshot's `snapValid`.
3. Soft state: the ready handler (`readyHandlerOk`: `updateLead`, `updateLeadership`); read states:
   `readyCheck` gives `readState`s before the write (R1), sent on `readStateC` (or dropped after
   1 s); `raftTerm` from the hard state.
4. The batch: `proto.Clone` of the snapshot (3h/2a's: a copy, read-only); `updateCommittedIndex.spec`;
   the send on `applyc` hands `applyBatch r γ apv B false` (with `B.prev = |st.delivered|`, matched
   by the receiver's `applycPos` cursor, the entries' `entriesRO`, the snapshot's validity and
   `snapImage` from the member's invariant over its snapshot directory, `advancedAt r rac |dl|`, the
   term bound `applyBatch_terms`; for a batch with conf changes, R1's `nodeConf`, lent: round 1, F3).
5. **Leader, before the write**: `readyCheck` gives `msgSent` of every message (the batch leaves the
   node leader); `processMessages.spec`; `transport.Send` (2f's: takes `sendable`).
6. **The write**: `SaveSnap` (2e's WAL+snapshotter: the snapshot record), `Save(hs, ents)`: before
   it the loop **deposits the batch's `readyEnter` in the disk** through 2e's `diskAcc γ.etcd ds` (the
   program's `diskState`, which holds `raftState γ.raft id D` with the WAL's records: 2e, "from 2e,
   round 2"), and `Save`'s update over `Wal.walRecs` (opened inside `diskAcc`'s, mask `⊤ \ diskN`)
   fires it at the synced write (moving `D` to `D.next b`, R1; a crash in between is `disk_crash`'s,
   by R1's `raftState_crash` of the deposited batch, within `crashScope`), giving the driver back
   (`nodeDriver n γ.raft (st.after b dl)`), `msgSent` of every message and the read states. No
   error: 2e's disk premise (`lg.Fatal` unreachable). With a snapshot: `Sync`, `notifyc <- {}` (the
   apply thread may now open the snapshot's db and `Release` the WAL below it),
   `raftStorage.ApplySnapshot` (R1's `readyStor_install`). `raftStorage.Append(rd.Entries)` (R1's
   `readyStor_append`).
7. **Follower, after the write**: `processMessages.spec`, `notifyc <- {}`; with a conf change in the
   batch, a second send that completes once the apply thread received the first, i.e. after it
   applied the batch's conf changes (`notifyc`'s protocol carries the node's `nodeConf` back);
   `transport.Send`. Leader: `notifyc <- {}` and the same wait on a conf change.
8. `r.Advance()` (R1's `node.Advance.spec`: `readyStor` empty; `nodeConf` the loop's: returned by
   the apply thread's `notifyc` receive for a batch with conf changes (applied or decided skip),
   else kept, the batch's entries having no conf change, `confSkipped` vacuous) gives `appliedLb n
   |dl|`; with a snapshot, R1's wand is applied by the loop at the snapshot's point
   (`snapImage_point`'s `a`, `confAt γ.raft a m`), the point the apply thread will open the image at
   (round 1, F3/F4); `close(raftAdvancedC)` carries `nodeAdvanced r |dl|`.
9. `<-r.stopped`: `onStop.spec` with the loop's resources.

Durability (K5): a follower's acknowledgement (`MsgAppResp`) is sent only after `Save` fired
`readyEnter` (R1: `msgSent` of non-leader messages comes from the enter update); a leader's own
messages may go before its write (Raft thesis 10.2.1: `readyCheck`), and its commit still needs a
quorum's acknowledgements. So an entry the apply thread applies is on a quorum's WAL.

**Changes** from `specs-ref`'s spec (`isRaftNode E γ r`, `isReadyHandler rh R`, `rnLoopTok γ L`,
`rnDoneTok`, the WAL token `rnWalTokL`, `memStorInv`, `memSnapLb`, `walSaveOk`, `walCloseOk`): over
`isRaftNode`/`rnLoop`/`readyHandlerOk`; the I/O premises are 2e's (the storage's disk premise, carried
by its handle); the loop fires R1's `readyEnter` at the WAL's write (was the old proof's own WAL
ghost).

**Margin**: none (a goroutine).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply

set_option autoImplicit false
set_option linter.iris.dupNamespace false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

def raftNode.start.spec : Prop :=
  ∀ (r : Loc) (γ : Names) (id : w64) (n rh s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isRaftNode r γ id n ∗ rnLoop r ∗ readyHandlerOk rh s γ ∗ readyHandlerTok rh }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.raftNode.ty @!!
      go!"start")) (Val #rh))
  {{ RET #(); True }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
