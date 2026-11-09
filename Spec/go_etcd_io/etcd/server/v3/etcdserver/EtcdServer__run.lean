/-
`(*EtcdServer).run()` (`server.go:752-853`): the apply loop, a goroutine (`start`'s `go s.run()`).

**Users**: `EtcdServer.start` (`server.go:604`, batch 2e: `srvRunTok_intro` from the pieces its
`srvBuilt` holds). Snippets `examples/specreq/etcdserverapply/apply.go` (`ReqWriteAnswered`,
`ReqReadAfterApplyWait`), `restart.go` (`ReqRestartContinues`, `ReqCrashKeepsAnswered`),
`raftnode.go` (`ReqRemovedSelfStops`).

**Proof sketch**. `srvRunTok s γ id ds` (`srvRunTok_intro`): the driver at `s.r` with `rnLoop`,
`rnStopper` and the cursor `applycPos (s.r) p₀.appliedi` (the node's delivered start: `Applied = 0`,
the `MemoryStorage` snapshot's index), `applyInit s γ p₀ c₀` (the backend's state machine at its
consistent index `c₀ ≥ p₀.appliedi`), 2e's `srvClosers s ds`; `srvStarted` gives the channels.
1. `s.r.raftStorage.Snapshot()`: R1's `MemoryStorage.Snapshot.spec` through `isRaftNode_storage` and
   `stor_read` (the stored snapshot empty or valid); a `MemoryStorage` never returns
   `ErrSnapshotTemporarilyUnavailable`. Its `ConfState` non-nil (the storage stores what it is
   given; bootstrap's from the backend): `panic("empty confstate")` unreachable.
2. `schedule.NewFIFOScheduler(lg)` (`Schedule.NewFIFOScheduler.spec`, `Pay := True`).
3. The ready handler `rh`: four closures over `s`'s atomics (`readyHandlerOk rh s γ`, the writers
   `readyHandlerTok rh` from `srvNode`'s atomics' writers); `updateLeadership` calls the lessor's
   `Demote` and the compactor's `Pause`/`Resume` (3c's, 2e's), `leaderChanged.Notify()` (2c's).
4. `s.r.start(rh)` (`raftNode.start.spec`).
5. `ep` allocated from `sn` (`applyInit_ep`: `applyThread s γ ep p₀`). The scheduler's chain end is
   `schedTail γs (∃ p, applyThread s γ ep p ∗ ⌜p.appliedi = k⌝)` where `applycPos (s.r) k` is held
   by the loop (round 1, F2).
6. The loop: on `applyc` (`applyc_recv` with the cursor): a batch with `B.prev = k`, the cursor at
   `B.last`; schedule `applyAll(&ep, &ap)` (`Schedule.NewJob.spec` with `funcOk` from
   `EtcdServer.applyAll.spec`: pre the chain end at `k = B.prev`, post at `B.last`). On
   `expiredLeaseC` (3c's `expiredCh`: a slice of expired leases, delivered only when
   `γ.cfg.leaseExpiry`): `revokeExpiredLeases.spec`. On `errorc` (`srvNode_errorc`: 2f's
   `errChanOk`; the transport's critical errors, `stopWithDelay`'s "removed" error): log, return.
   On `s.stop` (2e's stop request): return.
7. The deferred shutdown: close `stopping`; `cancel()`; `sched.Stop()` (`□ True`) gives back the
   chain's end, the apply thread's last state: every scheduled apply is done, so no conf change or
   snapshot touches the transport after the driver stops it (2f's `trRunning`); `s.wg.Wait()` (the
   attached goroutines' resources back); `s.r.stop()` (`raftNode.stop.spec`: `rnStopped`);
   `srvStopped s γ id ds` is assembled from `rnStopped` (the WAL's durable half, the node's
   vacancy) and the apply thread's last state (the backend's commit point); `Cleanup()` (2e's: from
   `srvClosers s ds`, `srvClosed ds`); `close(done)` deposits `srvStopped s γ id ds ∗ srvClosed ds`
   in the escrow 2e's `srvRunning` claims (`srvStopped_disk`: 2e's `memberDisk γ.etcd id ds`).

**K4-K6 through this loop**: every entry is applied in log order, after raft committed it, by the
FIFO chain; the history is the cluster's (`histAt`), so a member's restart (from `memberDisk`) or a
snapshot install continues it.

**Changes** from `specs-ref`'s `EtcdServer.run.spec`: one opaque `srvRunTok` in place of
`isServerRunC C s γ ci TM E ρ γr Er γn γg γcx γd v b ai₀ at₀ c₀ x₀ (srvStopReq ...) (srvDoneInv ...)`
(19 parameters); no auth-mode component, no receipt bound (`etcdState_revFits` is the cluster's,
W0's K7), **no restart premises** (the eight R2d'a premises, two of them found false: a restart is
a start whose `srvRunTok` 2e builds from the member's durable state, with the backend ahead of the
WAL allowed, `c₀ ≥ p₀.appliedi`, and no window token); no `σ.b = 0` scope (any snapshot). Round 1:
the directories `ds` (the stop's deposit is 2e's `memberDisk`), the `applyc` cursor, `errorc`.

**Margin**: none (a goroutine; the stop's deposit is in `srvStarted`'s `done` protocol).

**Scope** (verify round, A8-provability F3; a decision for the user): the `errorc` arm (a member
that applied its own removal, `stopWithDelay`; rafthttp's critical errors) runs the shutdown and
`Cleanup` while request-path calls may hold `srvGate` shares, closing the backend under their reads
(`issues/etcd-read-after-backend-close-panic.md`). No proof of this spec closes on that arm as the
gate stands: either the fork's gate in the Go code (reads take it shared, `Cleanup` exclusively,
later reads fail with `ErrStopped`: 2e's Q7 option), or a scope premise that the program's
request-path calls are drained before a self-stop, which no serving program can establish. Also
(A10-completeness O1) no hash runs during a snapshot install (`applySnapshot`'s scope).

Changes: verify-round: takes and gives back the thread's `threadTok` (A7-provability F2: `s.Logger()`, `createMergedSnapshotMessage`, `newSnapshotReaderCloser` take one). `run`'s is the fresh token of `start`'s `go s.run()` (Perennial's `wp_fork_tok_body`); the apply jobs' is the scheduler worker's, lent to each job (`Schedule.funcOk`). The `srvMember` that `Logger` takes comes from `srvNode_member`.
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

/-- **The apply loop**: runs until stopped; its shutdown deposits what the stopped member leaves
(`srvStopped`, with `Cleanup`'s `srvClosed`) where the stop right (2e's) claims it. -/
def EtcdServer.run.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat) (ds : Config.Dirs),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ srvStarted s γ id ∗ srvRunTok s γ id ds ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"run")) (Val #()))
  {{ RET #(); threadTok }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
