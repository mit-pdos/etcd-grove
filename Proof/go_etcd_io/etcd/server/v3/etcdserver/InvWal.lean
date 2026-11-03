/-
**The WAL's records, drafted** (the restart plan's R2b-1, 2026-11-02; `notes/restart-plan.md`,
"R2b-1: the WAL's records"). Lean-first (no Rocq counterpart). DRAFT: nothing proved imports this
module yet; R2b-1's proof moves its pieces into the WAL contract (`isRNWal`), the raft loop's
invariant and the receive (`rn_ready_recv`).

What a stopped member's image needs of raft (`srvDiskImage`: `StorageHolds S σ`) is that the
WAL's records hold the node's durable state. Today the server's proof enters each `Ready`'s batch
into the durable state (`raftState`) at its receive, and the WAL has an open token only
(`storage.walOpen`). R2b-1:

* **The records** (`walRecs w σ`, a trust-boundary token beside `walOpen`): what `wal.ReadAll`
  (the fork's, `goose-lean-walsnap`: the records read as the log they write,
  `nonissues/etcd-wal-stale-entries-above-snapshot.md`) returns from the WAL's last snapshot
  record: the snapshot record at `σ.base`, the hard state `σ.hs`, the entries above `σ.base`.
* **Their model** (`walSave`, `walSaveSnap`, `walFresh`): `Save(h, es)` replaces the hard state
  unless `h` is empty and truncate-appends the entries as raft's log does; `SaveSnap(m)` starts
  the records at `m`'s index, keeping the entries above it when `m` is within the saved commit (a
  snapshot of the applied log) and none when above it (a received snapshot: raft discarded its
  log), and changes nothing below the records' base (the restart opens at the highest record).
* **The contract** (`isRNWalR`): `Save` and `SaveSnap` update the records atomically (the raft
  loop and the apply thread both write the WAL), `Save` within the case etcd's server uses
  (consecutive entries above the records' base, the first at most one past their last), with any
  error as today, after which the records are not known (`walFailed`).
* **The durability invariant** (`rnDurInv`): the node's durable state and the records, the latter
  holding the former (`StorageHolds`), with the records' commit index's lower bounds
  (`walCommitLb`, which the apply thread's snapshot needs: at or below the saved commit).
* **Entering at the `Save`** (`rnReadyRecvR`): the receive keeps *enter* (`readyEnter`) unfired;
  the raft loop fires it inside the `Save`'s update, together with the records' change, so that the
  invariant's `StorageHolds` is kept by the pure laws `walSave_holds` and `walSnapSave_holds`.
* **The apply thread's snapshot** keeps `StorageHolds` too (`walOwnSnap_holds`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section model
variable [GooseExts]

/-- **The records of a fresh WAL** (`wal.Create`'s initial snapshot record at `⟨0, 0⟩`, no
entries, the zero hard state): what `bootstrap`'s first start leaves. -/
def walFresh : StorContents :=
  ⟨HardStateM.mk (W64 0) (W64 0) (W64 0), none, entryID.mk (W64 0) (W64 0), []⟩

/-- **The records after `Save(h, es)`** (the fork's `ReadAll`): the hard state replaced unless `h`
is empty (`phsNext`: an empty `HardState` is not written), the entries truncate-appended
(`appendEnts`, as raft's `MemoryStorage.Append`; for entries above the base, `ReadAll`'s
`append(ents[:offset], e)`). -/
def walSave (σ : StorContents) (h : HardStateM) (es : List EntryM) : StorContents :=
  { σ with hs := phsNext σ.hs h, ents := appendEnts σ.base σ.ents es }

/-- **The records after `SaveSnap(m)`** (the fork's `ReadAll` and `recoverSnapshot`, `ce3dbc097`):
a record below the records' base changes nothing (the restart opens the WAL at the record of the
highest index; R2b-1 review G1); otherwise they start at `m`'s index and term, with the snapshot
`m` (no data: the WAL keeps the metadata only), the entries above it kept when `m` is within the
saved commit (a snapshot of the applied log) and dropped when above it (a received snapshot: raft
discarded its log; review G2). The hard state kept. -/
def walSaveSnap (σ : StorContents) (m : SnapshotMetadataM) : StorContents :=
  if uint.nat m.Index' < σ.b then σ else
  { σ with
    base := entryID.mk m.Term' m.Index'
    snap := some (SnapshotM.mk [] m)
    ents := if uint.nat m.Index' ≤ σ.commit then σ.ents.drop (uint.nat m.Index' - σ.b) else [] }

/-- `Save`'s case the server uses: consecutive entries above the records' base, the first at most
one past their last (else `ReadAll` fails, `ErrSliceOutOfRange`, or truncates where `walSave` does
not; R2b-1 review F2: until then the first entry only). -/
def WalSaveOk (σ : StorContents) (es : List EntryM) : Prop :=
  ∀ e0, es.head? = some e0 → σ.b < uint.nat e0.Index' ∧ uint.nat e0.Index' ≤ σ.last + 1 ∧
    ∀ (j : Nat) (e : EntryM), es[j]? = some e → uint.nat e.Index' = uint.nat e0.Index' + j

/-- (DRAFT, R2b-1's proof) **A fresh WAL holds a fresh node** (as `kvBoot_holds`). -/
def walFresh_holds_stmt : Prop := StorageHolds RaftState.init walFresh

/-- (DRAFT, R2b-1's proof) **A batch without a snapshot, saved, keeps the WAL holding the durable
state**: records `σ` holding `S`, whose hard state is the loop's last handed one (`σ.hs = st`'s);
the batch's facts (`ReadyRestFacts` at no snapshot); then the records after `Save(h, es)` hold the
durable state after the batch (`readyDurable`), and `Save` is in its case. -/
def walSave_holds_stmt : Prop :=
  ∀ (st : NodeDriverState) (σ : StorContents) (ce : List LogEntry) (es : List EntryM)
    (h : HardStateM),
    StorageHolds st.durable σ → σ.hs = st.hardState → ReadyRestFacts st ce es h none →
    -- (R2b-1 review F2) the entries consecutive (raft's; a raft API law to add)
    (∀ (j : Nat) (e : EntryM) (e0 : EntryM), es.head? = some e0 → es[j]? = some e →
      uint.nat e.Index' = uint.nat e0.Index' + j) →
    WalSaveOk σ es ∧
      StorageHolds (readyDurable st.durable (phsNext st.hardState h) none es) (walSave σ h es)

/-- (DRAFT, R2b-1's proof) **A batch with a snapshot, saved** (`SaveSnap` of its snapshot, then
`Save`): as `walSave_holds_stmt`, through the snapshot's records. -/
def walSnapSave_holds_stmt : Prop :=
  ∀ (st : NodeDriverState) (σ : StorContents) (ce : List LogEntry) (es : List EntryM)
    (h : HardStateM) (l : SnapLoan),
    StorageHolds st.durable σ → σ.hs = st.hardState → ReadyRestFacts st ce es h (some l) →
    -- (R2b-1 review F1) the entries consecutive from past the snapshot: raft's (after a restore
    -- the log matches only at the snapshot), which `ReadyRestFacts` must state (a raft API law)
    (∀ (j : Nat) (e : EntryM), es[j]? = some e →
      uint.nat e.Index' = uint.nat l.snap.Metadata'.Index' + 1 + j) →
    WalSaveOk (walSaveSnap σ l.snap.Metadata') es ∧
      StorageHolds (readyDurable st.durable (phsNext st.hardState h) (some l) es)
        (walSave (walSaveSnap σ l.snap.Metadata') h es)

/-- (DRAFT, R2b-1's proof) **The apply thread's own snapshot keeps the WAL holding the durable
state**: a snapshot at an index `k` within the saved commit, whose term is the durable log's at
`k` when at or above its base (the applied log is the committed log; the durability invariant
must carry that `S`'s log agrees with the committed log delivered, R2b-1 review F5). Below the
records' base it changes nothing (review G1's fix). -/
def walOwnSnap_holds_stmt : Prop :=
  ∀ (S : RaftState) (σ : StorContents) (m : SnapshotMetadataM),
    StorageHolds S σ → uint.nat m.Index' ≤ σ.commit →
    (σ.b ≤ uint.nat m.Index' → plogTermAt S.base S.ents m.Index' = some m.Term') →
    StorageHolds S (walSaveSnap σ m)

end model

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- (DRAFT, R2b-1) **The WAL `w`'s records are `σ`** (opaque, exclusive; a trust-boundary token
beside `storage.walOpen`): see the file header. `bootstrap`'s contract gives it (a first start's
at `walFresh`, a restart's at the image's), `Save` and `SaveSnap` update it (`isRNWalR`); `Close`
leaves it (R2b-3: the closes' axioms make `srvFiles` of it). -/
opaque walRecs (w : Loc) (σ : StorContents) : IProp GF

/-- (DRAFT, R2b-1; the user's choice, 2026-11-02) **The WAL `w`'s records are not known** (opaque,
exclusive): what a failed `Save` leaves (it may have written part of its records). The raft loop
then calls `lg.Fatal`, which never returns, so it never stops, and no image is made of such a
WAL. In place of a premise that `Save` fails only on I/O. -/
opaque walFailed (w : Loc) : IProp GF

/-- (DRAFT, R2b-1) **The WAL contract with its records** (`isRNWal`'s, trust boundary): `Save` and
`SaveSnap` as atomic updates of the records (the raft loop and the apply thread both write the
WAL, so the records live in an invariant), `Save` in the case the server uses (`WalSaveOk`),
with any error as today: one of two updates fires, the records saved or, on an error, not known
(`walFailed`; the user's choice, 2026-11-02, over widening the premise `walSaveOk` to `Save`).
`Close` and `Sync` as `isRNWal`'s. (R2b-1 review F6: R2b-1's proof replaces `isRNWal`'s `Save`/`SaveSnap` by these, one spec per function; the draft conjoins
them.) -/
def isRNWalR (st : GoInterface) : IProp GF :=
  letI w := storage.walOf st
  iprop(isRNWal st ∗ ∃ si : GoInterfaceOk, ⌜st = GoInterface.ok si⌝ ∗
    □ (∀ (q : Qp) (hp : Loc) (hs : HardStateModel) (sl : GoSlice) (esL : List Loc)
        (es : List EntryModel) (Q Qf : IProp GF),
      {{ storage.walOpen w q ∗ hardStateAt hp hs ∗ sl ↦*□ esL ∗ entriesAt esL es ∗
          (AU <{ ∃∃ (σ : StorContents), walRecs w σ ∗ ⌜WalSaveOk σ (es.map EntryModel.toM)⌝ }>
            @ ⊤, ∅ <{ walRecs w (walSave σ hs.toM (es.map EntryModel.toM)), COMM Q }> ∧
           AU <{ ∃∃ (σ : StorContents), walRecs w σ }> @ ⊤, ∅ <{ walFailed w, COMM Qf }>) }}
        (App (App (Val #(methods si.ty go!"Save" si.v)) (Val #hp)) (Val #sl))
      {{ (err : GoInterface), RET #err; storage.walOpen w q ∗
          ((⌜err = GoInterface.nil⌝ ∗ Q) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ Qf)) }}) ∗
    □ (∀ (q : Qp) (sn mp : Loc) (dq dq' : DFrac) (md : SnapshotMetadataM) (Q : IProp GF),
      {{ storage.walOpen w q ∗ sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗
          smPtsV mp dq' md ∗
          AU <{ ∃∃ (σ : StorContents), walRecs w σ }>
            @ ⊤, ∅ <{ walRecs w (walSaveSnap σ md), COMM Q }> }}
        (App (Val #(methods si.ty go!"SaveSnap" si.v)) (Val #sn))
      {{ (err : GoInterface), RET #err; storage.walOpen w q ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smPtsV mp dq' md ∗
          ((⌜err = GoInterface.nil⌝ ∗ Q) ∨ ⌜¬ storage.walSaveOk⌝) }}))

/-- (DRAFT, R2b-1 round 2) **The ghost names of a WAL's durability** (allocated with the raft
wrapper, R2b-1's proof): the records' hard state (a ghost variable, half in the invariant, half the
raft loop's: the loop's driver knows the records' hard state is the last it handed), their commit
index (a monotone counter: `walCommitLb`), the pending token (in the invariant except between the
raft loop's `SaveSnap` of a received snapshot and its `Save`), the "not failed" token (in the
invariant once a `Save` failed; the loop holds it otherwise, so that at its stop the WAL is not
`walFailed`), and the stop's claim (`raftNode.stop`'s, R2b-2's `rnStopClaim`: whoever holds it
takes the contents out). -/
structure WalNames where
  hs : GName
  cm : GName
  pend : GName
  ok : GName
  stop : GName

/-- (DRAFT, R2b-1) **The records' commit index is at least `n`** (persistent): a lower bound of
the invariant's counter. What the raft loop's `notifyc` hands the apply thread after a `Save` (the
apply thread snapshots only after it, `applyAll`'s `<-apply.notifyc`), so that its snapshot is
within the saved commit. -/
def walCommitLb (ν : WalNames) (n : Nat) : IProp GF := monoNatLbOwn ν.cm n

/-- **The durable log agrees with the committed log `l`** above its base: what the apply thread's
own snapshot needs of the durable state at its index (`walOwnSnap_holds_stmt`'s term premise),
from the committed log it applied. The raft loop keeps it: the committed entries a `Ready` hands out
above the durable base are its batch's (`ReadyRestFacts`). -/
def DurAgrees (S : RaftState) (l : List LogEntry) : Prop :=
  ∀ (i : Nat) (e : LogEntry), uint.nat S.base.index' < i + 1 → l[i]? = some e →
    plogTermAt S.base S.ents (W64 ((i : Int) + 1)) = some e.term

/-- The namespace of the durability invariant. -/
def rnDurN : Namespace := nroot.@"rnDur"

/-- (DRAFT, R2b-1 round 2) **The WAL's records when they hold the durable state `S`**: records
`σ` holding it, the committed log `l` they are within, with which `S` agrees, the records' hard
state and commit in the ghost names. -/
def walHolds (γ : RNNames) (ν : WalNames) (w : Loc) (S : RaftState) : IProp GF :=
  iprop(∃ (σ : StorContents) (l : List LogEntry),
    walRecs w σ ∗ ⌜StorageHolds S σ ∧ σ.commit ≤ l.length ∧ DurAgrees S l⌝ ∗
    isCommittedLogLb γ.node.cl l ∗
    ghostVar ν.hs (1 : Qp).half σ.hs ∗ monoNatAuthOwn ν.cm 1 σ.commit)

/-- (DRAFT, R2b-1 round 2; R2b-1 review F3) **The durability invariant** of the raft wrapper of
names `γ` over its WAL `w`: until the stop takes its contents (its claim, `ν.stop`), the node's
durable state `S` (`raftState`, under a later: it holds an invariant) and either
* the records holding it (`walHolds`), with the pending token: the raft loop enters a batch and
  saves it in one step (the `Save`'s update fires *enter*), the apply thread's own snapshot moves
  the records only (`walOwnSnap_holds_stmt`);
* or a received snapshot's records saved, its `Save` pending (the loop holds the pending token):
  the records `walSaveSnap σ m` of records `σ` that held `S` (the apply thread's own snapshot is
  then below their base and changes nothing, review G1's fix);
* or a failed `Save`'s records (`walFailed`), with the "not failed" token: the loop gave it up and
  is in `lg.Fatal` for good. -/
def rnDurInv (γ : RNNames) (ν : WalNames) (w : Loc) : IProp GF :=
  inv rnDurN iprop((∃ (S : RaftState), ▷ raftState γ.node.cl γ.id S ∗
      ((walHolds γ ν w S ∗ token ν.pend) ∨
       (∃ (σ : StorContents) (m : SnapshotMetadataM) (l : List LogEntry),
          walRecs w (walSaveSnap σ m) ∗
          ⌜StorageHolds S σ ∧ σ.commit < uint.nat m.Index' ∧ σ.commit ≤ l.length ∧ DurAgrees S l⌝ ∗
          isCommittedLogLb γ.node.cl l ∗
          ghostVar ν.hs (1 : Qp).half σ.hs ∗ monoNatAuthOwn ν.cm 1 σ.commit) ∨
       (walFailed w ∗ token ν.ok))) ∨
    token ν.stop)

/-- (DRAFT, R2b-1 round 2) **The stop takes the contents out** (R2b-2's `raftNode.stop.specStop`:
`onStop`, with the loop idle, so not pending, and not failed): with the claim and the loop's
pending and "not failed" tokens, the durable state and records holding it, the committed log and
the hard state's half. -/
def rnDurTake_stmt (γ : RNNames) (ν : WalNames) (w : Loc) : Prop :=
  rnDurInv (GF := GF) γ ν w ∗ token ν.stop ∗ token ν.pend ∗ token ν.ok ⊢
    |={⊤}=> ∃ S : RaftState, ▷ raftState γ.node.cl γ.id S ∗ walHolds γ ν w S

/-- (DRAFT, R2b-1 round 2; R2b-1 review F4) **Raft's receive gives the delivered log and the
committed hard state without *enter*** (a raft API change: `readyGot` gains the last two
conjuncts). Raft's proof has both when it builds *enter* (`isCommittedLogLb`, `hsCommitted` and the
busy driver's `dlvLb` at the state after the `Ready`, all persistent), so the change hands them out
beside it. The server needs them before the `Save` for the hand-off on `applyc` (`rnApN`:
`deliveredLogLb (F ++ ce)`, the new term's `rnRtOk`), which today come from the entered driver. -/
def readyGotFacts_stmt [StorageModel GF] : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) (st : NodeDriverState) (rd : Ready),
    readyGot (GF := GF) n γ N id st rd ⊢
    ∃ (ce : List LogEntry) (es : List EntryM) (h : HardStateM) (L : Option SnapLoan)
      (ms : List QMsg) (ss : Option (w64 × StateType)),
      committedEntriesAt rd.CommittedEntries' st.delivered.length ce ∗
      isCommittedLogLb γ (st.delivered ++ ce) ∗
      (∃ rs, readStatesPts rd.ReadStates' rs ∗
        [∗list] s ∈ rs, readStateOk γ N s.RequestCtx' s.Index') ∗
      readyRest γ N id rd st ce es h L ms ss ∗
      readyLeaderMsgs γ N id st ms ss ∗
      readyEnter n γ N id st (st.afterReady ce es h L ss) ms ∗
      deliveredLogLb n γ N (st.afterReady ce es h L ss).delivered ∗
      (⌜phsNext st.hardState h = hsZero⌝ ∨
        committedAtTerm γ N (phsNext st.hardState h).Term' (phsNext st.hardState h).Commit' ∗
        ⌜((st.afterReady ce es h L ss).delivered.length : Int) ≤
          uint.Z (phsNext st.hardState h).Commit'⌝)

/-- (DRAFT, R2b-1) **The receive, entering at the `Save`** (`rn_ready_recv`'s new form, a
statement for R2b-1's proof): from the idle driver's view without the durable state (the
invariant holds it), the busy state holds *enter* unfired (`readyEnter` at the state after the
`Ready`), which the loop fires inside the `Save`'s update. Stated for the case without a snapshot;
the snapshot case is alike.

R2b-1 review round 1 (F4): too weak as drafted. The loop uses, before the `Save`, what the receive
gives today through the entered driver: the committed entries (`committedEntriesAt`,
`isCommittedLogLb`), the read states, `readyLeaderMsgs`, `readyRest` and, for the hand-off on
`applyc`, `deliveredLogLb (delivered ++ ce)` and the new hard state's term fact (`rnRtOk`), which
come from `nodeDriver` at the state after the `Ready` (`nodeDriver_deliveredLogLb`,
`nodeDriver_hardStateCommitted`). With *enter* at the `Save` (after the hand-off) the driver is not
there yet: raft's `readyGot` must give those two facts without *enter* (a raft API change), and the
receive returns today's `rnReadyData`/`rnReadySnap` minus the entered state, *enter* unfired. -/
def rnReadyRecvR_stmt (E : RNEnv GF) (γ : RNNames) : Prop :=
  ∀ (L : List EntryModel) (p : HardStateM) (S : RaftState) (r : StateType) (rd : Ready),
    letI := srvStor (GF := GF) γ.node
    iprop(rnEnvOk E γ ∗ rnReadStateBridge E γ ∗ rnCfgAt γ L ∗
      readyGot γ.nl γ.node.cl srvClusterN γ.id (rnDrvSt γ L p S r) rd) ⊢
      |={⊤}=> ∃ (ce : List LogEntry) (es : List EntryM) (h : HardStateM) (ms : List QMsg)
        (ss : Option (w64 × StateType)),
        ⌜ReadyRestFacts (rnDrvSt γ L p S r) ce es h none⌝ ∗
        readyEnter γ.nl γ.node.cl srvClusterN γ.id (rnDrvSt γ L p S r)
          ((rnDrvSt γ L p S r).afterReady ce es h none ss) ms

end defs

end EtcdGrove
end Perennial
