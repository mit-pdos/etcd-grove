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
  the records at `m`'s index, keeping the entries above it when the log holds `m`'s entry (a
  snapshot of the applied log) and none otherwise (a received snapshot that conflicts).
* **The contract** (`isRNWalR`): `Save` and `SaveSnap` update the records atomically (the raft
  loop and the apply thread both write the WAL), within the cases etcd's server uses (entries
  above the records' base and at most one past their last; a snapshot at or above the base), and
  fail only on I/O (`walSaveOk`).
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

/-- **The records after `SaveSnap(m)`** (the fork's `ReadAll`, from that record): they start at
`m`'s index and term, with the snapshot `m` (no data: the WAL keeps the metadata only); the entries
above it kept when the log holds `m`'s entry (a snapshot of the applied log), dropped otherwise (a
received snapshot whose log conflicts with it: raft discarded that log). The hard state kept. -/
def walSaveSnap (σ : StorContents) (m : SnapshotMetadataM) : StorContents :=
  { σ with
    base := entryID.mk m.Term' m.Index'
    snap := some (SnapshotM.mk [] m)
    ents := if plogTermAt σ.base σ.ents m.Index' = some m.Term' then
        σ.ents.drop (uint.nat m.Index' - σ.b) else [] }

/-- `Save`'s case the server uses: entries above the records' base, the first at most one past
their last (else `ReadAll` fails, `ErrSliceOutOfRange`). -/
def WalSaveOk (σ : StorContents) (es : List EntryM) : Prop :=
  ∀ e0, es.head? = some e0 → σ.b < uint.nat e0.Index' ∧ uint.nat e0.Index' ≤ σ.last + 1

/-- `SaveSnap`'s case the server uses: at or above the records' base. -/
def WalSnapOk (σ : StorContents) (m : SnapshotMetadataM) : Prop :=
  σ.b ≤ uint.nat m.Index'

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
    WalSaveOk σ es ∧
      StorageHolds (readyDurable st.durable (phsNext st.hardState h) none es) (walSave σ h es)

/-- (DRAFT, R2b-1's proof) **A batch with a snapshot, saved** (`SaveSnap` of its snapshot, then
`Save`): as `walSave_holds_stmt`, through the snapshot's records. -/
def walSnapSave_holds_stmt : Prop :=
  ∀ (st : NodeDriverState) (σ : StorContents) (ce : List LogEntry) (es : List EntryM)
    (h : HardStateM) (l : SnapLoan),
    StorageHolds st.durable σ → σ.hs = st.hardState → ReadyRestFacts st ce es h (some l) →
    WalSnapOk σ l.snap.Metadata' ∧ WalSaveOk (walSaveSnap σ l.snap.Metadata') es ∧
      StorageHolds (readyDurable st.durable (phsNext st.hardState h) (some l) es)
        (walSave (walSaveSnap σ l.snap.Metadata') h es)

/-- (DRAFT, R2b-1's proof) **The apply thread's own snapshot keeps the WAL holding the durable
state**: a snapshot at an index `k` within the saved commit, whose term is the durable log's at
`k` (the applied log is the committed log, which the durable log holds through the commit). -/
def walOwnSnap_holds_stmt : Prop :=
  ∀ (S : RaftState) (σ : StorContents) (m : SnapshotMetadataM),
    StorageHolds S σ → uint.nat m.Index' ≤ σ.commit →
    plogTermAt S.base S.ents m.Index' = some m.Term' →
    WalSnapOk σ m ∧ StorageHolds S (walSaveSnap σ m)

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

/-- (DRAFT, R2b-1) **The WAL contract with its records** (`isRNWal`'s, trust boundary): `Save` and
`SaveSnap` as atomic updates of the records (the raft loop and the apply thread both write the
WAL, so the records live in an invariant), in the cases the server uses (`WalSaveOk`,
`WalSnapOk`), failing only on I/O (`walSaveOk`, in place of `Save`'s any error today). `Close` and
`Sync` as `isRNWal`'s. -/
def isRNWalR (st : GoInterface) : IProp GF :=
  letI w := storage.walOf st
  iprop(isRNWal st ∗ ∃ si : GoInterfaceOk, ⌜st = GoInterface.ok si⌝ ∗
    □ (∀ (q : Qp) (hp : Loc) (hs : HardStateModel) (sl : GoSlice) (esL : List Loc)
        (es : List EntryModel) (Q : IProp GF),
      {{ storage.walOpen w q ∗ hardStateAt hp hs ∗ sl ↦*□ esL ∗ entriesAt esL es ∗
          AU <{ ∃∃ (σ : StorContents), walRecs w σ ∗ ⌜WalSaveOk σ (es.map EntryModel.toM)⌝ }>
            @ ⊤, ∅ <{ walRecs w (walSave σ hs.toM (es.map EntryModel.toM)), COMM Q }> }}
        (App (App (Val #(methods si.ty go!"Save" si.v)) (Val #hp)) (Val #sl))
      {{ (err : GoInterface), RET #err; storage.walOpen w q ∗
          ((⌜err = GoInterface.nil⌝ ∗ Q) ∨ ⌜¬ storage.walSaveOk⌝) }}) ∗
    □ (∀ (q : Qp) (sn mp : Loc) (dq dq' : DFrac) (md : SnapshotMetadataM) (Q : IProp GF),
      {{ storage.walOpen w q ∗ sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗
          smPtsV mp dq' md ∗
          AU <{ ∃∃ (σ : StorContents), walRecs w σ ∗ ⌜WalSnapOk σ md⌝ }>
            @ ⊤, ∅ <{ walRecs w (walSaveSnap σ md), COMM Q }> }}
        (App (Val #(methods si.ty go!"SaveSnap" si.v)) (Val #sn))
      {{ (err : GoInterface), RET #err; storage.walOpen w q ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smPtsV mp dq' md ∗
          ((⌜err = GoInterface.nil⌝ ∗ Q) ∨ ⌜¬ storage.walSaveOk⌝) }}))

/-- (DRAFT, R2b-1) **The records' commit index is at least `n`** (persistent; opaque until R2b-1's
proof, a lower bound of a ghost counter the durability invariant keeps at `σ.commit`): what the
raft loop's `notifyc` hands the apply thread after a `Save` (the apply thread snapshots only after
it, `applyAll`'s `<-apply.notifyc`), so that its snapshot is within the saved commit. -/
opaque walCommitLb (γ : RNNames) (n : Nat) : IProp GF

/-- The namespace of the durability invariant. -/
def rnDurN : Namespace := nroot.@"rnDur"

/-- (DRAFT, R2b-1) **The durability invariant** of the raft wrapper of names `γ`, over its WAL
`w`: the node's durable state `S` (`raftState`, which *enter* moves, under a later: it holds an
invariant) and the WAL's records `σ` holding it (`StorageHolds`). The loop's driver knows the
records' hard state is the last it handed (R2b-1's proof: a half of a ghost variable here, the
other half in the loop's `rnDrv`), and the records' commit has lower bounds (`walCommitLb`). The
raft loop's `Save` fires *enter* and the records' update in one step; the apply thread's
`SaveSnap` moves the records only (`walOwnSnap_holds_stmt`). -/
def rnDurInv (γ : RNNames) (w : Loc) : IProp GF :=
  inv rnDurN iprop(∃ (S : RaftState) (σ : StorContents),
    ▷ raftState γ.node.cl γ.id S ∗ walRecs w σ ∗ ⌜StorageHolds S σ⌝)

/-- (DRAFT, R2b-1) **The receive, entering at the `Save`** (`rn_ready_recv`'s new form, a
statement for R2b-1's proof): from the idle driver's view without the durable state (the
invariant holds it), the busy state holds *enter* unfired (`readyEnter` at the state after the
`Ready`), which the loop fires inside the `Save`'s update. Stated for the case without a snapshot;
the snapshot case is alike. -/
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
