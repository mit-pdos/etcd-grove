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
  error as today, after which the records are some records (the loop is in `lg.Fatal` for good).
* **The durability invariant** (`rnDurInv`, over the ghost names `WalNames` and the raft loop's
  view `WalView`): the node's durable state and the records holding it (`walAsViewed`), the
  handed log between their base and commit (`walCommitLb`, which the apply thread's snapshot
  needs), a received snapshot's pending `Save`, a failed `Save`, the stop's taking the contents
  out (`rnDurTake_stmt`).
* **Entering at the `Save`**: raft's receive gives the facts the server needs before *enter*
  (`readyGotR`, a raft API change), and the raft loop fires *enter* inside the `Save`'s update,
  together with the records' change, so that the invariant is kept by the pure laws
  `walSave_holds_stmt` and `walSnapSave_holds_stmt`.
* **The apply thread's snapshot** keeps it too (`walOwnSnap_holds_stmt`).
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
    -- (R2b-1 review F2) the entries consecutive: raft's `readyRest_indices` (round 2 review F7)
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
    -- (R2b-1 review F1) the entries consecutive from past the snapshot: raft's `readySnap`
    -- (`LogIndicesOk (snapId l.snap) es`, round 2 review F7)
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

instance storContents_countable : Pos.Countable StorContents :=
  .ofInjective (fun σ => Pos.Countable.encode (σ.hs, σ.snap, σ.base, σ.ents))
    (by
      rintro ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ h
      have h := Pos.encode_inj h
      simp_all)

/-- (DRAFT, R2b-1) The ghost name of the WAL `w`'s records (opaque: one per WAL, as `walGName`). -/
opaque walRecGName (w : Loc) : GName

/-- (DRAFT, R2b-1; round 2 review F5: a ghost variable, so timeless and exclusive by proof, only its
meaning trusted, as `storage.walOpen`) **The WAL `w`'s records are `σ`**: see the file header.
`bootstrap`'s contract gives it (a first start's at `walFresh`, a restart's at the image's), `Save`
and `SaveSnap` update it (`isRNWalR`); `Close` leaves it (R2b-3: the closes' axioms make `srvFiles`
of it). The records a restart reads are those from the snapshot record of the highest index at
or below the saved commit (`recoverSnapshot`, `validSnapshotEntries`): `walSaveSnap σ m` once a
hard state commits `m` (round 2 review F9; no image is taken before). -/
def walRecs (w : Loc) (σ : StorContents) : IProp GF :=
  ghostVar (walRecGName w) 1 σ

/-- (DRAFT, R2b-1) **The WAL contract with its records** (`isRNWal`'s replacement, trust boundary;
one spec per function: R2b-1's proof puts it in `isRNWal`'s place, round 2 review F10): `Save` and
`SaveSnap` as atomic updates of the records (the raft loop and the apply thread both write the WAL,
so the records live in an invariant; `Save` holds `w.mu` across its records), `Save` in the case
the server uses (`WalSaveOk`), with any error as today: one of two updates fires, the records
saved or, on an error, some records (the user's choice, 2026-11-02: no premise that `Save` fails
only on I/O; round 2 review F4: "some records", not a token without them, so that the apply
thread's snapshot can still update them while the loop is in `lg.Fatal`). `Close` and `Sync` as
`isRNWal`'s. -/
def isRNWalR (st : GoInterface) : IProp GF :=
  letI w := storage.walOf st
  iprop(∃ si : GoInterfaceOk, ⌜st = GoInterface.ok si⌝ ∗
    □ (∀ (q : Qp) (hp : Loc) (hs : HardStateModel) (sl : GoSlice) (esL : List Loc)
        (es : List EntryModel) (Q Qf : IProp GF),
      {{ storage.walOpen w q ∗ hardStateAt hp hs ∗ sl ↦*□ esL ∗ entriesAt esL es ∗
          (AU <{ ∃∃ (σ : StorContents), walRecs w σ ∗ ⌜WalSaveOk σ (es.map EntryModel.toM)⌝ }>
            @ ⊤, ∅ <{ walRecs w (walSave σ hs.toM (es.map EntryModel.toM)), COMM Q }> ∧
           AU <{ ∃∃ (σ : StorContents), walRecs w σ }> @ ⊤, ∅
             <{ ∃ σ' : StorContents, walRecs w σ', COMM Qf }>) }}
        (App (App (Val #(methods si.ty go!"Save" si.v)) (Val #hp)) (Val #sl))
      {{ (err : GoInterface), RET #err; storage.walOpen w q ∗
          ((⌜err = GoInterface.nil⌝ ∗ Q) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ Qf)) }}) ∗
    □ ({{ storage.walOpen w 1 }} (App (Val #(methods si.ty go!"Close" si.v)) (Val #()))
      {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil ∨ ¬ storage.walCloseOk⌝ }}) ∗
    □ (∀ (q : Qp) (sn mp : Loc) (dq dq' : DFrac) (md : SnapshotMetadataM) (Q : IProp GF),
      {{ storage.walOpen w q ∗ sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗
          smPtsV mp dq' md ∗
          AU <{ ∃∃ (σ : StorContents), walRecs w σ }>
            @ ⊤, ∅ <{ walRecs w (walSaveSnap σ md), COMM Q }> }}
        (App (Val #(methods si.ty go!"SaveSnap" si.v)) (Val #sn))
      {{ (err : GoInterface), RET #err; storage.walOpen w q ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smPtsV mp dq' md ∗
          ((⌜err = GoInterface.nil⌝ ∗ Q) ∨ ⌜¬ storage.walSaveOk⌝) }}) ∗
    □ (∀ q : Qp, {{ storage.walOpen w q }} (App (Val #(methods si.ty go!"Sync" si.v)) (Val #()))
      {{ (err : GoInterface), RET #err; storage.walOpen w q }}))

/-- (DRAFT, R2b-1, round 3) **The ghost names of a WAL's durability**: the loop's view (a ghost
variable, half in the invariant, half the raft loop's: the durable state, the records' hard state,
the received snapshot whose `Save` is pending if any, the log handed at the last `Save`; round 2
review F1/F2, as kvdurable's writer variable), the handed log's length (a monotone counter:
`walCommitLb`), the "not failed" token (in the invariant once a `Save` failed), the stop's claim
and the apply thread's token (both in the invariant once the stop took the contents; round 2 review
F4: the apply thread's `SaveSnap` excludes the taken state with its token). -/
structure WalNames where
  view : GName
  cm : GName
  ok : GName
  stop : GName
  app : GName

/-- The raft loop's view of the WAL's durability: the durable state `S`, the records' hard state,
the received snapshot whose `Save` is pending (if any), the committed log handed out at the last
`Save` (the apply thread's, once the loop is idle). -/
structure WalView where
  S : RaftState
  hs : HardStateM
  pend : Option SnapshotMetadataM
  l : List LogEntry

theorem logEntries_enc_inj [GooseExts] {l1 l2 : List LogEntry}
    (h : l1.map (fun e => (e.term, e.type, e.data)) = l2.map (fun e => (e.term, e.type, e.data))) :
    l1 = l2 := by
  induction l1 generalizing l2 with
  | nil => cases l2 with
    | nil => rfl
    | cons _ _ => simp at h
  | cons x xs ih => cases l2 with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
      obtain ⟨_, _, _⟩ := x; obtain ⟨_, _, _⟩ := y
      simp only at h1 h2 h3; subst h1 h2 h3
      rw [ih h4]

instance walView_countable : Pos.Countable WalView :=
  .ofInjective (fun v => Pos.Countable.encode
      ((v.S.term, v.S.vote, v.S.base, v.S.ents, v.S.commit, v.S.wcommit), v.hs,
        v.pend.map (SnapshotM.mk []), v.l.map (fun e => (e.term, e.type, e.data))))
    (by
      rintro ⟨⟨_, _, _, _, _, _⟩, _, p1, l1⟩ ⟨⟨_, _, _, _, _, _⟩, _, p2, l2⟩ h
      have h := Pos.encode_inj h
      simp only [Prod.mk.injEq] at h
      obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7, h8, h9⟩ := h
      have h8' : p1 = p2 := by
        cases p1 <;> cases p2 <;> simp_all
      subst h1 h2 h3 h4 h5 h6 h7 h8'; rw [logEntries_enc_inj h9])

/-- (DRAFT, R2b-1) **The handed log is at least `n` long** (persistent): a lower bound of the
invariant's counter. What the raft loop's `notifyc` hands the apply thread after a `Save` (it
snapshots only after it, `applyAll`'s `<-apply.notifyc`): its snapshot's index, at most its
applied index, is at most the handed log's length, so within the saved commit. -/
def walCommitLb (ν : WalNames) (n : Nat) : IProp GF := monoNatLbOwn ν.cm n

/-- **The durable log agrees with the committed log `l`** from its base on (round 2 review F8: the
base included): what the apply thread's own snapshot needs of the durable state at its index
(`walOwnSnap_holds_stmt`'s term premise), from the committed log it applied. The raft loop keeps
it: the committed entries a `Ready` hands out above the durable base are its batch's
(`ReadyRestFacts`), a received snapshot's base is the committed log's entry at its index. -/
def DurAgrees (S : RaftState) (l : List LogEntry) : Prop :=
  ∀ (i : Nat) (e : LogEntry), uint.nat S.base.index' ≤ i + 1 → l[i]? = some e →
    plogTermAt S.base S.ents (W64 ((i : Int) + 1)) = some e.term

/-- The namespace of the durability invariant. -/
def rnDurN : Namespace := nroot.@"rnDur"

/-- (DRAFT, R2b-1, round 3) **The records as the view says**: at no pending snapshot, records `σ`
holding the durable state, between whose base and commit the handed log ends (round 2 review F3:
the handed log, not the committed one; `σ.b ≤ |l|` is what the stop's image needs, `|l| ≤
σ.commit` the apply thread's snapshot), the durable log agreeing with it; at a received snapshot
`m` whose `Save` is pending, records `walSaveSnap σ m` of such records `σ` (the apply thread's own
snapshot is then below their base and changes nothing). Either way the records' hard state is the
view's. -/
def walAsViewed (w : Loc) (v : WalView) : IProp GF :=
  iprop(∃ σ : StorContents,
    walRecs w (match v.pend with | none => σ | some m => walSaveSnap σ m) ∗
    ⌜StorageHolds v.S σ ∧ σ.hs = v.hs ∧ σ.b ≤ v.l.length ∧ v.l.length ≤ σ.commit ∧
      DurAgrees v.S v.l ∧ (∀ m, v.pend = some m → σ.commit < uint.nat m.Index')⌝)

/-- (DRAFT, R2b-1, round 3; round 2 review F1-F5) **The durability invariant** of the raft wrapper
of names `γ` over its WAL `w`, with ghost names `ν`: until the stop takes the contents (its claim
and the apply thread's token), the loop's view `v` (half of it), the node's durable state
(`raftState`, the view's; no extra later: the invariant's own suffices) and either the records as
the view says (`walAsViewed`; the raft loop fires *enter* and the records' update in one step at
its `Save`, the apply thread's own snapshot moves the records only), or, once a `Save` failed, some
records and the "not failed" token (the loop is in `lg.Fatal` for good). The counter is at the
handed log's length. -/
def rnDurInv (γ : RNNames) (ν : WalNames) (w : Loc) : IProp GF :=
  inv rnDurN iprop((∃ v : WalView, ghostVar ν.view (1 : Qp).half v ∗
      raftState γ.node.cl γ.id v.S ∗ monoNatAuthOwn ν.cm 1 v.l.length ∗
      (walAsViewed w v ∨ ((∃ σ : StorContents, walRecs w σ) ∗ token ν.ok))) ∨
    (token ν.stop ∗ token ν.app))

/-- (DRAFT, R2b-1, round 3) **The stop takes the contents out** (R2b-2's `raftNode.stop.specStop`:
`onStop`, the loop idle and not failed): with the claim, the apply thread's token (which `stopped`
brings), the loop's view at no pending snapshot (its half) and its "not failed" token, the durable
state and the records holding it, between whose base and commit the handed log ends. -/
def rnDurTake_stmt (γ : RNNames) (ν : WalNames) (w : Loc) : Prop :=
  ∀ (v : WalView), v.pend = none →
    rnDurInv (GF := GF) γ ν w ∗ token ν.stop ∗ token ν.app ∗
      ghostVar ν.view (1 : Qp).half v ∗ token ν.ok ⊢
    |={⊤}=> ▷ raftState γ.node.cl γ.id v.S ∗
      ∃ σ : StorContents, walRecs w σ ∗
        ⌜StorageHolds v.S σ ∧ σ.b ≤ v.l.length ∧ v.l.length ≤ σ.commit⌝

/-- (DRAFT, R2b-1, round 3; round 2 review F6: in place of a law over today's `readyGot`, which
cannot be proved) **What receiving a `Ready` gives, with the facts the server needs before *enter***
(raft's `readyGot`'s new body, and the receive's postcondition `readyPost`): today's, and the
delivered log after the `Ready` (`deliveredLogLb`) and its hard state's committed fact
(`committedAtTerm`), which raft's proof has, persistent, where it builds *enter* (round 2 review:
`readyRecv_open`). The server hands the batch on `applyc` (`rnApN`: `deliveredLogLb (F ++ ce)`, the
new term's `rnRtOk`) before its `Save` fires *enter*. -/
def readyGotR [StorageModel GF] (n : Loc) (γ : Cluster) (N : Namespace) (id : w64)
    (st : NodeDriverState) (rd : Ready) : IProp GF :=
  iprop(∃ (ce : List LogEntry) (es : List EntryM) (h : HardStateM) (L : Option SnapLoan)
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
        uint.Z (phsNext st.hardState h).Commit'⌝))

end defs

end EtcdGrove
end Perennial
