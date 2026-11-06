/-
**The WAL's durability for the raft loop** (the restart plan's R2b-1, 2026-11-02 to 2026-11-03;
`notes/restart-plan.md`, "R2b-1"). Lean-first (no Rocq counterpart). The WAL's records, model and
contract are the WAL's API (`storage/WalRecs.lean`, `etcdserver/WalApi.lean`); here what ties them
to raft:

* **The pure laws** (stage 2): the records keep holding the durable state across a saved batch with
  or without a received snapshot (`walSave_holds`, `walSnapSave_holds`) and across the member's own
  snapshot (`walOwnSnap_holds`); a received batch is a `Save` step of the loop's view
  (`walSaveStep_ready`, `walSnapSteps_ready`), the apply thread's own snapshot one too
  (`walOwnSnapStep`).
* **The durability invariant** (`rnDurInv`, over the ghost names `WalNames`): until the stop takes
  the records, the loop's view `WalView` (half of it; the other half the loop's) and the records it
  describes (`walAsViewed`: `ViewOk`), the handed log as a monotone list (`walCommitLb`).
  Allocated over a fresh WAL (`rnDur_alloc`).
* **Its accessors**: the loop's `Save` and `SaveSnap` (`rnDur_save_au`, `rnDur_saveSnap_au`), the
  apply thread's own `SaveSnap` (`rnDur_ownSnap_au`), as the WAL contract's atomic updates; the
  stop's taking the records out (`rnDur_take`).

The loop enters a batch at its receive (the user's choice, 2026-11-03), so the view is at the durable
state before the batch until the `Save` moves it; at every idle point the records hold the node's
durable state. A failed `Save` is I/O (`¬ storage.walSaveOk`, the user's choice): no failed state.
-/
module

public import Proof.go_etcd_io.raft.v3.NodeApiVocab
public import Proof.go_etcd_io.raft.v3.InvNodeRule
public import Perennial.Ghost.MonoList
public import Proof.go_etcd_io.etcd.server.v3.storage.WalRecs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section model
variable [GooseExts]

/-- **A fresh WAL holds a fresh node** (proved: `walFresh_holds`) (as `kvBoot_holds`). -/
def walFresh_holds_stmt : Prop := StorageHolds RaftState.init walFresh

/-- (proved: `walSave_holds`) **A batch without a snapshot, saved, keeps the WAL holding the durable
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

/-- (proved: `walSnapSave_holds`) **A batch with a snapshot, saved** (`SaveSnap` of its snapshot, then
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

/-- (proved: `walOwnSnap_holds`) **The apply thread's own snapshot keeps the WAL holding the durable
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

/-! ### The pure laws, proved (R2b-1's stage 2, 2026-11-03) -/

section laws
variable [GooseExts]

theorem walFresh_holds : walFresh_holds_stmt := by
  unfold walFresh_holds_stmt StorageHolds walFresh
  refine ⟨Int.le_refl _, ?_, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [plogTermAt, RaftState.init]
  · rfl
  · simp [StorContents.b, StorContents.commit]
  · simp [StorContents.commit, RaftState.init]
  · simp [StorContents.commit, RaftState.init]
  · intro sv h; cases h
  · intro h; exact absurd rfl h

theorem appendEnts_nil (b : entryID) (old : List EntryM) : appendEnts b old [] = old := rfl

theorem appendEnts_cons (b : entryID) (old : List EntryM) (e0 : EntryM) (rest : List EntryM)
    (hb : uint.Z b.index' < uint.Z e0.Index') :
    appendEnts b old (e0 :: rest) =
      old.take ((uint.Z e0.Index' - uint.Z b.index' - 1).toNat) ++ (e0 :: rest) := by
  have h0 : (uint.Z b.index' + 1 - uint.Z e0.Index').toNat = 0 := by omega
  show plogTruncateAppend b old (List.drop (uint.Z b.index' + 1 - uint.Z e0.Index').toNat
    (e0 :: rest)) = _
  rw [h0, List.drop_zero]
  rfl

/-- A term found in a log is at an index within it. -/
theorem plogTermAt_some_le (b : entryID) (es : List EntryM) (i t : w64)
    (h : plogTermAt b es i = some t) :
    uint.Z b.index' ≤ uint.Z i ∧ uint.Z i ≤ uint.Z b.index' + es.length := by
  unfold plogTermAt at h
  split at h
  · cases h
  · next h1 =>
    split at h
    · next h2 => constructor <;> omega
    · next h2 =>
      have hlt : (uint.Z i - uint.Z b.index' - 1).toNat < es.length := by
        rcases Nat.lt_or_ge (uint.Z i - uint.Z b.index' - 1).toNat es.length with hlt | hge
        · exact hlt
        · rw [List.getElem?_eq_none hge] at h; cases h
      constructor <;> omega

/-- Appending entries from `e0` on (truncating there) keeps the terms below `e0`. -/
theorem plogTermAt_take_append (b : entryID) (old new : List EntryM) (e0 : EntryM) (i : w64)
    (hi : uint.Z i ≤ uint.Z b.index' + old.length) (he : uint.Z i < uint.Z e0.Index') :
    plogTermAt b (old.take ((uint.Z e0.Index' - uint.Z b.index' - 1).toNat) ++ new) i =
      plogTermAt b old i := by
  unfold plogTermAt
  split
  · rfl
  · split
    · rfl
    · next h1 h2 =>
      congr 1
      rw [List.getElem?_append_left (by rw [List.length_take]; omega)]
      rw [List.getElem?_take_of_lt (by omega)]

/-- Dropping to a later base commutes with a truncate-append past it. -/
theorem drop_take_append (l new : List EntryM) (d k : Nat) (hd : d ≤ k) (hl : d ≤ l.length) :
    (l.take k ++ new).drop d = (l.drop d).take (k - d) ++ new := by
  rw [List.drop_append_of_le_length (by rw [List.length_take]; omega), List.drop_take]

theorem walSave_holds : walSave_holds_stmt := by
  intro st σ ce es h Hh Hhs Hr Hcons
  unfold StorageHolds at Hh
  obtain ⟨H1, H2, H3, H4, H5, H6, Hw, H7, H8, H9⟩ := Hh
  simp only [ReadyRestFacts] at Hr
  obtain ⟨R1, R2, R3, R4, R5, R6, R7⟩ := Hr
  have Hc : σ.commit = uint.nat st.hardState.Commit' := by
    simp only [StorContents.commit, Hhs]
  cases es with
  | nil =>
    refine ⟨?_, ?_⟩
    · intro e0 he; simp at he
    unfold StorageHolds
    simp only [walSave, appendEnts_nil, readyDurable, RaftState.next, Option.map_none,
      Option.isSome_none, List.isEmpty_nil, Bool.not_true, Bool.or_false, Bool.false_eq_true,
      ↓reduceIte, StorContents.b, StorContents.commit, Hhs] at *
    refine ⟨H1, H2, H3, trivial, trivial, by omega, by omega, Nat.le_refl _, ?_, H9⟩
    intro sv hsv
    have := H8 sv hsv
    omega
  | cons e0 rest =>
    have R6' := R6 e0 rfl
    have R3' := R3 e0 rfl
    have h6 := H6
    have hc := Hc
    unfold StorContents.b StorContents.commit at h6 hc
    have hσe : uint.Z σ.base.index' < uint.Z e0.Index' := by word
    have hSe : uint.Z st.durable.base.index' < uint.Z e0.Index' := by word
    have hlen := (plogTermAt_some_le _ _ _ _ H2).2
    unfold RaftState.entsFrom at H3
    refine ⟨?_, ?_⟩
    · intro e1 he1
      simp only [List.head?_cons, Option.some.injEq] at he1
      subst he1
      refine ⟨by unfold StorContents.b; word, ?_, fun j e hj => Hcons j e e0 rfl hj⟩
      unfold StorContents.last StorContents.b
      unfold RaftState.last at R3'
      rw [H3, List.length_drop]
      word
    · unfold StorageHolds
      simp only [walSave, readyDurable, RaftState.next, Option.map_none, Option.isSome_none,
        List.isEmpty_cons, Bool.not_false, Bool.or_true, ↓reduceIte, StorContents.b,
        StorContents.commit, Hhs]
      rw [appendEnts_cons _ _ _ _ hσe, appendEnts_cons _ _ _ _ hSe]
      refine ⟨H1, ?_, ?_, trivial, trivial, ?_, ?_, ?_, ?_, ?_⟩
      · rw [plogTermAt_take_append _ _ _ _ _ hlen hσe]; exact H2
      · unfold RaftState.entsFrom
        simp only
        rw [H3, drop_take_append _ _ _ _ (by omega) (by omega)]
        congr 2
        omega
      · simp only [StorContents.b, StorContents.commit] at H6 Hc ⊢
        omega
      · exact Nat.le_refl _
      · exact Nat.le_refl _
      · intro sv hsv
        have := H8 sv hsv
        simp only [StorContents.b, StorContents.commit] at this Hc ⊢
        omega
      · simpa using H9
theorem walOwnSnap_holds : walOwnSnap_holds_stmt := by
  intro S σ m Hh Hk Ht
  unfold walSaveSnap
  split
  · exact Hh
  · next hlt =>
    have hk : σ.b ≤ uint.nat m.Index' := by omega
    have Ht' := Ht hk
    have hc : uint.nat m.Index' ≤ σ.commit := Hk
    unfold StorageHolds at Hh ⊢
    obtain ⟨H1, H2, H3, H4, H5, H6, Hw, H7, H8, H9⟩ := Hh
    unfold RaftState.entsFrom at H3 ⊢
    simp only [StorContents.b, StorContents.commit] at *
    refine ⟨by word, Ht', ?_, H4, H5, by omega, Hw, H7, ?_, fun _ => rfl⟩
    · rw [H3, List.drop_drop]
      congr 1
      word
    · intro sv hsv
      simp only [Option.some.injEq] at hsv
      subst hsv
      simp only
      omega

theorem walSnapSave_holds : walSnapSave_holds_stmt := by
  intro st σ ce es h l Hh Hhs Hr Hcons
  unfold StorageHolds at Hh
  obtain ⟨H1, H2, H3, H4, H5, H6, Hw, H7, H8, H9⟩ := Hh
  simp only [ReadyRestFacts] at Hr
  obtain ⟨R1, R2, R3, R4, R5⟩ := Hr
  have h6 := H6
  unfold StorContents.b StorContents.commit at h6
  rw [Hhs] at h6
  have hnlt : ¬ uint.nat l.snap.Metadata'.Index' < σ.b := by
    unfold StorContents.b; omega
  have hnle : ¬ uint.nat l.snap.Metadata'.Index' ≤ σ.commit := by
    unfold StorContents.commit; rw [Hhs]; omega
  have hσ1 : walSaveSnap σ l.snap.Metadata' =
      { σ with base := entryID.mk l.snap.Metadata'.Term' l.snap.Metadata'.Index',
               snap := some (SnapshotM.mk [] l.snap.Metadata'), ents := [] } := by
    unfold walSaveSnap; simp only [hnlt, hnle, ↓reduceIte]
  rw [hσ1]
  -- the entries start right past the snapshot
  have hA : appendEnts (entryID.mk l.snap.Metadata'.Term' l.snap.Metadata'.Index') [] es = es := by
    cases es with
    | nil => rfl
    | cons e0 rest =>
      have h0 := Hcons 0 e0 rfl
      rw [appendEnts_cons _ _ _ _ (by simp only; word)]
      simp
  refine ⟨?_, ?_⟩
  · intro e0 he0
    have h0 := Hcons 0 e0 (by cases es <;> simp_all)
    refine ⟨by unfold StorContents.b; simp only; omega, by
      unfold StorContents.last StorContents.b; simp only; omega, ?_⟩
    intro j e hj
    have := Hcons j e hj
    omega
  · unfold StorageHolds
    simp only [walSave, readyDurable, RaftState.next, Option.map_some, Option.isSome_some,
      Bool.true_or, ↓reduceIte, StorContents.b, StorContents.commit, Hhs]
    rw [hA]
    refine ⟨Int.le_refl _, ?_, ?_, trivial, trivial, ?_, Nat.le_refl _, Nat.le_refl _, ?_, ?_⟩
    · unfold plogTermAt; simp
    · unfold RaftState.entsFrom; simp
    · exact R4
    · intro sv hsv
      simp only [Option.some.injEq] at hsv
      subst hsv
      simp only
      omega
    · intro hne; exact absurd rfl hne
end laws

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- (R2b-1, round 3) **The ghost names of a WAL's durability**: the loop's view (a ghost
variable, half in the invariant, half the raft loop's: the durable state, the records' hard state,
the received snapshot whose `Save` is pending if any, the log handed at the last `Save`; round 2
review F1/F2, as kvdurable's writer variable), the handed log (a monotone list: `walCommitLb`), the
loop's "not stopped" token `ok`, the stop's claim and the apply thread's token (the three in the
invariant once the stop took the records; round 2 review F4: each thread rules the taken state out
with its token). -/
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

/-- A log entry is countable (raft's own instance, `InvApi.lean`'s, is not exported to the
server). -/
instance logEntry_countable_wal [GooseExts] : Pos.Countable LogEntry :=
  .ofInjective (fun e => Pos.Countable.encode (e.term, e.type, e.data))
    (by
      rintro ⟨_, _, _⟩ ⟨_, _, _⟩ h
      have h := Pos.encode_inj h
      simp_all)

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

/-- (R2b-1, round 4; round 3 review H2: a prefix, not a length, so that the apply thread
learns the handed log's terms) **The handed log extends `l`** (persistent): a lower bound of the
invariant's monotone list. What the raft loop's `notifyc` hands the apply thread after a `Save`
(it snapshots only after it, `applyAll`'s `<-apply.notifyc`): the log it applied is a prefix, so
its snapshot's index is within the saved commit and its term the durable log's there
(`DurAgrees`). -/
def walCommitLb (ν : WalNames) (l : List LogEntry) : IProp GF := monoListLbOwn ν.cm l

instance walCommitLb_persistent (ν : WalNames) (l : List LogEntry) :
    Persistent (walCommitLb (GF := GF) ν l) := by
  unfold walCommitLb; infer_instance

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

/-- (2026-11-03, R2b-1 stage 4) **The records the view `v` describes**, from the records `σ` before
its pending received snapshot: `σ`, or `σ` after the snapshot's `SaveSnap`. -/
def recsOf (v : WalView) (σ : StorContents) : StorContents :=
  match v.pend with | none => σ | some m => walSaveSnap σ m

/-- (2026-11-03, R2b-1 stage 4) **The records `σ` (before a pending snapshot) describe the view `v`**
(pure; `walAsViewed`'s): they hold its durable state, with its hard state, the handed log ending
between their base and their commit and the durable log agreeing with it, below a pending
snapshot. -/
def ViewOk (v : WalView) (σ : StorContents) : Prop :=
  StorageHolds v.S σ ∧ σ.hs = v.hs ∧ σ.b ≤ v.l.length ∧ v.l.length ≤ σ.commit ∧
    DurAgrees v.S v.l ∧ (∀ m, v.pend = some m → σ.commit < uint.nat m.Index')

/-- (R2d, Q14 (a), 2026-11-06; DRAFT) **The records' snapshot certificate** (persistent): the
records `σ` start at index `0`, or their snapshot is the snapshot of no data at their base
(`walSaveSnap`'s `SnapshotM.mk [] m`), valid in the cluster `cl` (`snapshotValid`). What a restart's
`MemoryStorage` needs to attach to raft at the records' base (`restartStorage`, R2d-6; Q14), carried
from the two `SaveSnap`s (`rnDur_saveSnap_au`, `rnDur_ownSnap_au`) to the stop's image
(`rnDur_take`). -/
def walSnapCert (cl : Cluster) (σ : StorContents) : IProp GF :=
  iprop(⌜σ.b = 0⌝ ∨ ∃ m : SnapshotMetadataM,
    ⌜σ.snap = some (SnapshotM.mk [] m) ∧ uint.nat m.Index' = σ.b⌝ ∗
      snapshotValid cl (SnapshotM.mk [] m))

instance walSnapCert_persistent (cl : Cluster) (σ : StorContents) :
    Persistent (walSnapCert (GF := GF) cl σ) := by
  unfold walSnapCert; infer_instance

instance walSnapCert_timeless (cl : Cluster) (σ : StorContents) :
    Timeless (walSnapCert (GF := GF) cl σ) := by
  unfold walSnapCert snapshotValid; infer_instance

/-- The fresh records' certificate: at index `0`. -/
theorem walSnapCert_fresh (cl : Cluster) : ⊢ walSnapCert (GF := GF) cl walFresh := by
  iintro; iunfold walSnapCert; ileft; ipureintro; rfl

/-- `Save` keeps the certificate (it keeps the base and the snapshot). -/
theorem walSnapCert_save (cl : Cluster) (σ : StorContents) (h : HardStateM) (es : List EntryM) :
    walSnapCert (GF := GF) cl (walSave σ h es) = walSnapCert cl σ := rfl

/-- `SaveSnap(m)` keeps the certificate, given the certificate of the snapshot it records. -/
theorem walSnapCert_saveSnap (cl : Cluster) (σ : StorContents) (m : SnapshotMetadataM) :
    walSnapCert (GF := GF) cl σ ∗ snapshotValid cl (SnapshotM.mk [] m) ⊢
      walSnapCert cl (walSaveSnap σ m) := by
  iintro ⟨Hc, #Hv⟩
  unfold walSaveSnap
  by_cases hlt : uint.nat m.Index' < σ.b
  · rw [if_pos hlt]; iexact Hc
  · rw [if_neg hlt]
    iunfold walSnapCert
    iright
    iexists m
    iframe Hv
    ipureintro
    exact ⟨rfl, rfl⟩

/-- (R2b-1, round 3) **The records as the view says**: at no pending snapshot, records `σ`
holding the durable state, between whose base and commit the handed log ends (round 2 review F3:
the handed log, not the committed one; `σ.b ≤ |l|` is what the stop's image needs, `|l| ≤
σ.commit` the apply thread's snapshot), the durable log agreeing with it; at a received snapshot
`m` whose `Save` is pending, records `walSaveSnap σ m` of such records `σ` (the apply thread's own
snapshot is then below their base and changes nothing). Either way the records' hard state is the
view's. -/
def walAsViewed (cl : Cluster) (w : Loc) (v : WalView) : IProp GF :=
  iprop(∃ σ : StorContents, walRecs w (recsOf v σ) ∗ ⌜ViewOk v σ⌝ ∗ walSnapCert cl (recsOf v σ))

instance walAsViewed_timeless (cl : Cluster) (w : Loc) (v : WalView) :
    Timeless (walAsViewed (GF := GF) cl w v) := by
  unfold walAsViewed; infer_instance

/-- (R2b-1, round 4; round 2 review F1-F5, round 3 H1, M1; 2026-11-03: no failed state, a failed
`Save` being I/O) **The durability invariant** of the raft wrapper's WAL `w`, with ghost names `ν`:
until the stop takes the records (its claim, the apply thread's token and the loop's token: each
thread, holding its own token at every access, rules the taken case out), the loop's view `v` (half
of it), the handed log as a monotone list (`walCommitLb`'s authority), and the records as the view
says (`walAsViewed`; the loop's `Save` moves the records and the view in one step, the apply
thread's own snapshot moves the records only). The node's durable state (`raftState`) is the
loop's own, beside its view half (`rnLoopTokP`), not the invariant's. -/
def rnDurInv (cl : Cluster) (ν : WalNames) (w : Loc) : IProp GF :=
  inv rnDurN iprop((∃ v : WalView, ghostVar ν.view (1 : Qp).half v ∗
      monoListAuthOwn ν.cm 1 v.l ∗ walAsViewed cl w v) ∨
    (token ν.stop ∗ token ν.app ∗ token ν.ok))

instance rnDurInv_persistent (cl : Cluster) (ν : WalNames) (w : Loc) :
    Persistent (rnDurInv (GF := GF) cl ν w) := by
  unfold rnDurInv; infer_instance

/-- (2026-11-03, R2b-1 stage 3c) **The view at the start**: the node's durable state at
`RaftState.init` (`StartNode`'s), the fresh records' hard state, nothing pending, nothing handed. -/
abbrev walView0 : WalView := ⟨RaftState.init, hsZero, none, []⟩

/-- (2026-11-03, R2b-1 stage 3c) **The durability's ghost state allocated** over a fresh WAL
(`walFresh`, what `bootstrap` gives a first start): the invariant at the start's view (the fresh
records hold `RaftState.init`, `walFresh_holds`), the loop's half of the view with its "not failed"
token, the stop's claim, the apply thread's token, and the handed log's lower bound at `[]`. -/
theorem rnDur_alloc (cl : Cluster) (w : Loc) :
    walRecs (GF := GF) w walFresh ⊢
      |={⊤}=> ∃ ν : WalNames, rnDurInv cl ν w ∗ ghostVar ν.view (1 : Qp).half walView0 ∗
        token ν.ok ∗ token ν.stop ∗ token ν.app ∗ walCommitLb ν [] := by
  iintro Hr
  imod (ghostVar_alloc (GF := GF) walView0) with ⟨%γv, Hv⟩
  imod (mono_list_own_alloc (GF := GF) ([] : List LogEntry)) with ⟨%γc, Hca, #Hcl⟩
  imod (token_alloc (GF := GF)) with ⟨%γo, Ho⟩
  imod (token_alloc (GF := GF)) with ⟨%γs, Hs⟩
  imod (token_alloc (GF := GF)) with ⟨%γa, Ha⟩
  icases (ghostVar_split_half γv 1 walView0).1 $$ Hv with ⟨Hv1, Hv2⟩
  imod (inv_alloc rnDurN ⊤ iprop((∃ v : WalView, ghostVar γv (1 : Qp).half v ∗
      monoListAuthOwn γc 1 v.l ∗ walAsViewed cl w v) ∨
    (token γs ∗ token γa ∗ token γo))) $$ [Hv1 Hca Hr] with #Hinv
  · inext
    ileft
    iexists walView0
    iframe Hv1
    isplitl [Hca]
    · iexact Hca
    iunfold walAsViewed
    iexists walFresh
    simp only [walView0, recsOf]
    iframe Hr
    isplitr
    rotate_left
    · iapply walSnapCert_fresh
    ipureintro
    unfold ViewOk
    refine ⟨walFresh_holds, rfl, Nat.le_refl _, Nat.zero_le _, ?_, ?_⟩
    · intro i e _ he; simp at he
    · intro m hm; simp at hm
  imodintro
  iexists ⟨γv, γc, γo, γs, γa⟩
  iunfold rnDurInv
  iframe Hinv Hv2 Ho Hs Ha
  iunfold walCommitLb
  iexact Hcl

/-- (2026-11-03, R2b-1 stage 4) **A `Save` from the view `v` to `v'`** (pure): from any records
`σ` the view describes (`ViewOk`), the batch `(h, es)` is in `Save`'s case (`WalSaveOk`) and the
saved records describe `v'`, at no pending snapshot. -/
def WalSaveStep (v v' : WalView) (h : HardStateM) (es : List EntryM) : Prop :=
  v'.pend = none ∧ v.l <+: v'.l ∧
    ∀ σ, ViewOk v σ → WalSaveOk (recsOf v σ) es ∧ ViewOk v' (walSave (recsOf v σ) h es)

/-- (2026-11-03, R2b-1 stage 4) **The raft loop's `Save`, as the WAL contract's atomic update**
(`walSave_spec`): from the loop's view `v` (its half) and its "not stopped" token (`ν.ok`, which
rules out the stop's taken state), a `Save` moving the view to `v'` (`WalSaveStep`): the loop's half
at `v'`, the token back and the handed log's lower bound at `v'.l`. -/
theorem rnDur_save_au (cl : Cluster) (ν : WalNames) (w : Loc) (v v' : WalView) (h : HardStateM)
    (es : List EntryM) (Hst : WalSaveStep v v' h es) :
    rnDurInv (GF := GF) cl ν w -∗ ghostVar ν.view (1 : Qp).half v -∗ token ν.ok -∗
      AU <{ ∃∃ (σ : StorContents), walRecs w σ ∗ ⌜WalSaveOk σ es⌝ }> @ ⊤, ∅
        <{ walRecs w (walSave σ h es),
          COMM ghostVar ν.view (1 : Qp).half v' ∗ token ν.ok ∗ walCommitLb ν v'.l }> := by
  obtain ⟨Hpn, Hpfx, Hstep⟩ := Hst
  iintro #Hinv Hv Hok
  iauintro
  unfold atomic_acc
  iunfold rnDurInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with (⟨%v0, Hv0, Hcm, Hw⟩ | ⟨-, -, Hok'⟩)
  rotate_left
  · iexfalso; iapply token_exclusive $$ Hok Hok'
  icombine Hv Hv0 gives %Hag
  have Hvv : v = v0 := Hag.2
  subst Hvv
  iunfold walAsViewed at Hw
  icases Hw with ⟨%σ, Hr, %Hok0, #Hc⟩
  obtain ⟨Hsok, Hok1⟩ := Hstep σ Hok0
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists recsOf v σ
  iframe Hr
  isplitr
  · ipureintro; exact Hsok
  isplit
  · iintro ⟨Hr, -⟩
    imod Hmask with -
    imod Hclose $$ [Hv0 Hcm Hr] with -
    · inext; ileft; iexists v; iframe Hv0 Hcm; iunfold walAsViewed; iexists σ; iframe Hr Hc
      ipureintro; exact Hok0
    imodintro
    iframe Hv Hok
  · iintro Hr
    imod Hmask with -
    imod (ghostVar_update_halves v' ν.view v v) $$ Hv Hv0 with ⟨Hv, Hv0⟩
    imod (monoListAuthOwn_update (GF := GF) (γ := ν.cm) v'.l Hpfx) $$ Hcm with ⟨Hcm, #Hlb⟩
    imod Hclose $$ [Hv0 Hcm Hr] with -
    · inext; ileft; iexists v'; iframe Hv0 Hcm; iunfold walAsViewed
      iexists walSave (recsOf v σ) h es
      have hr : recsOf v' (walSave (recsOf v σ) h es) = walSave (recsOf v σ) h es := by
        unfold recsOf; rw [Hpn]
      rw [hr, walSnapCert_save]
      iframe Hr Hc
      ipureintro; exact Hok1
    imodintro
    iframe Hv Hok
    iunfold walCommitLb
    iexact Hlb

/-- (2026-11-03, R2b-1 stage 4) **A received snapshot's `SaveSnap` from the view `v`** (pure): from
any records the view describes, the snapshot `m` is in `SaveSnap`'s case and the records describe
the view with `m` pending (its `Save` next). -/
def WalSnapStep (v : WalView) (m : SnapshotMetadataM) : Prop :=
  v.pend = none ∧
    ∀ σ, ViewOk v σ → (uint.nat m.Index' = σ.b → m.Term' = σ.base.term') ∧
      ViewOk { v with pend := some m } σ

/-- (2026-11-03, R2b-1 stage 4) **A batch without a snapshot is a `Save` step** (pure): from the
loop's view at the driver's state `st` (its durable state, hard state and delivered log) to the view
after the batch (`readyDurable`, the hard state after `h`, the delivered log grown by `ce`), from the
batch's facts (`ReadyRestFacts`: its entries above the hard state's commit, so the handed log keeps
its terms; the committed entries the durable log's) and its consecutive entries. -/
theorem walSaveStep_ready (st : NodeDriverState) (ce : List LogEntry) (es : List EntryM)
    (h : HardStateM) (Hr : ReadyRestFacts st ce es h none)
    (Hcons : ∀ (j : Nat) (e : EntryM) (e0 : EntryM), es.head? = some e0 → es[j]? = some e →
      uint.nat e.Index' = uint.nat e0.Index' + j) :
    WalSaveStep ⟨st.durable, st.hardState, none, st.delivered⟩
      ⟨readyDurable st.durable (phsNext st.hardState h) none es, phsNext st.hardState h, none,
        st.delivered ++ ce⟩ h es := by
  refine ⟨rfl, List.prefix_append _ _, ?_⟩
  intro σ Hv
  obtain ⟨Hh, Hhs, Hb, Hc, Hda, -⟩ := Hv
  simp only at Hh Hhs Hb Hc Hda
  simp only [recsOf]
  obtain ⟨Hsok, Hh'⟩ := walSave_holds st σ ce es h Hh Hhs Hr Hcons
  have Hr0 := Hr
  simp only [ReadyRestFacts] at Hr0
  obtain ⟨R1, R2, R3, R4, R5, R6, R7⟩ := Hr0
  have Hcσ : σ.commit = uint.nat st.hardState.Commit' := by
    simp only [StorContents.commit, Hhs]
  have HbS : uint.Z st.durable.base.index' ≤ uint.Z σ.base.index' := Hh.1
  have hσb : σ.b = uint.nat σ.base.index' := rfl
  have hCb : uint.nat (phsNext st.hardState h).Commit' < 2 ^ 64 := by word
  -- the durable base below the records' base, at most the handed log's length, below the commit
  have hBn : uint.nat st.durable.base.index' ≤ st.delivered.length := by
    simp only [StorContents.b] at Hb; word
  have hLc : st.delivered.length ≤ uint.nat st.hardState.Commit' := by rw [← Hcσ]; exact Hc
  refine ⟨Hsok, Hh', ?_, ?_, ?_, ?_, ?_⟩
  · simp only [walSave, Hhs]
  · simp only [walSave, StorContents.b, List.length_append] at Hb ⊢; omega
  · simp only [walSave, StorContents.commit, Hhs] at R4 ⊢; exact R4
  · -- the handed log's terms: the old part below the batch's first index, the committed entries
    -- the durable log's
    intro i e Hbase Hget
    simp only [readyDurable, RaftState.next, Option.map_none] at Hbase ⊢
    rcases Nat.lt_or_ge i st.delivered.length with hi | hi
    · rw [List.getElem?_append_left hi] at Hget
      have Hold := Hda i e Hbase Hget
      cases hes : es with
      | nil => simp only [appendEnts_nil]; exact Hold
      | cons e0 rest =>
        have he0 := R6 e0 (by rw [hes]; rfl)
        have hb0 : uint.Z st.durable.base.index' < uint.Z e0.Index' := by word
        rw [appendEnts_cons _ _ _ _ hb0]
        have hcm : uint.nat st.hardState.Commit' < 2 ^ 64 := by word
        have hiZ : uint.Z (W64 ((i : Int) + 1)) = (i : Int) + 1 := by
          have : (i : Int) + 1 < 2 ^ 64 := by omega
          word
        rw [plogTermAt_take_append]
        · exact Hold
        · exact (plogTermAt_some_le _ _ _ _ Hold).2
        · rw [hiZ]; word
    · obtain ⟨j, rfl⟩ : ∃ j, i = st.delivered.length + j := ⟨i - st.delivered.length, by omega⟩
      rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at Hget
      have hjce : j < ce.length := by
        rcases Nat.lt_or_ge j ce.length with h1 | h1
        · exact h1
        · rw [List.getElem?_eq_none h1] at Hget; cases Hget
      have hbl : uint.nat st.durable.base.index' ≤ st.delivered.length := hBn
      have Hent := R5 j e Hget (by simp only [readyDurable, RaftState.next, Option.map_none]; omega)
      simp only [readyDurable, RaftState.next, Option.map_none] at Hent
      have hlen : st.delivered.length + ce.length ≤ uint.nat (phsNext st.hardState h).Commit' := by
        simpa only [List.length_append] using R4
      have hiZ : uint.Z (W64 (((st.delivered.length + j : Nat) : Int) + 1)) =
          (st.delivered.length : Int) + j + 1 := by
        have : ((st.delivered.length + j : Nat) : Int) + 1 < 2 ^ 64 := by omega
        word
      unfold plogTermAt
      rw [hiZ]
      have hBZ : uint.Z st.durable.base.index' = (uint.nat st.durable.base.index' : Int) := by word
      rw [if_neg (by rw [hBZ]; omega), if_neg (by rw [hBZ]; omega)]
      have hidx : ((st.delivered.length : Int) + j + 1 - uint.Z st.durable.base.index' - 1).toNat =
          st.delivered.length + j - uint.nat st.durable.base.index' := by rw [hBZ]; omega
      rw [hidx, Hent]
      rfl
  · intro m hm; cases hm

/-- (2026-11-03, R2b-1 stage 4) **A batch with a received snapshot is a `SaveSnap` then a `Save`
step** (pure): from the loop's view at `st`, the snapshot pending, then the view after the batch at
the snapshot's log `l'` (the loan's delivered log: extending the log before, as long as the
snapshot's index, ending at its term). -/
theorem walSnapSteps_ready (st : NodeDriverState) (ce : List LogEntry) (es : List EntryM)
    (h : HardStateM) (l : SnapLoan) (l' : List LogEntry) (Hr : ReadyRestFacts st ce es h (some l))
    (Hcons : ∀ (j : Nat) (e : EntryM), es[j]? = some e →
      uint.nat e.Index' = uint.nat l.snap.Metadata'.Index' + 1 + j)
    (Hpfx : st.delivered <+: l') (Hlen : l'.length = uint.nat l.snap.Metadata'.Index')
    (Hlast : l'.getLast?.map (·.term) = some l.snap.Metadata'.Term') :
    WalSnapStep ⟨st.durable, st.hardState, none, st.delivered⟩ l.snap.Metadata' ∧
      WalSaveStep ⟨st.durable, st.hardState, some l.snap.Metadata', st.delivered⟩
        ⟨readyDurable st.durable (phsNext st.hardState h) (some l) es, phsNext st.hardState h,
          none, l'⟩ h es := by
  have Hr0 := Hr
  simp only [ReadyRestFacts] at Hr0
  obtain ⟨R1, R2, R3, R4, R5⟩ := Hr0
  refine ⟨⟨rfl, ?_⟩, ⟨rfl, Hpfx, ?_⟩⟩
  · intro σ Hv
    obtain ⟨Hh, Hhs, Hb, Hc, Hda, -⟩ := Hv
    simp only at Hh Hhs Hb Hc Hda
    have Hcσ : σ.commit = uint.nat st.hardState.Commit' := by
      simp only [StorContents.commit, Hhs]
    refine ⟨fun he => ?_, Hh, Hhs, Hb, Hc, Hda, ?_⟩
    · exfalso
      have : σ.b ≤ σ.commit := Hh.2.2.2.2.2.1
      omega
    · intro m hm
      simp only [Option.some.injEq] at hm
      subst hm
      omega
  · intro σ Hv
    obtain ⟨Hh, Hhs, Hb, Hc, Hda, -⟩ := Hv
    simp only at Hh Hhs Hb Hc Hda
    simp only [recsOf]
    obtain ⟨Hsok, Hh'⟩ := walSnapSave_holds st σ ce es h l Hh Hhs Hr Hcons
    have Hcσ : σ.commit = uint.nat st.hardState.Commit' := by
      simp only [StorContents.commit, Hhs]
    have hnlt : ¬ uint.nat l.snap.Metadata'.Index' < σ.b := by
      have : σ.b ≤ σ.commit := Hh.2.2.2.2.2.1
      omega
    have hnle : ¬ uint.nat l.snap.Metadata'.Index' ≤ σ.commit := by omega
    have hσ1 : walSaveSnap σ l.snap.Metadata' =
        { σ with base := entryID.mk l.snap.Metadata'.Term' l.snap.Metadata'.Index',
                 snap := some (SnapshotM.mk [] l.snap.Metadata'), ents := [] } := by
      unfold walSaveSnap; simp only [hnlt, hnle, ↓reduceIte]
    refine ⟨Hsok, Hh', ?_, ?_, ?_, ?_, ?_⟩
    · simp only [walSave, hσ1, Hhs]
    · simp only [walSave, hσ1, StorContents.b]; omega
    · simp only [walSave, hσ1, StorContents.commit, Hhs]; omega
    · intro i e Hbase Hget
      simp only [readyDurable, RaftState.next, Option.map_some] at Hbase ⊢
      have hi : i < l'.length := by
        rcases Nat.lt_or_ge i l'.length with h1 | h1
        · exact h1
        · rw [List.getElem?_eq_none h1] at Hget; cases Hget
      have hiE : i + 1 = uint.nat l.snap.Metadata'.Index' := by omega
      have hlast : l'.getLast? = some e := by
        rw [List.getLast?_eq_getElem?, Hlen]
        have : uint.nat l.snap.Metadata'.Index' - 1 = i := by omega
        rw [this]; exact Hget
      rw [hlast] at Hlast
      simp only [Option.map_some, Option.some.injEq] at Hlast
      unfold plogTermAt
      have hZ : uint.Z (W64 ((i : Int) + 1)) = uint.Z l.snap.Metadata'.Index' := by
        have : uint.nat l.snap.Metadata'.Index' < 2 ^ 64 := by word
        word
      rw [hZ, if_neg (Int.lt_irrefl _), if_pos rfl, Hlast]
    · intro m hm; cases hm

/-- (2026-11-03, R2b-1 stage 4) **The raft loop's `SaveSnap` of a received snapshot, as the WAL
contract's atomic update** (`walSaveSnap_spec`): the view's half moves to the snapshot pending. -/
theorem rnDur_saveSnap_au (cl : Cluster) (ν : WalNames) (w : Loc) (v : WalView) (m : SnapshotMetadataM)
    (Hst : WalSnapStep v m) :
    rnDurInv (GF := GF) cl ν w -∗ ghostVar ν.view (1 : Qp).half v -∗ token ν.ok -∗
      -- (R2d, Q14 (a), DRAFT) the received snapshot's WAL record valid (`srv_snapshotValid_record`)
      snapshotValid cl (SnapshotM.mk [] m) -∗
      AU <{ ∃∃ (σ : StorContents), walRecs w σ ∗
            ⌜uint.nat m.Index' = σ.b → m.Term' = σ.base.term'⌝ }> @ ⊤, ∅
        <{ walRecs w (walSaveSnap σ m),
          COMM ghostVar ν.view (1 : Qp).half { v with pend := some m } ∗ token ν.ok }> := by
  obtain ⟨Hpn, Hstep⟩ := Hst
  iintro #Hinv Hv Hok #Hsv
  iauintro
  unfold atomic_acc
  iunfold rnDurInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with (⟨%v0, Hv0, Hcm, Hw⟩ | ⟨-, -, Hok'⟩)
  rotate_left
  · iexfalso; iapply token_exclusive $$ Hok Hok'
  icombine Hv Hv0 gives %Hag
  have Hvv : v = v0 := Hag.2
  subst Hvv
  iunfold walAsViewed at Hw
  icases Hw with ⟨%σ, Hr, %Hok0, #Hc⟩
  obtain ⟨Hsok, Hok1⟩ := Hstep σ Hok0
  have hr0 : recsOf v σ = σ := by unfold recsOf; rw [Hpn]
  rw [hr0]
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists σ
  iframe Hr
  isplitr
  · ipureintro; exact Hsok
  isplit
  · iintro ⟨Hr, -⟩
    imod Hmask with -
    imod Hclose $$ [Hv0 Hcm Hr] with -
    · inext; ileft; iexists v; iframe Hv0 Hcm; iunfold walAsViewed; iexists σ
      rw [hr0]; iframe Hr Hc
      ipureintro; exact Hok0
    imodintro
    iframe Hv Hok
  · iintro Hr
    imod Hmask with -
    imod (ghostVar_update_halves { v with pend := some m } ν.view v v) $$ Hv Hv0 with ⟨Hv, Hv0⟩
    imod Hclose $$ [Hv0 Hcm Hr] with -
    · inext; ileft; iexists { v with pend := some m }; iframe Hv0
      isplitl [Hcm]
      · iexact Hcm
      iunfold walAsViewed
      iexists σ
      simp only [recsOf]
      iframe Hr
      isplitr
      rotate_left
      · iapply walSnapCert_saveSnap; iframe Hc Hsv
      ipureintro; exact Hok1
    imodintro
    iframe Hv Hok

/-- (2026-11-03, R2b-1 stage 5) **The apply thread's own snapshot is a WAL step** (pure): a snapshot
at an index of a handed log `l` (a prefix of the view's, `walCommitLb`), at the term `l` has there:
the records the view describes are in `SaveSnap`'s case, and after it they still describe the view
(`walOwnSnap_holds`; below a pending received snapshot it changes nothing). -/
theorem walOwnSnapStep (v : WalView) (σ : StorContents) (md : SnapshotMetadataM)
    (l : List LogEntry) (e : LogEntry) (Hpfx : l <+: v.l) (Hpos : 0 < uint.nat md.Index')
    (He : l[uint.nat md.Index' - 1]? = some e) (Ht : e.term = md.Term') (Hv : ViewOk v σ) :
    (uint.nat md.Index' = (recsOf v σ).b → md.Term' = (recsOf v σ).base.term') ∧
      ∃ σ', recsOf v σ' = walSaveSnap (recsOf v σ) md ∧ ViewOk v σ' := by
  obtain ⟨Hh, Hhs, Hb, Hc, Hda, Hpd⟩ := Hv
  have hlen : l.length ≤ v.l.length := Hpfx.length_le
  have hil : uint.nat md.Index' - 1 < l.length := (List.getElem?_eq_some_iff.1 He).1
  have hmc : uint.nat md.Index' ≤ σ.commit := by omega
  have He' : v.l[uint.nat md.Index' - 1]? = some e := by
    obtain ⟨t, ht⟩ := Hpfx
    rw [← ht, List.getElem?_append_left hil]; exact He
  have hmZ : W64 (((uint.nat md.Index' - 1 : Nat) : Int) + 1) = md.Index' := by
    have : uint.nat md.Index' < 2 ^ 64 := by word
    word
  cases hp : v.pend with
  | none =>
    simp only [recsOf, hp]
    -- the durable log's term at the snapshot's index, when at or above the records' base
    have Hterm : σ.b ≤ uint.nat md.Index' →
        plogTermAt v.S.base v.S.ents md.Index' = some md.Term' := by
      intro hb
      have hbase : uint.nat v.S.base.index' ≤ (uint.nat md.Index' - 1) + 1 := by
        have h1 := Hh.1
        simp only [StorContents.b] at hb
        word
      have := Hda (uint.nat md.Index' - 1) e hbase He'
      rw [hmZ, Ht] at this
      exact this
    refine ⟨fun heq => ?_, walSaveSnap σ md, rfl, ?_⟩
    · have h2 := Hh.2.1
      have hidx : σ.base.index' = md.Index' := by
        simp only [StorContents.b] at heq; word
      rw [hidx, Hterm (by omega)] at h2
      exact Option.some.inj h2
    · refine ⟨walOwnSnap_holds v.S σ md Hh hmc Hterm, ?_, ?_, ?_, Hda, ?_⟩
      · unfold walSaveSnap; split <;> exact Hhs
      · unfold walSaveSnap; split
        · exact Hb
        · simp only [StorContents.b]; omega
      · unfold walSaveSnap; split
        · exact Hc
        · simpa only [StorContents.commit] using Hc
      · intro m hm; rw [hp] at hm; cases hm
  | some m =>
    simp only [recsOf, hp]
    have hlt := Hpd m hp
    have hbc : σ.b ≤ σ.commit := Hh.2.2.2.2.2.1
    have hnlt : ¬ uint.nat m.Index' < σ.b := by omega
    have hb' : (walSaveSnap σ m).b = uint.nat m.Index' := by
      unfold walSaveSnap; rw [if_neg hnlt]; rfl
    refine ⟨fun heq => absurd heq (by omega), σ, ?_, Hh, Hhs, Hb, Hc, Hda, Hpd⟩
    have hbelow : uint.nat md.Index' < (walSaveSnap σ m).b := by omega
    symm
    exact if_pos hbelow

/-- (2026-11-03, R2b-1 stage 5) **The apply thread's own `SaveSnap`, as the WAL contract's atomic
update** (`walSaveSnap_spec`): with its token (`ν.app`, which rules out the stop's taken state) and a
handed log `l` it learned (`walCommitLb`) holding the snapshot's index at its term. -/
theorem rnDur_ownSnap_au (cl : Cluster) (ν : WalNames) (w : Loc) (md : SnapshotMetadataM) (l : List LogEntry)
    (e : LogEntry) (Hpos : 0 < uint.nat md.Index') (He : l[uint.nat md.Index' - 1]? = some e)
    (Ht : e.term = md.Term') :
    rnDurInv (GF := GF) cl ν w -∗ token ν.app -∗ walCommitLb ν l -∗
      -- (R2d, Q14 (a), DRAFT) the snapshot's WAL record valid (`srv_snap_make`'s, of no data)
      snapshotValid cl (SnapshotM.mk [] md) -∗
      AU <{ ∃∃ (σ : StorContents), walRecs w σ ∗
            ⌜uint.nat md.Index' = σ.b → md.Term' = σ.base.term'⌝ }> @ ⊤, ∅
        <{ walRecs w (walSaveSnap σ md), COMM token ν.app }> := by
  iintro #Hinv Ha #Hlb #Hsv
  iauintro
  unfold atomic_acc
  iunfold rnDurInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with (⟨%v, Hv, Hcm, Hw⟩ | ⟨-, Ha', -⟩)
  rotate_left
  · iexfalso; iapply token_exclusive $$ Ha Ha'
  iunfold walCommitLb at Hlb
  ihave %Hpv := mono_list_auth_lb_valid ν.cm 1 v.l l $$ Hcm Hlb
  iunfold walAsViewed at Hw
  icases Hw with ⟨%σ, Hr, %Hok0, #Hc⟩
  obtain ⟨Hpre, σ', Hσ', Hok1⟩ := walOwnSnapStep v σ md l e Hpv.2 Hpos He Ht Hok0
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists recsOf v σ
  iframe Hr
  isplitr
  · ipureintro; exact Hpre
  isplit
  · iintro ⟨Hr, -⟩
    imod Hmask with -
    imod Hclose $$ [Hv Hcm Hr] with -
    · inext; ileft; iexists v; iframe Hv Hcm; iunfold walAsViewed; iexists σ; iframe Hr Hc
      ipureintro; exact Hok0
    imodintro
    iframe Ha
  · iintro Hr
    imod Hmask with -
    imod Hclose $$ [Hv Hcm Hr] with -
    · inext; ileft; iexists v; iframe Hv Hcm; iunfold walAsViewed; iexists σ'
      rw [Hσ']; iframe Hr
      isplitr
      rotate_left
      · iapply walSnapCert_saveSnap; iframe Hc Hsv
      ipureintro; exact Hok1
    imodintro
    iframe Ha

/-- (2026-11-03, R2b-1 stage 6; the draft's `rnDurTake_stmt`, round 4) **The stop takes the records
out** (`onStop`, the loop idle, its view at no pending snapshot): with the stop's claim, the apply
thread's token (which `stopped` brings), the loop's view half and its token, the records holding the
view's durable state (the loop's own, `raftState`), between whose base and commit the handed log
ends. The invariant is left in its taken state.

(Round 3 review M2, still open for `raftNode.stop.spec`: the order is at the view's handed log
`v.l`, the stop's post at the apply side's `pre ++ A` (`rnApplyTok γ A`); equating them needs every
sent batch received.) -/
theorem rnDur_take (cl : Cluster) (ν : WalNames) (w : Loc) (v : WalView) (hp : v.pend = none) :
    rnDurInv (GF := GF) cl ν w -∗ token ν.stop -∗ token ν.app -∗
      ghostVar ν.view (1 : Qp).half v -∗ token ν.ok ={⊤}=∗
      ∃ σ : StorContents, walRecs w σ ∗
        ⌜StorageHolds v.S σ ∧ σ.b ≤ v.l.length ∧ v.l.length ≤ σ.commit⌝ ∗
        -- (R2d, Q14 (a), DRAFT) the records' snapshot certificate
        walSnapCert cl σ := by
  iintro #Hinv Hs Ha Hv Hok
  iunfold rnDurInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with (⟨%v0, Hv0, -, Hw⟩ | ⟨-, -, Hok'⟩)
  rotate_left
  · iexfalso; iapply token_exclusive $$ Hok Hok'
  icombine Hv Hv0 gives %Hag
  have Hvv : v = v0 := Hag.2
  subst Hvv
  iunfold walAsViewed at Hw
  icases Hw with ⟨%σ, Hr, %Hok0, #Hc⟩
  imod Hclose $$ [Hs Ha Hok] with -
  · inext; iright; iframe Hs Ha Hok
  imodintro
  iexists σ
  have hr : recsOf v σ = σ := by unfold recsOf; rw [hp]
  rw [hr]
  iframe Hr Hc
  ipureintro
  obtain ⟨Hh, -, Hb, Hc, -, -⟩ := Hok0
  exact ⟨Hh, Hb, Hc⟩

end defs

end EtcdGrove
end Perennial
