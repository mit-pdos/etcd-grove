/- Lean-first (no Rocq counterpart).

# The crash-aware durability invariant's pure steps (etcd-dist D6, task T2 / P5, 2026-11-25)

What the steps of `InvWalCrash.lean`'s invariant do to its pure crash facts: every complete prefix of
the WAL's history from the synced mark reads records the view accepts (`CrashReadsHold`), and the
history's read conditions (`HistReadOk`); and (P5 (b), 2026-11-26) what the history reads as at every
commit from its last saved one on (`HistReadsK`), which gives the read and `walCommitLe` of the prefix a
`Save` appends (`histReads_save`; until then the eager fold, `walRecsH`, with `walRead_of_fold`).

* a `Save` (`histOk_save`, `histReads_save`): the old prefixes keep reading what they read (the
  state before the batch, while it is pending), the new one reads the saved records (the reads at the
  `Save`'s commit, which keep a pending received snapshot again);
* a received snapshot's `SaveSnap` above the last saved commit (`crashReads_snapAbove`,
  `histReadOk_snapAbove`): the new prefix reads as the one before (the reader drops the record);
* the apply thread's own `SaveSnap` at or below the commit (`crashReads_ownSnap`, `histReadOk_ownSnap`):
  the new prefix reads the snapshot applied to the old read (`walOwnSnap_holds`);
* the *enter* (`crashReads_enter`): the pending batch's older prefixes hold the entered state, or are no
  longer crash images (the synced mark passed them).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvWalCrash

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-! ## Helpers on the reader -/

theorem walHsStep_filter_keep (c : Nat) :
    ∀ (H : WalHist) (p : HardStateM),
      (H.filter (walKeep c)).foldl walHsStep p = H.foldl walHsStep p := by
  intro H
  induction H with
  | nil => intro p; rfl
  | cons o H ih =>
    intro p
    cases o with
    | save hs es => simp only [List.filter_cons, walKeep, ite_true, List.foldl_cons]; exact ih _
    | snap m al =>
      by_cases hk : uint.nat m.Index' ≤ c
      · simp only [List.filter_cons, walKeep, hk, decide_true, ite_true, List.foldl_cons]; exact ih _
      · simp only [List.filter_cons, walKeep, hk, decide_false, Bool.false_eq_true, ite_false,
          List.foldl_cons, walHsStep]
        exact ih _

/-- **A read's hard state is the history's last saved one.** -/
theorem walRead_hs {I : WalHist} {σ : StorContents} (h : walRead I = some σ) :
    σ.hs = walLastHS I := by
  unfold walRead at h
  rw [walFoldChkFrom_fresh_hs h, walLastHS_eq, walLastHS_eq, walHsStep_filter_keep]

theorem walLastHS_snoc_snapP (I : WalHist) (m : SnapshotMetadataM) (al : Bool) :
    walLastHS (I ++ [WalOpG.snap m al]) = walLastHS I := by
  rw [walLastHS_eq, walLastHS_eq, List.foldl_append]; rfl

theorem walLastHS_snoc_saveP (I : WalHist) (h : HardStateM) (es : List EntryM) :
    walLastHS (I ++ [WalOpG.save h es]) = phsNext (walLastHS I) h := by
  rw [walLastHS_eq, walLastHS_eq, List.foldl_append]; rfl

/-- (P5) `HistCommitMono` after a record that keeps the last saved hard state's commit or raises it. -/
theorem histCommitMono_snoc {Hs : WalHist} {n : Nat} (o : WalOp) (hn : n ≤ Hs.length)
    (h : HistCommitMono Hs n)
    (hle : uint.nat (walLastHS Hs).Commit' ≤ uint.nat (walLastHS (Hs ++ [o])).Commit') :
    HistCommitMono (Hs ++ [o]) n := by
  intro j hnj hj
  by_cases hjl : j ≤ Hs.length
  · rw [List.take_append_of_le_length hjl]; exact Nat.le_trans (h j hnj hjl) hle
  · rw [List.take_of_length_le (by simp at hj ⊢; omega)]
    exact Nat.le_refl _

/-- **A snapshot record appended: the read**, by whether the reader keeps it (at or below the last
saved commit). -/
theorem walRead_snoc_snap (I : WalHist) (m : SnapshotMetadataM) (al : Bool) :
    walRead (I ++ [WalOpG.snap m al]) =
      if uint.nat m.Index' ≤ uint.nat (walLastHS I).Commit' then
        (walRead I).map (fun σ => walSaveSnap σ m)
      else walRead I := by
  unfold walRead
  rw [walLastHS_snoc_snapP, List.filter_append, walFoldChkFrom_append]
  split
  · next hk =>
    have hF : [WalOpG.snap m al].filter (walKeep (uint.nat (walLastHS I).Commit')) =
        [WalOpG.snap m al] := by simp [List.filter_cons, walKeep, hk]
    rw [hF]
    cases walFoldChkFrom walFresh (I.filter (walKeep (uint.nat (walLastHS I).Commit'))) <;> rfl
  · next hk =>
    have hF : [WalOpG.snap m al].filter (walKeep (uint.nat (walLastHS I).Commit')) = [] := by
      simp [List.filter_cons, walKeep, hk]
    rw [hF]
    cases walFoldChkFrom walFresh (I.filter (walKeep (uint.nat (walLastHS I).Commit'))) <;> rfl

/-- **`walCommitLe` across a snapshot record** (any index), given the read before it succeeds. -/
theorem walCommitLe_snoc_snap {I : WalHist} (m : SnapshotMetadataM) (al : Bool) (hcl : walCommitLe I)
    {σ : StorContents} (hr : walRead I = some σ) : walCommitLe (I ++ [WalOpG.snap m al]) := by
  unfold walCommitLe
  unfold walRead at hr
  unfold walCommitLe at hcl
  rw [walLastHS_snoc_snapP, List.filter_append]
  generalize hL : I.filter (walKeep (uint.nat (walLastHS I).Commit')) = L at hr hcl ⊢
  have hlast : σ.commit ≤ σ.last := by
    have := hcl L.length σ
    rw [List.take_length] at this
    exact this hr
  by_cases hk : walKeep (uint.nat (walLastHS I).Commit') (WalOpG.snap m al) = true
  · have hF : [WalOpG.snap m al].filter (walKeep (uint.nat (walLastHS I).Commit')) =
        [WalOpG.snap m al] := by simp [List.filter_cons, hk]
    rw [hF]
    intro n τ' hτ
    by_cases hn : n ≤ L.length
    · rw [List.take_append_of_le_length hn] at hτ
      exact hcl n τ' hτ
    · rw [List.take_of_length_le (by simp; omega), walFoldChkFrom_append, hr, Option.bind_some] at hτ
      simp only [walFoldChkFrom, Option.some.injEq] at hτ
      subst hτ
      exact walSaveSnap_commitLeP m hlast
  · have hF : [WalOpG.snap m al].filter (walKeep (uint.nat (walLastHS I).Commit')) = [] := by
      simp [List.filter_cons, hk]
    rw [hF, List.append_nil]
    exact hcl
where
  walSaveSnap_commitLeP {τ : StorContents} (m : SnapshotMetadataM) (h : τ.commit ≤ τ.last) :
      (walSaveSnap τ m).commit ≤ (walSaveSnap τ m).last := by
    unfold walSaveSnap
    split
    · exact h
    · next hlt =>
      by_cases hc : uint.nat m.Index' ≤ τ.commit
      · rw [if_pos hc]
        simp only [StorContents.commit, StorContents.last, StorContents.b, List.length_drop] at h hlt hc ⊢
        omega
      · rw [if_neg hc]
        simp only [StorContents.commit, StorContents.last, StorContents.b, List.length_nil] at h hlt hc ⊢
        omega

/-- `walIdxLe` across an appended operation. -/
theorem walIdxLe_snoc_save {B : Nat} {H : WalHist} {hs : HardStateM} {es : List EntryM}
    (h : walIdxLe B H) (he : ∀ e ∈ es, uint.nat e.Index' ≤ B) : walIdxLe B (H ++ [WalOpG.save hs es]) := by
  refine ⟨fun hs' es' e ho hmem => ?_, fun m al ho => ?_⟩
  · rcases List.mem_append.1 ho with ho | ho
    · exact h.1 hs' es' e ho hmem
    · simp only [List.mem_singleton, WalOpG.save.injEq] at ho
      obtain ⟨-, rfl⟩ := ho
      exact he e hmem
  · rcases List.mem_append.1 ho with ho | ho
    · exact h.2 m al ho
    · simp at ho

theorem walIdxLe_snoc_snap {B : Nat} {H : WalHist} {m : SnapshotMetadataM} {al : Bool}
    (h : walIdxLe B H) (hm : uint.nat m.Index' ≤ B) : walIdxLe B (H ++ [WalOpG.snap m al]) := by
  refine ⟨fun hs' es' e ho hmem => ?_, fun m' al' ho => ?_⟩
  · rcases List.mem_append.1 ho with ho | ho
    · exact h.1 hs' es' e ho hmem
    · simp at ho
  · rcases List.mem_append.1 ho with ho | ho
    · exact h.2 m' al' ho
    · simp only [List.mem_singleton, WalOpG.snap.injEq] at ho
      obtain ⟨rfl, -⟩ := ho
      exact hm

/-! ## (P5 (b)) The reads at a commit -/

theorem walRead_eq_at (I : WalHist) : walRead I = walReadAt I (uint.nat (walLastHS I).Commit') := rfl

theorem walCommitLe_eq_at (I : WalHist) :
    walCommitLe I = walCommitLeAt I (uint.nat (walLastHS I).Commit') := rfl

/-- A read at any commit ends with the history's last saved hard state. -/
theorem walReadAt_hs {I : WalHist} {c : Nat} {σ : StorContents} (h : walReadAt I c = some σ) :
    σ.hs = walLastHS I := by
  unfold walReadAt at h
  rw [walFoldChkFrom_fresh_hs h, walLastHS_eq, walLastHS_eq, walHsStep_filter_keep]

theorem walKeep_save (c : Nat) (hs : HardStateM) (es : List EntryM) :
    [WalOpG.save hs es].filter (walKeep c) = [WalOpG.save hs es] := by
  simp [List.filter_cons, walKeep]

/-- **A `Save` appended: the read at `c`** is the read before it, then the `Save`'s step. -/
theorem walReadAt_snoc_save (I : WalHist) (c : Nat) (hs : HardStateM) (es : List EntryM) :
    walReadAt (I ++ [WalOpG.save hs es]) c =
      (walReadAt I c).bind (fun τ => walFoldChkFrom τ [WalOpG.save hs es]) := by
  unfold walReadAt
  rw [List.filter_append, walKeep_save, walFoldChkFrom_append]

/-- **A snapshot record appended: the read at `c`**, by whether `c` keeps it. -/
theorem walReadAt_snoc_snap (I : WalHist) (c : Nat) (m : SnapshotMetadataM) (al : Bool) :
    walReadAt (I ++ [WalOpG.snap m al]) c =
      if uint.nat m.Index' ≤ c then (walReadAt I c).map (fun σ => walSaveSnap σ m) else walReadAt I c := by
  unfold walReadAt
  rw [List.filter_append, walFoldChkFrom_append]
  split
  · next hk =>
    have hF : [WalOpG.snap m al].filter (walKeep c) = [WalOpG.snap m al] := by
      simp [List.filter_cons, walKeep, hk]
    rw [hF]
    cases walFoldChkFrom walFresh (I.filter (walKeep c)) <;> rfl
  · next hk =>
    have hF : [WalOpG.snap m al].filter (walKeep c) = [] := by
      simp [List.filter_cons, walKeep, hk]
    rw [hF]
    cases walFoldChkFrom walFresh (I.filter (walKeep c)) <;> rfl

/-- `walCommitLeAt` across a `Save` whose read has its commit within its last index. -/
theorem walCommitLeAt_snoc_save {I : WalHist} {c : Nat} {hs : HardStateM} {es : List EntryM}
    {σ' : StorContents} (hcl : walCommitLeAt I c) (hr : walReadAt (I ++ [WalOpG.save hs es]) c = some σ')
    (hσ : σ'.commit ≤ σ'.last) : walCommitLeAt (I ++ [WalOpG.save hs es]) c := by
  unfold walCommitLeAt at hcl ⊢
  unfold walReadAt at hr
  rw [List.filter_append, walKeep_save] at hr ⊢
  exact walCommitLeFrom_snoc hcl hr hσ

/-- `walCommitLeAt` across a snapshot record (any index), given the read before it succeeds. -/
theorem walCommitLeAt_snoc_snap {I : WalHist} {c : Nat} (m : SnapshotMetadataM) (al : Bool)
    (hcl : walCommitLeAt I c) {σ : StorContents} (hr : walReadAt I c = some σ) :
    walCommitLeAt (I ++ [WalOpG.snap m al]) c := by
  unfold walCommitLeAt at hcl ⊢
  unfold walReadAt at hr
  rw [List.filter_append]
  generalize hL : I.filter (walKeep c) = L at hr hcl ⊢
  have hlast : σ.commit ≤ σ.last := by
    have := hcl L.length σ
    rw [List.take_length] at this
    exact this hr
  by_cases hk : uint.nat m.Index' ≤ c
  · have hF : [WalOpG.snap m al].filter (walKeep c) = [WalOpG.snap m al] := by
      simp [List.filter_cons, walKeep, hk]
    rw [hF]
    exact walCommitLeFrom_snoc hcl (walFoldChkFrom_snoc_snap hr)
      (walCommitLe_snoc_snap.walSaveSnap_commitLeP m hlast)
  · have hF : [WalOpG.snap m al].filter (walKeep c) = [] := by
      simp [List.filter_cons, walKeep, hk]
    rw [hF, List.append_nil]
    exact hcl

theorem recsAt_hs (v : WalView) (σ : StorContents) (c : Nat) : (recsAt v σ c).hs = σ.hs := by
  unfold recsAt
  split
  · rfl
  · split
    · exact walSaveSnap_hs _ _
    · rfl

theorem recsOf_hs (v : WalView) (σ : StorContents) : (recsOf v σ).hs = σ.hs := by
  unfold recsOf
  split
  · rfl
  · exact walSaveSnap_hs _ _

/-- **The reads give the history's last saved hard state** (the records' `hs`). -/
theorem histReadsK_hs {v : WalView} {σ : StorContents} {Hs : WalHist} (h : HistReadsK v σ Hs) :
    walLastHS Hs = σ.hs := by
  have h0 := (h _ (Nat.le_refl _)).1
  rw [← walReadAt_hs h0, recsAt_hs]

/-- **At the last saved commit, the history reads as the records** (a pending received snapshot is
above it: `ViewOk`), along a fold with its commit within its last index. -/
theorem histReadsK_read {v : WalView} {σ : StorContents} {Hs : WalHist} (h : HistReadsK v σ Hs)
    (hv : ViewOk v σ) : walRead Hs = some σ ∧ walCommitLe Hs := by
  have hc0 := histReadsK_hs h
  obtain ⟨h1, h2⟩ := h _ (Nat.le_refl _)
  refine ⟨?_, h2⟩
  rw [walRead_eq_at, h1]
  cases hm : v.pend with
  | none => simp only [recsAt, hm]
  | some m =>
    have hlt := hv.2.2.2.2.2 m hm
    simp only [StorContents.commit] at hlt
    have hk : ¬ uint.nat m.Index' ≤ uint.nat (walLastHS Hs).Commit' := by rw [hc0]; omega
    simp only [recsAt, hm, if_neg hk]

theorem histReadsK_of_none {v : WalView} {σ : StorContents} {Hs : WalHist} (hp : v.pend = none)
    (h : HistReads σ Hs) : HistReadsK v σ Hs := by
  intro c hc
  have hr : recsAt v σ c = σ := by unfold recsAt; rw [hp]
  rw [hr]; exact h c hc

/-- A snapshot record is kept at every commit at or above one that keeps it. -/
theorem walKeep_mono {c c' : Nat} (h : c ≤ c') (o : WalOp) (ho : walKeep c o = true) :
    walKeep c' o = true := by
  cases o with
  | save _ _ => rfl
  | snap m al => simp only [walKeep, decide_eq_true_eq] at ho ⊢; omega

/-- Some commit at or above `c0` keeps every record of the history. -/
theorem walKeep_all_exists (c0 : Nat) : ∀ (Hs : WalHist), ∃ c, c0 ≤ c ∧ ∀ o ∈ Hs, walKeep c o = true
  | [] => ⟨c0, Nat.le_refl _, fun o h => by simp at h⟩
  | o :: Hs => by
    obtain ⟨c, hc, hall⟩ := walKeep_all_exists c0 Hs
    cases o with
    | save hs es =>
      refine ⟨c, hc, fun o' ho' => ?_⟩
      rcases List.mem_cons.1 ho' with rfl | ho'
      · rfl
      · exact hall o' ho'
    | snap m al =>
      refine ⟨max c (uint.nat m.Index'), by omega, fun o' ho' => ?_⟩
      rcases List.mem_cons.1 ho' with rfl | ho'
      · simp only [walKeep, decide_eq_true_eq]; omega
      · exact walKeep_mono (by omega) o' (hall o' ho')

/-- **With nothing pending, the reads give the eager fold** (at a commit keeping every record). -/
theorem histReadsK_fold {v : WalView} {σ : StorContents} {Hs : WalHist} (h : HistReadsK v σ Hs)
    (hp : v.pend = none) : walFoldChkFrom walFresh Hs = some σ := by
  obtain ⟨c, hc, hall⟩ := walKeep_all_exists (uint.nat (walLastHS Hs).Commit') Hs
  have h1 := (h c hc).1
  unfold walReadAt at h1
  rw [List.filter_eq_self.2 hall] at h1
  rw [h1]; unfold recsAt; rw [hp]

/-- **The eager fold, with its base at or below its commit, gives the reads** (a first start's history,
a restart's as the slot `wal.restartOk` states it): at every commit from the last on, the fold. -/
theorem histReads_of_fold {Hs : WalHist} {σ : StorContents} (hf : walFoldChkFrom walFresh Hs = some σ)
    (hb : σ.b ≤ σ.commit) (hc : walCommitLeFrom walFresh Hs) : HistReads σ Hs := by
  intro c hcc
  have hσc : σ.commit = uint.nat (walLastHS Hs).Commit' := by
    simp only [StorContents.commit]; rw [walFoldChkFrom_fresh_hs hf]
  have hbc : σ.b ≤ c := by omega
  refine ⟨walFoldChkFrom_filter_keep hf hbc, ?_⟩
  intro n τ' hn
  obtain ⟨m, hm⟩ := filter_take_exists (walKeep c) Hs n
  rw [hm] at hn
  obtain ⟨τm, hτm, hrest⟩ := walFoldChkFrom_prefix m hf
  have hle : τm.b ≤ c := Nat.le_trans (walFoldChkFrom_b_ge hrest) hbc
  rw [walFoldChkFrom_filter_keep hτm hle] at hn
  simp only [Option.some.injEq] at hn; subst hn
  exact hc m _ hτm

/-- **The empty history reads as the fresh records** at every commit. -/
theorem histReads_fresh : HistReads walFresh [] := by
  intro c _
  refine ⟨rfl, ?_⟩
  intro n τ' h
  simp only [List.filter_nil, List.take_nil, walFoldChkFrom, Option.some.injEq] at h
  subst h
  simp [walFresh, StorContents.commit, StorContents.last, StorContents.b]

/-- A record above the base changes nothing once a snapshot above it sets the base; below the commit
(the apply thread's own) it changes nothing a later received snapshot above the commit leaves. -/
theorem walSaveSnap_above (τ : StorContents) (m : SnapshotMetadataM) (h1 : τ.b ≤ uint.nat m.Index')
    (h2 : τ.commit < uint.nat m.Index') :
    walSaveSnap τ m = ⟨τ.hs, some (SnapshotM.mk [] m), entryID.mk m.Term' m.Index', []⟩ := by
  unfold walSaveSnap
  rw [if_neg (by omega), if_neg (by omega)]

theorem walSaveSnap_below (τ : StorContents) (m : SnapshotMetadataM) (h : uint.nat m.Index' < τ.b) :
    walSaveSnap τ m = τ := by
  unfold walSaveSnap; exact if_pos h

/-- **The apply thread's own snapshot `md` (at or below the commit) and a pending received one `m`
(above it) commute**: either order is `m` applied. -/
theorem walSaveSnap_own_pend {σ : StorContents} {md m : SnapshotMetadataM} (hb : σ.b ≤ σ.commit)
    (hmd : uint.nat md.Index' ≤ σ.commit) (hm : σ.commit < uint.nat m.Index') :
    walSaveSnap (walSaveSnap σ m) md = walSaveSnap σ m ∧
      walSaveSnap (walSaveSnap σ md) m = walSaveSnap σ m := by
  have hA := walSaveSnap_above σ m (by omega) hm
  have hb2 : (walSaveSnap σ md).b ≤ σ.commit := by
    unfold walSaveSnap; split
    · exact hb
    · simp only [StorContents.b]; omega
  have hc2 : (walSaveSnap σ md).commit = σ.commit := by
    simp only [StorContents.commit, walSaveSnap_hs]
  refine ⟨?_, ?_⟩
  · rw [hA]
    apply walSaveSnap_below
    simp only [StorContents.b]; omega
  · rw [walSaveSnap_above (walSaveSnap σ md) m (by omega) (by omega), hA]
    congr 1
    exact walSaveSnap_hs σ md

/-! ## Raft's `committed ≤ lastIndex` passes to the records -/

/-- Records holding a durable state whose commit is within its last index have their commit within
their last index (`StorageHolds`: the records' entries are the state's from their base on, their
commit at most the state's). -/
theorem storageHolds_commit_le_last {S : RaftState} {σ : StorContents} (h : StorageHolds S σ)
    (hS : uint.nat S.commit ≤ S.last) : σ.commit ≤ σ.last := by
  obtain ⟨hb, -, he, -, -, hbc, -, hc, -⟩ := h
  have hbn : uint.nat S.base.index' ≤ uint.nat σ.base.index' := by word
  unfold StorContents.last
  unfold StorContents.b at hbc ⊢
  unfold RaftState.last at hS
  rw [he]
  unfold RaftState.entsFrom
  rw [List.length_drop]
  have hZ : (uint.Z σ.base.index' - uint.Z S.base.index').toNat =
      uint.nat σ.base.index' - uint.nat S.base.index' := by word
  rw [hZ]
  omega

/-! ## The steps -/

/-- **A `Save`** from the idle view `(v, none)` to the pending one `(v', some (v, γb, |Hs|))`: the new
prefix reads the saved records `σ'` (`histReads_save`), with `walCommitLe`, holding the new view's state
within its log; its entries within raft's room. -/
theorem histOk_save {Hs : WalHist} {n : Nat} {v v' : WalView} {γb : Iris.GName} {hs : HardStateM}
    {es : List EntryM} {σ' : StorContents} (h : HistOkK (v, none) Hs n)
    (hr' : walRead (Hs ++ [WalOpG.save hs es]) = some σ') (hcle' : walCommitLe (Hs ++ [WalOpG.save hs es]))
    (hok : ImgOk v'.S v'.l σ')
    (hidx : ∀ e ∈ es, uint.nat e.Index' ≤ 2 ^ 61 - 1)
    (hmono : uint.nat (walLastHS Hs).Commit' ≤ uint.nat (phsNext (walLastHS Hs) hs).Commit') :
    HistOkK (v', some (v, γb, Hs.length)) (Hs ++ [WalOpG.save hs es]) n := by
  obtain ⟨hn, -, hc, ⟨hidxH, hcle⟩, hmo⟩ := h
  have hmo' : HistCommitMono (Hs ++ [WalOpG.save hs es]) n :=
    histCommitMono_snoc _ hn hmo (by rw [walLastHS_snoc_saveP]; exact hmono)
  unfold HistOkK PosOkK HistReadOk
  refine ⟨by simp; omega, ?_, ?_, ⟨walIdxLe_snoc_save hidxH hidx, ?_⟩, hmo'⟩
  · intro v0 γ0 pos hp
    simp only [Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨-, -, rfl⟩ := hp
    simp
  · intro j hnj hj
    by_cases hjl : j ≤ Hs.length
    · obtain ⟨σ, hr, hok0⟩ := hc j hnj hjl
      refine ⟨σ, by rw [List.take_append_of_le_length hjl]; exact hr, ?_⟩
      simp only [crashOk] at hok0 ⊢
      rw [if_pos hjl]; exact hok0
    · have hj' : j = Hs.length + 1 := by simp at hj; omega
      subst hj'
      refine ⟨σ', by rw [List.take_of_length_le (by simp)]; exact hr', ?_⟩
      simp only [crashOk]
      rw [if_neg (by omega)]; exact hok
  · intro j hnj hj
    by_cases hjl : j ≤ Hs.length
    · rw [List.take_append_of_le_length hjl]; exact hcle j hnj hjl
    · rw [List.take_of_length_le (by simp at hj ⊢; omega)]
      exact hcle'

/-- (P5 (b)) **A `Save`: the reads** (the crux of the history's invariant). From the view `v` with the
records `σ` before its pending received snapshot, a `Save` step (`WalSaveStep`'s facts: the batch in
`Save`'s case for the records the view describes, the saved records `σ'` describing `v'`, nothing
pending after) at a commit at or above the last: at the new commit the history reads `recsOf v σ` before
the `Save` (the pending snapshot is at the saved records' base, at or below their commit, so the commit
keeps it again), so after it `σ'`; at every commit above, the same. -/
theorem histReads_save {v v' : WalView} {σ : StorContents} {Hs : WalHist} {hs : HardStateM}
    {es : List EntryM} (h : HistReadsK v σ Hs) (hv : ViewOk v σ) (hpn' : v'.pend = none)
    (hok : WalSaveOk (recsOf v σ) es) (hv' : ViewOk v' (walSave (recsOf v σ) hs es))
    (hcl : (walSave (recsOf v σ) hs es).commit ≤ (walSave (recsOf v σ) hs es).last)
    (hmono : uint.nat (walLastHS Hs).Commit' ≤ uint.nat (phsNext (walLastHS Hs) hs).Commit') :
    HistReadsK v' (walSave (recsOf v σ) hs es) (Hs ++ [WalOpG.save hs es]) := by
  have hhs := histReadsK_hs h
  have hc' : uint.nat (walLastHS (Hs ++ [WalOpG.save hs es])).Commit' =
      (walSave (recsOf v σ) hs es).commit := by
    rw [walLastHS_snoc_saveP]
    simp only [StorContents.commit, walSave, recsOf_hs, hhs]
  intro c hc
  rw [hc'] at hc
  have hrec : recsAt v σ c = recsOf v σ := by
    cases hm : v.pend with
    | none => simp only [recsAt, recsOf, hm]
    | some m =>
      have hlt := hv.2.2.2.2.2 m hm
      have hb0 := hv.1.2.2.2.2.2.1
      have hbm : (walSaveSnap σ m).b = uint.nat m.Index' := by
        unfold walSaveSnap; rw [if_neg (by omega)]; rfl
      have hbs : (walSave (recsOf v σ) hs es).b = uint.nat m.Index' := by
        have : (walSave (recsOf v σ) hs es).b = (recsOf v σ).b := by
          simp only [StorContents.b, walSave_base]
        rw [this]; simp only [recsOf, hm]; exact hbm
      have hb' := hv'.2.2.1
      have hl' := hv'.2.2.2.1
      simp only [recsAt, recsOf, hm]
      rw [if_pos (by omega)]
  obtain ⟨h1, h2⟩ := h c (by rw [walLastHS_snoc_saveP] at hc'; omega)
  have hr : walReadAt (Hs ++ [WalOpG.save hs es]) c = some (walSave (recsOf v σ) hs es) := by
    rw [walReadAt_snoc_save, h1, hrec, Option.bind_some]
    have := walFoldChkFrom_snoc_save (τ := recsOf v σ) (H := []) (h := hs) rfl hok
    rw [List.nil_append] at this
    exact this
  refine ⟨?_, walCommitLeAt_snoc_save h2 hr hcl⟩
  rw [hr]; unfold recsAt; rw [hpn']

/-- (P5 (b)) **A received snapshot's `SaveSnap` above the last saved commit: the reads**: below the
snapshot's index as before, from it on the snapshot applied (the view now has it pending). -/
theorem histReads_snapAbove {v : WalView} {σ : StorContents} {Hs : WalHist} {m : SnapshotMetadataM}
    {al : Bool} (h : HistReadsK v σ Hs) (hp : v.pend = none) :
    HistReadsK { v with pend := some m } σ (Hs ++ [WalOpG.snap m al]) := by
  intro c hc
  rw [walLastHS_snoc_snapP] at hc
  obtain ⟨h1, h2⟩ := h c hc
  have hr0 : recsAt v σ c = σ := by unfold recsAt; rw [hp]
  rw [hr0] at h1
  refine ⟨?_, walCommitLeAt_snoc_snap m al h2 h1⟩
  rw [walReadAt_snoc_snap, h1]
  by_cases hk : uint.nat m.Index' ≤ c
  · simp [recsAt, hk]
  · simp [recsAt, hk]

/-- (P5 (b)) **The apply thread's own `SaveSnap` at or below the last saved commit: the reads**: at every
commit from the last on, the snapshot applied to the records (below a pending received snapshot, which
then sets the base, it changes nothing: `walSaveSnap_own_pend`). -/
theorem histReads_ownSnap {v : WalView} {σ : StorContents} {Hs : WalHist} {md : SnapshotMetadataM}
    {al : Bool} (h : HistReadsK v σ Hs) (hv : ViewOk v σ)
    (hc : uint.nat md.Index' ≤ uint.nat (walLastHS Hs).Commit') :
    HistReadsK v (walSaveSnap σ md) (Hs ++ [WalOpG.snap md al]) := by
  have hhs := histReadsK_hs h
  intro c hcc
  rw [walLastHS_snoc_snapP] at hcc
  obtain ⟨h1, h2⟩ := h c hcc
  refine ⟨?_, walCommitLeAt_snoc_snap md al h2 h1⟩
  rw [walReadAt_snoc_snap, if_pos (by omega), h1]
  simp only [Option.map_some, Option.some.injEq]
  cases hm : v.pend with
  | none => simp only [recsAt, hm]
  | some m =>
    have hlt := hv.2.2.2.2.2 m hm
    have hb0 := hv.1.2.2.2.2.2.1
    have hmd : uint.nat md.Index' ≤ σ.commit := by simp only [StorContents.commit]; rw [← hhs]; exact hc
    obtain ⟨e1, e2⟩ := walSaveSnap_own_pend (σ := σ) (md := md) (m := m) hb0 hmd hlt
    simp only [recsAt, hm]
    by_cases hk : uint.nat m.Index' ≤ c
    · rw [if_pos hk, if_pos hk, e1, e2]
    · rw [if_neg hk, if_neg hk]

/-- **A received snapshot's `SaveSnap`** (above the last saved commit; the view moves only its pending
snapshot, so what it accepts is unchanged): the reader drops the record. -/
theorem histOk_snapAbove {Hs : WalHist} {n : Nat} {v v2 : WalView}
    {m : SnapshotMetadataM} {al : Bool} (h : HistOkK (v, none) Hs n)
    (hab : uint.nat (walLastHS Hs).Commit' < uint.nat m.Index')
    (hS : v2.S = v.S) (hl : v2.l = v.l) (hm : uint.nat m.Index' ≤ 2 ^ 61 - 1) :
    HistOkK (v2, none) (Hs ++ [WalOpG.snap m al]) n := by
  obtain ⟨hn, -, hc, ⟨hidxH, hcle⟩, hmo⟩ := h
  have hmo' : HistCommitMono (Hs ++ [WalOpG.snap m al]) n :=
    histCommitMono_snoc _ hn hmo (by rw [walLastHS_snoc_snapP]; exact Nat.le_refl _)
  have hrd : walRead (Hs ++ [WalOpG.snap m al]) = walRead Hs := by
    rw [walRead_snoc_snap, if_neg (by omega)]
  have hacc : ∀ j σ, crashOk (v, none) j σ → crashOk (v2, none) j σ := by
    intro j σ h; simp only [crashOk, hS, hl] at h ⊢; exact h
  unfold HistOkK PosOkK HistReadOk
  refine ⟨by simp; omega, fun _ _ _ hp => by simp at hp, ?_, ⟨walIdxLe_snoc_snap hidxH hm, ?_⟩, hmo'⟩
  · intro j hnj hj
    by_cases hjl : j ≤ Hs.length
    · obtain ⟨σ, hr, hok0⟩ := hc j hnj hjl
      exact ⟨σ, by rw [List.take_append_of_le_length hjl]; exact hr, hacc j σ hok0⟩
    · have hj' : j = Hs.length + 1 := by simp at hj; omega
      subst hj'
      obtain ⟨σ, hr, hok0⟩ := hc Hs.length hn (Nat.le_refl _)
      rw [List.take_length] at hr
      refine ⟨σ, by rw [List.take_of_length_le (by simp), hrd]; exact hr, ?_⟩
      simp only [crashOk, hS, hl] at hok0 ⊢; exact hok0
  · intro j hnj hj
    by_cases hjl : j ≤ Hs.length
    · rw [List.take_append_of_le_length hjl]; exact hcle j hnj hjl
    · rw [List.take_of_length_le (by simp at hj ⊢; omega)]
      obtain ⟨σ0, hr, -⟩ := hc Hs.length hn (Nat.le_refl _)
      have hcl0 := hcle Hs.length hn (Nat.le_refl _)
      rw [List.take_length] at hr hcl0
      exact walCommitLe_snoc_snap m al hcl0 hr

/-- **The apply thread's own snapshot preserves `ImgOk`**: at or below the records' commit, within the
handed log, at the term the durable log has there (from `DurAgrees` with the handed log). -/
theorem imgOk_ownSnap {S : RaftState} {l : List LogEntry} {σ : StorContents} {md : SnapshotMetadataM}
    {e : LogEntry} (h : ImgOk S l σ) (hc : uint.nat md.Index' ≤ σ.commit) (hda : DurAgrees S l)
    (hpos : 0 < uint.nat md.Index') (he : l[uint.nat md.Index' - 1]? = some e) (ht : e.term = md.Term') :
    ImgOk S l (walSaveSnap σ md) := by
  obtain ⟨hh, hb⟩ := h
  have hil : uint.nat md.Index' - 1 < l.length := (List.getElem?_eq_some_iff.1 he).1
  have hmZ : W64 (((uint.nat md.Index' - 1 : Nat) : Int) + 1) = md.Index' := by
    have : uint.nat md.Index' < 2 ^ 64 := by word
    word
  refine ⟨walOwnSnap_holds S σ md hh hc (fun hbm => ?_), ?_⟩
  · have hbase : uint.nat S.base.index' ≤ (uint.nat md.Index' - 1) + 1 := by
      have h1 := hh.1
      simp only [StorContents.b] at hbm
      word
    have := hda (uint.nat md.Index' - 1) e hbase he
    rw [hmZ, ht] at this
    exact this
  · unfold walSaveSnap
    split
    · exact hb
    · simp only [StorContents.b]; omega

/-- **The apply thread's own `SaveSnap`** at an index of the view's handed log, at or below the last
saved commit: the new prefix (past the pending `Save`) reads the old read with the snapshot applied. -/
theorem histOk_ownSnap {Hs : WalHist} {n : Nat} {vk : WalViewK}
    {md : SnapshotMetadataM} {al : Bool} {e : LogEntry} (h : HistOkK vk Hs n)
    (hc : uint.nat md.Index' ≤ uint.nat (walLastHS Hs).Commit') (hda : DurAgrees vk.1.S vk.1.l)
    (hpos : 0 < uint.nat md.Index') (he : vk.1.l[uint.nat md.Index' - 1]? = some e) (ht : e.term = md.Term')
    (hm : uint.nat md.Index' ≤ 2 ^ 61 - 1) :
    HistOkK vk (Hs ++ [WalOpG.snap md al]) n := by
  obtain ⟨hn, hpo, hcr, ⟨hidxH, hcle⟩, hmo⟩ := h
  have hmo' : HistCommitMono (Hs ++ [WalOpG.snap md al]) n :=
    histCommitMono_snoc _ hn hmo (by rw [walLastHS_snoc_snapP]; exact Nat.le_refl _)
  have hrd : walRead (Hs ++ [WalOpG.snap md al]) = (walRead Hs).map (fun σ => walSaveSnap σ md) := by
    rw [walRead_snoc_snap, if_pos hc]
  unfold HistOkK PosOkK HistReadOk
  refine ⟨by simp; omega, fun v0 γb pos hp => by have := hpo v0 γb pos hp; simp; omega, ?_,
    ⟨walIdxLe_snoc_snap hidxH hm, ?_⟩, hmo'⟩
  · intro j hnj hj
    by_cases hjl : j ≤ Hs.length
    · obtain ⟨σ, hr, hok0⟩ := hcr j hnj hjl
      exact ⟨σ, by rw [List.take_append_of_le_length hjl]; exact hr, hok0⟩
    · have hj' : j = Hs.length + 1 := by simp at hj; omega
      subst hj'
      obtain ⟨σ0, hr, hok0⟩ := hcr Hs.length hn (Nat.le_refl _)
      rw [List.take_length] at hr
      refine ⟨walSaveSnap σ0 md, by rw [List.take_of_length_le (by simp), hrd, hr]; rfl, ?_⟩
      have hc0 : uint.nat md.Index' ≤ σ0.commit := by
        simp only [StorContents.commit]; rw [walRead_hs hr]; exact hc
      obtain ⟨v, pb⟩ := vk
      cases pb with
      | none =>
        simp only [crashOk] at hok0 ⊢
        exact imgOk_ownSnap hok0 hc0 hda hpos he ht
      | some p =>
        obtain ⟨v0, γb, pos⟩ := p
        have hp := hpo v0 γb pos rfl
        simp only [crashOk] at hok0 ⊢
        rw [if_neg (by omega)] at hok0
        rw [if_neg (by omega)]
        exact imgOk_ownSnap hok0 hc0 hda hpos he ht
  · intro j hnj hj
    by_cases hjl : j ≤ Hs.length
    · rw [List.take_append_of_le_length hjl]; exact hcle j hnj hjl
    · rw [List.take_of_length_le (by simp at hj ⊢; omega)]
      obtain ⟨σ0, hr, -⟩ := hcr Hs.length hn (Nat.le_refl _)
      have hcl0 := hcle Hs.length hn (Nat.le_refl _)
      rw [List.take_length] at hr hcl0
      exact walCommitLe_snoc_snap md al hcl0 hr

/-- **The *enter***: the pending view `(v', some (v, γb, pos))` becomes the idle `(v', none)`, at the
synced mark `pos + 1` (the batch synced), or at the old mark when every record that held the state
before the batch within its log holds the entered one within its log (a commit-only batch). -/
theorem histOk_enter {Hs : WalHist} {n : Nat} {v v' : WalView} {γb : Iris.GName} {pos : Nat}
    (h : HistOkK (v', some (v, γb, pos)) Hs n) (hlast : walLastHS Hs = v'.hs)
    (hcase : n' = max n (pos + 1) ∨ (n' = n ∧
      ∀ σ, ImgOk v.S v.l σ → σ.commit ≤ uint.nat v'.hs.Commit' → ImgOk v'.S v'.l σ)) :
    HistOkK (v', none) Hs n' := by
  obtain ⟨hn, hpo, hcr, ⟨hidxH, hcle⟩, hmo⟩ := h
  have hp := hpo v γb pos rfl
  have hnn : n ≤ n' := by rcases hcase with rfl | ⟨rfl, -⟩ <;> omega
  unfold HistOkK PosOkK HistReadOk
  refine ⟨by rcases hcase with rfl | ⟨rfl, -⟩ <;> omega, fun _ _ _ hq => by simp at hq, ?_,
    ⟨hidxH, fun j h1 h2 => hcle j (by omega) h2⟩, fun j h1 h2 => hmo j (by omega) h2⟩
  intro j hnj hj
  obtain ⟨σ, hr, hok0⟩ := hcr j (by omega) hj
  refine ⟨σ, hr, ?_⟩
  simp only [crashOk] at hok0 ⊢
  by_cases hjp : j ≤ pos
  · rw [if_pos hjp] at hok0
    rcases hcase with rfl | ⟨-, himp⟩
    · omega
    · refine himp σ hok0 ?_
      simp only [StorContents.commit]
      rw [walRead_hs hr, ← hlast]
      exact hmo j (by omega) hj
  · rw [if_neg hjp] at hok0; exact hok0

/-- **The history's facts at an allocation** (a restart's read, `rnRestartWal`; a first start's empty
history, `histOk_fresh`): the synced mark at the history's end, whose only crash prefix is the whole
history, read as `σ` (`HistReads` at its last commit). -/
theorem histOk_restart {Hs : WalHist} {σ : StorContents} {v : WalView} (hr : HistReads σ Hs)
    (hidx : walIdxLe (2 ^ 61 - 1) Hs) (hok : ImgOk v.S v.l σ) :
    HistOkK (v, none) Hs Hs.length := by
  obtain ⟨hrd, hcl⟩ := hr _ (Nat.le_refl _)
  unfold HistOkK PosOkK HistReadOk
  refine ⟨Nat.le_refl _, fun _ _ _ hp => by simp at hp, ?_, ⟨hidx, ?_⟩, ?_⟩
  · intro j hnj hj
    have hj' : j = Hs.length := by omega
    subst hj'
    refine ⟨σ, by rw [List.take_length, walRead_eq_at]; exact hrd, ?_⟩
    simp only [crashOk]; exact hok
  · intro j hnj hj
    have hj' : j = Hs.length := by omega
    subst hj'
    rw [List.take_length, walCommitLe_eq_at]; exact hcl
  · intro j hnj hj
    have hj' : j = Hs.length := by omega
    subst hj'
    rw [List.take_length]; exact Nat.le_refl _

/-- **A first start's history** (`wal.Create`'s: empty). -/
theorem histOk_fresh {v : WalView} (hok : ImgOk v.S v.l walFresh) : HistOkK (v, none) [] 0 :=
  histOk_restart (Hs := []) histReads_fresh
    (by unfold walIdxLe; exact ⟨fun _ _ _ h => by simp at h, fun _ _ h => by simp at h⟩) hok

/-- (P5, 2026-11-25) **A commit-only batch keeps the crash images it does not sync** (`rnDurK_enter.law`'s
second case): a batch of no entries and no snapshot that `Save` does not sync (`¬ walMustSync`: its hard
state empty, or at the last saved term and vote, the view's `p`, whose term and vote are the durable
state's) moves only the durable commit (`RaftState.next` keeps the log and `wcommit`): every record that
held `S` within `l`, at a commit at or below the entered one, holds the entered state within the longer
handed log. -/
theorem imgOk_commitOnly {S : RaftState} {p h : HardStateM} {l l' : List LogEntry} {Hs : WalHist}
    (hns : ¬ walMustSync Hs h []) (hlast : walLastHS Hs = p) (ht : S.term = p.Term')
    (hv : S.vote = p.Vote') (hpfx : l <+: l') :
    ∀ σ, ImgOk S l σ → σ.commit ≤ uint.nat (phsNext p h).Commit' →
      ImgOk (readyDurable S (phsNext p h) none []) l' σ := by
  intro σ hok hc
  obtain ⟨hh, hb⟩ := hok
  have htv : (phsNext p h).Term' = p.Term' ∧ (phsNext p h).Vote' = p.Vote' := by
    unfold phsNext
    split
    · exact ⟨rfl, rfl⟩
    · rename_i hne
      unfold walMustSync hsEmptyP at hns
      rw [hlast] at hns
      constructor
      · exact Classical.byContradiction fun hT => hns (Or.inr ⟨hne, Or.inr hT⟩)
      · exact Classical.byContradiction fun hV => hns (Or.inr ⟨hne, Or.inl hV⟩)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, h9, h10⟩ := hh
  refine ⟨⟨h1, h2, h3, ?_, ?_, h6, h7, hc, h9, h10⟩, Nat.le_trans hb hpfx.length_le⟩
  · simp only [readyDurable, RaftState.next]; rw [htv.1, ← ht]; exact h4
  · simp only [readyDurable, RaftState.next]; rw [htv.2, ← hv]; exact h5

/-! ## (P5-RESTART, option (B), 2026-11-26) The certificates' base -/

/-- The fold keeps a snapshot from the base `σ0` or from `X`, over operations of `X`. -/
theorem walFold_snapFrom (σ0 : StorContents) (X : WalHist) :
    ∀ (H : WalHist) (τ σ : StorContents), (∀ o ∈ H, o ∈ X) → SnapFrom σ0 X τ →
      walFoldChkFrom τ H = some σ → SnapFrom σ0 X σ := by
  intro H
  induction H with
  | nil => intro τ σ _ hτ h; simp only [walFoldChkFrom, Option.some.injEq] at h; subst h; exact hτ
  | cons o H ih =>
    intro τ σ hA hτ h
    have hA' : ∀ o' ∈ H, o' ∈ X := fun o' ho' => hA o' (List.mem_cons_of_mem _ ho')
    cases o with
    | snap m al =>
      simp only [walFoldChkFrom] at h
      refine ih _ _ hA' ?_ h
      unfold walSaveSnap
      split
      · exact hτ
      · right
        exact ⟨m, al, hA _ List.mem_cons_self, rfl, rfl⟩
    | save hs es =>
      simp only [walFoldChkFrom, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨ents, -, h⟩ := h
      exact ih _ _ hA' hτ h

theorem snapFrom_mono {σ0 τ : StorContents} {X Y : WalHist} (hXY : ∀ o ∈ X, o ∈ Y)
    (h : SnapFrom σ0 X τ) : SnapFrom σ0 Y τ := by
  rcases h with h | ⟨m, al, hm, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨m, al, hXY _ hm, h⟩

/-- **The pure lemma of option (B)**: a read of an extension `H0 ++ X` of a history `H0` that reads as
`σ0` at every commit from its last saved one on (`HistReads`: a restarted history, nothing pending), at
a last saved commit at or above `H0`'s, has its snapshot from `σ0` or from a snapshot record of `X`. The
reader keeps exactly the records of `H0` that `H0`'s own read at that commit keeps, which fold to `σ0`;
the records of `X` it keeps fold on from `σ0`. -/
theorem walRead_ext_snapFrom {σ0 τ : StorContents} {H0 X : WalHist} (hr : HistReads σ0 H0)
    (hc : uint.nat (walLastHS H0).Commit' ≤ uint.nat (walLastHS (H0 ++ X)).Commit')
    (h : walRead (H0 ++ X) = some τ) : SnapFrom σ0 X τ := by
  obtain ⟨h0, -⟩ := hr _ hc
  unfold walReadAt at h0
  unfold walRead at h
  rw [List.filter_append, walFoldChkFrom_append, h0, Option.bind_some] at h
  exact walFold_snapFrom σ0 X _ σ0 τ (fun o ho => (List.mem_filter.1 ho).1) (Or.inl ⟨rfl, rfl⟩) h

/-- **Every read past the base has its snapshot from the base or from a record after it.** -/
theorem certBaseK_read {σ0 τ : StorContents} {k j : Nat} {Hs : WalHist} (hb : CertBaseK σ0 k Hs)
    (hkj : k ≤ j) (hj : j ≤ Hs.length) (h : walRead (Hs.take j) = some τ) :
    SnapFrom σ0 (Hs.drop k) τ := by
  obtain ⟨-, hr, hmono⟩ := hb
  have hsplit : Hs.take j = Hs.take k ++ (Hs.take j).drop k := by
    conv => lhs; rw [← List.take_append_drop k (Hs.take j)]
    rw [List.take_take, Nat.min_eq_left hkj]
  have hc := hmono j hkj hj
  rw [hsplit] at h hc
  refine snapFrom_mono ?_ (walRead_ext_snapFrom hr hc h)
  intro o ho
  rw [List.drop_take] at ho
  exact List.mem_of_mem_take ho

/-- **A record that keeps or raises the last saved commit keeps the base.** -/
theorem certBaseK_snoc {σ0 : StorContents} {k : Nat} {Hs : WalHist} (o : WalOp) (hb : CertBaseK σ0 k Hs)
    (hle : uint.nat (walLastHS Hs).Commit' ≤ uint.nat (walLastHS (Hs ++ [o])).Commit') :
    CertBaseK σ0 k (Hs ++ [o]) := by
  obtain ⟨hk, hr, hmono⟩ := hb
  have htk : (Hs ++ [o]).take k = Hs.take k := List.take_append_of_le_length hk
  refine ⟨by simp only [List.length_append, List.length_singleton]; omega, by rw [htk]; exact hr, ?_⟩
  intro j hkj hj
  rw [htk]
  simp only [List.length_append, List.length_singleton] at hj
  by_cases hjl : j ≤ Hs.length
  · rw [List.take_append_of_le_length hjl]; exact hmono j hkj hjl
  · have hj' : j = Hs.length + 1 := by omega
    have htj : (Hs ++ [o]).take j = Hs ++ [o] := by
      rw [List.take_of_length_le]; simp only [List.length_append, List.length_singleton]; omega
    rw [htj]
    have h1 := hmono Hs.length hk (Nat.le_refl _)
    rw [List.take_length] at h1
    omega

/-- **The base at an allocation**: the whole history, read as `σ` (a restart's; a first start's
empty one). -/
theorem certBaseK_restart {σ : StorContents} {Hs : WalHist} (hr : HistReads σ Hs) :
    CertBaseK σ Hs.length Hs := by
  refine ⟨Nat.le_refl _, by rw [List.take_length]; exact hr, ?_⟩
  intro j hkj hj
  have hj' : j = Hs.length := by omega
  subst hj'
  exact Nat.le_refl _

end pure

end EtcdGrove
end Perennial
