/- Lean-first (no Rocq counterpart).

# The crash-aware durability invariant's pure steps (etcd-dist D6, task T2 / P5, 2026-11-25)

What the steps of `InvWalCrash.lean`'s invariant do to its pure crash facts: every complete prefix of
the WAL's history from the synced mark reads records the view accepts (`CrashReadsHold`), and the
history's read conditions (`HistReadOk`), with the eager fold's `committed ≤ lastIndex` along the
history (`walCommitLeFrom walFresh Hs`), which gives `walCommitLe` of the prefix a `Save` appends
(`walCommitLe_of_fold`).

* a `Save` (`crashReads_save`, `histReadOk_save`): the old prefixes keep reading what they read (the
  state before the batch, while it is pending), the new one reads the saved records (`walRead_of_fold`);
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

/-- The eager `committed ≤ lastIndex` across a snapshot record. -/
theorem walCommitLeFrom_snoc_snap {H : WalHist} {σ : StorContents} (m : SnapshotMetadataM) (al : Bool)
    (h : walCommitLeFrom walFresh H) (hf : walFoldChkFrom walFresh H = some σ) :
    walCommitLeFrom walFresh (H ++ [WalOpG.snap m al]) := by
  have hl : σ.commit ≤ σ.last := by
    have := h H.length σ
    rw [List.take_length] at this
    exact this hf
  refine walCommitLeFrom_snoc (σ := walSaveSnap σ m) h ?_ (walCommitLe_snoc_snap.walSaveSnap_commitLeP m hl)
  rw [walFoldChkFrom_append, hf]; rfl

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
history's eager fold `σ'` (the saved records) has its base within its commit and its commit within its
last index, holds the new view's state within its log; its entries within raft's room. -/
theorem histOk_save {Hs : WalHist} {n : Nat} {v v' : WalView} {γb : Iris.GName} {hs : HardStateM}
    {es : List EntryM} {σ' : StorContents} (h : HistOkK (v, none) Hs n)
    (hf : walFoldChkFrom walFresh (Hs ++ [WalOpG.save hs es]) = some σ') (hb : σ'.b ≤ σ'.commit)
    (hcl : σ'.commit ≤ σ'.last) (hok : ImgOk v'.S v'.l σ')
    (hidx : ∀ e ∈ es, uint.nat e.Index' ≤ 2 ^ 61 - 1) :
    HistOkK (v', some (v, γb, Hs.length)) (Hs ++ [WalOpG.save hs es]) n := by
  obtain ⟨hn, -, hc, ⟨hidxH, hcle⟩, heag⟩ := h
  have hr' : walRead (Hs ++ [WalOpG.save hs es]) = some σ' := walRead_of_fold hf hb
  have heag' := walCommitLeFrom_snoc heag hf hcl
  unfold HistOkK PosOkK HistReadOk
  refine ⟨by simp; omega, ?_, ?_, ⟨walIdxLe_snoc_save hidxH hidx, ?_⟩, heag'⟩
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
      exact walCommitLe_of_fold hf hb heag'

/-- **A received snapshot's `SaveSnap`** (above the last saved commit; the view moves only its pending
snapshot, so what it accepts is unchanged): the reader drops the record. -/
theorem histOk_snapAbove {Hs : WalHist} {n : Nat} {v v2 : WalView} {σ : StorContents}
    {m : SnapshotMetadataM} {al : Bool} (h : HistOkK (v, none) Hs n)
    (hf : walFoldChkFrom walFresh Hs = some σ) (hab : uint.nat (walLastHS Hs).Commit' < uint.nat m.Index')
    (hS : v2.S = v.S) (hl : v2.l = v.l) (hm : uint.nat m.Index' ≤ 2 ^ 61 - 1) :
    HistOkK (v2, none) (Hs ++ [WalOpG.snap m al]) n := by
  obtain ⟨hn, -, hc, ⟨hidxH, hcle⟩, heag⟩ := h
  have hrd : walRead (Hs ++ [WalOpG.snap m al]) = walRead Hs := by
    rw [walRead_snoc_snap, if_neg (by omega)]
  have hacc : ∀ j σ, crashOk (v, none) j σ → crashOk (v2, none) j σ := by
    intro j σ h; simp only [crashOk, hS, hl] at h ⊢; exact h
  unfold HistOkK PosOkK HistReadOk
  refine ⟨by simp; omega, fun _ _ _ hp => by simp at hp, ?_, ⟨walIdxLe_snoc_snap hidxH hm, ?_⟩,
    walCommitLeFrom_snoc_snap m al heag hf⟩
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
theorem histOk_ownSnap {Hs : WalHist} {n : Nat} {vk : WalViewK} {σ : StorContents}
    {md : SnapshotMetadataM} {al : Bool} {e : LogEntry} (h : HistOkK vk Hs n)
    (hf : walFoldChkFrom walFresh Hs = some σ)
    (hc : uint.nat md.Index' ≤ uint.nat (walLastHS Hs).Commit') (hda : DurAgrees vk.1.S vk.1.l)
    (hpos : 0 < uint.nat md.Index') (he : vk.1.l[uint.nat md.Index' - 1]? = some e) (ht : e.term = md.Term')
    (hm : uint.nat md.Index' ≤ 2 ^ 61 - 1) :
    HistOkK vk (Hs ++ [WalOpG.snap md al]) n := by
  obtain ⟨hn, hpo, hcr, ⟨hidxH, hcle⟩, heag⟩ := h
  have hrd : walRead (Hs ++ [WalOpG.snap md al]) = (walRead Hs).map (fun σ => walSaveSnap σ md) := by
    rw [walRead_snoc_snap, if_pos hc]
  unfold HistOkK PosOkK HistReadOk
  refine ⟨by simp; omega, fun v0 γb pos hp => by have := hpo v0 γb pos hp; simp; omega, ?_,
    ⟨walIdxLe_snoc_snap hidxH hm, ?_⟩, walCommitLeFrom_snoc_snap md al heag hf⟩
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
    (h : HistOkK (v', some (v, γb, pos)) Hs n)
    (hcase : n' = max n (pos + 1) ∨ (n' = n ∧ ∀ σ, ImgOk v.S v.l σ → ImgOk v'.S v'.l σ)) :
    HistOkK (v', none) Hs n' := by
  obtain ⟨hn, hpo, hcr, ⟨hidxH, hcle⟩, heag⟩ := h
  have hp := hpo v γb pos rfl
  have hnn : n ≤ n' := by rcases hcase with rfl | ⟨rfl, -⟩ <;> omega
  unfold HistOkK PosOkK HistReadOk
  refine ⟨by rcases hcase with rfl | ⟨rfl, -⟩ <;> omega, fun _ _ _ hq => by simp at hq, ?_,
    ⟨hidxH, fun j h1 h2 => hcle j (by omega) h2⟩, heag⟩
  intro j hnj hj
  obtain ⟨σ, hr, hok0⟩ := hcr j (by omega) hj
  refine ⟨σ, hr, ?_⟩
  simp only [crashOk] at hok0 ⊢
  by_cases hjp : j ≤ pos
  · rw [if_pos hjp] at hok0
    rcases hcase with rfl | ⟨-, himp⟩
    · omega
    · exact himp σ hok0
  · rw [if_neg hjp] at hok0; exact hok0

/-- **The history's facts at an allocation** (a restart's read, `wal.restartOk`; a first start's empty
history, `histOk_fresh`): the synced mark at the history's end, whose only crash prefix is the whole
history, read as its fold. -/
theorem histOk_restart {Hs : WalHist} {σ : StorContents} {v : WalView}
    (hf : walFoldChkFrom walFresh Hs = some σ) (hb : σ.b ≤ σ.commit)
    (hidx : walIdxLe (2 ^ 61 - 1) Hs) (heag : walCommitLeFrom walFresh Hs) (hok : ImgOk v.S v.l σ) :
    HistOkK (v, none) Hs Hs.length := by
  have hcl : walCommitLe Hs := walCommitLe_of_fold hf hb heag
  unfold HistOkK PosOkK HistReadOk
  refine ⟨Nat.le_refl _, fun _ _ _ hp => by simp at hp, ?_, ⟨hidx, ?_⟩, heag⟩
  · intro j hnj hj
    have hj' : j = Hs.length := by omega
    subst hj'
    refine ⟨σ, by rw [List.take_length]; exact walRead_of_fold hf hb, ?_⟩
    simp only [crashOk]; exact hok
  · intro j hnj hj
    have hj' : j = Hs.length := by omega
    subst hj'
    rw [List.take_length]; exact hcl

theorem walCommitLeFrom_fresh_nil : walCommitLeFrom walFresh [] := by
  intro n τ' h
  simp only [List.take_nil, walFoldChkFrom, Option.some.injEq] at h
  subst h
  simp [walFresh, StorContents.commit, StorContents.last, StorContents.b]

/-- **A first start's history** (`wal.Create`'s: empty). -/
theorem histOk_fresh {v : WalView} (hok : ImgOk v.S v.l walFresh) : HistOkK (v, none) [] 0 :=
  histOk_restart (Hs := []) rfl (by simp [walFresh, StorContents.commit, StorContents.b])
    (by unfold walIdxLe; exact ⟨fun _ _ _ h => by simp at h, fun _ _ h => by simp at h⟩)
    walCommitLeFrom_fresh_nil hok

end pure

end EtcdGrove
end Perennial
