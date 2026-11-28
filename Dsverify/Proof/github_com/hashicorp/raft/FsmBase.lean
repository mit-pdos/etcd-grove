/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/FsmBase.lean (241f27e).
-/
/-
Shared definitions and lemmas of the FSM subsystem's proofs (`processLogs`, `runFSM`): the producer's
channel state `prodS`, a batch's tuples (`itemRes`, `batchOk`, `cover`), and their laws.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto gprot

namespace github_com.hashicorp.raft.fsmProof

/-- The FSM producer's channel state with the end `e` of the last batch sent (`fsmProd` without
the no-command facts). -/
def prodS (rc : RCtx GF) (e : Nat) : IProp GF :=
  iprop(∃ (sent : List GoInterface) (Mb : GMap Nat Nat),
    spscProducer rc.names.fsmCh sent ∗ ghostMapAuth rc.names.batch 1 Mb ∗
    ⌜∀ m, (Mb.lookup m).isSome ↔ m < sent.length⌝ ∗
    ⌜∀ m k, Mb.lookup m = some k → k ≤ e⌝ ∗
    (⌜sent = [] ∧ e = 0⌝ ∨ ⌜sent ≠ []⌝ ∗ batchEnd rc (sent.length - 1) e))

/-- A batch's range is not empty. -/
theorem fsmBatchP_lt (γ : GNames) (rc : RCtx GF) (i : SID) (k0 k1 : Nat) (v : GoInterface) :
    fsmBatchP γ rc i k0 k1 v ⊢ fsmBatchP γ rc i k0 k1 v ∗ ⌜k0 < k1⌝ := by
  unfold fsmBatchP
  iintro ⟨%sl, %items, %Hv, #Hsl, %Hok, Hits, Hcov⟩
  isplitl
  · iexists sl, items; iframe; iframe #; ipureintro; exact ⟨Hv, Hok⟩
  · ipureintro
    obtain ⟨hne, -, hr, -⟩ := Hok
    obtain ⟨it, hit⟩ := List.exists_mem_of_ne_nil items hne
    have := hr it hit
    omega

/-- The batch value sent on `fsmMutateCh`: the slice boxed in an `interface{}`. -/
abbrev batchV (sl : GoSlice) : GoInterface :=
  interface.mkOk (go.GoType.SliceType (go.GoType.PointerType commitTuple.ty)) #sl

theorem prodS_send (γ : GNames) (rc : RCtx GF) (i : SID) (e k1 : Nat) (sl : GoSlice) :
    prodS rc e ∗ fsmBatchP γ rc i e k1 (batchV sl) ⊢ |==>
      ∃ sent : List GoInterface, spscProducer rc.names.fsmCh sent ∗
        fsmP γ rc i sent.length (batchV sl) ∗
        (spscProducer rc.names.fsmCh (sent ++ [batchV sl]) -∗ prodS rc k1) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

/-- The committed entry at `y` is no command. -/
abbrev noCmd (γ : GNames) (y : Nat) : IProp GF :=
  iprop(∃ e' : Entry, CIdx γ y e' ∗ ⌜e'.kind ≠ kCommand⌝)

/-- The indexes `(e, lk]` are the keys `ks` of the pending batch or hold no command
(`fsmBatchP`'s last conjunct). -/
def cover (γ : GNames) (e lk : Nat) (ks : List Nat) : IProp GF :=
  iprop([∗list] y ∈ List.range' (e + 1) (lk - e), ⌜y ∈ ks⌝ ∨ noCmd γ y)

omit package_sem in
theorem range'_split3 (e lk x : Nat) (h1 : e ≤ lk) (h2 : lk < x) :
    List.range' (e + 1) (x - e) =
      List.range' (e + 1) (lk - e) ++ List.range' (lk + 1) (x - (lk + 1)) ++ [x] := by
  have : x - e = (lk - e + (x - (lk + 1))) + 1 := by omega
  rw [this, List.range'_concat, ← List.range'_append]
  simp only [Nat.one_mul]
  congr 3 <;> omega

omit package_sem in
theorem noCmdBetween_snoc (γ : GNames) (lk x : Nat) (h : lk < x) :
    noCmdBetween (GF := GF) γ lk x ∗ noCmd γ x ⊢ noCmdBetween γ lk (x + 1) := by
  unfold noCmdBetween
  have h1 : x + 1 - (lk + 1) = (x - (lk + 1)) + 1 := by omega
  have h2 : lk + 1 + 1 * (x - (lk + 1)) = x := by omega
  rw [h1, List.range'_concat, h2]
  iintro ⟨Ht, Hx⟩
  iapply BigSepL.bigSepL_snoc.2
  iframe Ht
  iexact Hx

omit package_sem in
theorem noCmdBetween_self (γ : GNames) (k : Nat) : ⊢ noCmdBetween (GF := GF) γ k (k + 1) := by
  unfold noCmdBetween
  simp only [Nat.sub_self, List.range'_zero]
  iapply BigSepL.bigSepL_nil.2; itrivial

omit package_sem in
theorem cover_extend (γ : GNames) (e lk x : Nat) (ks : List Nat) (h1 : e ≤ lk) (h2 : lk < x) :
    cover (GF := GF) γ e lk ks ∗ noCmdBetween γ lk x ⊢ cover γ e x (ks ++ [x]) := by
  unfold cover noCmdBetween
  rw [range'_split3 e lk x h1 h2]
  iintro ⟨Hc, Ht⟩
  iapply BigSepL.bigSepL_append.2
  isplitl [Hc Ht]
  · iapply BigSepL.bigSepL_append.2
    isplitl [Hc]
    · iapply BigSepL.bigSepL_mono_of_forall (fun {_ y} => ?_) $$ Hc
      iintro (%Hy | H)
      · ileft; ipureintro; exact List.mem_append_left _ Hy
      · iright; iexact H
    · iapply BigSepL.bigSepL_mono_of_forall (fun {_ y} => ?_) $$ Ht
      iintro H; iright; iexact H
  · iapply BigSepL.bigSepL_singleton.2
    ileft; ipureintro; simp

theorem fsmProd_open (γ : GNames) (rc : RCtx GF) (a : Nat) :
    fsmProd γ rc a ⊢ ∃ e, prodS rc e ∗ ⌜e ≤ a⌝ ∗ noCmdBetween γ e (a + 1) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

theorem fsmProd_close (γ : GNames) (rc : RCtx GF) (e a : Nat) (h : e ≤ a) :
    prodS rc e ∗ noCmdBetween γ e (a + 1) ⊢ fsmProd γ rc a := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

/-- `futures[k]` on the futures map, which may be `nil` (a follower's call). -/
theorem wp_lookup_futs (fm : GoMap) (M : GMap w64 Loc) (k : w64) :
    {{ ⌜fm = null ∧ M = ∅⌝ ∨ (fm ↦$ M : IProp GF) }}
      (App (App (Val (map.lookup2 go.uint64 (go.GoType.PointerType logFuture.ty))) (Val #fm)) (Val #k))
    {{ RET (PairV #((M !! k).getD null) #(decide ((M !! k).isSome)));
        ⌜fm = null ∧ M = ∅⌝ ∨ (fm ↦$ M : IProp GF) }} := by
  iintro %Ψ Hfm HΨ
  icases Hfm with (⟨%Hn, %HM⟩ | Hfm)
  · subst Hn HM
    have h0 : ((∅ : GMap w64 Loc) !! k) = none := by simp
    rw [h0]
    simp only [Option.getD_none, Option.isSome_none, Bool.false_eq_true, decide_false]
    rw [show (null : Loc) = map.nil from rfl]
    wp_pures
    rw [show (map.nil : Loc) = zero_val Loc from rfl]
    iapply HΨ
    ileft; ipureintro; simp
  · wp_apply (wp_map_lookup2 go.uint64 (go.GoType.PointerType logFuture.ty) fm M k (DFrac.own 1))
      $$ [$Hfm] as Hfm
    iapply HΨ
    iright; iexact Hfm

/-- The resources of one tuple of a batch (`fsmBatchP`'s middle conjunct). -/
abbrev itemRes (γ : GNames) (rc : RCtx GF) (i : SID) (it : BatchItem) : IProp GF :=
  iprop(it.tp ↦□ commitTuple.mk it.lp it.fp ∗ logPtr it.lp it.k it.e ∗ CIdx γ it.k it.e ∗
      durLb γ i it.k ∗ ⌜it.e.kind = kCommand ∨ it.e.kind = kConfig ∨ it.e.kind = kBarrier⌝ ∗
      (⌜it.fp = null⌝ ∨ (⌜it.lp = (it.fp.[logFuture, go!"log"])⌝ ∗ futResp γ rc i it.fp it.k it.e)))

/-- The pure facts of a pending batch `its` after the end `e` of the last batch sent, whose last
key is `lk` (`= e` when empty). -/
def batchOk (e lk : Nat) (its : List BatchItem) : Prop :=
  (its.map BatchItem.k).Pairwise (· < ·) ∧ (∀ it ∈ its, e < it.k ∧ it.k ≤ lk) ∧
    (its.getLast?.map BatchItem.k = some lk ∨ (its = [] ∧ lk = e))

omit package_sem in
theorem batchOk_snoc (e lk x : Nat) (its : List BatchItem) (it : BatchItem) (h : batchOk e lk its)
    (hel : e ≤ lk) (hlk : lk < x) (hk : it.k = x) : batchOk e x (its ++ [it]) := by
  obtain ⟨hp, hr, -⟩ := h
  refine ⟨?_, ?_, Or.inl (by simp [hk])⟩
  · rw [List.map_append, List.pairwise_append]
    refine ⟨hp, by simp, ?_⟩
    intro a ha b hb
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
    subst hb
    obtain ⟨it', hit', rfl⟩ := List.mem_map.mp ha
    have := (hr it' hit').2
    omega
  · intro it' hit'
    rcases List.mem_append.mp hit' with h' | h'
    · have := hr it' h'; omega
    · simp only [List.mem_singleton] at h'; subst h'; omega

theorem fsmBatchP_intro (γ : GNames) (rc : RCtx GF) (i : SID) (e k1 : Nat) (sl : GoSlice)
    (its : List BatchItem) (hb : batchOk e k1 its) (hne : its ≠ []) :
    sl ↦*□ its.map BatchItem.tp ∗ ([∗list] it ∈ its, itemRes γ rc i it) ∗
      cover γ e k1 (its.map BatchItem.k) ⊢ fsmBatchP γ rc i e k1 (batchV sl) := by
  obtain ⟨hp, hr, hl⟩ := hb
  have hl' : its.getLast?.map BatchItem.k = some k1 := by
    rcases hl with hl | ⟨h, -⟩
    · exact hl
    · exact absurd h hne
  iintro ⟨#Hsl, Hits, Hcov⟩
  unfold fsmBatchP cover
  iexists sl, its
  iframe Hsl Hits Hcov
  ipureintro
  exact ⟨rfl, hne, hp, hr, hl'⟩

/-! ### The consumer side -/

omit package_sem in
theorem range'_split3' (p k k1 : Nat) (h1 : p < k) (h2 : k ≤ k1) :
    List.range' (p + 1) (k1 - p) =
      List.range' (p + 1) (k - (p + 1)) ++ [k] ++ List.range' (k + 1) (k1 - k) := by
  have : k1 - p = (k - (p + 1)) + ((k1 - k) + 1) := by omega
  rw [this, ← List.range'_append_1]
  have h3 : p + 1 + (k - (p + 1)) = k := by omega
  rw [h3, List.range'_succ, List.append_assoc]
  rfl

omit package_sem in
theorem range'_bounds {s n j y : Nat} (h : (List.range' s n)[j]? = some y) : s ≤ y ∧ y < s + n := by
  have hj : j < n := by
    have := (List.getElem?_eq_some_iff.mp h).1
    simpa using this
  rw [List.getElem?_range' hj] at h
  injection h with h'
  omega

omit package_sem in
theorem noCmdBetween_app (γ : GNames) (k0 p k : Nat) (h1 : k0 ≤ p) (h2 : p < k) :
    noCmdBetween (GF := GF) γ k0 (p + 1) ∗ noCmdBetween γ p k ⊢ noCmdBetween γ k0 k := by
  unfold noCmdBetween
  have : k - (k0 + 1) = (p + 1 - (k0 + 1)) + (k - (p + 1)) := by omega
  rw [this, ← List.range'_append]
  have h3 : k0 + 1 + 1 * (p + 1 - (k0 + 1)) = p + 1 := by omega
  rw [h3]
  iintro ⟨H1, H2⟩
  iapply BigSepL.bigSepL_append.2
  iframe

/-- The remaining indexes `(p, k1]` of a batch being applied, with its remaining tuples `rest`. -/
def coverRest (γ : GNames) (p k1 : Nat) (rest : List BatchItem) : IProp GF :=
  iprop([∗list] y ∈ List.range' (p + 1) (k1 - p), ⌜y ∈ rest.map BatchItem.k⌝ ∨ noCmd γ y)

omit package_sem in
theorem coverRest_step (γ : GNames) (p k1 : Nat) (it : BatchItem) (rest : List BatchItem)
    (h1 : p < it.k) (h2 : it.k ≤ k1) (hr : ∀ b ∈ rest, it.k < b.k) :
    coverRest (GF := GF) γ p k1 (it :: rest) ⊢ noCmdBetween γ p it.k ∗ coverRest γ it.k k1 rest := by
  unfold coverRest noCmdBetween
  rw [range'_split3' p it.k k1 h1 h2]
  iintro H
  icases BigSepL.bigSepL_append.1 $$ H with ⟨H12, H3⟩
  icases BigSepL.bigSepL_append.1 $$ H12 with ⟨H1, -⟩
  isplitl [H1]
  · iapply BigSepL.bigSepL_mono (fun {j y} hy => ?_) $$ H1
    have hb := range'_bounds hy
    iintro (%Hm | H)
    · exfalso
      simp only [List.map_cons, List.mem_cons] at Hm
      rcases Hm with Hm | Hm
      · omega
      · obtain ⟨b, hb, hbk⟩ := List.mem_map.mp Hm
        have := hr b hb
        omega
    · iexact H
  · iapply BigSepL.bigSepL_mono (fun {j y} hy => ?_) $$ H3
    have hlt : it.k < y := (range'_bounds hy).1
    iintro (%Hm | H)
    · ileft; ipureintro
      simp only [List.map_cons, List.mem_cons] at Hm
      rcases Hm with Hm | Hm
      · omega
      · exact Hm
    · iright; iexact H

omit package_sem in
theorem pairwise_drop_head (items : List BatchItem) (j : Nat) (it : BatchItem) (rest : List BatchItem)
    (hp : (items.map BatchItem.k).Pairwise (· < ·)) (hd : items.drop j = it :: rest) :
    ∀ b ∈ rest, it.k < b.k := by
  have h : ((items.drop j).map BatchItem.k).Pairwise (· < ·) := by
    rw [List.map_drop]; exact hp.sublist (List.drop_sublist _ _)
  rw [hd, List.map_cons, List.pairwise_cons] at h
  intro b hb
  exact h.1 _ (List.mem_map_of_mem hb)

end github_com.hashicorp.raft.fsmProof

end proof

end Perennial
