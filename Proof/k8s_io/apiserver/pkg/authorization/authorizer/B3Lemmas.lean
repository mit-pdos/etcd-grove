/-
Lean-first (no Rocq counterpart).

Lemmas for the proofs of the union builder (`conditionsunion.go`: `Add`, `ToDecision`,
`collectReasonsAndErrors`): slices at a common fraction (`slices.Concat` takes its slices at one
fraction, and `collectReasonsAndErrors` concatenates its caller's prefix, at any fraction, with a
fresh literal), and pure facts about the model.
-/
module

public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authorizer

open Iris Iris.BI Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer

section pure
variable [GooseExts]

/-- Membership in `insertAll s ks`: in `s` or among `ks`. -/
theorem insertAll_isSome_b3 {K : Type} [DecidableEq K] (s : GMap K sets.Elem) (ks : List K) (k : K) :
    ((sets.insertAll s ks) !! k).isSome = Bool.or ((s !! k).isSome) (decide (k ∈ ks)) := by
  induction ks generalizing s with
  | nil => simp
  | cons k' ks ih =>
    rw [sets.insertAll_cons, ih]
    rw [GMap.lookup_insert_eq_iff]
    by_cases h : k' = k
    · subst h; simp
    · simp [h, Ne.symm h]

theorem PD.has_or_b3 (p q : PD) (k : w64) : (PD.or p q).has k = Bool.or (p.has k) (q.has k) := by
  unfold PD.or PD.has
  generalize decide (k = W64 0) = a
  generalize decide (k = W64 1) = b
  generalize decide (k = W64 2) = c
  cases p.deny <;> cases p.allow <;> cases p.noOpinion <;> cases q.deny <;> cases q.allow <;>
    cases q.noOpinion <;> cases a <;> cases b <;> cases c <;> rfl

theorem PD.has_empty (k : w64) : PD.empty.has k = false := by
  unfold PD.empty PD.has; simp

theorem Dec.subL_append_has (ks : List Dec) (m : Dec) (k : w64) :
    (Dec.subL (ks ++ [m])).has k = Bool.or ((Dec.subL ks).has k) ((Dec.pd m).has k) := by
  induction ks with
  | nil => simp [Dec.subL, PD.has_or_b3, PD.has_empty]
  | cons k' ks ih =>
    simp only [List.cons_append, Dec.subL, PD.has_or_b3, ih]
    cases (Dec.pd k').has k <;> cases (Dec.subL ks).has k <;> cases (Dec.pd m).has k <;> rfl

theorem Dec.cuadL_append (ks : List Dec) (m : Dec) :
    Dec.cuadL (ks ++ [m]) = Bool.or (Dec.cuadL ks) m.cuad := by
  induction ks with
  | nil => simp [Dec.cuadL]
  | cons k ks ih =>
    simp only [List.cons_append, Dec.cuadL, ih]
    cases Dec.cuad k <;> cases Dec.cuadL ks <;> cases m.cuad <;> rfl

theorem Dec.WFL_append (ks : List Dec) (m : Dec) (h : Dec.WFL ks) (hm : m.WF) :
    Dec.WFL (ks ++ [m]) := by
  induction ks with
  | nil => exact ⟨hm, trivial⟩
  | cons k ks ih => exact ⟨h.1, ih h.2⟩

/-- `Add`'s set: the children's possible decisions with the new child's. -/
theorem setIs_insertAll_b3 (S P : GMap w64 sets.Elem) (ks : List Dec) (m : Dec) (ps : List w64)
    (hS : setIs S (Dec.subL ks)) (hP : setIs P m.pd) (hps : ∀ k, k ∈ ps ↔ (P !! k).isSome) :
    setIs (sets.insertAll S ps) (Dec.subL (ks ++ [m])) := by
  intro k
  rw [insertAll_isSome_b3, Dec.subL_append_has, hS k, ← hP k]
  congr 1
  by_cases h : (P !! k).isSome = true
  · rw [h]; exact decide_eq_true ((hps k).2 h)
  · have h' : (P !! k).isSome = false := by simpa using h
    rw [h']; exact decide_eq_false (fun hk => h ((hps k).1 hk))

/-- A Go set of decisions has as many elements as its `PD` (`Len()`). -/
theorem setIs_size (S : GMap w64 sets.Elem) (p : PD) (h : setIs S p) :
    GMap.size S = p.card := by
  rw [GMap.size_eq_length S ([W64 0, W64 1, W64 2].filter (fun k => p.has k)) ?_ ?_]
  · obtain ⟨a, b, c⟩ := p
    cases a <;> cases b <;> cases c <;> rfl
  · exact List.Pairwise.sublist List.filter_sublist (by decide)
  · intro k
    rw [h k, List.mem_filter]
    constructor
    · exact fun hk => hk.2
    · intro hk
      refine ⟨?_, hk⟩
      rcases PD.has_valid p k hk with rfl | rfl | rfl <;> simp

mutual
/-- A decision containing an unconditional Allow or Deny may evaluate to Allow or Deny. -/
theorem Dec.cuad_pd : ∀ m : Dec, m.cuad = true → m.pd.deny = true ∨ m.pd.allow = true
  | .deny, _ => Or.inl rfl
  | .allow, _ => Or.inr rfl
  | .noOpinion, h => by simp [Dec.cuad] at h
  | .cmap _ _ _, h => by simp [Dec.cuad] at h
  | .union ks, h => by
    simp only [Dec.pd]
    exact Dec.cuadL_subL ks h
theorem Dec.cuadL_subL : ∀ ks : List Dec, Dec.cuadL ks = true →
    (Dec.subL ks).deny = true ∨ (Dec.subL ks).allow = true
  | [], h => by simp [Dec.cuadL] at h
  | k :: ks, h => by
    simp only [Dec.cuadL, Bool.or_eq_true] at h
    simp only [Dec.subL, PD.or, Bool.or_eq_true]
    rcases h with h | h
    · rcases Dec.cuad_pd k h with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr (Or.inl h')
    · rcases Dec.cuadL_subL ks h with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr (Or.inr h')
end

/-- A union may evaluate to some decision. -/
theorem Dec.union_card_pos (ks : List Dec) : 1 ≤ (Dec.pd (.union ks)).card := by
  have key : ∀ a b c : Bool, (c = true ∨ a = true ∨ b = true) → 1 ≤ (PD.mk a b c).card := by
    decide
  simp only [Dec.pd]
  apply key
  cases hc : Dec.cuadL ks
  · exact Or.inl rfl
  · exact Or.inr (Dec.cuadL_subL ks hc)

end pure

section decs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.authorizer.Assumptions]

theorem isDecisionRawL_snoc : ∀ (ds : List ConditionsAwareDecision) (ks : List Dec)
    (d : ConditionsAwareDecision) (m : Dec),
    iprop(□ isDecisionRawL ds ks) ⊢ (□ isDecisionRaw d m -∗ □ isDecisionRawL (ds ++ [d]) (ks ++ [m]) : IProp GF)
  | [], [], d, m => by
    simp only [List.nil_append, isDecisionRawL]
    iintro - #H
    imodintro
    isplitl
    · iexact H
    · itrivial
  | [], _ :: _, _, _ => by
    simp only [isDecisionRawL]
    iintro #H
    iexfalso; iexact H
  | _ :: _, [], _, _ => by
    simp only [isDecisionRawL]
    iintro #H
    iexfalso; iexact H
  | d' :: ds, k :: ks, d, m => by
    simp only [List.cons_append, isDecisionRawL]
    iintro #⟨#H1, #H2⟩ #H
    imodintro
    isplitl
    · iexact H1
    · iapply isDecisionRawL_snoc ds ks d m $$ H2 H

/-- A union builder's children with a new one. -/
theorem isDecisionL_snoc (ds : List ConditionsAwareDecision) (ks : List Dec)
    (d : ConditionsAwareDecision) (m : Dec) :
    isDecisionL (GF := GF) ds ks ⊢ isDecision d m -∗ isDecisionL (ds ++ [d]) (ks ++ [m]) := by
  unfold isDecisionL isDecision
  iintro #H1 #H2
  iapply isDecisionRawL_snoc ds ks d m $$ H1 H2

end decs

section slices
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- An empty slice holds at any fraction. -/
theorem ownSlice_nil_frac {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (s : GoSlice)
    (dq dq' : DFrac) : (s ↦*{dq} ([] : List V) : IProp GF) ⊢ s ↦*{dq'} ([] : List V) := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, %Hc⟩)
  · ileft; ipureintro; exact H
  · icases typedPointsto_not_null _ _ _ $$ H with %Hnn
    icases array_len _ _ _ _ $$ H with %Hlen
    iright
    isplitl []
    · have Hlen' : sint.Z s.len = 0 := by simpa using Hlen
      rw [Hlen']
      iapply array_empty _ _ Hnn
    · ipureintro; exact Hc

/-- A non-empty slice of strings is owned at a valid fraction. -/
theorem ownSlice_string_valid' (s : GoSlice) (dq : DFrac) (x : GoString) (xs : List GoString) :
    (s ↦*{dq} (x :: xs) : IProp GF) ⊢ ⌜✓ dq⌝ := by
  have hx : typedPointsto (GF := GF) (arrayIndexRef GoString 0 s.ptr) x dq ⊢ ⌜✓ dq⌝ :=
    (typedPointsto_split _ _ _).trans (heapPointsto_valid _ _ _)
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, %Hc⟩)
  · exact absurd H.2 (List.cons_ne_nil _ _)
  · icases array_acc s.ptr 0 dq _ _ x (Int.le_refl 0) rfl $$ H with ⟨Hx, -⟩
    iapply hx $$ Hx

/-- A non-empty slice of strings is owned at a valid fraction (keeping it). -/
theorem ownSlice_string_valid (s : GoSlice) (dq : DFrac) (x : GoString) (xs : List GoString) :
    (s ↦*{dq} (x :: xs) : IProp GF) ⊢ ⌜✓ dq⌝ ∗ s ↦*{dq} (x :: xs) :=
  persistent_entails_right (ownSlice_string_valid' s dq x xs)

/-- A slice of strings at any fraction and an owned one, both at one fraction (for
`slices.Concat`), with the first's return. -/
theorem ownSlice_string_common (s t : GoSlice) (dq : DFrac) (xs ys : List GoString) :
    (s ↦*{dq} xs ∗ t ↦* ys : IProp GF) ⊢ |==> ∃ dq' : DFrac, s ↦*{dq'} xs ∗ t ↦*{dq'} ys ∗
      (s ↦*{dq'} xs -∗ s ↦*{dq} xs) := by
  cases xs with
  | nil =>
    iintro ⟨Hs, Ht⟩
    imodintro
    iexists DFrac.own 1
    iframe Ht
    isplitl [Hs]
    · iapply ownSlice_nil_frac $$ Hs
    · iintro Hs
      iapply ownSlice_nil_frac $$ Hs
  | cons x xs =>
    iintro ⟨Hs, Ht⟩
    icases ownSlice_string_valid s dq x xs $$ Hs with ⟨%Hv, Hs⟩
    imod ownSlice_update_to_dfrac dq t ys Hv $$ Ht with Ht
    imodintro
    iexists dq
    iframe Hs Ht
    iintro Hs; iexact Hs

end slices

end authorizer
end EtcdGrove
end Perennial
