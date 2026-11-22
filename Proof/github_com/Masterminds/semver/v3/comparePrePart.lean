/-
Proof of `Spec/github_com/Masterminds/semver/v3/comparePrePart.lean` over the real code
(prove-ps2-semver, 2026-11-22), over `strconv.ParseUint`'s spec.
-/
module

public import Spec.github_com.Masterminds.semver.v3.comparePrePart
public import Perennial.Spec.strconv.ParseUint

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.Masterminds.semver.v3.Assumptions]

set_option linter.unusedSimpArgs false in
theorem semver.comparePrePart.wp_proof
    (wp_ParseUint : _root_.Perennial.strconv.ParseUint.spec (GF := GF) (hG := hG)) :
    semver.comparePrePart.spec (GF := GF) (hG := hG) := by
  intro s o
  wp_start as -
  ihave #Hsc : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  wp_auto
  unfold semver.cmpPrePart
  by_cases hso : s = o
  · subst hso
    simp only [decide_true, ↓reduceIte]
    wp_auto
    iapply HΦ; itrivial
  simp only [hso, decide_false, ↓reduceIte]
  wp_auto
  by_cases hs : s = []
  · subst hs
    have ho : o ≠ [] := fun h => hso h.symm
    simp only [ho, ne_eq, not_false_eq_true, decide_true, decide_false, Bool.not_true,
      Bool.not_false, ↓reduceIte]
    wp_auto
    simp only [decide_eq_false ho, Bool.not_false]
    wp_auto
    iapply HΦ; itrivial
  by_cases ho : o = []
  · subst ho
    simp only [hs, ne_eq, not_false_eq_true, decide_true, decide_false, Bool.not_true,
      Bool.not_false, ↓reduceIte]
    wp_auto
    simp only [decide_eq_false hs, Bool.not_false]
    wp_auto
    iapply HΦ; itrivial
  simp only [hs, ho, decide_false, ↓reduceIte]
  wp_auto
  simp only [decide_eq_false ho]
  wp_auto
  wp_apply (wp_ParseUint o (W64 10) (W64 64) (by word) (by word) (by word) (by word)) as %oi %n1 Ho1
  wp_apply (wp_ParseUint s (W64 10) (W64 64) (by word) (by word) (by word) (by word)) as %si %n2 Hs1
  ihave %H1 : ⌜(∃ n, internal.strconv.parseUint o 10 64 = .ok n ∧ oi = W64 n ∧
      n1 = GoInterface.nil) ∨
      ((∀ n, internal.strconv.parseUint o 10 64 ≠ .ok n) ∧ n1 ≠ GoInterface.nil)⌝ $$ [Ho1]
  · cases hpo : internal.strconv.parseUint o 10 64
    · icases Ho1 with %h12
      ipureintro; exact Or.inl ⟨_, rfl, h12.1, h12.2⟩
    all_goals
      icases Ho1 with ⟨-, Ho1⟩
      iunfold _root_.Perennial.strconv.numErrorOf at Ho1
      icases Ho1 with ⟨%l, %e, %he, -, -⟩
      ipureintro; refine Or.inr ⟨fun n h => (by cases h), ?_⟩
      rw [he]; intro h; cases h
  ihave %H2 : ⌜(∃ n, internal.strconv.parseUint s 10 64 = .ok n ∧ si = W64 n ∧
      n2 = GoInterface.nil) ∨
      ((∀ n, internal.strconv.parseUint s 10 64 ≠ .ok n) ∧ n2 ≠ GoInterface.nil)⌝ $$ [Hs1]
  · cases hps : internal.strconv.parseUint s 10 64
    · icases Hs1 with %h12
      ipureintro; exact Or.inl ⟨_, rfl, h12.1, h12.2⟩
    all_goals
      icases Hs1 with ⟨-, Hs1⟩
      iunfold _root_.Perennial.strconv.numErrorOf at Hs1
      icases Hs1 with ⟨%l, %e, %he, -, -⟩
      ipureintro; refine Or.inr ⟨fun n h => (by cases h), ?_⟩
      rw [he]; intro h; cases h
  rcases H1 with ⟨no, hpo, rfl, rfl⟩ | ⟨hpo, hn1⟩ <;>
    rcases H2 with ⟨ns, hps, rfl, rfl⟩ | ⟨hps, hn2⟩
  · simp only [hpo, hps]
    wp_auto
    by_cases hlt : uint.Z (W64 no) < uint.Z (W64 ns)
    · simp only [hlt, decide_true, ↓reduceIte]
      wp_auto
      iapply HΦ; itrivial
    · simp only [hlt, decide_false, ↓reduceIte]
      wp_auto
      iapply HΦ; itrivial
  · generalize hrs : internal.strconv.parseUint s 10 64 = rs at hps ⊢
    simp only [hpo]
    cases n2 with
    | nil => exact absurd rfl hn2
    | ok i2 =>
    cases rs
    · exact absurd rfl (hps _)
    all_goals
      wp_auto
      iapply HΦ; itrivial
  · generalize hro : internal.strconv.parseUint o 10 64 = ro at hpo ⊢
    simp only [hps]
    cases n1 with
    | nil => exact absurd rfl hn1
    | ok i1 =>
    cases ro
    · exact absurd rfl (hpo _)
    all_goals
      wp_auto
      iapply HΦ; itrivial
  · generalize hro : internal.strconv.parseUint o 10 64 = ro at hpo ⊢
    generalize hrs : internal.strconv.parseUint s 10 64 = rs at hps ⊢
    cases n1 with
    | nil => exact absurd rfl hn1
    | ok i1 =>
    cases n2 with
    | nil => exact absurd rfl hn2
    | ok i2 =>
    cases ro
    · exact absurd rfl (hpo _)
    all_goals
      cases rs
      · exact absurd rfl (hps _)
      all_goals
        wp_auto
        by_cases hlt : go.GoStringLt o s
        · simp only [hlt, decide_true, ↓reduceIte]
          wp_auto
          iapply HΦ; itrivial
        · simp only [hlt, decide_false, ↓reduceIte]
          wp_auto
          iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
