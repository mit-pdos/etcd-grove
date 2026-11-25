/-
net/http's `parsePattern` on a literal path pattern (`litPat`, `MuxTree.lean`): no method, no host,
its segments `pathSegs p` (`segVal`), no error.
-/
module

public import Net.Proof.net.http.MuxTree
public import Perennial.Spec.strings.IndexAny

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.perennial.goose.model.strings (wp_string_len)

namespace net.http

theorem indexAnyByte_none (s chars : List w8) (h : ∀ b ∈ s, b ∉ chars) :
    strings.indexAnyByte s chars = -1 := by
  unfold strings.indexAnyByte
  have : s.findIdx (fun b => decide (b ∈ chars)) = s.length := by
    rw [List.findIdx_eq_length]; intro b hb; simpa using h b hb
  rw [this]; simp

section wp
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]

set_option maxRecDepth 20000 in
/-- `parsePattern(p)` of a literal pattern. -/
theorem wp_parsePattern_lit (wp_IndexAny : strings.IndexAny.spec (GF := GF) (hG := hG))
    (wp_IndexByte : strings.IndexByte.spec (GF := GF) (hG := hG))
    (wp_PathUnescape : net.url.PathUnescape.spec (GF := GF) (hG := hG))
    (p : List w8) (hp : litPat p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings ∗ isPkgInit (PROP := IProp GF) pkg_id.net.url }}
      (App (Val (@! net.http.parsePattern)) (Val #p))
    {{ (pp : Loc) (sl : GoSlice), RET (PairV #pp #(interface.nil : GoInterface));
        pp ↦ ({ str' := p, method' := [], host' := [], segments' := sl, loc' := [] } : net.http.pattern) ∗
        sl ↦* ((pathSegs p).map segVal) ∗ ownSliceCap net.http.segment sl (DFrac.own 1) }} := by
  wp_start as ⟨#Hstr, #Hurl⟩
  try wp_auto
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  have hpne : p ≠ [] := by intro h; rw [h] at hp; simp [litPat] at hp
  wp_apply wp_string_len as %Hl
  try wp_auto
  rw [decide_eq_false (show W64 (p.length : Int) ≠ W64 0 by
    have : 0 < p.length := List.length_pos_iff.mpr hpne; word)]
  try wp_auto
  wp_apply wp_IndexAny p _ as %i %Hi
  have hi : i = W64 (-1) := by
    rw [Hi (by intro b hb; simp at hb; rcases hb with rfl | rfl <;> decide)]
    rw [indexAnyByte_none]
    intro b hb hbc
    have := hp.2 b hb
    simp at hbc; rcases hbc with rfl | rfl <;> simp [pathByte] at this
  subst hi
  try wp_auto
  have hp0 : p[0]? = some (W8 47) := by
    cases p with | nil => exact absurd rfl hpne | cons a l => simpa [litPat] using hp.1
  wp_apply wp_IndexByte
  rw [internal.bytealg.indexByte_eq_of p (W8 47) 0 hp0 (fun j hj => absurd hj (Nat.not_lt_zero _))]
  try wp_auto
  sorry

end wp

end net.http
end Perennial
