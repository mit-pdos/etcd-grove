/-
Proof of `Spec/k8s_io/apimachinery/pkg/runtime/SchemeBuilder__Register.lean` (prove-metav1,
2026-11-27): the range over `funcs`, each iteration `*sb = append(*sb, f)` (`wp_slice_append`), the
invariant `*sb` holding `xs ++ fs.take i`.
-/
module

public import Spec.k8s_io.apimachinery.pkg.runtime.SchemeBuilder__Register

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

attribute [-instance] pure_wp_slice_for_range

section loop
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A range loop over a slice the loop only reads** (`for i, x := range s { body }`): `P i` holds
before the `i`-th iteration, and the body ends normally. (A copy of
`Proof/k8s_io/api/DeepCopyBase.lean`'s `wp_slice_for_range`, which this package does not import.) -/
private theorem wp_slice_for_range_ro {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (t : go.GoType)
    [IntoValTyped (GF := GF) V t] (sl : GoSlice) (vs : List V) (dq : DFrac) (body : GoFunc)
    (P : Nat → IProp GF) (Φ : val → IProp GF) :
    sl ↦*{dq} vs -∗ P 0 -∗
    □ (∀ (i : Nat) (x : V), ⌜vs[i]? = some x⌝ -∗ P i -∗ sl ↦*{dq} vs -∗
        WP (App (App (Val #body) (Val #(W64 i))) (Val #x))
          {{ bv, ⌜bv = executeVal⌝ ∗ P (i + 1) ∗ sl ↦*{dq} vs }}) -∗
    (P vs.length -∗ sl ↦*{dq} vs -∗ Φ executeVal) -∗
    WP (App (App (Val (slice.forRange t)) (Val #sl)) (Val #body)) {{ Φ }} := by
  iintro Hs HP #Hiter HΦ
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  unfold slice.forRange
  try wp_auto
  ihave Hinv : (∃ (j : Nat), "i" ∷ i_ptr ↦ W64 j ∗ "HP" ∷ P j ∗ "Hs" ∷ sl ↦*{dq} vs ∗
      "HΦ" ∷ (P vs.length -∗ sl ↦*{dq} vs -∗ Φ executeVal) ∗ "%Hj" ∷ ⌜j ≤ vs.length⌝ :
      IProp GF) $$ [i HP Hs HΦ]
  · iexists 0
    iframe
    ipureintro; omega
  wp_for Hinv
  by_cases hj : j < vs.length
  · have hc : sint.Z (W64 (j : Int)) < sint.Z sl.len := by word
    simp only [decide_eq_true hc, ↓reduceIte]
    try wp_auto
    have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
    simp only [h0, hc, and_self, ↓reduceIte]
    have hsj : (sint.Z (W64 (j : Int))).toNat = j := by word
    obtain ⟨x, hx⟩ : ∃ x, vs[j]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
    wp_apply (wp_load_slice_index (t := t) sl (sint.Z (W64 (j : Int))) vs dq x h0) $$ [Hs] as Hs
    · iframe; ipureintro; rw [hsj]; exact hx
    iapply wp_wand $$ (Hiter $$ %j %x %hx HP Hs)
    iintro %bv ⟨%hbv, HP, Hs⟩
    subst hbv
    iapply wp_for_post_do
    try wp_auto
    iframe
    iexists (j + 1)
    have hw : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
    rw [hw]
    have hj1 : j + 1 ≤ vs.length := hj
    iframe
    ipureintro; exact hj1
  · have hc : ¬ sint.Z (W64 (j : Int)) < sint.Z sl.len := by word
    simp only [decide_eq_false hc, Bool.false_eq_true, ↓reduceIte]
    have hjl : j = vs.length := by omega
    subst hjl
    iapply HΦ $$ HP Hs

end loop

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.runtime.Assumptions]

theorem runtime.SchemeBuilder.Register.wp_proof :
    runtime.SchemeBuilder.Register.spec (GF := GF) (hG := hG) := by
  intro sb s xs funcs fs dq
  wp_start as ⟨Hsb, Hs, Hcap, Hf⟩
  try wp_auto
  ihave %Hfl := ownSlice_len _ _ _ $$ Hf
  wp_apply (wp_slice_for_range_ro (V := GoFunc) _ funcs fs dq _
    (fun i => iprop(∃ s' : GoSlice, sb ↦ s' ∗ s' ↦* (xs ++ fs.take i) ∗
      ownSliceCap GoFunc s' (DFrac.own 1) ∗ sb_ptr ↦ sb ∗ ∃ g : GoFunc, f_ptr ↦ g))) $$ Hf [Hsb Hs Hcap sb f]
  · iexists s
    simp only [List.take_zero, List.append_nil]
    iframe
  · imodintro
    iintro %i %x %hx ⟨%s1, Hsb, Hs, Hcap, sb, %g, f⟩ Hf
    try wp_auto
    wp_apply wp_slice_literal (V := GoFunc)
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    try wp_auto
    wp_apply (wp_slice_append s1 (xs ++ fs.take i) _ [x] _) $$ [Hs Hcap Hsl] as %s2 ⟨Hs, Hcap, -⟩
    · iframe
    try wp_auto
    have hi : i < fs.length := (List.getElem?_eq_some_iff.1 hx).1
    have htake : fs.take (i + 1) = fs.take i ++ [x] := by
      rw [List.take_add_one, hx]; rfl
    isplitr
    · ipureintro; rfl
    iframe
    rw [htake, ← List.append_assoc]
    iframe
  · iintro ⟨%s', Hsb, Hs, Hcap, -, -⟩ Hf
    rw [List.take_length]
    try wp_auto
    iapply HΦ
    iexists s'
    iframe

end proof

end EtcdGrove
end Perennial
