/-
A range loop over a slice the loop only reads, for the loops that spell out `fmt`'s `%v` of a slice
in `UnconditionalPartsOrFailClosed`, `ConditionsAwareDecisionUnion.Add` and the union authorizer's
`EvaluateConditions` (the fork's `goose-lean-authz-fmt2`, 2026-11-24, mit-pdos/etcd-grove#9). A copy
of `Proof/k8s_io/api/DeepCopyBase.lean`'s `wp_slice_for_range` (as `DescribeConfChange`'s), which
these packages do not import. Lean-first.
-/
module

public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authorizer

open Iris Iris.BI Iris.ProofMode

attribute [-instance] pure_wp_slice_for_range

section loop
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A range loop over a slice the loop only reads** (`for i, x := range s { body }`): `P i` holds
before the `i`-th iteration, and the body ends normally. -/
theorem wp_slice_for_range_ro {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (t : go.GoType)
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
  wp_auto
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
    wp_auto
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
    wp_auto
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

end authorizer
end EtcdGrove
end Perennial
