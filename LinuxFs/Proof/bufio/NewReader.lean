/-
`bufio.NewReader` (see `LinuxFs/Spec/bufio/NewReader.lean`).
-/
module

public import LinuxFs.Spec.bufio.NewReader

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.bufio.Assumptions]

/-- The builtin `max` of two `int`s: the larger. -/
theorem bufio.wp_max_int (x y : w64) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions go.max [go.int, go.int])) (Val #x)) (Val #y))
    {{ (m : w64), RET #m; ⌜(m = x ∨ m = y) ∧ sint.Z x ≤ sint.Z m ∧ sint.Z y ≤ sint.Z m⌝ }} := by
  wp_start
  wp_if_destruct
  · iapply HΦ; ipureintro; refine ⟨Or.inl rfl, Int.le_refl _, ?_⟩; word
  · iapply HΦ; ipureintro; refine ⟨Or.inr rfl, ?_, Int.le_refl _⟩; word

theorem bufio.NewReader.wp_proof : bufio.NewReader.spec (GF := GF) (hG := hG) := by
  intro ri S E r hty
  wp_start as HS
  try wp_auto
  wp_func_call
  wp_call
  try wp_auto
  simp only [ite_eq_right_of_eq_false _ _ (eq_false hty), decide_eq_false hty]
  try wp_auto
  wp_apply bufio.wp_max_int as %m %Hm
  have hm : m = W64 4096 := by
    rcases Hm with ⟨rfl | rfl, h1, h2⟩
    · rfl
    · revert h1; word
  subst hm
  wp_apply (wp_slice_make2 (V := w8) (W64 4096)) as %sl ⟨Hsl, -⟩
  · ipureintro; word
  wp_method_call
  wp_call
  try wp_auto
  iapply HΦ
  iunfold bufio.ownReader
  isplitr
  · iexact Hpkg
  iexists _, _
  iframe «$r0» Hsl
  have hz : ∀ l : List w8, r ++ subslice (sint.nat (0 : w64)) (sint.nat (0 : w64)) l = r := fun l => by
    simp only [subslice, show sint.nat (0 : w64) = 0 from rfl, List.take_zero, List.drop_nil,
      List.append_nil]
  simp only []
  rw [hz]
  iframe HS
  ipureintro
  rw [List.length_replicate]
  exact ⟨⟨trivial, by word, by word, by word, by omega⟩, fun h => absurd rfl h⟩

end proof

end EtcdGrove
end Perennial
