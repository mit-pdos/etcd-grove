/-
`bufio.NewReader` (see `Spec/bufio/NewReader.lean`).
-/
module

public import Spec.bufio.NewReader
public import Proof.bufio.Base

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
  isplitl []
  · ipureintro
    rw [List.length_replicate]
    exact ⟨trivial, by word, by word, by word, by omega, by omega⟩
  iapply io.errAt_nil

end proof

end EtcdGrove
end Perennial
