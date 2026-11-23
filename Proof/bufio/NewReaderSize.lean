/-
`bufio.NewReaderSize` (see `Spec/bufio/NewReaderSize.lean`).
-/
module

public import Spec.bufio.NewReaderSize

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

theorem bufio.NewReaderSize.wp_proof : bufio.NewReaderSize.spec (GF := GF) (hG := hG) := by
  intro ri Pre S E R size hty hpre
  wp_start as ⟨#Hrd, HS⟩
  try wp_auto
  simp only [ite_eq_right_of_eq_false _ _ (eq_false hty), decide_eq_false hty]
  try wp_auto
  wp_apply bufio.wp_max_int as %m %Hm
  have hm16 : sint.Z (W64 16) = 16 := rfl
  have hmZ : sint.Z m = max (sint.Z size) 16 := by
    rcases Hm with ⟨rfl | rfl, h1, h2⟩
    · rw [hm16] at h2; omega
    · rw [hm16] at h1 ⊢; omega
  wp_apply (wp_slice_make2 (V := w8) m) as %sl ⟨Hsl, -⟩
  · ipureintro; omega
  wp_apply bufio.wp_reset $$ [$«$r0»] as Hr
  try wp_auto
  iapply HΦ
  unfold bufio.ownBufReader bufio.readerRep
  iframe Hpkg Hrd
  iexists [], interface.nil
  rw [List.append_nil]
  iframe HS
  iexists sl, 0, 0, W64 (-1), W64 (-1), [], List.replicate (sint.nat m) (zero_val w8)
  simp only [List.nil_append, List.length_nil, List.append_nil, List.length_replicate]
  iframe Hr Hsl
  isplitr
  · ipureintro
    refine ⟨rfl, rfl, ?_, ?_, _root_.Perennial.io.ptrTyped_nil⟩
    · show 0 < (sint.Z m).toNat; omega
    · show bufio.preUpTo Pre (sint.Z m).toNat
      rw [hmZ]; exact hpre
  unfold _root_.Perennial.io.errAt
  ileft; ipureintro; rfl

end proof

end EtcdGrove
end Perennial
