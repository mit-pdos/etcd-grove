/-
`bufio.NewReaderSize.specFresh` over its body, and `bufio.NewReader.specFresh` over
`NewReaderSize`'s (see `Spec/bufio/NewReaderFresh.lean`).
-/
module

public import Spec.bufio.NewReaderFresh
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

theorem bufio.NewReaderSize.wp_proofFresh : bufio.NewReaderSize.specFresh (GF := GF) (hG := hG) := by
  intro ri size hty hsz
  wp_start as #Hpkg
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
  unfold bufio.freshReader
  iexists _, List.replicate (sint.nat m) (zero_val w8)
  iframe Hr Hsl
  ipureintro
  simp only [List.length_replicate]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | trivial | rfl | omega | (show 0 < (sint.Z m).toNat; omega) |
      (show (sint.Z m).toNat ≤ 2 ^ 12; omega)

theorem bufio.NewReader.wp_proofFresh
    (wp_NewReaderSize : bufio.NewReaderSize.specFresh (GF := GF) (hG := hG)) :
    bufio.NewReader.specFresh (GF := GF) (hG := hG) := by
  intro ri hty
  wp_start as #Hpkg
  try wp_auto
  wp_apply wp_NewReaderSize ri (W64 4096) hty (by decide) $$ [$Hpkg] as %br Hbr
  try wp_auto
  iapply HΦ $$ Hbr

end proof

end EtcdGrove
end Perennial
