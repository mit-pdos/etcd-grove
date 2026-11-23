/-
`bufio.NewReader`'s generic spec (see `Spec/bufio/NewReaderOk.lean`): `wp_proofE`, the one proof of
its body (`NewReaderSize(rd, 4096)`, by `bufio.NewReaderSize.specE`), and `wp_proofOk`, its instance at
`bufio.errE E` (round 2 of the review on #24, N4).
-/
module

public import Spec.bufio.NewReaderOk
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

theorem bufio.NewReader.wp_proofE
    (wp_NewReaderSize : bufio.NewReaderSize.specE (GF := GF) (hG := hG)) :
    bufio.NewReader.specE (GF := GF) (hG := hG) := by
  intro ri Pre S E Eb szOk R
  wp_start as ⟨%hty, %hsz, #Hpkg, #Hrd, #Hpu, HS⟩
  try wp_auto
  wp_apply wp_NewReaderSize ri Pre S E Eb szOk R (W64 4096) $$ [$Hpkg $Hrd $HS] as %br Hbr
  · have h : (max (sint.Z (W64 4096)) 16).toNat = 4096 := rfl
    rw [h]
    isplitr
    · ipureintro; exact hty
    isplitr
    · ipureintro; exact hsz
    iexact Hpu
  try wp_auto
  iapply HΦ $$ Hbr

theorem bufio.NewReader.wp_proofOk
    (wp_NewReaderE : bufio.NewReader.specE (GF := GF) (hG := hG)) :
    bufio.NewReader.specOk (GF := GF) (hG := hG) := by
  intro ri Pre S E R
  unfold bufio.ownBufReader
  iintro %Φ ⟨%hty, Hpkg, Hrd, Hpu, HS⟩ HΦ
  iapply wp_NewReaderE ri Pre S E (bufio.errE E) (fun _ => True) R $$ [Hpkg Hrd Hpu HS] HΦ
  iframe Hpkg Hrd Hpu HS
  ipureintro; exact hty

end proof

end EtcdGrove
end Perennial
