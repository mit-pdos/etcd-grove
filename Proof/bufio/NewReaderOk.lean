/-
`bufio.NewReader`'s generic spec (see `Spec/bufio/NewReaderOk.lean`).
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

theorem bufio.NewReader.wp_proofOk
    (wp_NewReaderSize : bufio.NewReaderSize.spec (GF := GF) (hG := hG)) :
    bufio.NewReader.specOk (GF := GF) (hG := hG) := by
  intro ri Pre S E R hty hpre
  wp_start as ⟨#Hrd, HS⟩
  try wp_auto
  wp_apply wp_NewReaderSize ri Pre S E R (W64 4096) hty (by
    show bufio.preUpTo Pre (max (sint.Z (W64 4096)) 16).toNat
    exact hpre) $$ [$Hpkg $Hrd $HS] as %br Hbr
  try wp_auto
  iapply HΦ $$ Hbr

end proof

end EtcdGrove
end Perennial
