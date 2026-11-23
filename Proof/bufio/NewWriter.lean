/-
`bufio.NewWriter` (see `Spec/bufio/NewWriter.lean`): `NewWriterSize(w, 4096)`.
-/
module

public import Spec.bufio.NewWriter
public import Spec.bufio.NewWriterSize

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

theorem bufio.NewWriter.wp_proof
    (wp_NewWriterSize : bufio.NewWriterSize.spec (GF := GF) (hG := hG)) :
    bufio.NewWriter.spec (GF := GF) (hG := hG) := by
  intro wi J Q Ew W
  wp_start as ⟨%hty, #Hpkg, #Hwr, HJ, #HQ⟩
  try wp_auto
  wp_apply wp_NewWriterSize wi J Q Ew W (W64 4096) $$ [$Hpkg $Hwr $HJ $HQ] as %bw Hbw
  · ipureintro; exact hty
  try wp_auto
  have h4 : bufio.writerSize (W64 4096) = 4096 := by
    unfold bufio.writerSize; rfl
  rw [h4] at *
  iapply HΦ
  iexact Hbw

end proof

end EtcdGrove
end Perennial
