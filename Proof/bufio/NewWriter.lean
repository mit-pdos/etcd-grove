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
  intro wi J Q Ew W hty
  wp_start as ⟨#Hwr, HJ, #HQ⟩
  try wp_auto
  wp_apply wp_NewWriterSize wi J Q Ew W _ hty $$ [$Hpkg $Hwr $HJ $HQ] as %bw Hbw
  try wp_auto
  iapply HΦ $$ Hbw

end proof

end EtcdGrove
end Perennial
