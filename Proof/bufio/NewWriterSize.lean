/-
`bufio.NewWriterSize` (see `Spec/bufio/NewWriterSize.lean`). Ported from dsverify-lab's
`Harness/Proof/bufio/Writer.lean` (`wp_NewWriter`); since 2026-11-23 an instance of the generic
`bufio.NewWriterSize.specRep` (one proof per function): its fields with the contract framed.
-/
module

public import Spec.bufio.NewWriterSize
public import Spec.bufio.NewWriterSizeRep

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

theorem bufio.NewWriterSize.wp_proof
    (wp_rep : bufio.NewWriterSize.specRep (GF := GF) (hG := hG)) :
    bufio.NewWriterSize.spec (GF := GF) (hG := hG) := by
  intro wi J Q Ew W size
  iintro %Φ ⟨%hty, #Hpkg, #Hwr, HJ, #HQ⟩ HΦ
  iapply wp_rep wi Ew size $$ [$Hpkg]
  · ipureintro; exact hty
  iintro !> %bw Hrep
  iapply HΦ
  unfold bufio.ownBufWriter
  rw [List.append_nil]
  iframe Hpkg Hwr HJ HQ Hrep

end proof

end EtcdGrove
end Perennial
