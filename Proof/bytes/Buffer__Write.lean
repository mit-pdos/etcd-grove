/-
Proof of `Spec/bytes/Buffer__Write.lean`: Perennial's proved `bytes.Buffer.Write` (mit-pdos/perennial#670),
restated over `bufferM.ownBuffer` (`bufferM.ownBuffer_eq`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.bytes.Buffer__Write
public import Perennial.Spec.bytes.Buffer__Write

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [bytes.Assumptions]

theorem bytes.Buffer.Write.wp_proof
    (wp_Write : _root_.Perennial.bytes.Buffer.Write.spec (GF := GF) (hG := hG)) :
    bytes.Buffer.Write.spec (GF := GF) (hG := hG) := by
  intro b bs sl dq d
  wp_start as ⟨Hb, Hsl⟩
  simp only [bufferM.ownBuffer_eq]
  wp_apply wp_Write $$ [$Hb $Hsl] as ⟨Hb, Hsl⟩
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
