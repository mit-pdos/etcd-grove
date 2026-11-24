/-
Proof of `Spec/bytes/Buffer__Bytes.lean`: Perennial's proved `bytes.Buffer.Bytes` (mit-pdos/perennial#670),
restated over `bufferM.ownBuffer` (`bufferM.ownBuffer_eq`), without its wand back to the buffer.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.bytes.Buffer__Bytes
public import Perennial.Spec.bytes.Buffer__Bytes

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

theorem bytes.Buffer.Bytes.wp_proof
    (wp_Bytes : _root_.Perennial.bytes.Buffer.Bytes.spec (GF := GF) (hG := hG)) :
    bytes.Buffer.Bytes.spec (GF := GF) (hG := hG) := by
  intro b bs
  iintro %Φ ⟨#Hpkg, Hb⟩ HΦ
  simp only [bufferM.ownBuffer_eq]
  wp_apply wp_Bytes $$ [$Hb] as %s ⟨Hs, -⟩
  iapply HΦ
  iexact Hs

end proof

end EtcdGrove
end Perennial
