/-
The proof of `Spec/os/File__Name.lean`: the translated `return f.name`.
-/
module

public import Spec.os.File__Name

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

theorem os.File.Name.wp_proof : os.File.Name.spec (GF := GF) (hG := hG) := by
  intro f fd name dq
  unfold os.ownFile
  wp_start as ⟨%inner, #Hf, Hfd, #Hn⟩
  ihave #Hf2 := Hf
  iStructNamed Hf2
  wp_auto
  iapply HΦ
  iexists inner
  iframe
  isplitl [] <;> iassumption

end proof

end EtcdGrove
end Perennial
