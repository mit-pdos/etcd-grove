/-
The proof of `Spec/os/File__Fd.lean`: two loads, through the `File` to its `file`'s `fd`.
-/
module

public import Spec.os.File__Fd

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

theorem os.File.Fd.wp_proof : os.File.Fd.spec (GF := GF) (hG := hG) := by
  intro f fd name dq
  unfold os.ownFile
  wp_start as ⟨%inner, #Hf, Hfd, #Hn⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
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
