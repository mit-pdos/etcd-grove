/-
The proof of `Spec/os/File__Close.lean`: a store of -1 to the fd field, and `wp_Close`.
-/
module

public import Spec.os.File__Close

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

theorem os.File.Close.wp_proof : os.File.Close.spec (GF := GF) (hG := hG) := by
  intro f fd name d
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hosfd⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  wp_auto
  wp_apply wp_Close fd d CoPset.subseteq_top $$ [Hinv Hosfd] as %e -
  · iframe; iexact Hinv
  by_cases he : e = W64 0
  · rw [decide_eq_true he]
    wp_auto
    iapply HΦ
    iexists inner
    iframe
    isplitl [] <;> iassumption
  · rw [decide_eq_false he]
    wp_auto
    wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
    iapply HΦ
    iexists inner
    iframe
    isplitl [] <;> iassumption

end proof

end EtcdGrove
end Perennial
