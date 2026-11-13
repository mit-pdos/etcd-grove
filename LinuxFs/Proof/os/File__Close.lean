/-
The proof of `Spec/os/File__Close.lean`: a store of -1 to the fd field, and `wp_osClose`.
-/
module

public import LinuxFs.Spec.os.File__Close
public import LinuxFs.Proof.os.ErrorOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
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
  ihave %hnn := typedPointsto_not_null _ _ _ $$ Hf
  rw [decide_eq_false hnn]
  wp_auto
  wp_apply wp_osFdKind fd (DFrac.own 1) d CoPset.subseteq_top $$ Hinv Hosfd as Hosfd
  wp_apply wp_osClose fd d CoPset.subseteq_top $$ [Hinv Hosfd] as %e -
  · iframe; iexact Hinv
  by_cases he : e = W64 0
  · rw [decide_eq_true he]
    wp_auto
    ihave #Hokn := (EtcdGrove.fmtErrorOkOrNil_nil (GF := GF))
    iapply HΦ
    iframe Hokn
    iexists inner
    iframe
    isplitl [] <;> iassumption
  · rw [decide_eq_false he]
    wp_auto
    wp_apply os.wp_wrapErrno_ok _ inner name e he $$ Hn as %pe #Hok
    ihave #Hokn := EtcdGrove.fmtErrorOkOrNil_of _ $$ Hok
    iapply HΦ
    iframe Hokn
    iexists inner
    iframe
    isplitl [] <;> iassumption

end proof

end EtcdGrove
end Perennial
