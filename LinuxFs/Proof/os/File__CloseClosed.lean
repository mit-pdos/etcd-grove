/-
The proof of `Spec/os/File__CloseClosed.lean`: the model's fd -1 test, and `os.ErrClosed` (the part's
`os` fact, `os.errClosed_of_pkgInit`) wrapped in a `*PathError`.
-/
module

public import LinuxFs.Spec.os.File__CloseClosed
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

theorem os.File.Close.wp_proofClosed : os.File.Close.specClosed (GF := GF) (hG := hG) := by
  intro f name
  unfold os.ownFile
  wp_start as ⟨-, %inner, #Hf, Hfd, #Hn⟩
  ihave ⟨%e, #Heok, #He⟩ := os.errClosed_of_pkgInit $$ Hpkg
  unfold os.ErrClosed at *
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  ihave %hnn := typedPointsto_not_null _ _ _ $$ Hf
  rw [decide_eq_false hnn]
  wp_auto
  unfold os.model.pathError
  iapply wp_fupd
  wp_auto
  iStructNamed pe
  ipersist Op
  ipersist Path
  ipersist Err
  imodintro
  iapply HΦ
  isplitl [Hfd]
  · iexists inner
    iframe
    isplitl [] <;> iassumption
  · iapply EtcdGrove.fmtErrorOkOrNil_of
    iapply (os.pathError_fmtErrorOk pe_ptr _ _ e) $$ Op Path Err Heok

end proof

end EtcdGrove
end Perennial
