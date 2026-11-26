/-
The proof of `Spec/os/File__CloseClosed.lean`: the model's fd -1 test, and `os.ErrClosed` (the part's
`os` fact, `os.errClosed_of_pkgInit`) wrapped in a `*PathError`.
-/
module

public import Spec.os.File__CloseClosed
public import Proof.os.ErrorOk
public import Proof.os.ErrnoPathErr

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
  wp_start as ⟨-, %inner, #Hf, Hfd, #Hn, #Hnb, #Hap, #Hsys⟩
  ihave ⟨%e, #Heok, #He⟩ := os.errClosed_of_pkgInit $$ Hpkg
  unfold os.ErrClosed at *
  ihave #Hf2 := Hf
  iStructNamed Hf2
  ihave %hnn := typedPointsto_not_null _ _ _ $$ Hf
  try wp_auto
  rw [decide_eq_false hnn]
  try wp_auto
  wp_apply os.wp_modelPathError_fields
  iintro %pe #Op #Path #Err
  try wp_auto
  iapply HΦ
  isplitl [Hfd]
  · iexists inner
    iframe
    (repeat' isplitl []) <;> iassumption
  · iapply EtcdGrove.fmtErrorOkOrNil_of
    iapply (os.pathError_fmtErrorOk pe _ _ e) $$ Op Path Err Heok

end proof

end EtcdGrove
end Perennial
