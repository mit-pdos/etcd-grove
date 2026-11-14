/-
`wal.Create`'s first segment after its create (W4 of `notes/wal-fsext-plan.md`, sixteenth session):
`wp_lockedClose`, `Close` of a `*fileutil.LockedFile` through its embedded `*os.File` (the deferred
`f.Close()` of every error exit after the segment's create). Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateSeg
public import LinuxFs.Spec.os.File__Close

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [os_sem : os.Assumptions]
variable [fu_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- **`Close` of a `*LockedFile`**: its embedded `*os.File`'s. -/
theorem wp_lockedClose (wp_Close : os.File.Close.spec (GF := GF) (hG := hG)) (lf f : Loc) (fd : w64)
    (name : GoString) (d : OsFd) :
    {{ osInv (GF := GF) ∗ fileutil.lockedFile lf f ∗ os.ownFile f fd name (DFrac.own 1) ∗
        osFd fd (DFrac.own 1) d }}
      (App (Val (lf @!! go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.LockedFile.ty @!!
        go!"Close")) (Val #()))
    {{ (err : GoInterface), RET #err; fmtErrorOkOrNil err }} := by
  iintro %Φ ⟨#Hinv, #Hlf, Hf, Hfd⟩ HΦ
  iunfold fileutil.lockedFile at Hlf
  iStructNamed Hlf
  wp_method_call
  wp_call
  (try wp_auto)
  wp_apply wp_Close f fd name d $$ [Hinv Hf Hfd] as %err ⟨-, #Herr⟩
  · iframe; iexact Hinv
  iapply HΦ $$ Herr

end proof

end WalFs
end EtcdGrove
end Perennial
