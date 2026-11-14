/-
`wal.Create`'s deferred `f.Close()` after a failed `renameWAL` (W4 of `notes/wal-fsext-plan.md`,
nineteenth session): the lock file open, or closed by `renameWALUnlock`'s `w.Close()` (`walLockLeft`,
`renameWALPost`'s error arms); the second close over `os.File.Close.specClosed`. Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateLocked
public import LinuxFs.Spec.os.File__CloseClosed
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__renameWAL

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

/-- **`Close` of a `*LockedFile` after a failed `renameWAL`** (`walLockLeft`: its `*os.File` open, or
closed by `renameWALUnlock`'s `w.Close()`). -/
theorem wp_lockedCloseLeft (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_CloseC : os.File.Close.specClosed (GF := GF) (hG := hG)) (lf f : Loc) (fd : w64)
    (name : GoString) (d : OsFd) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ fileutil.lockedFile lf f ∗
        walLockLeft (hG := hG) f fd name d }}
      (App (Val (lf @!! go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.LockedFile.ty @!!
        go!"Close")) (Val #()))
    {{ (err : GoInterface), RET #err; fmtErrorOkOrNil err }} := by
  iintro %Φ ⟨#Hos, #Hinv, #Hlf, Hl⟩ HΦ
  iunfold walLockLeft at Hl
  iunfold fileutil.lockedFile at Hlf
  iStructNamed Hlf
  wp_method_call
  wp_call
  (try wp_auto)
  icases Hl with (⟨Hf, Hfd⟩ | Hf)
  · wp_apply wp_Close f fd name d $$ [Hinv Hf Hfd] as %err ⟨-, #Herr⟩
    · iframe; iexact Hinv
    iapply HΦ $$ Herr
  · wp_apply wp_CloseC f name $$ [Hos Hinv Hf] as %err ⟨-, #Herr⟩
    · iframe; iframe #
    iapply HΦ $$ Herr

end proof

end WalFs
end EtcdGrove
end Perennial
