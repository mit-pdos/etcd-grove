/-
`Repair`'s calls through its `*fileutil.LockedFile` (W7 of `notes/wal-fsext-plan.md`; the W7-W12 log,
fourteenth session): `f.Name()` and `f.Seek(off, io.SeekStart)`, the embedded `*os.File`'s (as
`wp_lockedClose`, `CreateLocked.lean`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateLocked
public import Spec.os.File__Name
public import Proof.os.Off

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

/-- **`Name` of a `*LockedFile`**: its embedded `*os.File`'s. -/
theorem wp_lockedName (wp_Name : os.File.Name.spec (GF := GF) (hG := hG)) (lf f : Loc) (fd : w64)
    (name : GoString) (dq : DFrac) :
    {{ fileutil.lockedFile (GF := GF) lf f ∗ os.ownFile f fd name dq }}
      (App (Val (lf @!! go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.LockedFile.ty @!!
        go!"Name")) (Val #()))
    {{ RET #name; os.ownFile f fd name dq }} := by
  iintro %Φ ⟨#Hlf, Hf⟩ HΦ
  iunfold fileutil.lockedFile at Hlf
  iStructNamed Hlf
  wp_method_call
  wp_call
  (try wp_auto)
  wp_apply wp_Name f fd name dq $$ Hf as Hf
  iapply HΦ $$ Hf

/-- **`Seek(off, io.SeekStart)` of a `*LockedFile`**: its embedded `*os.File`'s
(`os.File.Seek.wp_start`). -/
theorem wp_lockedSeekStart (lf f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (o off : w64)
    (hfd : 0 ≤ fd.toInt) (h0 : 0 ≤ off.toInt) (hmax : off.toInt ≤ 0xffffffff000) :
    {{ fileutil.lockedFile (GF := GF) lf f ∗ os.ownFile f fd name dqf ∗ os.ownOff f o }}
      (App (App (Val (lf @!! go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.LockedFile.ty @!!
        go!"Seek")) (Val #off)) (Val #(W64 0)))
    {{ RET (PairV #off #GoInterface.nil); os.ownFile f fd name dqf ∗ os.ownOff f off }} := by
  iintro %Φ ⟨#Hlf, Hf, Ho⟩ HΦ
  iunfold fileutil.lockedFile at Hlf
  iStructNamed Hlf
  wp_method_call
  wp_call
  (try wp_auto)
  wp_apply os.File.Seek.wp_start f fd name dqf o off hfd h0 hmax $$ [Hf Ho] as ⟨Hf, Ho⟩
  · iframe
  iapply HΦ
  iframe

end proof

end WalFs
end EtcdGrove
end Perennial
