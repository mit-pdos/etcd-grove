/-
The locks of an open WAL's handle, for `ReleaseLockTo` and `Close` (W9/W10 of
`notes/wal-fsext-plan.md`): every lock of `w.locks` is a `*fileutil.LockedFile` whose file has a name
(`walLockNamed`, persistent: what the loop of `l.Name()` reads), the non-tail locks' (`walLockH`) and
the tail's (the tail writer's `os.ownFile`); list facts of the reslice `w.locks[k:]`. Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenAtTail

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Fs WalEnc

/-! ## List facts -/

theorem dropLast_drop {A : Type} (l : List A) (k : Nat) : (l.drop k).dropLast = l.dropLast.drop k := by
  rw [List.dropLast_eq_take, List.dropLast_eq_take, List.drop_take, List.length_drop]
  congr 1
  omega

theorem getLast?_drop {A : Type} (l : List A) (k : Nat) (hk : k < l.length) :
    (l.drop k).getLast? = l.getLast? := by
  rw [List.getLast?_eq_getElem?, List.getLast?_eq_getElem?, List.getElem?_drop, List.length_drop]
  congr 1
  omega

section handle
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- The lock `lf` holds a file with a name (persistent). -/
def walLockNamed (lf : Loc) : IProp GF :=
  iprop(∃ (f : Loc) (nm : GoString), fileutil.lockedFile lf f ∗ os.fileNamed f nm)

instance walLockNamed_persistent (lf : Loc) : Persistent (walLockNamed (GF := GF) lf) := by
  unfold walLockNamed; infer_instance

theorem walLockH_named (lf : Loc) :
    walLockH (GF := GF) lf ⊢ walLockH lf ∗ walLockNamed lf := by
  unfold walLockH walLockNamed
  iintro ⟨%f, %fd, %nm, %d, #Hl, Hf, Hfd⟩
  ihave #Hn := os.ownFile_named f fd nm (DFrac.own 1) $$ Hf
  isplitl [Hf Hfd]
  · iexists f, fd, nm, d
    iframe Hl Hf Hfd
  · iexists f, nm
    iframe Hl Hn

theorem walLocksH_named (ls : List Loc) :
    ([∗list] lf ∈ ls, walLockH (GF := GF) lf) ⊢
      ([∗list] lf ∈ ls, walLockH (GF := GF) lf) ∗ □ [∗list] lf ∈ ls, walLockNamed (GF := GF) lf := by
  induction ls with
  | nil =>
    iintro H
    iframe H
    imodintro
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro
  | cons x xs ih =>
    iintro ⟨Hx, Hxs⟩
    ihave ⟨Hx, #Hnx⟩ := walLockH_named x $$ Hx
    ihave ⟨Hxs, #Hnxs⟩ := ih $$ Hxs
    iframe Hx Hxs
    imodintro
    iframe Hnx Hnxs

/-- The tail writer's file has the tail's name. -/
theorem walTailW_named (f : Loc) (fd : w64) (name : GoString) (dir : GoString) (γ : GName) (i : Ino)
    (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (o0 sz : Nat) (out : List w8)
    (tm : Fs.OsMeta → List Fs.ByteG → Prop) :
    walTailW (W := W) f fd name dir γ i H md cuts o0 sz out tm ⊢
      walTailW (W := W) f fd name dir γ i H md cuts o0 sz out tm ∗ os.fileNamed f name := by
  unfold walTailW
  iintro ⟨Hf, Hrest⟩
  ihave #Hn := os.ownFile_named f fd name (DFrac.own 1) $$ Hf
  iframe Hf Hrest Hn

/-- Every lock of the handle is named: the non-tail locks' and the tail's. -/
theorem walLocks_named (lfs : List Loc) (lt f : Loc) (nm : GoString) (hl : lfs.getLast? = some lt) :
    ⊢ ([∗list] lf ∈ lfs.dropLast, walLockH (GF := GF) lf) -∗ fileutil.lockedFile lt f -∗
      os.fileNamed f nm -∗
      ([∗list] lf ∈ lfs.dropLast, walLockH (GF := GF) lf) ∗
        □ [∗list] lf ∈ lfs, walLockNamed (GF := GF) lf := by
  obtain ⟨ls, rfl⟩ := List.getLast?_eq_some_iff.1 hl
  rw [List.dropLast_concat]
  iintro Hls #Hlt #Hn
  ihave ⟨Hls, #Hns⟩ := walLocksH_named ls $$ Hls
  iframe Hls
  imodintro
  iapply (BigSepL.bigSepL_append (PROP := IProp GF)).2
  iframe Hns
  isplitl
  · unfold walLockNamed
    iexists f, nm
    iframe Hlt Hn
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

end handle

end WalFs
end EtcdGrove
end Perennial
