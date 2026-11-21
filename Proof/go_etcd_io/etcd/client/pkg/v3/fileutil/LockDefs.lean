/-
Shared definitions of `fileutil`'s lock specs (`LockFile`, and `wal.createNewWALFile` over it):

* `fileutil.openPost A C path flag f err`: what an `os.OpenFile(path, flag, perm)` gives, in the
  shape every open spec of the part has (`os.OpenFile.specCreateS`, `specCreateTruncS`,
  `wp_fileS`): some outcome `x`, the resources `A x ok` (`ok`: the open succeeded) and, on success,
  a fresh `*os.File` on a fresh fd, both whole, at offset 0 (`os.ownOff`), on a file `i` with
  `C x i`, with `flag`'s access mode; on an error a nil file and an error `fmt` formats (`ofdLockFile` wraps it with `%w`);
* `fileutil.OpenTriple P path flag perm A C`: the open spec, as a premise: `LockFile` opens the file
  as `os.OpenFile` does, so its spec holds for every open spec (one statement for every variant);
* `fileutil.lockedFile lf f`: the `*LockedFile` `lf` holds the `*os.File` `f`, read-only (nothing
  writes the field);
* the lock (2026-11-15, the lock semantics, `notes/wal-units/locks.md`): `fileutil.lockKind k`, the
  kind `k` of the locks the package's initializer chose (OFD's or `flock`'s, `fileutil.kindOf`), the
  same for every call (persistent; from the package fact); `fileutil.lkFd k i flag`, the description of
  an fd of `flag` on the file `i` holding an exclusive lock of kind `k`; `fileutil.lockPost`'s success
  gives it, whole, and the lock's token (`osLock k i fd`).
-/
module

public import Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.Defs
public import Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.PkgInit
public import Spec.fmt.ErrorOk
public import Proof.os.Off
public import GooseLang.Ext.Fs.Locks

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- See the file header. -/
def fileutil.openPost {X : Type} (A : X → Bool → IProp GF) (C : X → Ino → Prop) (path : GoString)
    (flag : w64) (f : Loc) (err : GoInterface) : IProp GF :=
  iprop(∃ x : X,
    (⌜err = interface.nil⌝ ∗ A x true ∗ ∃ (fd : w64) (i : Ino), ⌜0 ≤ fd.toInt ∧ C x i⌝ ∗
        os.ownFile f fd path (DFrac.own 1) ∗ os.ownOff f (W64 0) ∗
        osFd fd (DFrac.own 1) (openFd i (flag ||| W64 0x80000))) ∨
    (⌜err ≠ interface.nil ∧ f = null⌝ ∗ A x false ∗ fmtErrorOkOrNil err))

/-- See the file header. -/
def fileutil.OpenTriple {X : Type} (P : IProp GF) (path : GoString) (flag : w64) (perm : w32)
    (A : X → Bool → IProp GF) (C : X → Ino → Prop) : Prop :=
  {{ P }}
    (App (App (App (Val (@! os.OpenFile)) (Val #path)) (Val #flag)) (Val #perm))
  {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); fileutil.openPost A C path flag f err }}

/-- See the file header. -/
def fileutil.lockedFile (lf f : Loc) : IProp GF :=
  iprop(lf ↦□ go_etcd_io.etcd.client.pkg.v3.fileutil.LockedFile.mk f)

instance fileutil.lockedFile_persistent (lf f : Loc) :
    Persistent (fileutil.lockedFile (GF := GF) lf f) := by
  unfold fileutil.lockedFile; infer_instance

/-- The lock kind of `fileutil`'s choice (`ofd`): OFD's or `flock`'s. -/
def fileutil.kindOf (ofd : Bool) : LockKind := if ofd then .ofd else .flock

/-- `fileutil`'s lock functions are those of the kind `k` (see the file header). -/
def fileutil.lockKind (k : LockKind) : IProp GF :=
  iprop(∃ ofd : Bool, ⌜k = fileutil.kindOf ofd⌝ ∗
    globalAddr go_etcd_io.etcd.client.pkg.v3.fileutil.linuxLockFile ↦□ fileutil.lockFn ofd ∗
    globalAddr go_etcd_io.etcd.client.pkg.v3.fileutil.linuxTryLockFile ↦□ fileutil.tryLockFn ofd)

instance fileutil.lockKind_persistent (k : LockKind) :
    Persistent (fileutil.lockKind (GF := GF) k) := by
  unfold fileutil.lockKind; infer_instance

/-- The description of an fd opened with `flag` on the file `i`, holding an exclusive lock of kind
`k` (see the file header). -/
def fileutil.lkFd (k : LockKind) (i : Ino) (flag : w64) : OsFd :=
  (openFd i (flag ||| W64 0x80000)).setLk k (some true)

/-- What `LockFile` gives (see `LockFile`'s spec). -/
def fileutil.lockPost {X : Type} (A : X → Bool → IProp GF) (C : X → Ino → Prop) (path : GoString)
    (flag : w64) (lf : Loc) (err : GoInterface) : IProp GF :=
  iprop(∃ x : X,
    (⌜err = interface.nil⌝ ∗ A x true ∗ ∃ (f : Loc) (fd : w64) (i : Ino) (k : LockKind),
        ⌜0 ≤ fd.toInt ∧ C x i⌝ ∗
        fileutil.lockedFile lf f ∗ os.ownFile f fd path (DFrac.own 1) ∗ os.ownOff f (W64 0) ∗
        osFd fd (DFrac.own 1) (fileutil.lkFd k i flag) ∗ osLock k i fd ∗ fileutil.lockKind k) ∨
    (⌜err ≠ interface.nil ∧ lf = null⌝ ∗ ∃ b : Bool, A x b))

/-- `lockPost`, a failed lock witnessed by `W` (wal-fsfix2): on an error after the open succeeded (`b`),
`W` (`LockFile`'s blocking request: `¬ FsNoErrIno`, the file system can fail on every file). -/
def fileutil.lockPostW {X : Type} (W : Prop) (A : X → Bool → IProp GF) (C : X → Ino → Prop)
    (path : GoString) (flag : w64) (lf : Loc) (err : GoInterface) : IProp GF :=
  iprop(∃ x : X,
    (⌜err = interface.nil⌝ ∗ A x true ∗ ∃ (f : Loc) (fd : w64) (i : Ino) (k : LockKind),
        ⌜0 ≤ fd.toInt ∧ C x i⌝ ∗
        fileutil.lockedFile lf f ∗ os.ownFile f fd path (DFrac.own 1) ∗ os.ownOff f (W64 0) ∗
        osFd fd (DFrac.own 1) (fileutil.lkFd k i flag) ∗ osLock k i fd ∗ fileutil.lockKind k) ∨
    (⌜err ≠ interface.nil ∧ lf = null⌝ ∗ ∃ b : Bool, A x b ∗ ⌜b = true → W⌝))

/-- `lockPostW` without its witness. -/
theorem fileutil.lockPost_of_W {X : Type} (W : Prop) (A : X → Bool → IProp GF) (C : X → Ino → Prop)
    (path : GoString) (flag : w64) (lf : Loc) (err : GoInterface) :
    fileutil.lockPostW W A C path flag lf err ⊢ fileutil.lockPost A C path flag lf err := by
  unfold fileutil.lockPostW fileutil.lockPost
  iintro ⟨%x, (⟨%h, HA, Hr⟩ | ⟨%h, %b, HA, -⟩)⟩
  · iexists x; ileft; iframe; ipureintro; exact h
  · iexists x; iright; isplitr
    · ipureintro; exact h
    iexists b; iexact HA

/-- What an exclusive lock of an fd just opened leaves: on success, the fd locked (`lkFd`) and the
lock's token; on failure, the fd as opened, with no lock (its tokens `emp`, for its `Close`). -/
theorem fileutil.lockOut_split (k : LockKind) (fd : w64) (i : Ino) (flag : w64) (e : w64) :
    lockOut (GF := GF) k fd (openFd i (flag ||| W64 0x80000)) (some true) e ⊢
      (⌜e = 0⌝ ∗ osFd fd (DFrac.own 1) (fileutil.lkFd k i flag) ∗ osLock (GF := GF) k i fd) ∨
      (⌜e ≠ 0⌝ ∗ osFd fd (DFrac.own 1) (openFd i (flag ||| W64 0x80000)) ∗
        lockToks (GF := GF) fd (openFd i (flag ||| W64 0x80000))) := by
  unfold lockOut fileutil.lkFd
  iintro ⟨%d', Hfd, Ht, %h⟩
  obtain ⟨-, h2, h3⟩ := h
  by_cases he : e = 0
  · have hd := h2 he; subst hd
    ileft
    iframe Hfd
    isplitr
    · ipureintro; exact he
    have hk : ((openFd i (flag ||| W64 0x80000)).setLk k (some true)).lk k = some true := by
      cases k <;> rfl
    ihave Ht := (lockTok_some (GF := GF) k fd _ hk).1 $$ Ht
    rw [setLk_ino, show (openFd i (flag ||| W64 0x80000)).ino = i from rfl]
    iexact Ht
  · have hd := h3 (by simp) he; subst hd
    iright
    iframe Hfd
    isplitr
    · ipureintro; exact he
    iapply lockToks_unlocked <;> rfl

end defs

end EtcdGrove
end Perennial
