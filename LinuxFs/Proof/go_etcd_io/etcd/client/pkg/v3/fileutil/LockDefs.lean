/-
Shared definitions of `fileutil`'s lock specs (`LockFile`, and `wal.createNewWALFile` over it):

* `fileutil.openPost A C path flag f err`: what an `os.OpenFile(path, flag, perm)` gives, in the
  shape every open spec of the part has (`os.OpenFile.specCreateS`, `specCreateTruncS`,
  `wp_fileS`): some outcome `x`, the resources `A x ok` (`ok`: the open succeeded) and, on success,
  a fresh `*os.File` on a fresh fd, both whole, on a file `i` with `C x i`, with `flag`'s access
  mode; on an error a nil file and an error `fmt` formats (`ofdLockFile` wraps it with `%w`);
* `fileutil.OpenTriple P path flag perm A C`: the open spec, as a premise: `LockFile` opens the file
  as `os.OpenFile` does, so its spec holds for every open spec (one statement for every variant);
* `fileutil.lockedFile lf f`: the `*LockedFile` `lf` holds the `*os.File` `f`, read-only (nothing
  writes the field). The lock itself is not modelled (plan §6 Q1): the fd is the file's.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.Defs
public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.PkgInit
public import Spec.fmt.ErrorOk

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
        os.ownFile f fd path (DFrac.own 1) ∗ osFd fd (DFrac.own 1) (openFd i (flag ||| W64 0x80000))) ∨
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

/-- What `LockFile` gives (see `LockFile`'s spec). -/
def fileutil.lockPost {X : Type} (A : X → Bool → IProp GF) (C : X → Ino → Prop) (path : GoString)
    (flag : w64) (lf : Loc) (err : GoInterface) : IProp GF :=
  iprop(∃ x : X,
    (⌜err = interface.nil⌝ ∗ A x true ∗ ∃ (f : Loc) (fd : w64) (i : Ino), ⌜0 ≤ fd.toInt ∧ C x i⌝ ∗
        fileutil.lockedFile lf f ∗ os.ownFile f fd path (DFrac.own 1) ∗
        osFd fd (DFrac.own 1) (openFd i (flag ||| W64 0x80000))) ∨
    (⌜err ≠ interface.nil ∧ lf = null⌝ ∗ ∃ b : Bool, A x b))

end defs

end EtcdGrove
end Perennial
