/-
`wal.createNewWALFile[T](path, forceNew)` (wal.go): opens `path` with `O_WRONLY|O_CREATE` (and
`O_TRUNC` if `forceNew`), mode `PrivateFileMode`: for `T = *fileutil.LockedFile` (`Create`,
`filePipeline.alloc`) with `fileutil.LockFile`, for `T = *os.File` (`Repair`'s `.broken` copy) with
`os.OpenFile`.

Generic in the open, as `fileutil.LockFile.spec` (`fileutil.OpenTriple`, the shape of the part's
open specs `os.OpenFile.specCreateS`, `specCreateTruncS`, `wp_fileS`), at the flag `walOpenFlag
forceNew`:
* `specLocked`: `LockFile`'s post (`fileutil.lockPost`);
* `specFile`: the open's own post (`fileutil.openPost`).
The package initialized (`isPkgInit wal`; `fileutil`'s through it). Proved in
`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/createNewWALFile.lean`. Lean-first (plan W2,
W4's "not done" lists).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.LockDefs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

/-- `createNewWALFile`'s open flag: `O_WRONLY|O_CREATE`, and `O_TRUNC` if `forceNew`. -/
def wal.walOpenFlag (forceNew : Bool) : w64 := if forceNew then W64 0x241 else W64 0x41

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk]
  [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile.specLocked : Prop :=
  ∀ (path : GoString) (forceNew : Bool) (P : IProp GF) (X : Type) (A : X → Bool → IProp GF)
    (C : X → Ino → Prop),
  fileutil.OpenTriple P path (wal.walOpenFlag forceNew) (W32 384) A C →
  {{ osInv (GF := GF) ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗
      P }}
    (App (App (Val #(functions go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile
        [go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.LockedFile.ty])) (Val #path))
      (Val #forceNew))
  {{ (lf : Loc) (err : GoInterface), RET (PairV #lf #err);
      fileutil.lockPost A C path (wal.walOpenFlag forceNew) lf err }}

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile.specFile : Prop :=
  ∀ (path : GoString) (forceNew : Bool) (P : IProp GF) (X : Type) (A : X → Bool → IProp GF)
    (C : X → Ino → Prop),
  fileutil.OpenTriple P path (wal.walOpenFlag forceNew) (W32 384) A C →
  {{ P }}
    (App (App (Val #(functions go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile
        [go.GoType.PointerType os.File.ty])) (Val #path)) (Val #forceNew))
  {{ (f : Loc) (err : GoInterface), RET (PairV #f #err);
      fileutil.openPost A C path (wal.walOpenFlag forceNew) f err }}

/-- Both instances. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile.spec : Prop :=
  go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile.specLocked (GF := GF) (hG := hG) ∧
  go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile.specFile (GF := GF) (hG := hG)

end spec

end EtcdGrove
end Perennial
