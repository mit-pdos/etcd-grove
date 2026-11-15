/-
`fileutil.LockFile(path, flag, perm)` (lock_linux.go): calls `linuxLockFile`, which the package's
`init` set to `ofdLockFile` or left `flockLockFile` (the package fact allows both): each opens the
file (`os.OpenFile(path, flag, perm)`), takes an exclusive lock on it (`fcntl(F_OFD_SETLKW)` or
`flock(LOCK_EX)`), closes it on a lock error, and returns `&LockedFile{f}`.

Generic in the open: for every open spec `fileutil.OpenTriple P path flag perm A C` (the part's
`os.OpenFile.specCreateS`, `specCreateTruncS`, `wp_fileS`, in the shape `fileutil.openPost`),
`LockFile` takes `P` and gives `fileutil.lockPost`: on success the open's success resources and the
locked file (`fileutil.lockedFile lf f`, the file and its fd whole), the fd holding an exclusive lock
of the package's kind `k` (`fileutil.lkFd k i flag`, `fileutil.lockKind k`) with its token
(`osLock k i fd`: no other open file description holds one; 2026-11-15, the lock semantics,
`notes/wal-units/locks.md`); on an error a nil `*LockedFile` and the open's resources of either
outcome (a lock error closes the file it opened, unlocked: the file stays created). A blocking lock
takes no successful step while another description holds the lock (it waits, or fails). `flag`'s
access mode writes (`F_WRLCK` needs a writable fd; the model is stuck otherwise). The package
initialized (`isPkgInit fileutil`: the lock function, `wrlck`; its dependencies `fmt`, `os`,
`syscall`). Proved in `LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/LockFile.lean`.
Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.LockDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.LockFile.spec : Prop :=
  ∀ (path : GoString) (flag : w64) (perm : w32) (P : IProp GF) (X : Type)
    (A : X → Bool → IProp GF) (C : X → Ino → Prop),
  fileutil.OpenTriple P path flag perm A C →
  decide ((flag ||| W64 0x80000).toNat % 4 ≠ O_RDONLY) = true →
  {{ osInv (GF := GF) ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ∗
      P }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.LockFile)) (Val #path))
      (Val #flag)) (Val #perm))
  {{ (lf : Loc) (err : GoInterface), RET (PairV #lf #err); fileutil.lockPost A C path flag lf err }}

end spec

end EtcdGrove
end Perennial
