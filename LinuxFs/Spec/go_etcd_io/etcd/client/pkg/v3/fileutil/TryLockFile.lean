/-
`fileutil.TryLockFile(path, flag, perm)` (lock_linux.go): calls `linuxTryLockFile`, which the
package's `init` set to `ofdTryLockFile` or left `flockTryLockFile` (the package fact allows both):
each opens the file (`os.OpenFile(path, flag, perm)`), tries an exclusive lock on it
(`fcntl(F_OFD_SETLK)` or `flock(LOCK_EX|LOCK_NB)`), closes it on a lock error (replaced by
`ErrLocked` when `errors.Is(err, EWOULDBLOCK)`), and returns `&LockedFile{f}`.

As `LockFile`'s spec (generic in the open, `fileutil.OpenTriple`; post `fileutil.lockPost`: the lock
is not modelled), plus: an error is one whose `Error()` returns (`errOk`), as `wal.openWALFiles`
wraps it with `%w` (`fmt.ErrorfErrs`). Proved in
`LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/TryLockFile.lean`, over the hypothesis
`errors.IsErrno.spec`. W5 of `notes/wal-fsext-plan.md`; Lean-first.
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
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.TryLockFile.spec : Prop :=
  ∀ (path : GoString) (flag : w64) (perm : w32) (P : IProp GF) (X : Type)
    (A : X → Bool → IProp GF) (C : X → Ino → Prop),
  fileutil.OpenTriple P path flag perm A C →
  {{ osInv (GF := GF) ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ∗
      P }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.TryLockFile)) (Val #path))
      (Val #flag)) (Val #perm))
  {{ (lf : Loc) (err : GoInterface), RET (PairV #lf #err);
      fileutil.lockPost A C path flag lf err ∗
      (⌜err = interface.nil⌝ ∨ ∃ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ ∗ errOk e) }}

end spec

end EtcdGrove
end Perennial
