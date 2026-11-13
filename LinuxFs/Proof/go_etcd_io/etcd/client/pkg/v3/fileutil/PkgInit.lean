/-
The package fact of `client/pkg/v3/fileutil` (the part's translation, with bodies), read-only for good:

* `linuxLockFile`, `linuxTryLockFile` (lock_linux.go): `flockLockFile`/`flockTryLockFile` as declared,
  replaced by `ofdLockFile`/`ofdTryLockFile` by its `init` when the `F_OFD_GETLK` probe on fd 0
  succeeds. The probe's result is any errno in the model (`syscall.FcntlFlock`'s, F_OFD_GETLK:
  `ArbitraryInt`; `syscall.FcntlFlock.wp_getlk`), so the fact allows **both** (`ofd`, a boolean, the
  same for the two variables);
* `wrlck` (lock_linux.go): the write-lock description `{Type: F_WRLCK, Whence: SEEK_SET, Start: 0,
  Len: 0}` (the other fields zero);
* `ErrLocked` (lock.go, `errors.New("fileutil: file already locked")`): an error whose `Error()`
  returns (`errOk`).

Its `wp_initialize'`: `Init.lean` (`etc/gen-init.py`, `LFS_SPECIAL`). WAL package init, 2026-11-13.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.DepsPkgInit
public import LinuxFs.Spec.fmt.ErrorfErrs

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section fns
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

namespace EtcdGrove

/-- The lock functions `fileutil` uses: OFD locks (`ofd`) or `flock`'s. -/
def fileutil.lockFn (ofd : Bool) : GoFunc :=
  functions (if ofd then go_etcd_io.etcd.client.pkg.v3.fileutil.ofdLockFile
    else go_etcd_io.etcd.client.pkg.v3.fileutil.flockLockFile) []

/-- The try-lock functions `fileutil` uses: OFD locks (`ofd`) or `flock`'s. -/
def fileutil.tryLockFn (ofd : Bool) : GoFunc :=
  functions (if ofd then go_etcd_io.etcd.client.pkg.v3.fileutil.ofdTryLockFile
    else go_etcd_io.etcd.client.pkg.v3.fileutil.flockTryLockFile) []

end EtcdGrove

end fns

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace EtcdGrove

/-- `fileutil`'s fact: the lock functions (both OFD's or both `flock`'s), the write-lock description
and `ErrLocked`, read-only. -/
abbrev fileutil.fileutilInit : IProp GF :=
  iprop((∃ ofd : Bool,
      globalAddr go_etcd_io.etcd.client.pkg.v3.fileutil.linuxLockFile ↦□ fileutil.lockFn ofd ∗
      globalAddr go_etcd_io.etcd.client.pkg.v3.fileutil.linuxTryLockFile ↦□ fileutil.tryLockFn ofd) ∗
    (∃ w : syscall.Flock_t, globalAddr go_etcd_io.etcd.client.pkg.v3.fileutil.wrlck ↦□ w ∗
      ⌜w.Type' = W16 1 ∧ w.Whence' = W16 0 ∧ w.Start' = W64 0 ∧ w.Len' = W64 0⌝) ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.client.pkg.v3.fileutil.ErrLocked ↦□ GoInterface.ok e ∗ errOk e))

end EtcdGrove

namespace go_etcd_io.etcd.client.pkg.v3.fileutil

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil :=
  define_is_pkg_init EtcdGrove.fileutil.fileutilInit
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.client.pkg.v3.fileutil

end init

end Perennial
