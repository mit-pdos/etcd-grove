/-
The package fact of `server/v3/storage/wal` (the part's translation, with bodies): what the WAL's
specs read of its package variables, read-only for good.

* `crcTable = crc32.MakeTable(crc32.Castagnoli)` (decoder.go, wal.go:69): the Castagnoli table
  (`walCrcTable`, which the encoder's and decoder's specs take);
* `walFsyncSec`, `walWriteSec`, `walWriteBytes` (metrics.go, untranslated `prometheus` constructors):
  metrics whose `Observe`/`Add` return (`wal.metricsInit`, `Metrics.lean`);
* `SegmentSizeBytes` (wal.go, `64 * 1000 * 1000`, a `var` only tests assign): `64000000`.

The error variables (`ErrMetadataConflict`, `ErrFileNotFound`, ...) are not in it: no spec reads
them yet. Its `wp_initialize'`: `Init.lean` (`etc/gen-init.py`, `LFS_PKGS` and `LFS_SPECIAL`).
WAL package init, 2026-11-13.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.DecDefs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Metrics
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.DepsPkgInit
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.walpb.PkgInit
public import LinuxFs.Proof.go_etcd_io.etcd.pkg.v3.ioutil.PkgInit

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace EtcdGrove

/-- `wal`'s fact: the CRC table, the metrics and the segment size, read-only. -/
abbrev wal.walInit : IProp GF :=
  iprop(WalFs.walCrcTable ∗ wal.metricsInit ∗
    globalAddr go_etcd_io.etcd.server.v3.storage.wal.SegmentSizeBytes ↦□ (W64 64000000))

end EtcdGrove

namespace go_etcd_io.etcd.server.v3.storage.wal

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal :=
  define_is_pkg_init EtcdGrove.wal.walInit
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.storage.wal

end init

end Perennial
