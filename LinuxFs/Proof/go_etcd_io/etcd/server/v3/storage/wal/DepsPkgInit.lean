/-
The package-initialization instances of the WAL's imports with no fact (`True`) in the part
`LinuxFs/`: the part's translations of `client/pkg/v3/fileutil`, `pkg/v3/crc` and `hash/crc32`, and the
main tree's (names-only) of zap, `zapcore`, semver, prometheus, `pkg/v3/pbutil` and `hash`, whose main
instances (in the cache's, the lease's, the backend's and the apply layer's `Base.lean`, and
`Proof/hash/PkgInit.lean`, over the main tree's raft through `PkgInitExt`) the part cannot import.
`fileutil`'s variables (`linuxLockFile`, `linuxTryLockFile`, ...) are not in its fact: no spec of the part
reads them yet. Their `wp_initialize'`: the generated `Init.lean`s (`etc/gen-init.py`, `LFS_PKGS`).
WAL package init, 2026-11-13.
-/
module

public import GeneratedProof.go_uber_org.zap
public import GeneratedProof.go_uber_org.zap.zapcore
public import GeneratedProof.github_com.Masterminds.semver.v3
public import GeneratedProof.github_com.prometheus.client_golang.prometheus
public import GeneratedProof.go_etcd_io.etcd.pkg.v3.pbutil
public import GeneratedProof.hash
public import LinuxFs.GeneratedProof.hash.crc32
public import LinuxFs.GeneratedProof.go_etcd_io.etcd.pkg.v3.crc
public import LinuxFs.GeneratedProof.go_etcd_io.etcd.client.pkg.v3.fileutil
public import LinuxFs.Proof.google_golang_org.protobuf.proto.PkgInit
public import LinuxFs.Proof.os.PkgInit
public import LinuxFs.Proof.bufio.PkgInit
public import LinuxFs.Proof.path.filepath.PkgInit
public import LinuxFs.Proof.syscall.PkgInit
public import LinuxFs.Proof.golang_org.x.sys.unix.PkgInit
public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.verify.PkgInit
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.time
public import Perennial.Proof.sort
public import Perennial.Proof.strings
public import Perennial.Proof.fmt
public import Perennial.Proof.io
public import Perennial.Proof.errors

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace go_etcd_io.etcd.server.v3.storage.wal

instance zapcore_isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_uber_org.zap.zapcore :=
  define_is_pkg_init iprop(True)
instance zapcore_get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_uber_org.zap.zapcore :=
  build_get_is_pkg_init_wf
instance zap_isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_uber_org.zap :=
  define_is_pkg_init iprop(True)
instance zap_get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_uber_org.zap :=
  build_get_is_pkg_init_wf
instance semver_isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.Masterminds.semver.v3 :=
  define_is_pkg_init iprop(True)
instance semver_get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.Masterminds.semver.v3 :=
  build_get_is_pkg_init_wf
instance prometheus_isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus :=
  define_is_pkg_init iprop(True)
instance prometheus_get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus :=
  build_get_is_pkg_init_wf
instance pbutil_isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil :=
  define_is_pkg_init iprop(True)
instance pbutil_get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil :=
  build_get_is_pkg_init_wf
instance hash_isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.hash :=
  define_is_pkg_init iprop(True)
instance hash_get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.hash :=
  build_get_is_pkg_init_wf
instance crc32_isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.hash.crc32 :=
  define_is_pkg_init iprop(True)
instance crc32_get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.hash.crc32 :=
  build_get_is_pkg_init_wf
instance crc_isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.crc :=
  define_is_pkg_init iprop(True)
instance crc_get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.crc :=
  build_get_is_pkg_init_wf
instance fileutil_isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil :=
  define_is_pkg_init iprop(True)
instance fileutil_get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.storage.wal

end init

end Perennial
