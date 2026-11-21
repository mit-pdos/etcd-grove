/-
The package-initialization instances of the WAL's imports with no fact (`True`) that nothing else
declares: `pkg/v3/crc` (and `hash/crc32` until 2026-11-21, now with a fact of its own,
`Proof/hash/crc32/PkgInit.lean`); and the imports giving the others' (zap, `zapcore`, semver,
prometheus, `pkg/v3/pbutil`, `hash`, `proto`, ...: their own `PkgInit.lean`s, raft's `Base.lean`).
(`fileutil`'s, with a fact: `Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/PkgInit.lean`.) Their
`wp_initialize'`: the generated `Init.lean`s (`etc/gen-init.py`). WAL package init, 2026-11-13; one
home for the shared instances, 2026-11-15 (notes/wal-lean-integration.md).
-/
module

public import Proof.go_uber_org.zap.PkgInit
public import Proof.github_com.Masterminds.semver.v3.PkgInit
public import Proof.github_com.prometheus.client_golang.prometheus.PkgInit
public import Proof.go_etcd_io.etcd.pkg.v3.pbutil.PkgInit
public import Proof.hash.PkgInit
public import Proof.hash.crc32.PkgInit
public import GeneratedProof.go_etcd_io.etcd.pkg.v3.crc
public import GeneratedProof.go_etcd_io.etcd.client.pkg.v3.fileutil
public import Proof.go_etcd_io.raft.v3.Base
public import Proof.os.PkgInit
public import Proof.bufio.PkgInit
public import Proof.path.filepath.PkgInit
public import Proof.syscall.PkgInit
public import Proof.golang_org.x.sys.unix.PkgInit
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.PkgInit
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

instance crc_isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.crc :=
  define_is_pkg_init iprop(True)
instance crc_get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.crc :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.storage.wal

end init

end Perennial
