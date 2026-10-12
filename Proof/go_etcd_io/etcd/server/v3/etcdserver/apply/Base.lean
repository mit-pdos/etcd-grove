/-
Package initialization for etcd's server `apply` package (`server/v3/etcdserver/apply`: the
applier chain between the apply thread and the `txn` package), and the instances of the
packages it reaches that no other `Base` states. Every other package it imports already has its
instance: the txn package's (`txn/Base.lean`), mvcc's (`storage/mvcc/Base.lean`: mvcc,
`traceutil`, `lease`, prometheus), the cache's (`cache/v3/Base.lean`: `zap`, `proto`,
`etcdserverpb`, `membershippb`, `authpb`), the server's (`etcdserver/Base.lean`: `cindex`,
`backend`), `etcdserver/errors/Base.lean`, and Perennial's (`context`, `errors`, `sync`, `time`).

The instances below are `True` (the packages are translated names-only or types-only); until
2026-10-12 they were in the server's `BaseApply.lean`, which now imports this file: the apply
package must not import the server's translation (the server's proofs will import the apply
package's, unit 3 of the apply plan).

As there, the package facts are assumptions about package initialization, not proved from
`initialize'` (the package's initializer runs the axiomatized initializer of `alarms` and its
`init`, `prometheus.MustRegister(alarms)`). `applyInit` states what the translated code reads of
the package variables: its own gauge `alarms` (a `*prometheus.GaugeVec`, read by the backend's
`Alarm`), and one error variable of an imported package it returns, `etcdserver/errors`'
`ErrCorrupt` (the corrupt applier), a fixed non-nil error, stated here rather than in its
package's facts (`ErrNoSpace` only, the server's), as the txn package does for its foreign
errors; `ErrNoSpace` (quota, capped) is `errors`' fact and mvcc's `ErrCompacted` (`dispatch`)
mvcc's.
-/
module

public import Code.go_etcd_io.etcd.server.v3.etcdserver.apply
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.apply
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.errors.Base
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.sync
public import Perennial.Proof.time
public import Perennial.Proof.context
public import Perennial.Proof.errors

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

-- `github.com/Masterminds/semver/v3` (names only: `MustParse`, `Version.LessThan`/`String`)
namespace github_com.Masterminds.semver.v3

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.Masterminds.semver.v3 :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.Masterminds.semver.v3 :=
  build_get_is_pkg_init_wf

end github_com.Masterminds.semver.v3

-- `etcdserver/api` (names only: `UpdateCapability`, passed as a value)
namespace go_etcd_io.etcd.server.v3.etcdserver.api

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.api

-- `etcdserver/version` (types only: `DowngradeInfo`)
namespace go_etcd_io.etcd.server.v3.etcdserver.version

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.version :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.version :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.version

-- `client/pkg/v3/types` (names only: `ID.String`)
namespace go_etcd_io.etcd.client.pkg.v3.types

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.client.pkg.v3.types

-- `pkg/v3/pbutil` (names only: `MustUnmarshalMessage`)
namespace go_etcd_io.etcd.pkg.v3.pbutil

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.pkg.v3.pbutil

-- `pkg/v3/wait` (names only: the `Wait` interface)
namespace go_etcd_io.etcd.pkg.v3.wait

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.pkg.v3.wait

-- `server/v3/auth` (names only: the `AuthStore` interface, `AuthInfo`)
namespace go_etcd_io.etcd.server.v3.auth

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.auth

-- `api/v3alarm` (names only: `AlarmStore`)
namespace go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm

-- `api/membership` (names only: `RaftCluster`)
namespace go_etcd_io.etcd.server.v3.etcdserver.api.membership

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.api.membership

-- raft v3.7's `raftpb` (etcd's own raft dependency; types only)
namespace go_etcd_io.raft.v3.raftpb

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb :=
  build_get_is_pkg_init_wf

end go_etcd_io.raft.v3.raftpb

-- `server/v3/storage` (names only: `Quota`, `BackendQuota`)
namespace go_etcd_io.etcd.server.v3.storage

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.storage

namespace go_etcd_io.etcd.server.v3.etcdserver.apply

/-- The apply package's facts: its gauge `alarms` holds a fixed `*prometheus.GaugeVec` (whose
`WithLabelValues` is the trust boundary, `Spec/github_com/prometheus/client_golang/prometheus/
GaugeVec__WithLabelValues.lean`), and `etcdserver/errors.ErrCorrupt` a fixed non-nil error. -/
abbrev applyInit : IProp GF :=
  iprop((∃ gv : Loc, globalAddr alarms ↦□ gv) ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.server.v3.etcdserver.errors.ErrCorrupt ↦□ GoInterface.ok e))

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply :=
  define_is_pkg_init applyInit
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.apply

end init

end Perennial
