/-
Package initialization instances for the packages the apply thread's translation
(`server/v3/etcdserver`, `EtcdCache/Code/go_etcd_io/etcd/server/v3/etcdserver.lean`) reaches,
beyond those of `Cache/Base.lean` (protobuf, `etcdserverpb`, ...), `Server/Base.lean`
(`cindex`, `schema`, `backend`, `verify`) and mvcc's `Base.lean` (`storage/mvcc`, with the
facts of its initializer the KV core's proofs use, `pkg/v3/traceutil`, `server/v3/lease`,
`pkg/v3/schedule`, prometheus; 2026-10-10: the three were here too, as `True`, until the
mvcc translation got bodies and `storage/mvcc`'s instance needed prometheus's). Generated
by a script from the translation's `PkgInfo` imports.

As there, these are assumptions about package initialization, not proved from
`initialize'`. They are `True` (the packages are translated names-only or types-only).
`etcdserver/errors`' (`ErrNoSpace`, which the entry applier compares the applier's error
with) is in its own `errors/Base.lean` (2026-10-11: moved there, unchanged, for the server's
txn package, which imports it without the apply thread's translation). The instances of the
packages the server's `apply` package reaches (`apply` itself, `raftpb`, `pbutil`, `wait`,
`auth`, `v3alarm`, `membership`, `storage`, `client/pkg/v3/types`) are in `apply/Base.lean`
(2026-10-12: moved there, unchanged but for `apply`'s, which now states the package's facts,
for the apply package, which must not import the server's translation).
-/
module

public import Code.go_etcd_io.etcd.server.v3.etcdserver
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Base
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.errors.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

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

namespace net.http

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.net.http :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.net.http :=
  build_get_is_pkg_init_wf

end net.http

namespace github_com.dustin.go_humanize

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.dustin.go_humanize :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.dustin.go_humanize :=
  build_get_is_pkg_init_wf

end github_com.dustin.go_humanize

-- zap, zapcore, protoreflect and proto: `Proof/go_etcd_io/etcd/cache/v3/Base.lean` (clientv3
-- imports them too).

namespace go_opentelemetry_io.contrib.instrumentation.google_golang_org.grpc.otelgrpc

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_opentelemetry_io.contrib.instrumentation.google_golang_org.grpc.otelgrpc :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_opentelemetry_io.contrib.instrumentation.google_golang_org.grpc.otelgrpc :=
  build_get_is_pkg_init_wf

end go_opentelemetry_io.contrib.instrumentation.google_golang_org.grpc.otelgrpc

namespace go_etcd_io.bbolt

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.bbolt :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.bbolt :=
  build_get_is_pkg_init_wf

end go_etcd_io.bbolt

namespace go_etcd_io.etcd.client.pkg.v3.transport

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.transport :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.transport :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.client.pkg.v3.transport

namespace go_etcd_io.etcd.pkg.v3.featuregate

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.featuregate :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.featuregate :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.pkg.v3.featuregate

namespace go_etcd_io.etcd.server.v3.etcdserver.api.v3discovery

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3discovery :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3discovery :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.api.v3discovery

namespace go_etcd_io.etcd.server.v3.config

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.config

namespace go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp

namespace go_etcd_io.etcd.server.v3.etcdserver.api.snap

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.api.snap

-- etcdserver/errors: its own `errors/Base.lean` (imported above; the server txn package needs it
-- without the apply thread's translation).

namespace go_etcd_io.raft.v3

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.raft.v3 :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.raft.v3 :=
  build_get_is_pkg_init_wf

end go_etcd_io.raft.v3

namespace go_etcd_io.etcd.pkg.v3.contention

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.contention :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.contention :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.pkg.v3.contention

namespace go_etcd_io.etcd.pkg.v3.idutil

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.idutil :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.idutil :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.pkg.v3.idutil

namespace go_etcd_io.etcd.pkg.v3.notify

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.notify :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.notify :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.pkg.v3.notify

namespace go_etcd_io.etcd.server.v3.etcdserver.api.v2stats

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.api.v2stats

namespace go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor

namespace go_etcd_io.etcd.server.v3.etcdserver.read

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.read

namespace go_etcd_io.etcd.server.v3.etcdserver

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver

end init

end Perennial
