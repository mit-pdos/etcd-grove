/-
Package initialization instances for the packages `v3rpc.Server` (`grpc.go`) brings into `v3rpc`'s
imports (item 4, the server start): grpc's health service and its protobuf package, grpc's
reflection interface, grpc-prometheus's provider. All are translated names-only (or types-only:
`Code/google_golang_org/grpc/{health,reflection}.toml`,
`Code/github_com/grpc_ecosystem/go_grpc_middleware/providers/prometheus.toml`) and their package
facts are `True`, as the other names-only packages' (`cache/v3/Base.lean`): an assumption about
package initialization, not proved from `initialize'`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import GeneratedProof.google_golang_org.grpc.health
public import GeneratedProof.google_golang_org.grpc.health.grpc_health_v1
public import GeneratedProof.google_golang_org.grpc.reflection
public import GeneratedProof.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance grpc_health_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.health :=
  define_is_pkg_init iprop(True)
instance grpc_health_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.health :=
  build_get_is_pkg_init_wf

instance grpc_health_v1_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.health.grpc_health_v1 :=
  define_is_pkg_init iprop(True)
instance grpc_health_v1_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.health.grpc_health_v1 :=
  build_get_is_pkg_init_wf

instance grpc_reflection_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.reflection :=
  define_is_pkg_init iprop(True)
instance grpc_reflection_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.reflection :=
  build_get_is_pkg_init_wf

instance grpc_prometheus_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus :=
  define_is_pkg_init iprop(True)
instance grpc_prometheus_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF)
      pkg_id.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus :=
  build_get_is_pkg_init_wf

end init

end Perennial
