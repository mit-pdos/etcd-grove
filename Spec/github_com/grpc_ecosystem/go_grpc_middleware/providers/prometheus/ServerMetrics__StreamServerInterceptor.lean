/-
grpc-prometheus's `(*ServerMetrics).StreamServerInterceptor(opts...)` (names only; item 4, the
server start): the first interceptor of etcd's stream chain.
-/
module

public import Proof.google_golang_org.grpc.InvGrpcServer
public import GeneratedProof.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `m.StreamServerInterceptor()` (no option) returns a transparent stream interceptor
(`srvStreamInterceptorOk`, no resource). -/
abbrev grpc_prometheus.ServerMetrics.StreamServerInterceptor.spec : Prop :=
  ∀ (m : Loc),
  {{ promSrvMetrics (GF := GF) m }}
    (App (Val (m @!! go.GoType.PointerType github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.ServerMetrics.ty @!! go!"StreamServerInterceptor"))
      (Val #slice.nil))
  {{ (ic : GoFunc), RET #ic; srvStreamInterceptorOk ic iprop(True) }}

end spec

end EtcdGrove
end Perennial
