/-
prometheus's `Register(c)` (names only; item 4, the server start): `getServerMetrics` registers
grpc-prometheus's server metrics with the default registry.
-/
module

public import Proof.google_golang_org.grpc.InvGrpcServer
public import GeneratedProof.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus
public import GeneratedProof.github_com.prometheus.client_golang.prometheus

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `prometheus.Register(m)` of grpc-prometheus's server metrics returns an error or `nil`. -/
abbrev prometheus.Register.spec : Prop :=
  ∀ (m : Loc),
  {{ promSrvMetrics (GF := GF) m }}
    (App (Val (@! github_com.prometheus.client_golang.prometheus.Register))
      (Val #(interface.mkOk (go.GoType.PointerType github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.ServerMetrics.ty) #m : GoInterface)))
  {{ (err : GoInterface), RET #err; True }}

end spec

end EtcdGrove
end Perennial
