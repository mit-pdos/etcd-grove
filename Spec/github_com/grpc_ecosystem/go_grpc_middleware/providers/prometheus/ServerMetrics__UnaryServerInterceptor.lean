/-
grpc-prometheus's `(*ServerMetrics).UnaryServerInterceptor(opts...)` (names only; item 4, the server
start): the second interceptor of etcd's unary chain.
-/
module

public import Proof.google_golang_org.grpc.InvGrpcServer
public import GeneratedProof.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus
public import Proof.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.Defs
public import Proof.google_golang_org.grpc.InvGrpcProm

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

/-- `m.UnaryServerInterceptor()` (no option) returns a transparent interceptor (`srvInterceptorOk`,
no resource, for any requests), one of grpc-prometheus's (`promUnaryIc`: 2026-11-24, so that etcd's
members' axiom can name etcd's unary chain, `notes/axiom-review/norefusal-link.md`; the restatement
only names the value Go returns, the closure `interceptors.UnaryServerInterceptor(reporter)` builds). -/
abbrev grpc_prometheus.ServerMetrics.UnaryServerInterceptor.spec : Prop :=
  ∀ (m : Loc),
  {{ promSrvMetrics (GF := GF) m }}
    (App (Val (m @!! go.GoType.PointerType github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.ServerMetrics.ty @!! go!"UnaryServerInterceptor"))
      (Val #slice.nil))
  {{ (ic : GoFunc), RET #ic; (□ ∀ Q : GoInterface → IProp GF, srvInterceptorOk ic iprop(True) Q) ∗
      ⌜promUnaryIc ic⌝ }}

end spec

end EtcdGrove
end Perennial
