/-
grpc-prometheus's `(*ServerMetrics).InitializeMetrics(server)` (names only; item 4, the server
start): `v3rpc.Server` zeroes the metrics of its server's methods.
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

/-- `m.InitializeMetrics(gs)` on a server being built returns it as it was. -/
abbrev grpc_prometheus.ServerMetrics.InitializeMetrics.spec : Prop :=
  ∀ (m gs : Loc) (ics sics : List GoFunc) (svcs : List GoString)
    (regs sregs : List (GoString × val × GoInterface)),
  {{ promSrvMetrics (GF := GF) m ∗ grpcSrvNew gs ics sics svcs regs sregs }}
    (App (Val (m @!! go.GoType.PointerType github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.ServerMetrics.ty @!! go!"InitializeMetrics"))
      (Val #(interface.mkOk (go.GoType.PointerType google_golang_org.grpc.Server.ty) #gs : GoInterface)))
  {{ RET #(); grpcSrvNew gs ics sics svcs regs sregs }}

end spec

end EtcdGrove
end Perennial
