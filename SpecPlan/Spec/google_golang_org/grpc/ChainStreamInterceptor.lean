/-
`grpc.ChainStreamInterceptor` (grpc-go, assumed: `server.go`).

Users: `v3rpc.Server` (`grpc.go:83`, this batch).

Why true: the option appends to `opts.chainStreamInts`; chained in order (`chainStreamServerInterceptors`).

Changes: from `specs-ref/.../grpc/ChainStreamInterceptor.lean`: over `SrvCfg`.

Margin: none.
-/
module

public import SpecPlan.Spec.google_golang_org.grpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Grpc

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `grpc.ChainStreamInterceptor(...)`: a server option acting as shown. -/
def ChainStreamInterceptor.spec : Prop :=
  ∀ (sl : GoSlice) (sics : List GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ sl ↦*□ sics }}
    (App (Val (@! google_golang_org.grpc.ChainStreamInterceptor)) (Val #sl))
  {{ (v : GoInterface), RET #v; srvOptAt v (fun B => { B with sics := B.sics ++ sics }) }}

end spec

end Grpc
end EtcdGrove
end Perennial
