/-
`grpc.ChainUnaryInterceptor` (grpc-go, assumed: `server.go`).

Users: `v3rpc.Server` (`grpc.go:82`, this batch).

Why true: the option appends the interceptors to `opts.chainUnaryInts`; `NewServer` chains them in order, the first outermost (`chainUnaryServerInterceptors`).

Changes: from `specs-ref/.../grpc/ChainUnaryInterceptor.lean`: over `SrvCfg`.

Margin: none.
-/
module

public import Spec.google_golang_org.grpc.Api

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

/-- `grpc.ChainUnaryInterceptor(...)`: a server option acting as shown. -/
def ChainUnaryInterceptor.spec : Prop :=
  ∀ (sl : GoSlice) (ics : List GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ sl ↦*□ ics }}
    (App (Val (@! google_golang_org.grpc.ChainUnaryInterceptor)) (Val #sl))
  {{ (v : GoInterface), RET #v; srvOptAt v (fun B => { B with ics := B.ics ++ ics }) }}

end spec

end Grpc
end EtcdGrove
end Perennial
