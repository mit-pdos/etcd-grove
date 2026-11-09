/-
`grpc.NewServer(opts...)` (grpc-go, assumed: `server.go`).

Users: `v3rpc.Server` (`grpc.go:89`, this batch).

Why true: `NewServer` applies the options in order and allocates a server with no service
registered; it neither listens nor starts goroutines that run handlers.

Changes: from `specs-ref/Spec/google_golang_org/grpc/NewServer.lean`: over `SrvCfg`.

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

/-- `grpc.NewServer(opts...)` with options acting as `fs`: a server being built, nothing
registered. -/
def NewServer.spec : Prop :=
  ∀ (opts : GoSlice) (vs : List GoInterface) (fs : List (SrvCfg → SrvCfg)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ opts ↦*□ vs ∗ ([∗list] v; f ∈ vs; fs, srvOptAt v f) }}
    (App (Val (@! google_golang_org.grpc.NewServer)) (Val #opts))
  {{ (gs : Loc), RET #gs;
      srvBuild gs (fs.foldl (fun B f => f B) { ics := [], sics := [], regs := [], sregs := [] }) }}

end spec

end Grpc
end EtcdGrove
end Perennial
