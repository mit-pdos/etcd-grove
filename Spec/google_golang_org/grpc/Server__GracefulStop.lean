/-
`(*grpc.Server).GracefulStop()` (grpc-go, assumed: `server.go`).

Users: 2e's stop of a member (`embed.Etcd.Close`, `EtcdServer`'s stop path).

Why true: `GracefulStop` stops accepting and waits for the runs in flight to return. It may be called at any time, concurrently with `Serve` and with itself.

Changes: new.

Margin: nothing is given back: the runs' resources are their own (each returns its thread's
token to the fuel when it exits).
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

/-- `gs.GracefulStop()`: returns. -/
def Server.GracefulStop.spec : Prop :=
  ∀ (gs : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc }}
    (App (Val (gs @!! go.GoType.PointerType google_golang_org.grpc.Server.ty @!! go!"GracefulStop")) (Val #()))
  {{ RET #(); True }}

end spec

end Grpc
end EtcdGrove
end Perennial
