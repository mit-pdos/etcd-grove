/-
`(*grpc.Server).GracefulStop()` (grpc-go, assumed: `server.go`).

Users: 2e's stop of a member (`embed.Etcd.Close`, `EtcdServer`'s stop path).

Why true: `GracefulStop` stops accepting and waits for the runs in flight to return. It may be called at any time, concurrently with `Serve` and with itself.

Changes: new.

Margin: the thread tokens are not given back (each run returns its thread's token to the pool, which
stays grpc's); the run resources are (integration X: `drainTok`, what 2e's stop needs to recover the
`srvGate` shares the member's handlers held). `ServeHTTP`'s runs are not waited for (`startHTTP`
lends none).
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

/-- `gs.GracefulStop()`: returns once the runs in flight have; the run resources each `start` lent
come back (integration X: `drainTok`). -/
def Server.GracefulStop.spec : Prop :=
  ∀ (gs : Loc) (ds : List (IProp GF × Nat)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ [∗list] d ∈ ds, drainTok gs d.1 d.2 }}
    (App (Val (gs @!! go.GoType.PointerType google_golang_org.grpc.Server.ty @!! go!"GracefulStop")) (Val #()))
  {{ RET #(); [∗list] d ∈ ds, [∗list] _u ∈ List.replicate d.2 (), d.1 }}

end spec

end Grpc
end EtcdGrove
end Perennial
