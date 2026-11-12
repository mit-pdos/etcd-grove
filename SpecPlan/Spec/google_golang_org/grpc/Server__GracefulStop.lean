/-
`(*grpc.Server).GracefulStop()` (grpc-go, assumed: `server.go`).

Users: 2e's stop of a member (`embed.Etcd.Close`, `EtcdServer`'s stop path).

Why true: `GracefulStop` stops accepting and waits for the runs in flight to return. It may be called at any time, concurrently with `Serve` and with itself.

Changes: new.
verify-round (A6 second tier): the `n` thread tokens `start` took for the runs' pool come back too
(`threadToks n`): once the runs have returned, the pool holds them all, and the stopped server
starts no run; a member restarted in the same program needs them again.

Margin: the run resources are (integration X: `drainTok`, what 2e's stop needs to recover the
`srvGate` shares the member's handlers held). `ServeHTTP`'s runs are not waited for (`startHTTP`
lends none).
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

/-- `gs.GracefulStop()`: returns once the runs in flight have; the run resources each `start` lent
come back (integration X: `drainTok`), with the thread tokens of the runs' pool. -/
def Server.GracefulStop.spec : Prop :=
  ∀ (gs : Loc) (ds : List (IProp GF × Nat)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ [∗list] d ∈ ds, drainTok gs d.1 d.2 }}
    (App (Val (gs @!! go.GoType.PointerType google_golang_org.grpc.Server.ty @!! go!"GracefulStop")) (Val #()))
  {{ RET #(); [∗list] d ∈ ds, ([∗list] _u ∈ List.replicate d.2 (), d.1) ∗ threadToks d.2 }}

end spec

end Grpc
end EtcdGrove
end Perennial
