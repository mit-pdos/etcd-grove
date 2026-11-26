/- Lean-first (no Rocq counterpart).

**DRAFT (etcd_safe S0, 2026-11-26; unreached, not reviewed).** `gs.GracefulStop()` of the gRPC server a member
machine serves etcd's API with (grpc-go's `(*Server).GracefulStop`, `models/grpc/server.go:1405`), at the
distributed deployment's boundary. The axiom is `Proof/.../etcd/dist/GracefulStopDist.lean`.
`plans/etcd-safe-restart-design.md` §1.3 (the stopper: `GracefulStop`, then `HardStop`), §3.

* `grpcServing gs E` (exclusive, opaque): the right to stop `gs`, the gRPC server of the member whose apply
  environment is `E`, serving etcd's table over the serving stocks `memberUpL` hands it (the gRPC run pool's
  store readers among them). Produced by `serve_dist` (`server.serve`'s axiom: pending the Go change,
  `notes/etcd-dist-restart-axioms.md`); nothing produces it today.
* `GracefulStop_dist.spec`: from `grpcServing gs E`, `GracefulStop` returns with the store readers of the
  serving stocks (`srvStopReaders E`), what `HardStop`'s stop request takes (`srvStopReq`): so a member that
  served can be stopped, which `HardStop.spec`'s header (`EtcdServer__HardStop.lean:8-16`) says only a
  `GracefulStop` spec can allow.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRestart
public import Proof.google_golang_org.grpc.InvGrpc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- (DRAFT, trusted opaque) **The right to stop the member's gRPC server `gs`** (see the file header): `gs` serves
etcd's table for the member whose apply environment is `E`, over the serving stocks the member handed it. Its
intended reading: `gs`'s run pool holds the store readers `srvStopReaders E` while no run is active, and lends one
to each run (`grpcRunOkMd`'s contracts give it back when the handler returns). -/
opaque grpcServing (gs : Loc) (E : apply.AEnv GF) : IProp GF := iprop(False)

/-- **`gs.GracefulStop()` by the holder of the right to stop it** (DRAFT; see the axiom's docstring): it returns
with the serving stocks' store readers. -/
abbrev GracefulStop_dist.spec : Prop :=
  ∀ (gs : Loc) (E : apply.AEnv GF),
  {{ grpcServing gs E }}
    (App (Val (gs @!! go.GoType.PointerType google_golang_org.grpc.Server.ty @!! go!"GracefulStop")) (Val #()))
  {{ RET #(); srvStopReaders E }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
