/-
Trust boundary: `grpc.StatsHandler` (an axiom; see `Spec/google_golang_org/grpc/StatsHandler.lean`).
-/
module

public import Spec.google_golang_org.grpc.StatsHandler

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (item 4, the server start): a stats handler is called around each call
(`TagRPC` may return a derived context, `HandleRPC` observes): with `grpcStatsHandlerOk` (no value
under etcd's keys, every call let run) what a run is given is as `grpcRunCtx` states. -/
axiom grpc.StatsHandler.wp_proof : grpc.StatsHandler.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
