/-
**A server stats handler** (split out of `InvGrpcServer.lean`, 2026-11-25,
`notes/phase7-endstate.md` §4): `grpcStatsHandlerOk h`, an axiomatized property of the
`stats.Handler` `h`, which `otelgrpc.NewServerHandler`'s spec gives and `grpc.StatsHandler`'s takes
(the option's kind `.stats h`, `InvGrpcServer.lean`).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.GooseLang.Lang

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- **The `stats.Handler` `h` adds no value under etcd's context keys and lets every call run**
(an axiomatized property, introduced by `otelgrpc.NewServerHandler`'s spec): what `grpcRunCtx`
presumes of the stats handlers in front of a method's handler. Since 2026-11-06 (`grpcRunCtx`'s
`trace.spanCtxOk`), also: the span it stores under otel's span key, if any, is a span (otelgrpc's:
its tracer's, `End`, `AddEvent`, `RecordError` returning). -/
axiom grpcStatsHandlerOk [GooseExts] (h : GoInterface) : Prop

end EtcdGrove
end Perennial
