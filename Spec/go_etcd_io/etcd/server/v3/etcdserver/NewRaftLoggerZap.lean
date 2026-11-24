/-
`NewRaftLoggerZap(lg)` (`server/etcdserver/zap_raft.go:39`; `etcdserver` is translated, this function
names-only): the trust boundary (premises to axioms, item C, 2026-11-24). Until then the closed theorems
took it as the Iris premise `rnLoggerZapOk` (`InvNodeStart.lean`, now gone), whose triple this is,
unchanged. `newRaftNode`'s proof takes it as a callee. Interim: retired once zap's `WithOptions`,
`AddCallerSkip` and `Sugar` have specs and the body is translated (plan item C, claim #40).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `NewRaftLoggerZap(lg)`, for a non-nil `*zap.Logger`, returns some `raft.Logger` interface value.

Why it is true of Go (`zap_raft.go:39-41` at the etcd pin): the body is
`skipCallerLg := lg.WithOptions(zap.AddCallerSkip(1)); return &zapRaftLogger{lg: skipCallerLg, sugar: skipCallerLg.Sugar()}`.
`(*Logger).WithOptions` clones the logger (`l.clone()`, a struct copy through the receiver, which a nil
receiver would panic on: hence `lg ≠ nil`) and applies the option (`AddCallerSkip` adds to the clone's
`callerSkip`); `Sugar` clones again and wraps it. None of them blocks, allocates without bound or fails
for a non-nil logger, even a zero `zap.Logger{}` (its core is then nil, which only logging reads). The
result is a non-nil `*zapRaftLogger` converted to `raft.Logger`; the post claims nothing of it. -/
abbrev NewRaftLoggerZap.spec : Prop :=
  ∀ lg : Loc,
  {{ (⌜lg ≠ null⌝ : IProp GF) }} (App (Val (@! NewRaftLoggerZap)) (Val #lg)) {{ (l : GoInterface), RET #l; True }}

end spec

end EtcdGrove
end Perennial
