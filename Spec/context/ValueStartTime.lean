/-
A context's `Value(traceutil.StartTimeKey{})` (`EtcdServer.raftRequest` reads the request's start
time the server's `Put`/`Txn` stored with `context.WithValue`). Until sweep repairs 1's B2
(2026-11-08) a trust-boundary axiom for every `isContext`, false of a `WithValue` at the key with a
non-time value or a user `Context` whose `Value` panics; now a theorem over `startTimeOk`
(`Proof/context/ReqKeys.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Proof.context.ReqKeys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- `ctx.Value(StartTimeKey{})` of a context whose start time is a time (`startTimeOk`): `nil` or a
`time.Time`. -/
abbrev context.ValueStartTime.spec : Prop :=
  ∀ (ctx : GoInterfaceOk),
  {{ context.startTimeOk (GF := GF) ctx }}
    (App (Val #(methods ctx.ty go!"Value" ctx.v)) (Val #startTimeKeyAny))
  {{ (v : GoInterface), RET #v; ⌜startTimeRes v⌝ }}

end spec

end EtcdGrove
end Perennial
