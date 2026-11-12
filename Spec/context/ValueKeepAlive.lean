/-
A context's `Value(keepAliveCtxKey{})` (`client/v3`'s `lessor.keepAliveCtxCloser` compares a
keep-alive's contexts by their value at that key). Until sweep repairs 1's B2b (2026-11-08) a
trust-boundary axiom for every `isContext`; now a theorem over `keepAliveOk`
(`Proof/context/ReqKeys.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvLease
public import Perennial.Proof.context
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

/-- `ctx.Value(keepAliveCtxKey{})` of a context whose keep-alive key answers a context pointer
(`keepAliveOk`): `nil` or a `*context.Context`. -/
abbrev context.ValueKeepAlive.spec : Prop :=
  ∀ (ctx : GoInterfaceOk),
  {{ context.keepAliveOk (GF := GF) ctx }}
    (App (Val #(methods ctx.ty go!"Value" ctx.v)) (Val #keepAliveKeyAny))
  {{ (v : GoInterface), RET #v; ⌜keepAliveRes v⌝ }}

end spec

end EtcdGrove
end Perennial
