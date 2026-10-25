/-
A context's `Value(keepAliveCtxKey{})` (item 1, the client lease, 2026-10-18: `client/v3`'s
`lessor.keepAliveCtxCloser` compares a keep-alive's contexts by their value at that key): the trust
boundary. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvLease
public import Spec.context.WithValue
public import Perennial.Proof.context

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- `ctx.Value(key)` on a context (`context.isContext`, whose `Value` Perennial specifies only at
`&cancelCtxKey`) for clientv3's unexported context keys:
1. `keepAliveCtxKey` (`lessor.KeepAlive`'s `context.WithValue(ctx, keepAliveCtxKey{}, &ctx)`):
   returns `nil` or a `*context.Context`;
2. `channelKeyContextKey` (PR #21765, `channel_key.go`): a default client call context (`ctxOk`,
   not wrapped by `WithChannelKey` with a custom key) carries no custom channel key
   (`clientv3.ctxChannelKeyIs (GoInterface.ok ctx) none`). -/
abbrev context.ValueKeepAlive.spec : Prop :=
  (∀ (ctx key : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
    key.ty = go_etcd_io.etcd.client.v3.keepAliveCtxKey.ty →
    {{ context.isContext ctx cd }}
      (App (Val #(methods ctx.ty go!"Value" ctx.v)) (Val #(GoInterface.ok key)))
    {{ (v : GoInterface), RET #v;
        ⌜v = GoInterface.nil ∨
          ∃ p : Loc, v = interface.mkOk (go.GoType.PointerType _root_.Perennial.context.Context.ty) #p⌝ }}) ∧
  (∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
    ctxOk ctx cd ⊢ clientv3.ctxChannelKeyIs (GoInterface.ok ctx) none)

end spec

end EtcdGrove
end Perennial
