/-
A context's `Value(keepAliveCtxKey{})` (item 1, the client lease, 2026-10-18: `client/v3`'s
`lessor.keepAliveCtxCloser` compares a keep-alive's contexts by their value at that key): the trust
boundary. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvLease
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
`&cancelCtxKey`) for a key of clientv3's type `keepAliveCtxKey` (an empty struct, comparable;
unexported, so only `client/v3` stores a value under it: `lessor.KeepAlive`'s
`context.WithValue(ctx, keepAliveCtxKey{}, &ctx)`): returns `nil` or a `*context.Context` (the
caller compares two such values with `==`, which does not panic on them). -/
abbrev context.ValueKeepAlive.spec : Prop :=
  ∀ (ctx key : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  key.ty = go_etcd_io.etcd.client.v3.keepAliveCtxKey.ty →
  {{ context.isContext ctx cd }}
    (App (Val #(methods ctx.ty go!"Value" ctx.v)) (Val #(GoInterface.ok key)))
  {{ (v : GoInterface), RET #v;
      ⌜v = GoInterface.nil ∨
        ∃ p : Loc, v = interface.mkOk (go.GoType.PointerType _root_.Perennial.context.Context.ty) #p⌝ }}

end spec

end EtcdGrove
end Perennial
