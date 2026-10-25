/-
`NewCtxClient(ctx, opts...)` (`client/v3/client.go`; PR etcd#22658): creates a `*Client` with a
context and `epMu` but no underlying gRPC connection or resolver (`c.resolver = nil`), running
`opts` and defaulting `c.lg` to `zap.NewNop()` if `c.lg.Load() == nil`. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClientNew
public import Perennial.Proof.context
public import Perennial.Proof.sync.RWMutexGuard

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `NewCtxClient(ctx, opts...)` on a context `ctx` and options `opts` satisfying
`ctxClientOptOk` creates a `*Client` `c` with `c.resolver = null`, `c.endpoints = slice.nil`,
`c.epMu` guarding `True`, and `isClientLogger c` (defaulting to `zap.NewNop()` if `opts` leave
`c.lg` nil). -/
abbrev NewCtxClient.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (optsSl : GoSlice)
    (opts : List GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      context.isContext ctx cs ∗
      optsSl ↦*□ opts ∗
      □ (∀ (i : Nat) (opt : GoFunc), ⌜opts[i]? = some opt⌝ -∗ ctxClientOptOk opt) }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.NewCtxClient)) (Val #(GoInterface.ok ctx)))
      (Val #optsSl))
  {{ (c : Loc), RET #c; ⌜c ≠ null⌝ ∗ isClientLogger c ∗
      (∃ mu : Loc, clientF c go!"epMu" ↦□ mu ∗ sync.isRWMutexGuard mu (fun _ => iprop(True))) ∗
      clientF c go!"endpoints" ↦ slice.nil ∗
      clientF c go!"resolver" ↦□ (null : Loc) ∗
      (∃ (ctx' : GoInterfaceOk) (γ' : context.ContextNames) (cancel : GoFunc),
        clientF c go!"ctx" ↦□ GoInterface.ok ctx' ∗ clientF c go!"cancel" ↦□ cancel ∗
        context.cancelSpec cancel γ' iprop(True) ∗
        context.isContext ctx' { cs with PDone := iprop(True), Done_gn := γ' }) }}

end spec

end EtcdGrove
end Perennial
