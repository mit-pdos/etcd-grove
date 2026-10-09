/-
`ready.WaitReady(ctx)`. Lean-first (no Rocq counterpart); see `InvReady.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvReady

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `r.WaitReady(ctx)`: `nil` once it saw the `ready` ready (in an epoch at least `e0`), or
a non-nil error once the context is done. -/
abbrev ready.WaitReady.spec : Prop :=
  ∀ (r : Loc) (γ : ReadyNames) (e0 : Nat) (ctx : GoInterfaceOk)
    (s : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isReady r γ ∗ readyEpochLb γ e0 ∗ context.isContext ctx s }}
    (App (Val (r @!! go.GoType.PointerType ready.ty @!! go!"WaitReady"))
      (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; readyWaitResult γ e0 s id err }}

end spec

end EtcdGrove
end Perennial
