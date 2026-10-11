/-
`notifier.wait(ctx)`. Lean-first (no Rocq counterpart); see `InvNotifier.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvNotifier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `n.wait(ctx)`: `nil` once a notification happened after the call (the count is above the
caller's lower bound `k0`), or a non-nil error once the context is done
(`notifierWaitResult`). -/
abbrev notifier.wait.spec : Prop :=
  ∀ (n : Loc) (γ : NotifierNames) (k0 : Nat) (ctx : GoInterfaceOk)
    (s : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      notifierHandle n γ ∗ notifierLb γ k0 ∗ context.isContext ctx s }}
    (App (Val (n @!! go.GoType.PointerType notifier.ty @!! go!"wait")) (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; notifierHandle n γ ∗ notifierWaitResult γ k0 s err }}

end spec

end EtcdGrove
end Perennial
