/-
`notifier.notify()`. Lean-first (no Rocq counterpart); see `InvNotifier.lean`.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `n.notify()`: one more notification (wakes the `wait`s that read the previous
channel). -/
abbrev notifier.notify.spec : Prop :=
  ∀ (n : Loc) (γ : NotifierNames) (k0 : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      notifierHandle n γ ∗ notifierLb γ k0 }}
    (App (Val (n @!! go.GoType.PointerType notifier.ty @!! go!"notify")) (Val #()))
  {{ RET #(); notifierHandle n γ ∗ notifierLb γ (k0 + 1) }}

end spec

end EtcdGrove
end Perennial
