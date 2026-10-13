/-
`batchTx.LockInsideApply` (`batch_tx.go`). `t.LockInsideApply()`: the batch lock (the lock holder's `W`), then the post-lock hook `f`
(if not nil) under it, on the hooks' `Pk` and the caller's `Pre` (`{Pk ∗ Pre} f() {Q}`); with no
hook, `Q` made of `Pk ∗ Pre` by the caller.
Lean-first (no Rocq counterpart); see `InvBatch.lean` and `InvBackend.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBatch

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `t.LockInsideApply()`: the batch lock (the lock holder's `W`), then the post-lock hook `f`
(if not nil) under it, on the hooks' `Pk` and the caller's `Pre` (`{Pk ∗ Pre} f() {Q}`); with no
hook, `Q` made of `Pk ∗ Pre` by the caller. -/
abbrev backend.batchTx.LockInsideApply.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (qo : Qp) (dq : DFrac) (f : GoFunc)
    (Pre Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ bOpen γ qo ∗ plHookAt γ dq f ∗ Pre ∗
      ((⌜f = func.nil⌝ ∗ (Pk ∗ Pre -∗ Q)) ∨
       (⌜f ≠ func.nil⌝ ∗ □ ({{ Pk ∗ Pre }} (App (Val #f) (Val #())) {{ RET #(); Q }}))) }}
    (App (Val (btOf t @!! go.GoType.PointerType batchTx.ty @!! go!"LockInsideApply")) (Val #()))
  {{ RET #(); ∃ st : BSess, batchLocked γ P b st ∗ ⌜freeOk P st⌝ ∗ W ∗ Q ∗ bOpen γ qo ∗
      plHookAt γ dq f }}

end spec

end EtcdGrove
end Perennial
