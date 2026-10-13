/-
`batchTx.LockInsideApply` (`batch_tx.go`). `t.LockInsideApply()`: the batch lock, then the post-lock hook `f` (if not nil) under it.
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

/-- `t.LockInsideApply()`: the batch lock, then the post-lock hook `f` (if not nil) under it. -/
abbrev backend.batchTx.LockInsideApply.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (WR : IProp GF) (b : Loc) (t : Loc) (qo : Qp) (f : GoFunc) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P WR b ∗ bF go!"batchTx" b ↦□ t ∗ bOpen γ qo ∗ plHook γ f ∗ ((⌜f = func.nil⌝ ∗ Q) ∨ (⌜f ≠ func.nil⌝ ∗ WP (App (Val #f) (Val #())) {{ v, ⌜v = #()⌝ ∗ Q }})) }}
    (App (Val (btOf t @!! go.GoType.PointerType batchTx.ty @!! go!"LockInsideApply")) (Val #()))
  {{ RET #(); ∃ st : BSess, batchLocked γ P b st ∗ ⌜freeOk P st⌝ ∗ WR ∗ bOpen γ qo ∗ plHook γ f ∗
      Q }}

end spec

end EtcdGrove
end Perennial
