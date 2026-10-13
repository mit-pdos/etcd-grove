/-
`LockOutsideApply` (the backend). `t.LockOutsideApply()`: the batch lock, free state and the client's resources `W ∗ Pk`.
Lean-first (no Rocq counterpart); see `InvBackend.lean` and `notes/decisions.md`, "The backend:
the buffers, bbolt as a key-value contract, the locks and the views".
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend

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

/-- `t.LockOutsideApply()`: the batch lock, free state and the client's resources `W ∗ Pk`. -/
abbrev backend.batchTxBuffered.LockOutsideApply.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (qo : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ bOpen γ qo }}
    (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"LockOutsideApply")) (Val #()))
  {{ RET #(); ∃ st : BSess, batchLocked γ P b st ∗ ⌜freeOk P st⌝ ∗ (W ∗ Pk) ∗ bOpen γ qo }}

end spec

end EtcdGrove
end Perennial
