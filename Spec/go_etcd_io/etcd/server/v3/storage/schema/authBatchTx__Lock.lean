/-
`(*authBatchTx).Lock()` (`auth.go`): the backend's `LockInsideApply` on the transaction.
Lean-first (no Rocq counterpart); the authstore-noax stage (2026-11-18, `notes/decisions.md`,
"authstore-noax").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthBackendReal
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__LockInsideApply

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage backend

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [backend_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- An `authBatchTx` over the real backend's batch transaction `t`: as
`batchTxBuffered.LockInsideApply.spec` (the post-lock hook's contract, the lock's state). -/
abbrev schema.authBatchTx.Lock.spec : Prop :=
  ∀ (atl : Loc) (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t : Loc) (qo : Qp) (dq : DFrac)
    (f : GoFunc) (Pre Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ schema.abtF go!"tx" atl ↦□ (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty) #t : GoInterface) ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ bOpen γ qo ∗ plHookAt γ dq f ∗ Pre ∗
      ((⌜f = func.nil⌝ ∗ (Pk ∗ Pre -∗ Q)) ∨
       (⌜f ≠ func.nil⌝ ∗ □ ({{ Pk ∗ Pre }} (App (Val #f) (Val #())) {{ RET #(); Q }}))) }}
    (App (Val (atl @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty @!! go!"Lock")) (Val #()))
  {{ RET #(); ∃ st : BSess, batchLocked γ P b st ∗ ⌜freeOk P st⌝ ∗ W ∗ Q ∗ bOpen γ qo ∗
      plHookAt γ dq f }}

end spec

end EtcdGrove
end Perennial
