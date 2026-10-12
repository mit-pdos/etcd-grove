/-
`Unlock` (the backend). `t.Unlock()`: the session's writes written back into the read buffer, and committed if a
delete is pending or the batch limit reached (the pre-commit hook then runs, with the client's
resource); the readers' view becomes the writer's contents. A session that changed nothing the
readers see (`freeOk`) needs only the client's resource; otherwise the clients' whole view,
given back at its new value. A write-back's budget either way.
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

/-- `t.Unlock()`: the session's writes written back into the read buffer, and committed if a
delete is pending or the batch limit reached (the pre-commit hook then runs, with the client's
resource); the readers' view becomes the writer's contents. A session that changed nothing the
readers see (`freeOk`) needs only the client's resource; otherwise the clients' whole view,
given back at its new value. A write-back's budget either way. -/
abbrev backend.batchTxBuffered.Unlock.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (WR : IProp GF) (b : Loc) (t : Loc) (st : BSess) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P WR b ∗ bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗ wbTok γ ∗
      ((⌜freeOk P st⌝ ∗ WR ∗ Q) ∨
       (∃ vd : VData, bView γ 1 vd ∗ (bView γ 1 (sData P st.S) -∗ WR ∗ Q))) }}
    (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"Unlock")) (Val #()))
  {{ RET #(); Q }}

end spec

end EtcdGrove
end Perennial
