/-
`Unlock` (the backend). `t.Unlock()`: the session's writes written back into the read buffer, and committed if a
delete is pending or the batch limit reached (the pre-commit hook then runs, with the hooks'
resource `Pk`); the readers' view becomes the writer's contents. A session that changed nothing
the readers see (`viewSame`: it may have put in or deleted from the hook's buckets, and then
commits) gives the lock's resources `W ∗ Pk`; otherwise it gives the clients' whole view and
`Pk`, and gets the view back at its new value, from which it makes `W` (a wand: `W` may hold part
of the view). A write-back's budget either way. (`Pk` is handed over up front in both cases: the
commit's hook needs it, before the new view exists.)
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
delete is pending or the batch limit reached (the pre-commit hook then runs, with the hooks'
resource `Pk`); the readers' view becomes the writer's contents. A session that changed nothing
the readers see (`viewSame`: it may have put in or deleted from the hook's buckets, and then
commits) gives the lock's resources `W ∗ Pk`; otherwise it gives the clients' whole view and
`Pk`, and gets the view back at its new value, from which it makes `W` (a wand: `W` may hold part
of the view). A write-back's budget either way. (`Pk` is handed over up front in both cases: the
commit's hook needs it, before the new view exists.) -/
abbrev backend.batchTxBuffered.Unlock.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (st : BSess) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗ wbTok γ ∗
      ((⌜viewSame P st⌝ ∗ W ∗ Pk ∗ Q) ∨
       (∃ vd : VData, bView γ 1 vd ∗ Pk ∗ (bView γ 1 (sData P st.S) -∗ W ∗ Q))) }}
    (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"Unlock")) (Val #()))
  {{ RET #(); Q }}

end spec

end EtcdGrove
end Perennial
