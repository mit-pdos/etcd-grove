/-
`SetTxPostLockInsideApplyHook` (the backend). `b.SetTxPostLockInsideApplyHook(hook)`: the post-lock hook replaced (under the batch lock;
its `Unlock` may write the buffer back: a write-back's budget).
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

/-- `b.SetTxPostLockInsideApplyHook(hook)`: the post-lock hook replaced (under the batch lock;
its `Unlock` may write the buffer back: a write-back's budget). -/
abbrev backend.backend.SetTxPostLockInsideApplyHook.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (qo : Qp) (f hook : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗ bOpen γ qo ∗ plHook γ f ∗ wbTok γ }}
    (App (Val (b @!! go.GoType.PointerType backend.ty @!! go!"SetTxPostLockInsideApplyHook")) (Val #hook))
  {{ RET #(); bOpen γ qo ∗ plHook γ hook }}

end spec

end EtcdGrove
end Perennial
