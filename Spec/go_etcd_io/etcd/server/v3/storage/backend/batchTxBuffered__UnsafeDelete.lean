/-
`UnsafeDelete` (the backend). `t.UnsafeDelete(bucket, key)` under the lock: bbolt's writer deletes the entry; a pending
delete (the `Unlock` commits).
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

/-- `t.UnsafeDelete(bucket, key)` under the lock: bbolt's writer deletes the entry; a pending
delete (the `Unlock` commits). Not in a safe-range bucket (`P.SB`). -/
abbrev backend.batchTxBuffered.UnsafeDelete.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (st : BSess) (bk : GoInterface) (bi : BucketInfo) (key : GoSlice) (kb : GoString)
    (dk : DFrac),
  P.has bi → sint.Z st.pend + 1 < 2 ^ 58 → P.SB bi.name = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗ isBucket bk bi ∗ key ↦*{dk} kb }}
    (App (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"UnsafeDelete")) (Val #bk)) (Val #key))
  {{ RET #(); batchLocked γ P b (st.del bi kb) ∗ key ↦*{dk} kb }}

end spec

end EtcdGrove
end Perennial
