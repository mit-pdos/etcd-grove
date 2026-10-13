/-
`UnsafeDeleteBucket` (the backend). `t.UnsafeDeleteBucket(bucket)` under the lock: the bucket deleted (absent or not); a pending
delete.
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

/-- `t.UnsafeDeleteBucket(bucket)` under the lock: the bucket deleted (absent or not); a pending
delete. Not a safe-range bucket (`P.SB`), nor one with a hook's own key (`P.hk`). -/
abbrev backend.batchTxBuffered.UnsafeDeleteBucket.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (st : BSess) (bk : GoInterface) (bi : BucketInfo),
  P.has bi → sint.Z st.pend + 1 < 2 ^ 58 → P.SB bi.name = false → (∀ k, P.hk bi.name k = false) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗ isBucket bk bi }}
    (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"UnsafeDeleteBucket")) (Val #bk))
  {{ RET #(); batchLocked γ P b (st.delBucket bi) }}

end spec

end EtcdGrove
end Perennial
