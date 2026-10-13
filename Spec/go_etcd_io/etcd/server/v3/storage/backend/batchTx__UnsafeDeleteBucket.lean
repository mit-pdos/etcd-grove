/-
`batchTx.UnsafeDeleteBucket` (`batch_tx.go`). `t.UnsafeDeleteBucket(bucket)` on the writer: the bucket deleted (absent or not), one more pending operation.
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

/-- `t.UnsafeDeleteBucket(bucket)` on the writer: the bucket deleted (absent or not), one more pending operation. -/
abbrev backend.batchTx.UnsafeDeleteBucket.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (WR : IProp GF) (b : Loc) (t : Loc) (st : BSess) (bk : GoInterface) (bi : BucketInfo),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P WR b ∗ bF go!"batchTx" b ↦□ t ∗ btW γ t st ∗ isBucket bk bi }}
    (App (Val (btOf t @!! go.GoType.PointerType batchTx.ty @!! go!"UnsafeDeleteBucket")) (Val #bk))
  {{ RET #(); btW γ t (st.delBucket bi) }}

end spec

end EtcdGrove
end Perennial
