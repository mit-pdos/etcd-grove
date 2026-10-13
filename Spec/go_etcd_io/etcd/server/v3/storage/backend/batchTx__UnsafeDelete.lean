/-
`batchTx.UnsafeDelete` (`batch_tx.go`). `t.UnsafeDelete(bucket, key)` on the writer: bbolt's writer deletes the entry (the bucket must exist: else `lg.Fatal`), one more pending operation.
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

/-- `t.UnsafeDelete(bucket, key)` on the writer: bbolt's writer deletes the entry (the bucket must exist: else `lg.Fatal`), one more pending operation. -/
abbrev backend.batchTx.UnsafeDelete.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (st : BSess) (bk : GoInterface) (bi : BucketInfo) (key : GoSlice) (kb : GoString) (dk : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ btW γ t st ∗ isBucket bk bi ∗ key ↦*{dk} kb }}
    (App (App (Val (btOf t @!! go.GoType.PointerType batchTx.ty @!! go!"UnsafeDelete")) (Val #bk)) (Val #key))
  {{ RET #(); btW γ t (st.del bi kb) ∗ key ↦*{dk} kb }}

end spec

end EtcdGrove
end Perennial
