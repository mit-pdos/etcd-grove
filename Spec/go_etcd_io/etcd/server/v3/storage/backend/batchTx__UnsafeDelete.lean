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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- (The backend-compaction stage, review round 2, R2-6: the key either the caller's own slice or
one of the session's bbolt transaction, `own`, as bbolt's `Bucket.Delete_kv`.) `t.UnsafeDelete(bucket, key)` on the writer: bbolt's writer deletes the entry (the bucket must exist: else `lg.Fatal`), one more pending operation. -/
abbrev backend.batchTx.UnsafeDelete.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (st : BSess) (bk : GoInterface) (bi : BucketInfo) (key : GoSlice) (kb : GoString) (dk : DFrac)
    (own : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ btW γ t st ∗ isBucket bk bi ∗
      (if own then key ↦*{dk} kb else txBytes st.tx key kb) }}
    (App (App (Val (btOf t @!! go.GoType.PointerType batchTx.ty @!! go!"UnsafeDelete")) (Val #bk)) (Val #key))
  {{ RET #(); btW γ t (st.del bi kb) ∗ (if own then key ↦*{dk} kb else txBytes st.tx key kb) }}

end spec

end EtcdGrove
end Perennial
