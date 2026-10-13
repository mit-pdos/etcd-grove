/-
`batchTx.UnsafeRange` (`batch_tx.go`). `t.UnsafeRange(bucket, key, endKey, limit)` on the writer: the range of bbolt's writer's contents (the bucket must exist: else `lg.Fatal`), as slices valid while its transaction `st.tx` is open.
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

/-- `t.UnsafeRange(bucket, key, endKey, limit)` on the writer: the range of bbolt's writer's contents (the bucket must exist: else `lg.Fatal`), as slices valid while its transaction `st.tx` is open. -/
abbrev backend.batchTx.UnsafeRange.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (WR : IProp GF) (b : Loc) (t : Loc) (st : BSess) (bk : GoInterface) (bi : BucketInfo) (key endKey : GoSlice) (kb eb : GoString) (dk de : DFrac) (limit : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P WR b ∗ bF go!"batchTx" b ↦□ t ∗ btW γ t st ∗ isBucket bk bi ∗ key ↦*{dk} kb ∗ endKey ↦*{de} eb }}
    (App (App (App (App (Val (btOf t @!! go.GoType.PointerType batchTx.ty @!! go!"UnsafeRange")) (Val #bk)) (Val #key)) (Val #endKey)) (Val #limit))
  {{ (keys vals : GoSlice), RET (PairV #keys #vals); btW γ t st ∗ key ↦*{dk} kb ∗ endKey ↦*{de} eb ∗
      kvsOutRd st.tx keys vals (cursorRange (bktEnts (bktOf st.S bi.name)) kb eb limit) }}

end spec

end EtcdGrove
end Perennial
