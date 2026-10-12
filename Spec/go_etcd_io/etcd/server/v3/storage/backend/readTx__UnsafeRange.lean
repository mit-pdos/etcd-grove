/-
`UnsafeRange` (the backend). `rt.UnsafeRange(bucket, key, endKey, limit)` of the held shared read transaction: `rtRange`
of the readers' state (an end key nil or not empty; no limit above 1 on a bucket that is not
safe-range: that panics).
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

/-- `rt.UnsafeRange(bucket, key, endKey, limit)` of the held shared read transaction: `rtRange`
of the readers' state (an end key nil or not empty; no limit above 1 on a bucket that is not
safe-range: that panics). -/
abbrev backend.readTx.UnsafeRange.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (WR : IProp GF) (b : Loc) (rt : Loc) (rtx : Loc) (rv : RView) (qo : Qp) (bk : GoInterface) (bi : BucketInfo) (key endKey : GoSlice) (kb eb : GoString) (dk de : DFrac) (limit : w64),
  (endKey = slice.nil ↔ eb = []) → (sint.Z (rangeLimit eb limit) ≤ 1 ∨ bi.safe = true) → P.has bi →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P WR b ∗ bF go!"readTx" b ↦□ rt ∗ rtHeld γ P b rtx rv ∗ bOpen γ qo ∗ isBucket bk bi ∗
      key ↦*{dk} kb ∗ endKey ↦*{de} eb }}
    (App (App (App (App (Val (rt @!! go.GoType.PointerType readTx.ty @!! go!"UnsafeRange")) (Val #bk)) (Val #key)) (Val #endKey)) (Val #limit))
  {{ (keys vals : GoSlice), RET (PairV #keys #vals); rtHeld γ P b rtx rv ∗ bOpen γ qo ∗
      key ↦*{dk} kb ∗ endKey ↦*{de} eb ∗ kvsOutRd rtx keys vals (rtRange rv bi kb eb limit) }}

end spec

end EtcdGrove
end Perennial
