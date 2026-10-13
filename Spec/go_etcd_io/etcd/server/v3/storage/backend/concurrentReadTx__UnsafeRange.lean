/-
`UnsafeRange` (the backend). `crt.UnsafeRange(bucket, key, endKey, limit)`: `rtRange` of its state.
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

/-- `crt.UnsafeRange(bucket, key, endKey, limit)`: `rtRange` of its state. -/
abbrev backend.concurrentReadTx.UnsafeRange.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (crt rtx : Loc) (rv : RView) (bk : GoInterface) (bi : BucketInfo) (key endKey : GoSlice) (kb eb : GoString) (dk de : DFrac) (limit : w64),
  (endKey = slice.nil ↔ eb = []) → (sint.Z (rangeLimit eb limit) ≤ 1 ∨ bi.safe = true) → P.has bi →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ crtSnap γ P b crt rtx rv ∗ isBucket bk bi ∗ key ↦*{dk} kb ∗ endKey ↦*{de} eb }}
    (App (App (App (App (Val (crt @!! go.GoType.PointerType concurrentReadTx.ty @!! go!"UnsafeRange")) (Val #bk)) (Val #key)) (Val #endKey)) (Val #limit))
  {{ (keys vals : GoSlice), RET (PairV #keys #vals); crtSnap γ P b crt rtx rv ∗
      key ↦*{dk} kb ∗ endKey ↦*{de} eb ∗ kvsOutRd rtx keys vals (rtRange rv bi kb eb limit) }}

end spec

end EtcdGrove
end Perennial
