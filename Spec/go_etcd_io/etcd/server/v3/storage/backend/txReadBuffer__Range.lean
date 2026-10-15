/-
`txReadBuffer.Range` (`tx_buffer.go`). `txr.Range(bucket, key, endKey, limit)`: the bucket's buffer's `Range` (nothing if the
bucket has none); the read buffer unchanged (any fraction).
Lean-first (no Rocq counterpart); see `InvBuffer.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBuffer

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

/-- `txr.Range(bucket, key, endKey, limit)`: the bucket's buffer's `Range` (nothing if the
bucket has none); the read buffer unchanged (any fraction). -/
abbrev backend.txReadBuffer.Range.spec : Prop :=
  ∀ (txr : Loc) (dq : DFrac) (m : GoMap) (P : BksPhys) (R : RBuf) (b : GoInterface)
    (bi : BucketInfo) (key endKey : GoSlice) (kb eb : GoString) (dk de : DFrac) (limit : w64),
  R.Wf →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ rbAt txr dq m P R ∗ isBucket b bi ∗ key ↦*{dk} kb ∗ endKey ↦*{de} eb }}
    (App (App (App (App (Val (txr @!! go.GoType.PointerType txReadBuffer.ty @!! go!"Range")) (Val #b)) (Val #key)) (Val #endKey)) (Val #limit))
  {{ (keys vals : GoSlice), RET (PairV #keys #vals); rbAt txr dq m P R ∗ key ↦*{dk} kb ∗
      endKey ↦*{de} eb ∗ kvsOut keys vals (bbRange (bkOf R.bks bi.id) kb eb limit) }}

end spec

end EtcdGrove
end Perennial
