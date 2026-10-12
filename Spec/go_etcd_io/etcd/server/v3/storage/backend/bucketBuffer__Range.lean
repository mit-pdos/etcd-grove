/-
`bucketBuffer.Range` (`tx_buffer.go`). `bb.Range(key, endKey, limit)` of a sorted buffer: `bbRange` of its entries, as fresh
slices of its entries' key and value slices; the buffer unchanged (any fraction).
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

/-- `bb.Range(key, endKey, limit)` of a sorted buffer: `bbRange` of its entries, as fresh
slices of its entries' key and value slices; the buffer unchanged (any fraction). -/
abbrev backend.bucketBuffer.Range.spec : Prop :=
  ∀ (bb : Loc) (dq : DFrac) (p : BBPhys) (es : List Ent) (key endKey : GoSlice)
    (kb eb : GoString) (dk de : DFrac) (limit : w64),
  entsSorted es →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ bbAt bb dq p es ∗ key ↦*{dk} kb ∗ endKey ↦*{de} eb }}
    (App (App (App (Val (bb @!! go.GoType.PointerType bucketBuffer.ty @!! go!"Range")) (Val #key)) (Val #endKey)) (Val #limit))
  {{ (keys vals : GoSlice), RET (PairV #keys #vals); bbAt bb dq p es ∗ key ↦*{dk} kb ∗
      endKey ↦*{de} eb ∗ kvsOut keys vals (bbRange es kb eb limit) }}

end spec

end EtcdGrove
end Perennial
