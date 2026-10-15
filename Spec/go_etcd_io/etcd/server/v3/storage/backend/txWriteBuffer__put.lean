/-
`txWriteBuffer.put` (`tx_buffer.go`). `txw.put(bucket, k, v)`: the bucket flagged as written by `put`, the entry added.
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

/-- `txw.put(bucket, k, v)`: the bucket flagged as written by `put`, the entry added. -/
abbrev backend.txWriteBuffer.put.spec : Prop :=
  ∀ (txw : Loc) (W : WBuf) (b : GoInterface) (bi : BucketInfo) (k v : GoSlice) (kb vb : GoString),
  (bkOf W.bks bi.id).length < bufBound →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ ownWB txw W ∗ isBucket b bi ∗ k ↦*□ kb ∗ v ↦*□ vb }}
    (App (App (App (Val (txw @!! go.GoType.PointerType txWriteBuffer.ty @!! go!"put")) (Val #b)) (Val #k)) (Val #v))
  {{ RET #(); ownWB txw (W.put bi.id (kb, vb)) }}

end spec

end EtcdGrove
end Perennial
