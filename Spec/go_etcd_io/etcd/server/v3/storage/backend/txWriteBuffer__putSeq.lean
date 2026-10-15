/-
`txWriteBuffer.putSeq` (`tx_buffer.go`). `txw.putSeq(bucket, k, v)`, `k` above the bucket's buffered keys (its `verify.Verify`
check holds): the entry added.
Lean-first (no Rocq counterpart); see `InvBuffer.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBuffer
public import Spec.go_etcd_io.etcd.client.pkg.v3.verify.Verify

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

/-- `txw.putSeq(bucket, k, v)`, `k` above the bucket's buffered keys (its `verify.Verify`
check holds): the entry added. -/
abbrev backend.txWriteBuffer.putSeq.spec : Prop :=
  ∀ (txw : Loc) (W : WBuf) (b : GoInterface) (bi : BucketInfo) (k v : GoSlice) (kb vb : GoString),
  (bkOf W.bks bi.id).length < bufBound → (∀ e ∈ bkOf W.bks bi.id, strLt e.1 kb) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ ownWB txw W ∗ isBucket b bi ∗ k ↦*□ kb ∗ v ↦*□ vb }}
    (App (App (App (Val (txw @!! go.GoType.PointerType txWriteBuffer.ty @!! go!"putSeq")) (Val #b)) (Val #k)) (Val #v))
  {{ RET #(); ownWB txw (W.putSeq bi.id (kb, vb)) }}

end spec

end EtcdGrove
end Perennial
