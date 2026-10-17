/-
`txWriteBuffer.writeback` (`tx_buffer.go`). `txw.writeback(txr)`: each bucket of the write buffer merged into the read buffer's
(`writebackR`: canonical, newest wins), the write buffer reset (`writebackW`), the version
incremented. It needs only the buckets written by `putSeq` alone sorted (`WBuf.WfR` with every
bucket allowed to repeat a key: since etcd#22298 both branches `dedupe` a bucket written by `put`;
before it the code assumed no duplicate keys where the read buffer had the bucket, see
`issues/etcd-backend-duplicate-put-stale-read.md`) and the read buffer canonical.
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

/-- `txw.writeback(txr)`: each bucket of the write buffer merged into the read buffer's
(`writebackR`: canonical, newest wins), the write buffer reset (`writebackW`), the version
incremented. A bucket written by `put` may repeat a key in either branch, which `dedupe`
canonicalizes before the merge (etcd#22298; before it, only for a bucket the read buffer did not
have: `writeback.spec_old` in the proof's file); a bucket written by `putSeq` alone is sorted
(`writeback` neither sorts nor deduplicates it); the read buffer canonical. -/
abbrev backend.txWriteBuffer.writeback.spec : Prop :=
  ∀ (txw : Loc) (W : WBuf) (txr : Loc) (R : RBuf),
  W.WfR (fun _ => True) → R.Wf → (∀ id, (bkOf R.bks id).length + (bkOf W.bks id).length < bufBound) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ ownWB txw W ∗ ownRB txr R }}
    (App (Val (txw @!! go.GoType.PointerType txWriteBuffer.ty @!! go!"writeback")) (Val #txr))
  {{ RET #(); ownWB txw (writebackW W R) ∗ ownRB txr (writebackR W R) }}

end spec

end EtcdGrove
end Perennial
