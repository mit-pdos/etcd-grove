/-
`txWriteBuffer.writeback` (`tx_buffer.go`). `txw.writeback(txr)`: each bucket of the write buffer merged into the read buffer's
(`writebackR`: canonical, newest wins), the write buffer reset (`writebackW`), the version
incremented. It needs the write buffer's buckets as `put`/`putSeq` keep them (`WBuf.Wf`: the
code assumes no duplicate keys, see `issues/etcd-backend-duplicate-put-stale-read.md`) and the
read buffer canonical.
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
incremented. It needs the write buffer's buckets as `put`/`putSeq` keep them (`WBuf.Wf`: the
code assumes no duplicate keys, see `issues/etcd-backend-duplicate-put-stale-read.md`) and the
read buffer canonical. -/
abbrev backend.txWriteBuffer.writeback.spec : Prop :=
  ∀ (txw : Loc) (W : WBuf) (txr : Loc) (R : RBuf),
  W.Wf → R.Wf → (∀ id, (bkOf R.bks id).length + (bkOf W.bks id).length < bufBound) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ ownWB txw W ∗ ownRB txr R }}
    (App (Val (txw @!! go.GoType.PointerType txWriteBuffer.ty @!! go!"writeback")) (Val #txr))
  {{ RET #(); ownWB txw (writebackW W R) ∗ ownRB txr (writebackR W R) }}

end spec

end EtcdGrove
end Perennial
