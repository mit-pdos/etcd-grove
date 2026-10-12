/-
`checkRange` (`range.go`): the revision check of a range in a transaction.
Lean-first; see `InvRange.lean`, `RangeModel.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvRange

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `checkRange(rv, req)` on a read transaction (the `mvcc.ReadView` whose dynamic type is
`*metricsTxnWrite`, of the committed log `log` at revision `rev`; its first revision is `-1`):
`checkRangeErr`. -/
abbrev txn.checkRange.spec : Prop :=
  ∀ (mw s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64) (req : Loc) (o : OpFull),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
      mvcc.isTxnRead mw s γ log rev ∗ txn.rangeRequestIs req o }}
    (App (App (Val (@! txn.checkRange))
      (Val #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw : GoInterface)))
      (Val #req))
  {{ (err : GoInterface), RET #err; mvcc.isTxnRead mw s γ log rev ∗ txn.checkRangeErr rev o err }}

end spec

end EtcdGrove
end Perennial
