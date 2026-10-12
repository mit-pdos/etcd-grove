/-
`txn.checkPut` (put.go). Lean-first (no Rocq counterpart); see `Proof/.../etcdserver/txn/Write.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Write

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `checkPut(trace, txnWrite, lessor, p)` (`Txn`'s check of a put at its read transaction):
`nil` if the lease is none or found (`leaseOk`) and the previous key-value is there if needed;
else `lease.ErrLeaseNotFound` (checked first) or `errors.ErrKeyNotFound`. -/
abbrev txn.checkPut.spec : Prop :=
  ∀ (trace mw s : Loc) (γ : mvcc.StoreNames) (kind : mvcc.TxnKind) (le : GoInterface) (γl : GName)
    (p : Loc) (o : OpFull),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ ⌜trace ≠ null⌝ ∗ mvcc.isTxn mw s γ kind ∗
      txn.putRequestIs p o ∗ txn.isTxnLessor le γl }}
    (App (App (App (App (Val (@! txn.checkPut)) (Val #trace)) (Val #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw : GoInterface))) (Val #le)) (Val #p))
  {{ (err : GoInterface), RET #err; mvcc.isTxn mw s γ kind ∗
      ((⌜err = GoInterface.nil ∧
          (txn.needsPrev o = true → (mvcc.findKey o.key (txn.kindState kind)).isSome)⌝ ∗
          txn.leaseOk γl o.leaseID) ∨
       (⌜o.leaseID ≠ W64 0⌝ ∗ txn.errVarIs go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound err) ∨
       (⌜txn.needsPrev o = true ∧ mvcc.findKey o.key (txn.kindState kind) = none⌝ ∗
          txn.errVarIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrKeyNotFound err)) }}

end spec

end EtcdGrove
end Perennial
