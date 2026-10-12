/-
`txn.getPrevKV` (put.go). Lean-first (no Rocq counterpart); see `Proof/.../etcdserver/txn/Write.lean`.
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

/-- `getPrevKV(trace, txnWrite, p)` of a transaction (a read or a write one: `checkPut` reads at
`Txn`'s read transaction, `Put` at its write transaction): if the put reads the previous
key-value (`IgnoreValue`, `IgnoreLease` or `PrevKv`), the transaction's range read of the key at
`context.TODO()`, which does not fail: the key's key-value at the state the transaction reads,
if it has one (`prevKvIs`); else `nil`. -/
abbrev txn.getPrevKV.spec : Prop :=
  ∀ (trace mw s : Loc) (γ : mvcc.StoreNames) (kind : mvcc.TxnKind) (p : Loc) (o : OpFull),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ ⌜trace ≠ null⌝ ∗ mvcc.isTxn mw s γ kind ∗
      txn.putRequestIs p o }}
    (App (App (App (Val (@! txn.getPrevKV)) (Val #trace)) (Val #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw : GoInterface))) (Val #p))
  {{ (r : Loc), RET (PairV #r #(GoInterface.nil)); mvcc.isTxn mw s γ kind ∗
      if txn.readsPrev o then txn.prevKvIs r (txn.kindState kind) o.key else ⌜r = null⌝ }}

end spec

end EtcdGrove
end Perennial
