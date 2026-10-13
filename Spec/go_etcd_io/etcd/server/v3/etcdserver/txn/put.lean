/-
`txn.put` (put.go). Lean-first (no Rocq counterpart); see `Proof/.../etcdserver/txn/Write.lean`.
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

/-- `put(ctx, txnWrite, p, prevKV)` at a write transaction (committed log `ilog`, pending
changes `pend`), `prevKV` being `getPrevKV`'s answer there, the previous key-value there if the
put needs it, and the lease it writes one it may attach: the put's change (`putChangeOf`: the
request's value and lease, or the previous ones) pending, and the response at the pending
revision with the previous key-value if requested (`PrevKv`: the answer's own `*KeyValue`, made
read-only). -/
abbrev txn.put.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (mw s : Loc)
    (γ : mvcc.StoreNames) (ilog : mvcc.Log) (pend : List mvcc.Change) (puts deletes putSize : w64)
    (p : Loc) (o : OpFull) (prev : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ mvcc.txnCtx ctx cd ∗
      mvcc.isTxnWrite mw s γ ilog pend puts deletes putSize ∗ txn.putRequestIs p o ∗
      (if txn.readsPrev o then txn.prevKvIs prev (txn.pendState ilog pend) o.key
        else ⌜prev = null⌝) ∗
      ⌜txn.needsPrev o = true → (mvcc.findKey o.key (txn.pendState ilog pend)).isSome⌝ ∗
      txn.leaseOk γ.leases (txn.putLeaseOf o (mvcc.findKey o.key (txn.pendState ilog pend))) ∗
      ⌜pend.length + 1 < 2 ^ 63⌝ }}
    (App (App (App (App (Val (@! txn.put)) (Val #(GoInterface.ok ctx))) (Val #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw : GoInterface))) (Val #p))
      (Val #prev))
  {{ (resp : Loc), RET #resp;
      (∃ puts' putSize' : w64, mvcc.isTxnWrite mw s γ ilog
        (pend ++ [txn.putChangeOf o (mvcc.findKey o.key (txn.pendState ilog pend))]) puts' deletes
        putSize') ∗
      txn.putResponseIs resp (W64 (ilog.length : Int))
        (if o.base.prevKV then mvcc.findKey o.key (txn.pendState ilog pend) else none) ∗
      txn.respHdrOwn (structFieldRef go_etcd_io.etcd.api.v3.etcdserverpb.PutResponse go!"Header" resp) }}

end spec

end EtcdGrove
end Perennial
