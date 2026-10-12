/-
`txn.checkAndGetPrevKV` (put.go). Lean-first (no Rocq counterpart); see `Proof/.../etcdserver/txn/Write.lean`.
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

/-- `checkAndGetPrevKV(trace, txnWrite, p)`: `getPrevKV`'s answer, or, if the put needs the
previous key-value (`IgnoreValue` or `IgnoreLease`) and the key has none,
`errors.ErrKeyNotFound`. -/
abbrev txn.checkAndGetPrevKV.spec : Prop :=
  ∀ (trace mw s : Loc) (γ : mvcc.StoreNames) (kind : mvcc.TxnKind) (p : Loc) (o : OpFull),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ ⌜trace ≠ null⌝ ∗ mvcc.isTxn mw s γ kind ∗
      txn.putRequestIs p o }}
    (App (App (App (Val (@! txn.checkAndGetPrevKV)) (Val #trace)) (Val #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw : GoInterface))) (Val #p))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err); mvcc.isTxn mw s γ kind ∗
      ((⌜err = GoInterface.nil⌝ ∗
          ⌜txn.needsPrev o = true → (mvcc.findKey o.key (txn.kindState kind)).isSome⌝ ∗
          if txn.readsPrev o then txn.prevKvIs r (txn.kindState kind) o.key else ⌜r = null⌝) ∨
       (⌜txn.needsPrev o = true ∧ mvcc.findKey o.key (txn.kindState kind) = none ∧ r = null⌝ ∗
          txn.errVarIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrKeyNotFound err)) }}

end spec

end EtcdGrove
end Perennial
