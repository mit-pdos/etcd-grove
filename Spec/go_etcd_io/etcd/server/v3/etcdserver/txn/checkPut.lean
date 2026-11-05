/-
`txn.checkPut` (put.go). Lean-first (no Rocq counterpart); see `Proof/.../etcdserver/txn/Write.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ApiVocab

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.storage.mvcc
open mvcc.api (MvccState MTxn MvccReachable MvccName BkRef mvccN mvccLeases)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn

/-- `checkPut(trace, txnWrite, lessor, p)` at a transaction of either kind: the lease check
(`ErrLeaseNotFound`), then `checkAndGetPrevKV`'s (`ErrKeyNotFound`).

(Strict M1, 2026-11-05: over mvcc's API as `notes/mvcc-api-clients/TxnSpecs.lean` drafts it.)
(The trace given back as `∃ te', ownTrace trace te'`, decided by the coordinator, 2026-11-05:
`getPrevKV` reads in `Trace.StepWithFunction`, which gives back `∃ e'`.) -/

abbrev txn.checkPut.spec : Prop :=
  ∀ (t : GoInterface) (γ : MvccName) (trace : Loc) (te : Bool) (k : MTxn) (le : GoInterface)
    (γl : GName) (p : Loc) (o : OpFull) (L : List w64)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64),
  {{ pkgInit ∗ ⌜trace ≠ null⌝ ∗ mvcc.api.mvccTxn t γ trace k ∗ traceutil.ownTrace trace te ∗
      ⌜txn.Reach k.state⌝ ∗ txn.putRequestIs p o ∗ txn.isTxnLessor le γl ∗
      lease.lessorUser γl L I }}
    (App (App (App (App (Val (@! txn.checkPut)) (Val #trace)) (Val #t)) (Val #le)) (Val #p))
  {{ (err : GoInterface), RET #err; mvcc.api.mvccTxn t γ trace k ∗
      (∃ te' : Bool, traceutil.ownTrace trace te') ∗
      lease.lessorUser γl L I ∗
      ((⌜err = GoInterface.nil ∧
          (txn.needsPrev o = true → (mvcc.findKey o.key (txn.mstate k)).isSome)⌝ ∗
          txn.leaseOk L o.leaseID) ∨
       (⌜o.leaseID ≠ W64 0 ∧ o.leaseID ∉ L⌝ ∗
          txn.errVarIs go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound err) ∨
       (⌜txn.needsPrev o = true ∧ mvcc.findKey o.key (txn.mstate k) = none⌝ ∗
          txn.errVarIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrKeyNotFound err)) }}

end spec

end EtcdGrove
end Perennial
