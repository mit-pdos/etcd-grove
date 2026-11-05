/-
`txn.checkAndGetPrevKV` (put.go). Lean-first (no Rocq counterpart); see `Proof/.../etcdserver/txn/Write.lean`.
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

/-- `checkAndGetPrevKV(trace, txnWrite, p)` at a transaction of either kind: `getPrevKV`'s answer,
or `ErrKeyNotFound` when an ignore flag needs a previous key-value the state has not.

(Strict M1, 2026-11-05: over mvcc's API as `notes/mvcc-api-clients/TxnSpecs.lean` drafts it.)
(The trace given back as `∃ te', ownTrace trace te'`, decided by the coordinator, 2026-11-05:
`getPrevKV` reads in `Trace.StepWithFunction`, which gives back `∃ e'`.) -/

abbrev txn.checkAndGetPrevKV.spec : Prop :=
  ∀ (t : GoInterface) (γ : MvccName) (trace : Loc) (te : Bool) (k : MTxn) (p : Loc) (o : OpFull),
  {{ pkgInit ∗ ⌜trace ≠ null⌝ ∗ mvcc.api.mvccTxn t γ trace k ∗ traceutil.ownTrace trace te ∗
      ⌜txn.Reach k.state⌝ ∗ txn.putRequestIs p o }}
    (App (App (App (Val (@! txn.checkAndGetPrevKV)) (Val #trace)) (Val #t)) (Val #p))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err); mvcc.api.mvccTxn t γ trace k ∗
      (∃ te' : Bool, traceutil.ownTrace trace te') ∗
      ((⌜err = GoInterface.nil⌝ ∗
          ⌜txn.needsPrev o = true → (mvcc.findKey o.key (txn.mstate k)).isSome⌝ ∗
          if txn.readsPrev o then txn.prevKvIs r (txn.mstate k) o.key else ⌜r = null⌝) ∨
       (⌜txn.needsPrev o = true ∧ mvcc.findKey o.key (txn.mstate k) = none ∧ r = null⌝ ∗
          txn.errVarIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrKeyNotFound err)) }}

end spec

end EtcdGrove
end Perennial
