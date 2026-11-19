/-
`txn.put` (put.go). Lean-first (no Rocq counterpart); see `Proof/.../etcdserver/txn/Write.lean`.
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
open mvcc.api (MvccState MTxn MvccReachable MvccName MvccStorage mvccN mvccLeases)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn

/-- `put(ctx, txnWrite, p, prevKV)` at a write transaction begun at `σ` with `pend` pending.

(Strict M1, 2026-11-05: restated over mvcc's API as `notes/mvcc-api-clients/TxnSpecs.lean`
drafts it, frozen; `notes/mvcc-api-clients/clients-txn.md`. Auth-lease S4 item 7b, 2026-11-17: in the
lessor window `w`, the put moving the items toward its target.) -/
abbrev txn.put.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (tw : GoInterface) (γ : MvccName)
    (trace : Loc) (te : Bool) (σ : MvccState) (pend : List mvcc.Change) (p : Loc) (o : OpFull)
    (prev : Loc) (L : List w64) (w : Option lease.LWin),
  {{ pkgInit ∗ mvcc.txnCtx ctx cd ∗ traceutil.ctxTraceIs ctx (some trace) ∗
      mvcc.api.mvccTxn tw γ trace (.write σ pend) ∗ traceutil.ownTrace trace te ∗
      txn.putRequestIs p o ∗
      (if txn.readsPrev o then txn.prevKvIs prev (txn.pendState σ.log pend) o.key
        else ⌜prev = null⌝) ∗
      ⌜txn.needsPrev o = true → (mvcc.findKey o.key (txn.pendState σ.log pend)).isSome⌝ ∗
      txn.leaseOk L (txn.putLeaseOf o (mvcc.findKey o.key (txn.pendState σ.log pend))) ∗
      lease.leaseOwnW (mvccLeases γ) L (mvcc.pendItems σ.log pend) w ∗
      ⌜lease.winMove w (mvcc.pendItems σ.log pend) (mvcc.pendItems σ.log
        (pend ++ [txn.putChangeOf o (mvcc.findKey o.key (txn.pendState σ.log pend))]))⌝ ∗
      ⌜o.key.length ≤ etcdKeyMax ∧ (o.ignoreValue = false → o.val.length ≤ etcdKeyMax)⌝ }}
    (App (App (App (App (Val (@! txn.put)) (Val #(GoInterface.ok ctx))) (Val #tw)) (Val #p))
      (Val #prev))
  {{ (resp : Loc), RET #resp;
      mvcc.api.mvccTxn tw γ trace
        (.write σ (pend ++ [txn.putChangeOf o (mvcc.findKey o.key (txn.pendState σ.log pend))])) ∗
      traceutil.ownTrace trace te ∗
      txn.putResponseIs resp (W64 (σ.log.length : Int))
        (if o.base.prevKV then mvcc.findKey o.key (txn.pendState σ.log pend) else none) ∗
      txn.respHdrOwn (structFieldRef go_etcd_io.etcd.api.v3.etcdserverpb.PutResponse go!"Header" resp) ∗
      lease.leaseOwnW (mvccLeases γ) L (mvcc.pendItems σ.log
        (pend ++ [txn.putChangeOf o (mvcc.findKey o.key (txn.pendState σ.log pend))])) w }}

end spec

end EtcdGrove
end Perennial
