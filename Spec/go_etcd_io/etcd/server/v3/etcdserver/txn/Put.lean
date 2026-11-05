/-
`txn.Put` (put.go). Lean-first (no Rocq counterpart); see `Proof/.../etcdserver/txn/Write.lean`.
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

/-- **`Put(ctx, lg, lessor, kv, p)`**: the lease check first (the lessor's owner `L I`); not found,
`ErrLeaseNotFound`, no transaction (`Pre` back; the caller gives its updates only for a live
lease, which it knows from `L`: so none is left unused); else one write
transaction, begun at the state `σ₀` of the caller's update (`putAU`), its `ErrKeyNotFound` (no
change) or its put committed (`putPend o σ₀`) by the caller's two updates, the hook run once under
the batch lock (`Post`). The caller's pin, if any, is in its `R`.

(Strict M1, 2026-11-05: restated over mvcc's API as `notes/mvcc-api-clients/TxnSpecs.lean`
drafts it, frozen; `notes/mvcc-api-clients/clients-txn.md`.) -/
abbrev txn.Put.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg : Loc) (le kv : GoInterface)
    (γ : MvccName) (p : Loc) (o : OpFull) (q : Qp) (B : BkRef) (P Pre Q Post : IProp GF)
    (f : GoFunc) (L : List w64) (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64)
    (ot : Option Loc) (te : Bool) (R : MvccState → IProp GF),
  {{ pkgInit ∗ mvcc.api.isMvcc kv γ ∗ threadTok ∗ txn.isTxnLessor le (mvccLeases γ) ∗
      lease.lessorUser (mvccLeases γ) L I ∗ txn.putRequestIs p o ∗ mvcc.txnCtx ctx cd ∗
      traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗
      txn.kvBackend γ q B P f ∗ txn.csA P f Pre Q Post ∗
      (if decide (o.leaseID = W64 0 ∨ o.leaseID ∈ L) then txn.putAU γ o L I R
       else iprop(True)) }}
    (App (App (App (App (App (Val (@! txn.Put)) (Val #(GoInterface.ok ctx))) (Val #lg)) (Val #le))
      (Val #kv)) (Val #p))
  {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      threadTok ∗ txn.kvBackend γ q B P f ∗ ⌜trace ≠ null⌝ ∗
      (∃ te' : Bool, traceutil.ownTrace trace te') ∗ ⌜∀ t0, ot = some t0 → te = false → trace = t0⌝ ∗
      ((⌜o.leaseID ≠ W64 0 ∧ o.leaseID ∉ L ∧ resp = null⌝ ∗
          txn.errVarIs go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound err ∗ Pre ∗
          lease.lessorUser (mvccLeases γ) L I) ∨
       ∃ σ₀ : MvccState, ⌜txn.Reach σ₀ ∧ σ₀.pending = none⌝ ∗ Post ∗ R σ₀ ∗
        ((⌜txn.needsPrev o = true ∧ mvcc.findKey o.key (mvcc.stateAfter σ₀.log) = none ∧
              resp = null⌝ ∗
            txn.errVarIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrKeyNotFound err ∗
            lease.lessorUser (mvccLeases γ) L I) ∨
         (⌜err = GoInterface.nil ∧
              (txn.needsPrev o = true → (mvcc.findKey o.key (mvcc.stateAfter σ₀.log)).isSome)⌝ ∗
            txn.putResponseIs resp (W64 (σ₀.log.length : Int))
              (if o.base.prevKV then mvcc.findKey o.key (mvcc.stateAfter σ₀.log) else none) ∗
            txn.respHdrOwn (structFieldRef go_etcd_io.etcd.api.v3.etcdserverpb.PutResponse go!"Header" resp) ∗
            txn.leaseOk L (txn.putLeaseOf o (mvcc.findKey o.key (mvcc.stateAfter σ₀.log))) ∗
            lease.lessorUser (mvccLeases γ) L (mvcc.pendItems σ₀.log (txn.putPend o σ₀))))) }}

end spec

end EtcdGrove
end Perennial
