/-
`txn.DeleteRange` (delete.go). Lean-first (no Rocq counterpart); see `Proof/.../etcdserver/txn/Write.lean`.
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

/-- **`DeleteRange(ctx, lg, kv, dr)`**: one write transaction, begun at the state `σ₀` of the
caller's update (`delAU`), the range's keys at `σ₀` deleted, committed by the caller's two
updates (`delPend o σ₀ true`), the response; or, with `PrevKv`, the range read's context error
(not at a context never canceled), nothing deleted (`delPend o σ₀ false = []`). `Post` either way.

(Strict M1, 2026-11-05: restated over mvcc's API as `notes/mvcc-api-clients/TxnSpecs.lean`
drafts it, frozen; `notes/mvcc-api-clients/clients-txn.md`.) -/
abbrev txn.DeleteRange.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (nd : Bool) (lg : Loc)
    (kv : GoInterface) (γ : MvccName) (dr : Loc) (o : OpFull) (q : Qp) (B : MvccStorage)
    (P Pre Q Post : IProp GF) (f : GoFunc) (ot : Option Loc) (te : Bool) (L : List w64)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (R : MvccState → Bool → IProp GF),
  {{ pkgInit ∗ mvcc.api.isMvcc kv γ ∗ mvcc.api.mvccReaders γ 1 ∗
      txn.deleteRangeRequestIs dr o ∗
      lease.leaseOwn (mvccLeases γ) L I ∗ mvcc.txnCtx ctx cd ∗ traceutil.ctxTraceIs ctx ot ∗
      traceutil.ownTraceOpt ot te ∗ (if nd then mvcc.neverDone cd else iprop(True)) ∗
      txn.kvBackend γ q B P f ∗ txn.csA P f Pre Q Post ∗ txn.delAU γ o I R }}
    (App (App (App (App (Val (@! txn.DeleteRange)) (Val #(GoInterface.ok ctx))) (Val #lg))
      (Val #kv)) (Val #dr))
  {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      mvcc.api.mvccReaders γ 1 ∗ txn.kvBackend γ q B P f ∗ ⌜trace ≠ null⌝ ∗ Post ∗
      (∃ te' : Bool, traceutil.ownTrace trace te') ∗ ⌜∀ t0, ot = some t0 → te = false → trace = t0⌝ ∗
      ∃ σ₀ : MvccState, ⌜txn.Reach σ₀ ∧ σ₀.pending = none⌝ ∗
        ((⌜err = GoInterface.nil⌝ ∗ R σ₀ true ∗
            txn.deleteRangeResponseIs resp
              (W64 ((mvcc.writeRev σ₀.log (txn.delChanges (mvcc.stateAfter σ₀.log) o) : Nat) : Int))
              (rangeIn (mvcc.stateAfter σ₀.log) o).length
              (if o.base.prevKV then rangeIn (mvcc.stateAfter σ₀.log) o else []) ∗
            txn.respHdrOwn (structFieldRef go_etcd_io.etcd.api.v3.etcdserverpb.DeleteRangeResponse go!"Header" resp) ∗
            lease.leaseOwn (mvccLeases γ) L
              (mvcc.pendItems σ₀.log (txn.delChanges (mvcc.stateAfter σ₀.log) o))) ∨
         (⌜err ≠ GoInterface.nil ∧ o.base.prevKV = true ∧ resp = null ∧ nd = false⌝ ∗ R σ₀ false ∗
            lease.leaseOwn (mvccLeases γ) L I)) }}

end spec

end EtcdGrove
end Perennial
