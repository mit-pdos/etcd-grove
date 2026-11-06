/-
`Txn` (`txn.go`). Lean-first; see `TxnRun.lean`, `InvTxn.lean`, `SoleWriter.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ApiVocab
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvWarn

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

/-- **`Txn(...)` at the sole writer of `log`** (the apply thread), at a context never canceled:
the read transaction at the caller's read update, whose commit the caller gives with the pin
(`σ.log = log`) and `Qr σ`; for a request that writes, once the checks passed, txn turns `Qr σ`
into the write updates by the caller's wand, told that the checks passed (the paths find their
previous key-values, `PathsIgnOk`) (`txnBeginAU`: the begin, with the pin again, then the commit
of the run's changes). Either one of `checkTxn`'s errors (no response, no trace, nothing
written, `Pre`, `Qr σ` back), or the
server's transaction at `log` (`srvRunTxn`), its response with header revision `writeRev log chs`,
the leases still known; a write request's under the batch lock (`Post`) and committed by the
caller's updates (`Qw σ`), a read-only one on the read transaction (`Pre`). No size premise: every
sort's from `Txn.Range`'s `stateOk`, at the read transaction or at the write transaction's pending
state.

(Strict M1, 2026-11-05: restated over mvcc's API as `notes/mvcc-api-clients/TxnSpecs.lean`
drafts it, frozen; `notes/mvcc-api-clients/clients-txn.md`. The wand's `PathsIgnOk`: decided by
the coordinator, 2026-11-06, `clients-txn.md` §8.) -/
abbrev txn.Txn.specSole : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg rt : Loc) (shared : Bool)
    (kv le : GoInterface) (skip : Bool) (γ : MvccName) (log : mvcc.Log) (t : TxnModel) (q : Qp)
    (B : MvccStorage) (P Pre Q Post : IProp GF) (f : GoFunc) (L : List w64) (ot : Option Loc) (te : Bool)
    (Qr Qw : MvccState → IProp GF),
  {{ pkgInit ∗ mvcc.api.isMvcc kv γ ∗ threadTok ∗ txn.kvBackend γ q B P f ∗
      txn.isTxnLessor le (mvccLeases γ) ∗ txn.txnRequestIs rt t ∗ mvcc.txnCtx ctx cd ∗
      traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗ mvcc.neverDone cd ∗
      txn.leasesKnown L (mvcc.stateAfter log) ∗
      lease.lessorUser (mvccLeases γ) L (mvcc.leaseItemsOf (mvcc.stateAfter log)) ∗
      ⌜txn.TxnPreA log t⌝ ∗
      txn.csA P f Pre Q Post ∗
      txn.readAU γ (fun σ => iprop(⌜σ.log = log⌝ ∗ Qr σ)) ∗
      (if txn.txnReadonly t then iprop(True)
       else iprop(∀ σ : MvccState,
         ⌜txn.PathsIgnOk (mvcc.stateAfter log) (t.branch (txn.txnOk (mvcc.stateAfter log) t))⌝ -∗
         Qr σ -∗ txn.txnBeginAU γ log t Qw)) }}
    (App (App (App (App (App (App (App (Val (@! txn.Txn)) (Val #(GoInterface.ok ctx))) (Val #lg))
      (Val #rt)) (Val #shared)) (Val #kv)) (Val #le)) (Val #skip))
  {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      threadTok ∗ txn.kvBackend γ q B P f ∗
      ∃ σr : MvccState, ⌜σr.log = log ∧ txn.Reach σr⌝ ∗
      ((⌜resp = null ∧ trace = null ∧ err ≠ GoInterface.nil ∧
            (txn.txnLeased t → ¬ (txn.PathsIgnOk (mvcc.stateAfter log)
              (t.branch (txn.txnOk (mvcc.stateAfter log) t)) ∧ txn.PathsLeaseOk (mvcc.stateAfter log)
              L (t.branch (txn.txnOk (mvcc.stateAfter log) t))))⌝ ∗ txn.checkErrIs err ∗
          Pre ∗ Qr σr ∗
          lease.lessorUser (mvccLeases γ) L (mvcc.leaseItemsOf (mvcc.stateAfter log)) ∗
          (∃ (t' : Loc) (te' : Bool), traceutil.ownTrace t' te' ∗
            ⌜∀ t0, ot = some t0 → te = false → t' = t0⌝)) ∨
       (⌜err = GoInterface.nil ∧ trace ≠ null ∧
          (txn.txnReadonly t = true → txn.txnChs log t = []) ∧
          txn.PathsIgnOk (mvcc.stateAfter log) (t.branch (txn.txnOk (mvcc.stateAfter log) t)) ∧
          txn.PathsLeaseOk (mvcc.stateAfter log) L (t.branch (txn.txnOk (mvcc.stateAfter log) t))⌝ ∗
        (∃ te' : Bool, traceutil.ownTrace trace te') ∗ ⌜∀ t0, ot = some t0 → te = false → trace = t0⌝ ∗
        txn.txnResponseIs skip resp
          (W64 (mvcc.writeRev log (txn.txnChs log t) : Int)) t
          (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).1
          (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.2 ∗
        txn.respHdrOwn (structFieldRef etcdserverpb.TxnResponse go!"Header" resp) ∗
        txn.leasesKnown L (mvcc.stateAfter (mvcc.commitLog log (txn.txnChs log t))) ∗
        lease.lessorUser (mvccLeases γ) L
          (mvcc.leaseItemsOf (mvcc.stateAfter (mvcc.commitLog log (txn.txnChs log t)))) ∗
        (if txn.txnReadonly t then iprop(Pre ∗ Qr σr)
         else iprop(Post ∗ ∃ σw : MvccState, ⌜σw.log = log⌝ ∗ Qw σw)))) }}

/-- **`Txn(...)` at a reader** (the server's read-only transactions): a read-only request, the
read transaction at the state `σ` of the caller's update (`Q σ`), any context. One of `checkTxn`'s
errors; or the server's run at `σ.log`, header revision `σ.rev`; or the context done during a
range: `fmt.Errorf`'s error, the response partly filled.

(Strict M1, 2026-11-05: restated over mvcc's API as `notes/mvcc-api-clients/TxnSpecs.lean`
drafts it, frozen; `notes/mvcc-api-clients/clients-txn.md`.) -/
abbrev txn.Txn.specRead : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg rt : Loc) (shared : Bool)
    (kv le : GoInterface) (skip : Bool) (γ : MvccName) (t : TxnModel) (ot : Option Loc) (te : Bool)
    (Q : MvccState → IProp GF),
  {{ pkgInit ∗ mvcc.api.isMvcc kv γ ∗ threadTok ∗ txn.isTxnLessor le (mvccLeases γ) ∗
      txn.txnRequestIs rt t ∗ mvcc.txnCtx ctx cd ∗ traceutil.ctxTraceIs ctx ot ∗
      traceutil.ownTraceOpt ot te ∗ ⌜lg ≠ null ∧ txn.txnReadonly t = true ∧ txn.txnGetsOk t⌝ ∗
      txn.readAU γ Q }}
    (App (App (App (App (App (App (App (Val (@! txn.Txn)) (Val #(GoInterface.ok ctx))) (Val #lg))
      (Val #rt)) (Val #shared)) (Val #kv)) (Val #le)) (Val #skip))
  {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      threadTok ∗ ∃ σ : MvccState, Q σ ∗ ⌜txn.Reach σ⌝ ∗
        ((⌜resp = null ∧ trace = null ∧ err ≠ GoInterface.nil⌝ ∗ txn.checkErrIs err ∗
          (∃ (t' : Loc) (te' : Bool), traceutil.ownTrace t' te' ∗
            ⌜∀ t0, ot = some t0 → te = false → t' = t0⌝)) ∨
         (⌜err = GoInterface.nil ∧ trace ≠ null⌝ ∗
           (∃ te' : Bool, traceutil.ownTrace trace te') ∗ ⌜∀ t0, ot = some t0 → te = false → trace = t0⌝ ∗
           txn.txnResponseIs skip resp (W64 (σ.rev : Int)) t
             (txn.srvRunTxn (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) t).1
             (txn.srvRunTxn (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) t).2.2 ∗
           txn.respHdrOwn (structFieldRef etcdserverpb.TxnResponse go!"Header" resp)) ∨
         (⌜trace ≠ null⌝ ∗ (∃ te' : Bool, traceutil.ownTrace trace te') ∗
           ⌜∀ t0, ot = some t0 → te = false → trace = t0⌝ ∗
           mvcc.ctxErrorf err ∗ txn.roTxnRespRd resp ∗
           txn.respHdrOwn (structFieldRef etcdserverpb.TxnResponse go!"Header" resp))) }}

/-- **`Txn`'s spec**: at the sole writer (`specSole`, the apply thread) and at a reader
(`specRead`, the server's read-only transactions); one function's two triples, by caller. -/

abbrev txn.Txn.spec : Prop := txn.Txn.specSole (GF := GF) ∧ txn.Txn.specRead (GF := GF)

end spec

end EtcdGrove
end Perennial
