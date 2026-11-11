/-
The results of the server's txn package (`server/v3/etcdserver/txn`), restated at top level, with
the trust base of each printed in the build log (`#print axioms`). Each unit's results are in a
section of their own, in unit order.

Unit 0 (translation and scaffolding) proved no function of the package; its `Link.lean` linked
the trust-boundary axioms. Unit 1: `Put` and `DeleteRange` (`put.go`, `delete.go`). Unit 2: the
range (`range.go`). Unit 3: the transaction (`txn.go`), `txn_runTxn`.

**Over mvcc's API** (strict M1, 2026-11-05; this file restated at the `origin/lean` merge,
2026-11-06): the specs take the store as `mvcc.api.isMvcc kv γ` and the caller's updates of the
store's abstract state (`txn.readAU`, `txnBeginAU`, `putAU`, `delAU`), which pin the log a
transaction finds; the sole writer's resources over mvcc's internals (`soleWriter`, `kvWriter`,
`idxCert`) are gone, and with them the results stated over them (`put_soleWriter`,
`deleteRange_soleWriter`, `range_soleWriter`, `count_result`). `txn_readonly_no_revision` and
`txn_check_error_no_write` are now part of `Txn.specSole` itself (`txnReadonly t = true →
txnChs log t = []`; the error disjunct gives `Pre` and the caller's `Qr` back, nothing committed).
The post-lock hook is the API's critical-section contract `txn.csA P f Pre Q Post` with the store's
backend at the hook `f` (`txn.kvBackend γ q B P f`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Link
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.RangeLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.SoleWriter
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.HistoryLaws

@[expose] public section

-- `#print axioms` prints the axioms by their full names: shortening each name to the
-- shortest unambiguous one in this environment took most of this module's build (25s of
-- 31s for the server's `txn/Results.lean`).
set_option pp.fullNames true

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace txn

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.storage.mvcc
  go_etcd_io.etcd.api.v3
open mvcc.api (MvccState MvccName MvccStorage mvccLeases)

/-! ## Unit 1: `Put` and `DeleteRange` (`put.go`, `delete.go`)

Every function of `put.go` and `delete.go` has a `Spec`/`Proof` pair and a linked result
(`Link.lean`). `Put` and `DeleteRange` open one write transaction at the caller's update.

* **`Put` is the client's put** (`put_putKv`): with the lease found (or none) and, for an ignore
  flag, the previous key-value there, the transaction commits the one change `putChangeOf o pv` at
  the state `σ₀` it found, whose state is the client model's `applyTxnOp` of `putTxnOp o`; the
  response's revision is the new one, its `PrevKv` the previous key-value iff `PrevKv` asked. Else
  `lease.ErrLeaseNotFound` (no transaction) or `errors.ErrKeyNotFound` (nothing committed).
* **`DeleteRange` is the client's delete** (`deleteRange_filter`): the keys of the request's range
  in `σ₀`'s state deleted (`delChanges`), committed as one revision if any; or, with `PrevKv`, the
  range read's context error (the caller's context done): nothing deleted.
-/

section unit1
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

/-- **`Put` is the client's put** (`Spec/go_etcd_io/etcd/server/v3/etcdserver/txn/Put.lean`). -/
theorem put_putKv : Put.spec (GF := GF) (hG := hG) := wp_Put

/-- **`DeleteRange` is the client's delete**
(`Spec/go_etcd_io/etcd/server/v3/etcdserver/txn/DeleteRange.lean`). -/
theorem deleteRange_filter : DeleteRange.spec (GF := GF) (hG := hG) := wp_DeleteRange

/-- `put(ctx, txnWrite, p, prevKV)` (`Txn`'s put, in a write transaction). -/
theorem put_put : put.spec (GF := GF) (hG := hG) := wp_put

/-- `deleteRange(ctx, txnWrite, dr)` (`Txn`'s delete, in a write transaction). -/
theorem deleteRange_deleteRange : deleteRange.spec (GF := GF) (hG := hG) := wp_deleteRange

/-- `checkPut(trace, txnRead, lessor, p)` (`Txn`'s check of a put, at its read transaction). -/
theorem put_checkPut : checkPut.spec (GF := GF) (hG := hG) := wp_checkPut

end unit1

#print axioms put_putKv
#print axioms deleteRange_filter
#print axioms put_put
#print axioms deleteRange_deleteRange
#print axioms put_checkPut

/-! ## Unit 2: the range (`range.go`)

Every function of `range.go` has a `Spec`/`Proof` pair and a linked result (`Link.lean`).

* **`Range` in the client's terms** (`range_rangeSel`): `rangeKvsOk` of the client model's
  `rangeSel` at the state the read found, unless the sort is cut early
  (`issues/etcd-range-sort-none-limit.md`).
-/

section unit2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **`Range` in the client's terms**: `Range`'s spec (`txn.Range.spec`) with the success case
stated over the client model's selection (`rangeResultClient`: `rangeKvsOk` of `rangeSel` of the
state read, up to a fast keys-only read's zero lease), for a request whose sort is not cut early
(`cutEarly`, `issues/etcd-range-sort-none-limit.md`). -/
theorem range_rangeSel (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (nd : Bool)
    (lg : Loc) (kv : GoInterface) (γ : MvccName) (r : Loc) (o : OpFull) (withTotal : Bool)
    (ot : Option Loc) (te : Bool) (Q : MvccState → IProp GF) (hcut : ¬ cutEarly o) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
        mvcc.api.isMvcc kv γ ∗ mvcc.api.mvccReaders γ 1 ∗ rangeRequestIs r o ∗
        mvcc.txnCtx ctx cd ∗
        traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗
        (if nd then mvcc.neverDone cd else iprop(True)) ∗ zapLoggerOrNil lg ∗ ⌜validSortTarget o⌝ ∗
        readAU γ Q }}
      (App (App (App (App (App (Val (@! txn.Range)) (Val #(GoInterface.ok ctx))) (Val #lg))
        (Val #kv)) (Val #r)) (Val #withTotal))
    {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
        mvcc.api.mvccReaders γ 1 ∗ ⌜trace ≠ null⌝ ∗
        (∃ te' : Bool, traceutil.ownTrace trace te') ∗ ∃ σ : MvccState, Q σ ∗ ⌜Reach σ⌝ ∗
          rangeResultClient resp err σ.log (W64 (σ.rev : Int)) σ.crev o withTotal }} := by
  wp_start_folded as ⟨#Hkv, Hrd, #Hr, #Hctx, #Hct, Hto, Hnd, #Hlg, %Hvs, Hau⟩
  ihave %Hset := rangeRequestIs_sortSet r o $$ Hr
  iapply (wp_Range ctx cd nd lg kv γ r o withTotal ot te Q) $$ [Hrd Hto Hnd Hau]
  · iframe # ∗
    ipureintro; exact Hvs
  inext
  iintro %resp %tr %err ⟨Hrd, %Htr, Hte, -, %σ, HQ, %Hreach, #Hres, -, -⟩
  iapply HΦ
  iframe Hrd Hte
  isplitr
  · ipureintro; exact Htr
  iexists σ
  iframe HQ
  isplitr
  · ipureintro; exact Hreach
  iapply rangeResult_client resp err σ.log (W64 (σ.rev : Int)) σ.crev o withTotal Hset hcut $$ Hres

end unit2

#print axioms Perennial.EtcdGrove.txn.range_rangeSel
#print axioms Perennial.EtcdGrove.txn.wp_Range
#print axioms Perennial.EtcdGrove.txn.wp_Count
#print axioms Perennial.EtcdGrove.txn.wp_executeRange
#print axioms Perennial.EtcdGrove.txn.wp_checkRange
#print axioms Perennial.EtcdGrove.txn.wp_sortRangeResults
#print axioms Perennial.EtcdGrove.txn.wp_filterRangeResults
#print axioms Perennial.EtcdGrove.txn.wp_asembleRangeResponse
#print axioms Perennial.EtcdGrove.txn.wp_mkGteRange
#print axioms Perennial.EtcdGrove.txn.srvRangeOk_rangeKvsOk

/-! ## Unit 3: `Txn` (`txn.go`)

Every function of `txn.go` (and `etcdserverpb.RequestOp.GetRequestRange`) has a `Spec`/`Proof`
pair and a linked result (`Link.lean`).

* **`Txn`** (`txn_srvRunTxn`, the spec `Txn.spec`): at the sole writer of `log` (`specSole`), one
  of `checkTxn`'s errors, nothing written; or the server's transaction `srvRunTxn` (`TxnRun.lean`:
  the comparisons' verdicts, every one at the state after `log`, the chosen branch run at the next
  revision) committed by the caller's updates, the response's header revision `writeRev`, nothing
  for a read-only request; at a reader (`specRead`), the server's run at the state read.
* **The client model's `runTxn`** (`txn_runTxn`): when every nested transaction's verdict is the
  same at the state after `log` and at the state the operations before it left (`OpsStable`;
  always without nested transactions, `opsStable_flat`), the committed state, the verdict and the
  results are the client's `runTxn` at `log`. etcd evaluates every comparison first
  (`compareToPath`); the client model evaluates a nested transaction's comparisons when it runs
  (`nonissues/etcd-txn-nested-compare-snapshot.md`).
* **The path** (`compareToPath_txnPath`), **serializable is not linearizable**
  (`txn_serializable_iff`).
-/

section unit3
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **`Txn`** (`Spec/go_etcd_io/etcd/server/v3/etcdserver/txn/Txn.lean`). -/
theorem txn_srvRunTxn : Txn.spec (GF := GF) (hG := hG) := wp_Txn

/-- **The server's transaction at the sole writer of `log` is the client model's `runTxn`**, when
the nested verdicts are stable (`OpsStable`): one of `checkTxn`'s errors, nothing written; or the
changes `txnChs log t` committed, whose state is `runTxn`'s, the response that of `runTxn`'s
verdict and results, its header revision `writeRev log (txnChs log t)`, nothing for a read-only
request. Under the critical-section contract: `Pre` and the read update's `Qr` back on an error or
a read-only request, else `Post` and the write updates' `Qw`. -/
theorem txn_runTxn (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg rt : Loc)
    (shared : Bool) (kv le : GoInterface) (skip : Bool) (γ : MvccName) (log : mvcc.Log)
    (t : TxnModel) (q : Qp) (B : MvccStorage) (P Pre Q Post : IProp GF) (f : GoFunc)
    (L : List w64) (ot : Option Loc) (te : Bool) (Qr Qw : MvccState → IProp GF)
    (hst : OpsStable (mvcc.stateAfter log) (W64 (log.length : Int)) (mvcc.stateAfter log)
      (t.branch (txnOk (mvcc.stateAfter log) t))) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
        mvcc.api.isMvcc kv γ ∗ mvcc.api.mvccReaders γ 1 ∗ kvBackend γ q B P f ∗
        isTxnLessor le (mvccLeases γ) ∗ txnRequestIs rt t ∗ mvcc.txnCtx ctx cd ∗
        traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗ mvcc.neverDone cd ∗
        zapLoggerOrNil lg ∗ leasesKnown L (mvcc.stateAfter log) ∗
        lease.lessorUser (mvccLeases γ) L (mvcc.leaseItemsOf (mvcc.stateAfter log)) ∗
        ⌜TxnPreA log t⌝ ∗
        csA P f Pre Q Post ∗
        readAU γ (fun σ => iprop(⌜σ.log = log⌝ ∗ Qr σ)) ∗
        (if txnReadonly t then iprop(True)
         else iprop(∀ σ : MvccState,
           ⌜PathsIgnOk (mvcc.stateAfter log) (t.branch (txnOk (mvcc.stateAfter log) t))⌝ -∗
           Qr σ -∗ txnBeginAU γ log t Qw)) }}
      (App (App (App (App (App (App (App (Val (@! txn.Txn)) (Val #(GoInterface.ok ctx)))
        (Val #lg)) (Val #rt)) (Val #shared)) (Val #kv)) (Val #le)) (Val #skip))
    {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
        mvcc.api.mvccReaders γ 1 ∗ kvBackend γ q B P f ∗
        ∃ σr : MvccState, ⌜σr.log = log ∧ Reach σr⌝ ∗
        ((⌜resp = null ∧ trace = null ∧ err ≠ GoInterface.nil⌝ ∗ checkErrIs err ∗ Pre ∗ Qr σr ∗
            lease.lessorUser (mvccLeases γ) L (mvcc.leaseItemsOf (mvcc.stateAfter log))) ∨
         (⌜err = GoInterface.nil ∧ trace ≠ null ∧
            mvcc.stateAfter (mvcc.commitLog log (txnChs log t)) =
              (runTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1 ∧
            (txnReadonly t = true → txnChs log t = [])⌝ ∗
          txnResponseIs skip resp (W64 (mvcc.writeRev log (txnChs log t) : Int)) t
            (runTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).1
            (runTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.2 ∗
          leasesKnown L (runTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1 ∗
          lease.lessorUser (mvccLeases γ) L
            (mvcc.leaseItemsOf (runTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1) ∗
          (if txnReadonly t then iprop(Pre ∗ Qr σr)
           else iprop(Post ∗ ∃ σw : MvccState, ⌜σw.log = log⌝ ∗ Qw σw)))) }} := by
  wp_start_folded as ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16⟩
  iapply (wp_Txn.1 ctx cd lg rt shared kv le skip γ log t q B P Pre Q Post f L ot te Qr Qw)
    $$ [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16]
  · iframe Hpkg H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16
  inext
  iintro %resp %trace %err ⟨Hrd, Hkb, %σr, %Hσr, Hout⟩
  iapply HΦ
  iframe Hrd Hkb
  iexists σr
  isplitr
  · ipureintro; exact Hσr
  icases Hout with (⟨%Hn, Herr, HPre, HQr, Hu, -⟩ | ⟨%Hok, -, -, Hresp, -, Hknown, Hu, HPP⟩)
  · ileft; iframe Herr HPre HQr Hu; ipureintro; exact ⟨Hn.1, Hn.2.1, Hn.2.2.1⟩
  · iright
    obtain ⟨h1, h2, h3⟩ := srvRunTxn_runTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t hst
    have hs : mvcc.stateAfter (mvcc.commitLog log (txnChs log t)) =
        (runTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1 := by
      rw [stateAfter_commitLog, h2]
    isplitl []; · ipureintro; exact ⟨Hok.1, Hok.2.1, hs, Hok.2.2.1⟩
    iframe HPP
    rw [← h1, ← h3, ← hs]
    iframe Hresp Hknown Hu

/-- **`compareToPath` is `txnPath`** (`Spec/go_etcd_io/etcd/server/v3/etcdserver/txn/compareToPath.lean`):
the verdicts of the transaction's comparisons and of its chosen nested transactions', in
pre-order, all at the read state; its length is one plus the number of nested transactions
(`txnPath_length`). -/
theorem compareToPath_txnPath : compareToPath.spec (GF := GF) (hG := hG) := wp_compareToPath

/-- **`IsTxnSerializable` is the client's "not linearizable"** (`TxnModel.linearizable`). -/
theorem txn_serializable_iff (rt : Loc) (t : TxnModel) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
        txnRequestIs rt t }}
      (App (Val (@! txn.IsTxnSerializable)) (Val #rt))
    {{ RET #(!t.linearizable); True }} := by
  rw [← serializable_linearizable]
  exact wp_IsTxnSerializable rt t

/-- Without nested transactions, the server's transaction is the client's (`srvRunTxn_runTxn`). -/
theorem srvRunTxn_runTxn_flat (r : w64) (s : List EtcdKv) (t : TxnModel)
    (h : opsFlat (t.branch (txnOk s t))) :
    (srvRunTxn r s t).1 = (runTxn r s t).1 ∧
      mvcc.applyChanges r s (srvRunTxn r s t).2.1 = (runTxn r s t).2.1 ∧
      (srvRunTxn r s t).2.2 = (runTxn r s t).2.2 :=
  srvRunTxn_runTxn r s t (opsStable_flat s r s _ h)

end unit3

#print axioms Perennial.EtcdGrove.txn.txn_srvRunTxn
#print axioms Perennial.EtcdGrove.txn.txn_runTxn
#print axioms Perennial.EtcdGrove.txn.compareToPath_txnPath
#print axioms Perennial.EtcdGrove.txn.txn_serializable_iff
#print axioms Perennial.EtcdGrove.txn.srvRunTxn_runTxn_flat
#print axioms Perennial.EtcdGrove.txn.wp_txn
#print axioms Perennial.EtcdGrove.txn.wp_executeTxn
#print axioms Perennial.EtcdGrove.txn.wp_checkTxn
#print axioms Perennial.EtcdGrove.txn.wp_newTxnResp
#print axioms Perennial.EtcdGrove.txn.wp_IsTxnReadonly

/-! ## Unit 0: mvcc's read-only write transaction (`Txn`'s read-only path), through mvcc's API
(`ApiResults.lean`) -/

end txn
end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.mvcc.api.mvccApi_NewReadOnlyTxnWrite_wp_api

/-! ## Unit 4: the history laws of the log (`HistoryLaws.lean`)

The server's log model validates the client's history axioms: each `etcdState_*` law holds of
`stateAt` (per prefix: `stateAtPfx`); `revs` needs `NoDupKeysPerRev` (a revision writes a key at
most once) for the version, the others only the word bound. A commit keeps `LogOk` and
`NoDupKeysPerRev` when it passes etcd's check of a transaction's requests. These validate the
axioms; they do not discharge them (`etcdState` is abstract).
-/

section unit4
#print axioms Perennial.EtcdGrove.txn.stateAt_revInv
#print axioms Perennial.EtcdGrove.txn.stateAt_create_persist
#print axioms Perennial.EtcdGrove.txn.stateAt_modrev_persist
#print axioms Perennial.EtcdGrove.txn.stateAt_modrev_det
#print axioms Perennial.EtcdGrove.txn.stateAtPfx_wf
#print axioms Perennial.EtcdGrove.txn.stateAtPfx_create_persist
#print axioms Perennial.EtcdGrove.txn.stateAtPfx_modrev_det
#print axioms Perennial.EtcdGrove.txn.stateAtPfx_modrev_persist
#print axioms Perennial.EtcdGrove.txn.stateAt_of_prefix
#print axioms Perennial.EtcdGrove.txn.keys_nodup_iff_check
end unit4
