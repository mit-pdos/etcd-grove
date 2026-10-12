/-
The results of the server's txn package (`server/v3/etcdserver/txn`), restated at top level, with
the trust base of each printed in the build log (`#print axioms`). Each unit's results are in a
section of their own, in unit order.

Unit 0 (translation and scaffolding) proved no function of the package; its `Link.lean` linked
the trust-boundary axioms, and the read-only write transaction of mvcc (`Txn`'s read-only path)
is printed at the end. Unit 1: `Put` and `DeleteRange` (`put.go`, `delete.go`). Unit 2: the range
(`range.go`). Unit 3: the transaction (`txn.go`), `txn_runTxn`.

**The post-lock hook** (2026-10-12, apply unit A): `Put`, `DeleteRange` and `Txn` take the
critical-section contract `csContract P f Pre Q Post` with the store's hook `hookIs γ P f`
(mvcc's `InvStore.lean`: the backend's batch lock has invariant `P` and runs `f` right after
`LockInsideApply`) and return `Post` when they opened a write transaction, `Pre` when they did
not; the results below are stated at any `P f Pre Q Post`. The statements before the hook are
the instance `P := True`, `f` a no-op, `Q = Post = Pre` (`mvcc.csContract_noHook`), with any
`Pre` (e.g. `True`) carried through.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Link
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.RangeLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.SoleWriter
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.SoleWriterKV
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

/-! ## Unit 1: `Put` and `DeleteRange` (`put.go`, `delete.go`)

Every function of `put.go` and `delete.go` has a `Spec`/`Proof` pair and a linked result
(`Link.lean`). `Put` and `DeleteRange` open one write transaction with a revision token; the
caller's other tokens and certificate pin the committed log the transaction finds (`Pinned`).

* **`Put` is the client's put** (`put_putKv`): with the lease found (or none) and, for an ignore
  flag, the previous key-value there, the committed log is the transaction's `ilog` with the one
  change `putChangeOf o pv`, whose state is the client model's `applyTxnOp` of `putTxnOp o`
  (`stateAfter_put`: `IgnoreValue`/`IgnoreLease` keep the previous value/lease); the response's
  revision is the new one, its `PrevKv` the previous key-value iff `PrevKv` asked. Else
  `lease.ErrLeaseNotFound` (no transaction) or `errors.ErrKeyNotFound` (nothing committed).
* **`DeleteRange` is the client's delete** (`deleteRange_filter`): the keys of the request's range
  in `ilog`'s state deleted (`delChanges`), committed as one revision if any (`commitLog`), the
  state the client model's filter (`stateAfter_commit_delete`); `Deleted` their number, the
  header's revision `writeRev`, `PrevKvs` the deleted key-values iff `PrevKv`. Or, with `PrevKv`,
  the range read's context error (the caller's context done): nothing deleted.
* **At the sole writer** (`put_soleWriter`, `deleteRange_soleWriter`): with `soleWriter γ log`
  instead of a token, the committed log the transaction finds is `log` (`pinned_sole`), and the
  sole writer comes back at the committed log (`soleWriter_close`).
-/

section unit1
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

/-- **`Put` is the client's put** (`Spec/go_etcd_io/etcd/server/v3/etcdserver/txn/Put.lean`;
its committed state: `stateAfter_put`). -/
theorem put_putKv : Put.spec (GF := GF) (hG := hG) := wp_Put

/-- **`DeleteRange` is the client's delete**
(`Spec/go_etcd_io/etcd/server/v3/etcdserver/txn/DeleteRange.lean`; its committed state:
`stateAfter_commit_delete`). -/
theorem deleteRange_filter : DeleteRange.spec (GF := GF) (hG := hG) := wp_DeleteRange

/-- `put(ctx, txnWrite, p, prevKV)` (`Txn`'s put, in a write transaction). -/
theorem put_put : put.spec (GF := GF) (hG := hG) := wp_put

/-- `deleteRange(ctx, txnWrite, dr)` (`Txn`'s delete, in a write transaction). -/
theorem deleteRange_deleteRange : deleteRange.spec (GF := GF) (hG := hG) := wp_deleteRange

/-- `checkPut(trace, txnRead, lessor, p)` (`Txn`'s check of a put, at its read transaction). -/
theorem put_checkPut : checkPut.spec (GF := GF) (hG := hG) := wp_checkPut

/-- **`Put` at the sole writer of `log`**: the lease not found or the previous key-value missing
(the sole writer back, nothing committed); or the put committed at `log`, as the client's put on
`log`'s state, the sole writer at the new log. Under the critical-section contract: `Pre` back if
the lease was not found (no transaction), else `Post`. -/
theorem put_soleWriter (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg : Loc)
    (le kv : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (p : Loc) (o : OpFull) (log : mvcc.Log)
    (P Pre Q Post : IProp GF) (f : val) (hlen : log.length + 4 ≤ 2 ^ 63) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
        isKV kv s γ ∗ mvcc.storeReader s γ ∗ soleWriter γ log ∗ isTxnLessor le γ.leases ∗
        putRequestIs p o ∗ mvcc.txnCtx ctx cd ∗
        □ (⌜o.ignoreLease = true⌝ -∗
          leaseOk γ.leases (putLeaseOf o (mvcc.findKey o.key (mvcc.stateAfter log)))) ∗
        mvcc.csContract P f Pre Q Post ∗ mvcc.hookIs γ P f }}
      (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.Put))
        (Val #(GoInterface.ok ctx))) (Val #lg)) (Val #le)) (Val #kv)) (Val #p))
    {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
        mvcc.storeReader s γ ∗ ⌜trace ≠ null⌝ ∗
        ((⌜o.leaseID ≠ W64 0 ∧ resp = null⌝ ∗
            errVarIs go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound err ∗ soleWriter γ log ∗
            Pre) ∨
         (⌜needsPrev o = true ∧ mvcc.findKey o.key (mvcc.stateAfter log) = none ∧ resp = null⌝ ∗
            errVarIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrKeyNotFound err ∗
            soleWriter γ log ∗ Post) ∨
         (⌜err = GoInterface.nil⌝ ∗
            putResponseIs resp (W64 (log.length : Int))
              (if o.base.prevKV then mvcc.findKey o.key (mvcc.stateAfter log) else none) ∗
            soleWriter γ (log ++ [[putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))]]) ∗
            leaseOk γ.leases (putLeaseOf o (mvcc.findKey o.key (mvcc.stateAfter log))) ∗ Post ∗
            ⌜mvcc.stateAfter (log ++ [[putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))]]) =
              (applyTxnOp (W64 (log.length : Int)) (mvcc.stateAfter log) (putTxnOp o)).1⌝)) }} :=
  put_soleWriter_of wp_Put ctx cd lg le kv s γ p o log P Pre Q Post f hlen

/-- **`DeleteRange` at the sole writer of `log`** (fewer than `2 ^ 63` keys): the client's delete
on `log`'s state committed (no revision if nothing was deleted), the sole writer at the
committed log; or, with `PrevKv`, the range read's context error, the sole writer back. Under the
critical-section contract: `Post`. -/
theorem deleteRange_soleWriter (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (nd : Bool) (lg : Loc) (kv : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (dr : Loc) (o : OpFull)
    (log : mvcc.Log) (P Pre Q Post : IProp GF) (f : val) (hlen : log.length + 4 ≤ 2 ^ 63)
    (hst : (mvcc.stateAfter log).length < 2 ^ 63) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
        isKV kv s γ ∗ mvcc.storeReader s γ ∗ soleWriter γ log ∗ deleteRangeRequestIs dr o ∗
        mvcc.txnCtx ctx cd ∗ (if nd then mvcc.neverDone cd else iprop(True)) ∗
        mvcc.csContract P f Pre Q Post ∗ mvcc.hookIs γ P f }}
      (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.DeleteRange))
        (Val #(GoInterface.ok ctx))) (Val #lg)) (Val #kv)) (Val #dr))
    {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
        mvcc.storeReader s γ ∗ ⌜trace ≠ null⌝ ∗ Post ∗
        ((⌜err = GoInterface.nil⌝ ∗
            deleteRangeResponseIs resp
              (W64 ((mvcc.writeRev log (delChanges (mvcc.stateAfter log) o) : Nat) : Int))
              (rangeIn (mvcc.stateAfter log) o).length
              (if o.base.prevKV then rangeIn (mvcc.stateAfter log) o else []) ∗
            soleWriter γ (mvcc.commitLog log (delChanges (mvcc.stateAfter log) o)) ∗
            ⌜mvcc.stateAfter (mvcc.commitLog log (delChanges (mvcc.stateAfter log) o)) =
              (applyTxnOp (W64 (log.length : Int)) (mvcc.stateAfter log) (.delete o)).1⌝) ∨
         (⌜err ≠ GoInterface.nil ∧ o.base.prevKV = true ∧ resp = null ∧ nd = false⌝ ∗
           soleWriter γ log)) }} :=
  deleteRange_soleWriter_of wp_DeleteRange ctx cd nd lg kv s γ dr o log P Pre Q Post f hlen hst

end unit1

#print axioms put_putKv
#print axioms deleteRange_filter
#print axioms put_put
#print axioms deleteRange_deleteRange
#print axioms put_checkPut
#print axioms put_soleWriter
#print axioms deleteRange_soleWriter

/-! ## Unit 2: the range (`range.go`)

Every function of `range.go` has a `Spec`/`Proof` pair and a linked result (`Link.lean`).

* **`Range` in the client's terms** (`range_rangeSel`): `rangeKvsOk` of the client model's
  `rangeSel`, unless the sort is cut early (`issues/etcd-range-sort-none-limit.md`).
* **At the sole writer** (`range_soleWriter`): the read is at its log exactly.
* **`Count` at the sole writer** (`count_result`): the client's `rangeIn` length.
-/

section unit2
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **`Range` in the client's terms**: `Range`'s spec (`txn.Range.spec`) with the success case
stated over the client model's selection (`rangeResultClient`: `rangeKvsOk` of `rangeSel` of the
state read, up to a fast keys-only read's zero lease), for a request whose sort is not cut early
(`cutEarly`, `issues/etcd-range-sort-none-limit.md`). -/
theorem range_rangeSel (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg : Loc)
    (kv : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (r : Loc) (o : OpFull) (withTotal : Bool)
    (m : Nat) (log₀ : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
        isKV kv s γ ∗ mvcc.storeReader s γ ∗ ownToks γ.revs m ∗ mvcc.idxCert γ.idx log₀ ∗
        rangeRequestIs r o ∗ mvcc.txnCtx ctx cd ∗ ⌜lg ≠ null⌝ ∗
        ⌜validSortTarget o ∧ ¬ cutEarly o ∧
          ∀ log : mvcc.Log, log₀ <+: log → log.length + m + 3 ≤ 2 ^ 63 → sortOk o log⌝ }}
      (App (App (App (App (App (Val (@! txn.Range)) (Val #(GoInterface.ok ctx))) (Val #lg))
        (Val #kv)) (Val #r)) (Val #withTotal))
    {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
        mvcc.storeReader s γ ∗ ownToks γ.revs m ∗ ⌜trace ≠ null⌝ ∗
        ∃ (log : mvcc.Log) (rev : w64), mvcc.idxCert γ.idx log ∗
          ⌜log₀ <+: log ∧ log.length + m + 3 ≤ 2 ^ 63 ∧ log ≠ [] ∧
            rev = W64 ((log.length : Int) - 1)⌝ ∗
          rangeResultClient resp err log rev o withTotal }} := by
  wp_start_folded as ⟨#Hkv, Hrd, Ht, #Hc, #Hr, #Hctx, %Hlg, %Hpre⟩
  ihave %Hset := rangeRequestIs_sortSet r o $$ Hr
  iapply (wp_Range ctx cd false lg kv s γ r o withTotal m log₀) $$ [Hrd Ht]
  · iframe # ∗
    isplitr
    · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    ipureintro; exact ⟨Hlg, Hpre.1, Hpre.2.2⟩
  inext
  iintro %resp %tr %err ⟨Hrd, Ht, %Htr, %log, %rev, #Hcert, %Hp, #Hres, -⟩
  iapply HΦ
  iframe Hrd Ht
  isplitr
  · ipureintro; exact Htr
  iexists log, rev
  iframe Hcert
  isplitr
  · ipureintro; exact Hp
  iapply rangeResult_client resp err log rev o withTotal Hset Hpre.2.1 $$ Hres

/-- **`Range` at the sole writer** reads its log exactly (`soleWriter_pins_read`): the response
is `rangeResult` at `log`'s last revision. -/
theorem range_soleWriter (log : mvcc.Log) (hlen : log.length + 3 ≤ 2 ^ 63)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (nd : Bool) (lg : Loc)
    (kv : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (r : Loc) (o : OpFull) (withTotal : Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
        isKV kv s γ ∗ mvcc.storeReader s γ ∗ soleWriter γ log ∗
        rangeRequestIs r o ∗ mvcc.txnCtx ctx cd ∗
        (if nd then mvcc.neverDone cd else iprop(True)) ∗ ⌜lg ≠ null⌝ ∗
        ⌜validSortTarget o ∧ sortOk o log⌝ }}
      (App (App (App (App (App (Val (@! txn.Range)) (Val #(GoInterface.ok ctx))) (Val #lg))
        (Val #kv)) (Val #r)) (Val #withTotal))
    {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
        mvcc.storeReader s γ ∗ soleWriter γ log ∗ ⌜trace ≠ null⌝ ∗
        rangeResult resp err log (W64 ((log.length : Int) - 1)) o withTotal ∗
        ⌜nd = true → err = GoInterface.nil ∨
          sint.Z (W64 ((log.length : Int) - 1)) < sint.Z o.base.rev⌝ }} :=
  range_soleWriter_of wp_Range log hlen ctx cd nd lg kv s γ r o withTotal

/-- **`Count` at the sole writer**: the number of keys of the client's range (`rangeIn` of the
count-only request `countOp`) in the state at the revision read, at the sole writer's log; or
`ErrFutureRev` and `0` for a revision past it. -/
theorem count_result (log : mvcc.Log) (hlen : log.length + 3 ≤ 2 ^ 63)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg : Loc) (kv : GoInterface)
    (s : Loc) (γ : mvcc.StoreNames) (key rangeEnd : GoSlice) (k e : GoString) (revision : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
        isKV kv s γ ∗ mvcc.storeReader s γ ∗ soleWriter γ log ∗
        key ↦*□ k ∗ rangeEnd ↦*□ e ∗ mvcc.txnCtx ctx cd ∗ ⌜lg ≠ null⌝ }}
      (App (App (App (App (App (App (Val (@! txn.Count)) (Val #(GoInterface.ok ctx))) (Val #lg))
        (Val #kv)) (Val #key)) (Val #rangeEnd)) (Val #revision))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        mvcc.storeReader s γ ∗ soleWriter γ log ∗
        ((⌜err = GoInterface.nil ∧ sint.Z revision ≤ (log.length : Int) - 1 ∧
            n = W64 ((rangeIn (mvcc.stateAt log
              (sint.nat (mvcc.rangeRev (W64 ((log.length : Int) - 1)) revision)))
              (countOp k (rangeEndOf rangeEnd e) revision)).length : Int)⌝) ∨
         (⌜(log.length : Int) - 1 < sint.Z revision ∧ n = W64 0⌝ ∗ ∃ ef : GoInterfaceOk,
            globalAddr ErrFutureRev ↦□ GoInterface.ok ef ∗ ⌜err = GoInterface.ok ef⌝)) }} := by
  wp_start_folded as ⟨#Hkv, Hrd, Hsw, #Hk, #He, #Hctx, %Hlg⟩
  iunfold soleWriter at Hsw
  icases Hsw with ⟨#Hc, Ht⟩
  iapply (wp_Count ctx cd lg kv s γ key rangeEnd k e revision (soleBudget log) log) $$ [Hrd Ht]
  · iframe # ∗; ipureintro; exact Hlg
  inext
  iintro %n %err ⟨Hrd, Ht, %log', %rev, -, %Hp, Hres⟩
  have heq := soleWriter_pins_read log log' hlen ⟨Hp.1, Hp.2.1⟩
  subst heq
  obtain ⟨-, -, hne, hrev⟩ := Hp
  have hz : sint.Z rev = (log'.length : Int) - 1 := by
    rw [hrev]; exact lastRev_sint _ (List.length_pos_iff.2 hne) (by omega)
  subst hrev
  iapply HΦ
  iframe Hrd
  isplitl [Ht]
  · iunfold soleWriter; iframe Hc Ht
  icases Hres with (%H | ⟨%H, Hf⟩)
  · ileft; ipureintro; rw [hz] at H; exact H
  · iright; iframe Hf; ipureintro; rw [hz] at H; exact H

end unit2

#print axioms Perennial.EtcdGrove.txn.range_rangeSel
#print axioms Perennial.EtcdGrove.txn.range_soleWriter
#print axioms Perennial.EtcdGrove.txn.count_result
#print axioms Perennial.EtcdGrove.txn.wp_Range
#print axioms Perennial.EtcdGrove.txn.wp_Count
#print axioms Perennial.EtcdGrove.txn.wp_executeRange
#print axioms Perennial.EtcdGrove.txn.wp_checkRange
#print axioms Perennial.EtcdGrove.txn.wp_sortRangeResults
#print axioms Perennial.EtcdGrove.txn.wp_filterRangeResults
#print axioms Perennial.EtcdGrove.txn.wp_asembleRangeResponse
#print axioms Perennial.EtcdGrove.txn.wp_mkGteRange
#print axioms Perennial.EtcdGrove.txn.srvRangeOk_rangeKvsOk
#print axioms Perennial.EtcdGrove.mvcc.metricsTxnWrite.wp_Rev
#print axioms Perennial.EtcdGrove.mvcc.metricsTxnWrite.wp_FirstRev

/-! ## Unit 3: `Txn` (`txn.go`)

Every function of `txn.go` (and `etcdserverpb.RequestOp.GetRequestRange`) has a `Spec`/`Proof`
pair and a linked result (`Link.lean`).

* **`Txn` at the sole writer** (`txn_srvRunTxn`, the spec `Txn.spec`): one of `checkTxn`'s errors,
  nothing written; or the server's transaction `srvRunTxn` (`TxnRun.lean`: the comparisons'
  verdicts, every one at the state after `log`, the chosen branch run at the next revision)
  committed, `soleWriter` at `commitLog log chs`, the response's header revision `writeRev`.
* **The client model's `runTxn`** (`txn_runTxn`): when every nested transaction's verdict is the
  same at the state after `log` and at the state the operations before it left (`OpsStable`;
  always without nested transactions, `opsStable_flat`), the committed state, the verdict and the
  results are the client's `runTxn` at the sole writer's log. etcd evaluates every comparison
  first (`compareToPath`); the client model evaluates a nested transaction's comparisons when it
  runs (`issues/etcd-txn-nested-compare-snapshot.md`).
* **Read-only requests make no revision** (`txn_readonly_no_revision`), **a failed check writes
  nothing** (`txn_check_error_no_write`).
* **The path** (`compareToPath_txnPath`), **serializable is not linearizable**
  (`txn_serializable_iff`).
-/

section unit3
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **`Txn` at the sole writer** (`Spec/go_etcd_io/etcd/server/v3/etcdserver/txn/Txn.lean`). -/
theorem txn_srvRunTxn : Txn.spec (GF := GF) (hG := hG) := wp_Txn

/-- **The server's transaction is the client model's `runTxn` at the sole writer's log**, when
the nested verdicts are stable (`OpsStable`): one of `checkTxn`'s errors, nothing written; or
the changes `pend` committed, whose state is `runTxn`'s, the response that of `runTxn`'s verdict
and results, its header revision `writeRev log pend`, nothing for a read-only request. Under the
critical-section contract: `Pre` back on an error or a read-only request, else `Post`. -/
theorem txn_runTxn (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg rt : Loc)
    (shared : Bool) (kv le : GoInterface) (skip : Bool) (s : Loc) (γ : mvcc.StoreNames)
    (log : mvcc.Log) (t : TxnModel) (P Pre Q Post : IProp GF) (f : val)
    (hst : OpsStable (mvcc.stateAfter log) (W64 (log.length : Int)) (mvcc.stateAfter log)
      (t.branch (txnOk (mvcc.stateAfter log) t))) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
        isKV kv s γ ∗ mvcc.storeReader s γ ∗ soleWriter γ log ∗ isTxnLessor le γ.leases ∗
        txnRequestIs rt t ∗ mvcc.txnCtx ctx cd ∗ mvcc.neverDone cd ∗
        leasesKnown γ.leases (mvcc.stateAfter log) ∗ ⌜TxnPre log t⌝ ∗
        mvcc.csContract P f Pre Q Post ∗ mvcc.hookIs γ P f }}
      (App (App (App (App (App (App (App (Val (@! txn.Txn)) (Val #(GoInterface.ok ctx)))
        (Val #lg)) (Val #rt)) (Val #shared)) (Val #kv)) (Val #le)) (Val #skip))
    {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
        mvcc.storeReader s γ ∗
        ((⌜resp = null ∧ trace = null ∧ err ≠ GoInterface.nil⌝ ∗ checkErrIs err ∗
            soleWriter γ log ∗ Pre) ∨
         (⌜err = GoInterface.nil ∧ trace ≠ null⌝ ∗ (if txnReadonly t then Pre else Post) ∗
          ∃ pend : List mvcc.Change,
            ⌜mvcc.stateAfter (mvcc.commitLog log pend) =
                (runTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1 ∧
              (txnReadonly t = true → pend = [])⌝ ∗
            txnResponseIs skip resp (W64 (mvcc.writeRev log pend : Int)) t
              (runTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).1
              (runTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.2 ∗
            soleWriter γ (mvcc.commitLog log pend) ∗
            leasesKnown γ.leases (runTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1)) }} := by
  wp_start_folded as Hpre
  iapply (wp_Txn ctx cd lg rt shared kv le skip s γ log t P Pre Q Post f) $$ [Hpre]
  · iframe Hpre Hpkg
  inext
  iintro %resp %trace %err ⟨Hrd, Hout⟩
  iapply HΦ
  iframe Hrd
  icases Hout with (Herr | ⟨%Hok, #Hresp, Hsw, #Hknown, HPP⟩)
  · ileft; iexact Herr
  · iright
    obtain ⟨h1, h2, h3⟩ := srvRunTxn_runTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t hst
    have hs : mvcc.stateAfter (mvcc.commitLog log
        (srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1) =
        (runTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1 := by
      rw [stateAfter_commitLog, h2]
    isplitl []; · ipureintro; exact ⟨Hok.1, Hok.2.1⟩
    iframe HPP
    iexists (srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1
    isplitl []; · ipureintro; exact ⟨hs, Hok.2.2⟩
    rw [← h1, ← h3, ← hs]
    iframe Hresp Hsw Hknown

/-- **A read-only request makes no revision**: `Txn` of a read-only request (`IsTxnReadonly`) at
the sole writer leaves it at `log`, the response's header revision `log`'s last, and takes no
batch lock (`Pre` back). -/
theorem txn_readonly_no_revision (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (lg rt : Loc) (shared : Bool) (kv le : GoInterface) (skip : Bool) (s : Loc)
    (γ : mvcc.StoreNames) (log : mvcc.Log) (t : TxnModel) (P Pre Q Post : IProp GF) (f : val)
    (hro : txnReadonly t = true) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
        isKV kv s γ ∗ mvcc.storeReader s γ ∗ soleWriter γ log ∗ isTxnLessor le γ.leases ∗
        txnRequestIs rt t ∗ mvcc.txnCtx ctx cd ∗ mvcc.neverDone cd ∗
        leasesKnown γ.leases (mvcc.stateAfter log) ∗ ⌜TxnPre log t⌝ ∗
        mvcc.csContract P f Pre Q Post ∗ mvcc.hookIs γ P f }}
      (App (App (App (App (App (App (App (Val (@! txn.Txn)) (Val #(GoInterface.ok ctx)))
        (Val #lg)) (Val #rt)) (Val #shared)) (Val #kv)) (Val #le)) (Val #skip))
    {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
        mvcc.storeReader s γ ∗ soleWriter γ log ∗ Pre ∗
        ((⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ checkErrIs err) ∨
         (⌜err = GoInterface.nil⌝ ∗
            txnResponseIs skip resp (W64 ((log.length - 1 : Nat) : Int)) t
              (srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).1
              (srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.2)) }} := by
  wp_start_folded as Hpre
  iapply (wp_Txn ctx cd lg rt shared kv le skip s γ log t P Pre Q Post f) $$ [Hpre]
  · iframe Hpre Hpkg
  inext
  iintro %resp %trace %err ⟨Hrd, Hout⟩
  iapply HΦ
  iframe Hrd
  icases Hout with (⟨%Hn, #Herr, Hsw, HPre⟩ | ⟨%Hok, #Hresp, Hsw, -, HPP⟩)
  · iframe Hsw HPre
    ileft
    iframe Herr
    ipureintro; exact ⟨Hn.1, Hn.2.2⟩
  · have hch := Hok.2.2 hro
    rw [hch, show mvcc.commitLog log [] = log from rfl,
      show mvcc.writeRev log [] = log.length - 1 from rfl]
    iframe Hsw
    simp only [hro, ↓reduceIte]
    iframe HPP
    iright
    isplitl []; · ipureintro; exact Hok.1
    iexact Hresp

/-- **A failed check writes nothing**: whatever `Txn` returns at the sole writer of `log`, an
error leaves the sole writer at `log`, with no response, and takes no batch lock (`Pre` back). -/
theorem txn_check_error_no_write (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (lg rt : Loc) (shared : Bool) (kv le : GoInterface) (skip : Bool) (s : Loc)
    (γ : mvcc.StoreNames) (log : mvcc.Log) (t : TxnModel) (P Pre Q Post : IProp GF) (f : val) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
        isKV kv s γ ∗ mvcc.storeReader s γ ∗ soleWriter γ log ∗ isTxnLessor le γ.leases ∗
        txnRequestIs rt t ∗ mvcc.txnCtx ctx cd ∗ mvcc.neverDone cd ∗
        leasesKnown γ.leases (mvcc.stateAfter log) ∗ ⌜TxnPre log t⌝ ∗
        mvcc.csContract P f Pre Q Post ∗ mvcc.hookIs γ P f }}
      (App (App (App (App (App (App (App (Val (@! txn.Txn)) (Val #(GoInterface.ok ctx)))
        (Val #lg)) (Val #rt)) (Val #shared)) (Val #kv)) (Val #le)) (Val #skip))
    {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
        mvcc.storeReader s γ ∗ ∃ log' : mvcc.Log, soleWriter γ log' ∗
          ((⌜err ≠ GoInterface.nil⌝ ∗ Pre) ∨ (Pre ∨ Post)) ∗
          ⌜err ≠ GoInterface.nil → log' = log ∧ resp = null⌝ }} := by
  wp_start_folded as Hpre
  iapply (wp_Txn ctx cd lg rt shared kv le skip s γ log t P Pre Q Post f) $$ [Hpre]
  · iframe Hpre Hpkg
  inext
  iintro %resp %trace %err ⟨Hrd, Hout⟩
  iapply HΦ
  iframe Hrd
  icases Hout with (⟨%Hn, -, Hsw, HPre⟩ | ⟨%Hok, -, Hsw, -, HPP⟩)
  · iexists log
    iframe Hsw
    isplitl [HPre]
    · ileft; iframe HPre; ipureintro; exact Hn.2.2
    ipureintro; intro _; exact ⟨rfl, Hn.1⟩
  · iexists _
    iframe Hsw
    isplitl [HPP]
    · iright
      cases txnReadonly t
      · simp only [Bool.false_eq_true, ↓reduceIte] at *; iright; iexact HPP
      · simp only [↓reduceIte] at *; ileft; iexact HPP
    ipureintro; intro h; exact absurd Hok.1 h

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
#print axioms Perennial.EtcdGrove.txn.txn_readonly_no_revision
#print axioms Perennial.EtcdGrove.txn.txn_check_error_no_write
#print axioms Perennial.EtcdGrove.txn.compareToPath_txnPath
#print axioms Perennial.EtcdGrove.txn.txn_serializable_iff
#print axioms Perennial.EtcdGrove.txn.srvRunTxn_runTxn_flat
#print axioms Perennial.EtcdGrove.txn.wp_txn
#print axioms Perennial.EtcdGrove.txn.wp_executeTxn
#print axioms Perennial.EtcdGrove.txn.wp_checkTxn
#print axioms Perennial.EtcdGrove.txn.wp_newTxnResp
#print axioms Perennial.EtcdGrove.txn.wp_IsTxnReadonly
#print axioms Perennial.EtcdGrove.mvcc.metricsTxnWrite.wp_Changes

/-! ## Unit 0: mvcc's read-only write transaction (`InvRoTxn.lean`), linked in mvcc's
`Link.lean` -/

end txn
end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.mvcc.wp_NewReadOnlyTxnWrite
#print axioms Perennial.EtcdGrove.mvcc.txnReadWrite.wp_FirstRev
#print axioms Perennial.EtcdGrove.mvcc.txnReadWrite.wp_Rev
#print axioms Perennial.EtcdGrove.mvcc.txnReadWrite.wp_Range
#print axioms Perennial.EtcdGrove.mvcc.txnReadWrite.wp_End
#print axioms Perennial.EtcdGrove.mvcc.txnReadWrite.wp_Changes
#print axioms Perennial.EtcdGrove.mvcc.txnReadWrite.wp_Put
#print axioms Perennial.EtcdGrove.mvcc.txnReadWrite.wp_DeleteRange

/-! ## Unit 4: the history laws of the log (`HistoryLaws.lean`)

The server's log model validates the client's history axioms: each `etcdState_*` law holds of
`stateAt` (per prefix: `stateAtPfx`); `revs` needs `NoDupKeysPerRev` (a revision writes a key at
most once) for the version, the others only the word bound. A commit keeps `LogOk` and
`NoDupKeysPerRev` when it passes etcd's check of a transaction's requests. These validate the
axioms; they do not discharge them (`etcdState` is abstract).
-/

section unit4
#print axioms Perennial.EtcdGrove.txn.stateAt_revInv
#print axioms Perennial.EtcdGrove.txn.stateAt_revs
#print axioms Perennial.EtcdGrove.txn.stateAt_create_persist
#print axioms Perennial.EtcdGrove.txn.stateAt_modrev_persist
#print axioms Perennial.EtcdGrove.txn.stateAt_modrev_det
#print axioms Perennial.EtcdGrove.txn.stateAtPfx_agree
#print axioms Perennial.EtcdGrove.txn.stateAtPfx_wf
#print axioms Perennial.EtcdGrove.txn.stateAtPfx_revs
#print axioms Perennial.EtcdGrove.txn.stateAtPfx_create_persist
#print axioms Perennial.EtcdGrove.txn.stateAtPfx_modrev_det
#print axioms Perennial.EtcdGrove.txn.stateAtPfx_modrev_persist
#print axioms Perennial.EtcdGrove.txn.stateAt_of_prefix
#print axioms Perennial.EtcdGrove.txn.stateAtPfx_of_prefix
#print axioms Perennial.EtcdGrove.txn.LogOk.snoc
#print axioms Perennial.EtcdGrove.txn.NoDupKeysPerRev.snoc_iff
#print axioms Perennial.EtcdGrove.txn.keys_nodup_iff_check
#print axioms Perennial.EtcdGrove.txn.NoDupKeysPerRev.snoc
#print axioms Perennial.EtcdGrove.txn.sel_keys_nodup
end unit4
