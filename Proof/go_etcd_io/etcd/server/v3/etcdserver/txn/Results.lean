/-
The trust base of the server's txn package's results: `#print axioms` of each. Built with the
rest; read its output to check it.

Unit 0 (translation and scaffolding): no function of the package is proved yet; `Link.lean`
links the trust-boundary axioms the package's functions call, and imports mvcc's results, of
which the read-only write transaction (`Txn`'s read-only path) is printed here. The later units
add the package's results (`txn_runTxn`, `put_putKv`, `deleteRange_filter`, the range's).

Unit 2 (`range.go`): `range_rangeSel` (`Range` in the client model's terms: `rangeKvsOk` of
`rangeSel`, unless the sort is cut early), `range_soleWriter` (at the sole writer, the read is at
its log exactly), `count_result` (`Count` at the sole writer: the client's `rangeIn` length).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Link
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.RangeLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.SoleWriter

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace txn

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.storage.mvcc
  go_etcd_io.etcd.api.v3

section results
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
        rangeRequestIs r o ∗ context.isContext ctx cd ∗ ⌜lg ≠ null⌝ ∗
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
  iapply (wp_Range ctx cd lg kv s γ r o withTotal m log₀) $$ [Hrd Ht]
  · iframe # ∗; ipureintro; exact ⟨Hlg, Hpre.1, Hpre.2.2⟩
  inext
  iintro %resp %tr %err ⟨Hrd, Ht, %Htr, %log, %rev, #Hcert, %Hp, #Hres⟩
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
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg : Loc)
    (kv : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (r : Loc) (o : OpFull) (withTotal : Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
        isKV kv s γ ∗ mvcc.storeReader s γ ∗ soleWriter γ log ∗
        rangeRequestIs r o ∗ context.isContext ctx cd ∗ ⌜lg ≠ null⌝ ∗
        ⌜validSortTarget o ∧ sortOk o log⌝ }}
      (App (App (App (App (App (Val (@! txn.Range)) (Val #(GoInterface.ok ctx))) (Val #lg))
        (Val #kv)) (Val #r)) (Val #withTotal))
    {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
        mvcc.storeReader s γ ∗ soleWriter γ log ∗ ⌜trace ≠ null⌝ ∗
        rangeResult resp err log (W64 ((log.length : Int) - 1)) o withTotal }} := by
  wp_start_folded as ⟨#Hkv, Hrd, Hsw, #Hr, #Hctx, %Hlg, %Hpre⟩
  iunfold soleWriter at Hsw
  icases Hsw with ⟨#Hc, Ht⟩
  iapply (wp_Range ctx cd lg kv s γ r o withTotal (soleBudget log) log) $$ [Hrd Ht]
  · iframe # ∗
    ipureintro
    refine ⟨Hlg, Hpre.1, fun log' h1 h2 => ?_⟩
    rw [soleWriter_pins_read log log' hlen ⟨h1, h2⟩]
    exact Hpre.2
  inext
  iintro %resp %tr %err ⟨Hrd, Ht, %Htr, %log', %rev, -, %Hp, #Hres⟩
  have heq := soleWriter_pins_read log log' hlen ⟨Hp.1, Hp.2.1⟩
  subst heq
  obtain ⟨-, -, -, hrev⟩ := Hp
  subst hrev
  iapply HΦ
  iframe Hrd Hres
  isplitl
  · iunfold soleWriter; iframe Hc Ht
  · ipureintro; exact Htr

/-- **`Count` at the sole writer**: the number of keys of the client's range (`rangeIn` of the
count-only request `countOp`) in the state at the revision read, at the sole writer's log; or
`ErrFutureRev` and `0` for a revision past it. -/
theorem count_result (log : mvcc.Log) (hlen : log.length + 3 ≤ 2 ^ 63)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg : Loc) (kv : GoInterface)
    (s : Loc) (γ : mvcc.StoreNames) (key rangeEnd : GoSlice) (k e : GoString) (revision : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
        isKV kv s γ ∗ mvcc.storeReader s γ ∗ soleWriter γ log ∗
        key ↦*□ k ∗ rangeEnd ↦*□ e ∗ context.isContext ctx cd ∗ ⌜lg ≠ null⌝ }}
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

end results

end txn
end EtcdGrove
end Perennial

/-! Unit 2: the range (`range.go`), linked in `Link.lean`, and the results above. -/
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

/-! mvcc's read-only write transaction (`InvRoTxn.lean`), linked in mvcc's `Link.lean`. -/
#print axioms Perennial.EtcdGrove.mvcc.wp_NewReadOnlyTxnWrite
#print axioms Perennial.EtcdGrove.mvcc.txnReadWrite.wp_FirstRev
#print axioms Perennial.EtcdGrove.mvcc.txnReadWrite.wp_Rev
#print axioms Perennial.EtcdGrove.mvcc.txnReadWrite.wp_Range
#print axioms Perennial.EtcdGrove.mvcc.txnReadWrite.wp_End
#print axioms Perennial.EtcdGrove.mvcc.txnReadWrite.wp_Changes
#print axioms Perennial.EtcdGrove.mvcc.txnReadWrite.wp_Put
#print axioms Perennial.EtcdGrove.mvcc.txnReadWrite.wp_DeleteRange
