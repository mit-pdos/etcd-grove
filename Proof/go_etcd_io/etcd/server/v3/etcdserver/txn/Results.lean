/-
The results of the server's txn package (`server/v3/etcdserver/txn`), restated at top level, with
the trust base of each printed in the build log (`#print axioms`). Each unit's results are in a
section of their own, in unit order.

Unit 0 (translation and scaffolding) proved no function of the package; its `Link.lean` linked
the trust-boundary axioms, and the read-only write transaction of mvcc (`Txn`'s read-only path)
is printed at the end. Unit 1: `Put` and `DeleteRange` (`put.go`, `delete.go`). The later units
add the range's results and `txn_runTxn`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace txn

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

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
`log`'s state, the sole writer at the new log. -/
theorem put_soleWriter (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg : Loc)
    (le kv : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (p : Loc) (o : OpFull) (log : mvcc.Log)
    (hlen : log.length + 4 ≤ 2 ^ 63) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
        isKV kv s γ ∗ mvcc.storeReader s γ ∗ soleWriter γ log ∗ isTxnLessor le γ.leases ∗
        putRequestIs p o ∗ context.isContext ctx cd ∗
        □ (⌜o.ignoreLease = true⌝ -∗
          leaseOk γ.leases (putLeaseOf o (mvcc.findKey o.key (mvcc.stateAfter log)))) }}
      (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.Put))
        (Val #(GoInterface.ok ctx))) (Val #lg)) (Val #le)) (Val #kv)) (Val #p))
    {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
        mvcc.storeReader s γ ∗ ⌜trace ≠ null⌝ ∗
        ((⌜o.leaseID ≠ W64 0 ∧ resp = null⌝ ∗
            errVarIs go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound err ∗ soleWriter γ log) ∨
         (⌜needsPrev o = true ∧ mvcc.findKey o.key (mvcc.stateAfter log) = none ∧ resp = null⌝ ∗
            errVarIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrKeyNotFound err ∗
            soleWriter γ log) ∨
         (⌜err = GoInterface.nil⌝ ∗
            putResponseIs resp (W64 (log.length : Int))
              (if o.base.prevKV then mvcc.findKey o.key (mvcc.stateAfter log) else none) ∗
            soleWriter γ (log ++ [[putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))]]) ∗
            leaseOk γ.leases (putLeaseOf o (mvcc.findKey o.key (mvcc.stateAfter log))) ∗
            ⌜mvcc.stateAfter (log ++ [[putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))]]) =
              (applyTxnOp (W64 (log.length : Int)) (mvcc.stateAfter log) (putTxnOp o)).1⌝)) }} := by
  wp_start_folded as ⟨#Hkv, Hrd, Hsw, #Hle, #Hp, #Hctx, #Hl⟩
  icases soleWriter_split γ log hlen $$ Hsw with ⟨Htok, Hsw⟩
  iunfold soleWriterOpen at Hsw
  icases Hsw with ⟨#Hc, Htoks⟩
  iapply (wp_Put ctx cd lg le kv s γ p o (soleBudget log - 1) log) $$ [Hrd Htok Htoks]
  · iframe # ∗
    imodintro
    iintro %ilog %Hpi
    obtain ⟨Hpin, Hil⟩ := Hpi
    rw [pinned_sole log ilog hlen Hpin]
    iapply Hl
    ipureintro; exact Hil
  inext
  iintro %resp %trace %err ⟨Hrd, Htoks, %Ht, Hout⟩
  ihave Hsw : soleWriterOpen γ log $$ [Htoks]
  · iunfold soleWriterOpen; iframe # ∗
  iapply HΦ
  iframe Hrd
  isplitl []
  · ipureintro; exact Ht
  icases Hout with (⟨%Hn, #He, Htok⟩ | ⟨%ilog, %Hpi, Hout⟩)
  · -- the lease not found
    ileft
    isplitl []
    · ipureintro; exact Hn
    iframe He
    have h := soleWriter_close (GF := GF) γ log [] hlen
    simp only [mvcc.commitLog, ↓reduceIte] at h
    iapply h
    iframe Hsw Htok Hc
  have hil := pinned_sole log ilog hlen Hpi.1
  subst hil
  icases Hout with (⟨%Hn, #He, Htok, -⟩ | ⟨%Herr, #Hresp, #Hc', #Hlok⟩)
  · -- the previous key-value missing
    iright; ileft
    isplitl []
    · ipureintro; exact Hn
    iframe He
    have h := soleWriter_close (GF := GF) γ ilog [] hlen
    simp only [mvcc.commitLog, ↓reduceIte] at h
    iapply h
    iframe Hsw Htok Hc
  · -- the put committed
    iright; iright
    isplitl []
    · ipureintro; exact Herr
    iframe Hresp Hlok
    isplitl [Hsw]
    · have hc : mvcc.commitLog ilog [putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter ilog))] =
          ilog ++ [[putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter ilog))]] := by
        unfold mvcc.commitLog; simp
      rw [← hc]
      iapply soleWriter_close γ ilog _ hlen $$ [Hsw]
      rw [hc]
      iframe Hsw Hc'
      simp only [List.cons_ne_nil, ↓reduceIte]
      itrivial
    ipureintro; exact stateAfter_put ilog o

/-- **`DeleteRange` at the sole writer of `log`** (fewer than `2 ^ 63` keys): the client's delete
on `log`'s state committed (no revision if nothing was deleted), the sole writer at the
committed log; or, with `PrevKv`, the range read's context error, the sole writer back. -/
theorem deleteRange_soleWriter (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (lg : Loc) (kv : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (dr : Loc) (o : OpFull)
    (log : mvcc.Log) (hlen : log.length + 4 ≤ 2 ^ 63) (hst : (mvcc.stateAfter log).length < 2 ^ 63) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
        isKV kv s γ ∗ mvcc.storeReader s γ ∗ soleWriter γ log ∗ deleteRangeRequestIs dr o ∗
        context.isContext ctx cd }}
      (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.DeleteRange))
        (Val #(GoInterface.ok ctx))) (Val #lg)) (Val #kv)) (Val #dr))
    {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
        mvcc.storeReader s γ ∗ ⌜trace ≠ null⌝ ∗
        ((⌜err = GoInterface.nil⌝ ∗
            deleteRangeResponseIs resp
              (W64 ((mvcc.writeRev log (delChanges (mvcc.stateAfter log) o) : Nat) : Int))
              (rangeIn (mvcc.stateAfter log) o).length
              (if o.base.prevKV then rangeIn (mvcc.stateAfter log) o else []) ∗
            soleWriter γ (mvcc.commitLog log (delChanges (mvcc.stateAfter log) o)) ∗
            ⌜mvcc.stateAfter (mvcc.commitLog log (delChanges (mvcc.stateAfter log) o)) =
              (applyTxnOp (W64 (log.length : Int)) (mvcc.stateAfter log) (.delete o)).1⌝) ∨
         (⌜err ≠ GoInterface.nil ∧ o.base.prevKV = true ∧ resp = null⌝ ∗ soleWriter γ log)) }} := by
  wp_start_folded as ⟨#Hkv, Hrd, Hsw, #Hdr, #Hctx⟩
  icases soleWriter_split γ log hlen $$ Hsw with ⟨Htok, Hsw⟩
  iunfold soleWriterOpen at Hsw
  icases Hsw with ⟨#Hc, Htoks⟩
  iapply (wp_DeleteRange ctx cd lg kv s γ dr o (soleBudget log - 1) log) $$ [Hrd Htok Htoks]
  · iframe # ∗
    ipureintro
    intro ilog hp
    rw [pinned_sole log ilog hlen hp]
    exact hst
  inext
  iintro %resp %trace %err ⟨Hrd, Htoks, %Ht, %ilog, %Hpi, Hout⟩
  have hil := pinned_sole log ilog hlen Hpi.1
  subst hil
  ihave Hsw : soleWriterOpen γ ilog $$ [Htoks]
  · iunfold soleWriterOpen; iframe # ∗
  iapply HΦ
  iframe Hrd
  isplitl []
  · ipureintro; exact Ht
  icases Hout with (⟨%Herr, #Hresp, #Hc', Htok⟩ | ⟨%Hn, Htok, -⟩)
  · -- deleted
    ileft
    isplitl []
    · ipureintro; exact Herr
    iframe Hresp
    isplitl [Hsw Htok]
    · iapply soleWriter_close γ ilog _ hlen
      iframe Hsw Hc' Htok
    ipureintro; exact stateAfter_commit_delete ilog o
  · -- the context error
    iright
    isplitl []
    · ipureintro; exact Hn
    have h := soleWriter_close (GF := GF) γ ilog [] hlen
    simp only [mvcc.commitLog, ↓reduceIte] at h
    iapply h
    iframe Hsw Htok Hc

end unit1

#print axioms put_putKv
#print axioms deleteRange_filter
#print axioms put_put
#print axioms deleteRange_deleteRange
#print axioms put_checkPut
#print axioms put_soleWriter
#print axioms deleteRange_soleWriter

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
