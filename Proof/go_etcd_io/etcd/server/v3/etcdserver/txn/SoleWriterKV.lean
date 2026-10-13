/-
The server's txn package at the sole writer (`Put`, `DeleteRange`, `Range`): each entry point's
spec, as a hypothesis, at the sole writer of a log (`soleWriter`) instead of a token and a
certificate. `Results.lean` restates them at the linked results (`put_soleWriter`, ...); the
apply package's backend applier (`apply/applierV3backend__Put.lean`, ...) uses them at its
callees' specs. Moved from `Results.lean` (2026-10-12, apply unit 1), statements unchanged.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Put
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.DeleteRange
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Range
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.SoleWriter

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace txn

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.storage.mvcc
  go_etcd_io.etcd.api.v3

section sole
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- **`Put` at the sole writer of `log`**: the lease not found or the previous key-value missing
(the sole writer back, nothing committed); or the put committed at `log`, as the client's put on
`log`'s state, the sole writer at the new log. Under the critical-section contract: `Pre` back if
the lease was not found (no transaction), else `Post`. -/
theorem put_soleWriter_of (hPut : Put.spec (GF := GF) (hG := hG)) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg : Loc)
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
            respHdrOwn (structFieldRef go_etcd_io.etcd.api.v3.etcdserverpb.PutResponse go!"Header" resp) ∗
            soleWriter γ (log ++ [[putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))]]) ∗
            leaseOk γ.leases (putLeaseOf o (mvcc.findKey o.key (mvcc.stateAfter log))) ∗ Post ∗
            ⌜mvcc.stateAfter (log ++ [[putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))]]) =
              (applyTxnOp (W64 (log.length : Int)) (mvcc.stateAfter log) (putTxnOp o)).1⌝)) }} := by
  wp_start_folded as ⟨#Hkv, Hrd, Hsw, #Hle, #Hp, #Hctx, #Hl, Hcs, #Hhook⟩
  icases soleWriter_split γ log hlen $$ Hsw with ⟨Htok, Hsw⟩
  iunfold soleWriterOpen at Hsw
  icases Hsw with ⟨#Hc, Htoks, %Hl2⟩
  iapply (hPut ctx cd lg le kv s γ p o (soleBudget log - 1) log P Pre Q Post f)
    $$ [Hrd Htok Htoks Hcs]
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
  · iunfold soleWriterOpen; iframe # ∗; ipureintro; exact Hl2
  iapply HΦ
  iframe Hrd
  isplitl []
  · ipureintro; exact Ht
  icases Hout with (⟨%Hn, #He, Htok, HPre⟩ | ⟨%ilog, %Hpi, HPost, Hout⟩)
  · -- the lease not found
    ileft
    isplitl []
    · ipureintro; exact Hn
    iframe He HPre
    have h := soleWriter_close (GF := GF) γ log [] hlen
    simp only [mvcc.commitLog, ↓reduceIte] at h
    iapply h
    iframe Hsw Htok Hc
  have hil := pinned_sole log ilog hlen Hpi.1
  subst hil
  icases Hout with (⟨%Hn, #He, Htok, -⟩ | ⟨%Herr, #Hresp, Hhdr, #Hc', #Hlok⟩)
  · -- the previous key-value missing
    iright; ileft
    isplitl []
    · ipureintro; exact Hn
    iframe He HPost
    have h := soleWriter_close (GF := GF) γ ilog [] hlen
    simp only [mvcc.commitLog, ↓reduceIte] at h
    iapply h
    iframe Hsw Htok Hc
  · -- the put committed
    iright; iright
    isplitl []
    · ipureintro; exact Herr
    iframe Hresp Hhdr Hlok HPost
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
committed log; or, with `PrevKv`, the range read's context error, the sole writer back. Under the
critical-section contract: `Post`. -/
theorem deleteRange_soleWriter_of (hDel : DeleteRange.spec (GF := GF) (hG := hG)) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
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
            respHdrOwn (structFieldRef go_etcd_io.etcd.api.v3.etcdserverpb.DeleteRangeResponse go!"Header" resp) ∗
            soleWriter γ (mvcc.commitLog log (delChanges (mvcc.stateAfter log) o)) ∗
            ⌜mvcc.stateAfter (mvcc.commitLog log (delChanges (mvcc.stateAfter log) o)) =
              (applyTxnOp (W64 (log.length : Int)) (mvcc.stateAfter log) (.delete o)).1⌝) ∨
         (⌜err ≠ GoInterface.nil ∧ o.base.prevKV = true ∧ resp = null ∧ nd = false⌝ ∗
           soleWriter γ log)) }} := by
  wp_start_folded as ⟨#Hkv, Hrd, Hsw, #Hdr, #Hctx, #Hnd, Hcs, #Hhook⟩
  icases soleWriter_split γ log hlen $$ Hsw with ⟨Htok, Hsw⟩
  iunfold soleWriterOpen at Hsw
  icases Hsw with ⟨#Hc, Htoks, %Hl2⟩
  iapply (hDel ctx cd nd lg kv s γ dr o (soleBudget log - 1) log P Pre Q Post f)
    $$ [Hrd Htok Htoks Hcs]
  · iframe # ∗
    ipureintro
    intro ilog hp
    rw [pinned_sole log ilog hlen hp]
    exact hst
  inext
  iintro %resp %trace %err ⟨Hrd, Htoks, %Ht, HPost, %ilog, %Hpi, Hout⟩
  have hil := pinned_sole log ilog hlen Hpi.1
  subst hil
  ihave Hsw : soleWriterOpen γ ilog $$ [Htoks]
  · iunfold soleWriterOpen; iframe # ∗; ipureintro; exact Hl2
  iapply HΦ
  iframe Hrd
  isplitl []
  · ipureintro; exact Ht
  iframe HPost
  icases Hout with (⟨%Herr, #Hresp, Hhdr, #Hc', Htok⟩ | ⟨%Hn, Htok, -⟩)
  · -- deleted
    ileft
    isplitl []
    · ipureintro; exact Herr
    iframe Hresp Hhdr
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

/-- **`Range` at the sole writer** reads its log exactly (`soleWriter_pins_read`): the response
is `rangeResult` at `log`'s last revision. -/
theorem range_soleWriter_of (hRange : Range.spec (GF := GF) (hG := hG)) (log : mvcc.Log) (hlen : log.length + 3 ≤ 2 ^ 63)
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
          sint.Z (W64 ((log.length : Int) - 1)) < sint.Z o.base.rev⌝ }} := by
  wp_start_folded as ⟨#Hkv, Hrd, Hsw, #Hr, #Hctx, #Hnd, %Hlg, %Hpre⟩
  iunfold soleWriter at Hsw
  icases Hsw with ⟨#Hc, Ht, %Hl2⟩
  iapply (hRange ctx cd nd lg kv s γ r o withTotal (soleBudget log) log) $$ [Hrd Ht]
  · iframe # ∗
    isplitr
    · ipureintro; exact Hlg
    isplitr
    · ipureintro; exact Hpre.1
    iintro !> %log' %h -
    ipureintro
    rw [soleWriter_pins_read log log' hlen ⟨h.1, h.2⟩]
    exact Hpre.2
  inext
  iintro %resp %tr %err ⟨Hrd, Ht, %Htr, %log', %rev, -, %Hp, #Hres, -, %Hnd'⟩
  have heq := soleWriter_pins_read log log' hlen ⟨Hp.1, Hp.2.1⟩
  subst heq
  obtain ⟨-, -, -, hrev⟩ := Hp
  subst hrev
  iapply HΦ
  iframe Hrd Hres
  isplitl
  · iunfold soleWriter; iframe Hc Ht; ipureintro; exact Hl2
  · ipureintro; exact ⟨Htr, Hnd'⟩

end sole

end txn
end EtcdGrove
end Perennial
