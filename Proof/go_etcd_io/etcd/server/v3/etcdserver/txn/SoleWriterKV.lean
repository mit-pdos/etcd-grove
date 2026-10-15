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

/-! ## A caller's floor (the vertical slice's unit V2)

The sole writer's transaction reads a committed log no longer than its own (`pinned_sole`); given
also a certificate of some log `F` (a floor: a log a client saw), the transaction is opened at
the longer of the two certified logs (they are in prefix order), so its committed log, the sole
writer's, extends `F` (`pinned_floor`): every log a client saw before a write was applied is a
prefix of the log the write met. -/

/-- Two certified logs have a certified common extension, one of them. -/
theorem cert_join (γ : mvcc.IdxNames) (log F : mvcc.Log) :
    mvcc.idxCert (GF := GF) γ log ∗ mvcc.idxCert γ F ⊢
      ∃ L0 : mvcc.Log, mvcc.idxCert γ L0 ∗ ⌜log <+: L0 ∧ F <+: L0⌝ := by
  iintro ⟨#H1, #H2⟩
  ihave %Hp := mvcc.idxCert_prefix γ log F $$ [$H1 $H2]
  rcases Hp with h | h
  · iexists F; iframe H2; ipureintro; exact ⟨h, List.prefix_refl _⟩
  · iexists log; iframe H1; ipureintro; exact ⟨List.prefix_refl _, h⟩

/-- At the sole writer's tokens, a pin at a common extension `L0` of the sole writer's log and a
floor `F` is the sole writer's log, which extends `F`. -/
theorem pinned_floor (log F L0 ilog : mvcc.Log) (h : log.length + 4 ≤ 2 ^ 63) (hl : log <+: L0)
    (hf : F <+: L0) (hp : Pinned L0 (soleBudget log - 1) ilog) : ilog = log ∧ F <+: log := by
  have hp' : Pinned log (soleBudget log - 1) ilog := ⟨hl.trans hp.1, hp.2⟩
  have e := pinned_sole log ilog h hp'
  subst e
  exact ⟨rfl, hf.trans hp.1⟩

/-- **`Put` at the sole writer of `log`**: the lease not found or the previous key-value missing
(the sole writer back, nothing committed); or the put committed at `log`, as the client's put on
`log`'s state, the sole writer at the new log. Under the critical-section contract: `Pre` back if
the lease was not found (no transaction), else `Post`. -/
theorem put_soleWriter_of (hPut : Put.spec (GF := GF) (hG := hG)) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg : Loc)
    (le kv : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (p : Loc) (o : OpFull) (log : mvcc.Log)
    (P Pre Q Post : IProp GF) (f : val) (L : List w64) (ot : Option Loc) (te : Bool)
    (hlen : log.length + 4 ≤ 2 ^ 63) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
        isKV kv s γ ∗ mvcc.storeReader s γ ∗ soleWriter γ log ∗ mvcc.storeWT γ ∗
        isTxnLessor le γ.leases ∗ lease.lessorUser γ.leases L ∗
        putRequestIs p o ∗ mvcc.txnCtx ctx cd ∗ traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗
        □ (⌜o.ignoreLease = true⌝ -∗
          leaseOk L (putLeaseOf o (mvcc.findKey o.key (mvcc.stateAfter log)))) ∗
        □ (⌜needsPrev o = true → (mvcc.findKey o.key (mvcc.stateAfter log)).isSome⌝ -∗
          mvcc.certOk γ (log ++ [[putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))]])) ∗
        mvcc.csContract P f Pre Q Post ∗ mvcc.hookIs γ P f }}
      (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.Put))
        (Val #(GoInterface.ok ctx))) (Val #lg)) (Val #le)) (Val #kv)) (Val #p))
    {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
        mvcc.storeReader s γ ∗ lease.lessorUser γ.leases L ∗ ⌜trace ≠ null⌝ ∗
        (∃ te' : Bool, traceutil.ownTrace trace te') ∗ ⌜∀ t0, ot = some t0 → te = false → trace = t0⌝ ∗
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
            leaseOk L (putLeaseOf o (mvcc.findKey o.key (mvcc.stateAfter log))) ∗ Post ∗
            ⌜mvcc.stateAfter (log ++ [[putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))]]) =
              (applyTxnOp (W64 (log.length : Int)) (mvcc.stateAfter log) (putTxnOp o)).1⌝)) }} := by
  wp_start_folded as ⟨#Hkv, Hrd, Hsw, Hwt, #Hle, Hu, #Hp, #Hctx, #Hct, Hto, #Hl, #Hcok, Hcs, #Hhook⟩
  icases soleWriter_split γ log hlen $$ Hsw with ⟨Htok, Hsw⟩
  iunfold soleWriterOpen at Hsw
  icases Hsw with ⟨#Hc, Htoks, %Hl2⟩
  iapply (hPut ctx cd lg le kv s γ p o (soleBudget log - 1) log P Pre Q Post f L ot te)
    $$ [Hrd Htok Hwt Htoks Hcs Hu Hto]
  · iframe # ∗
    isplitr
    · imodintro
      iintro %ilog %Hpi
      obtain ⟨Hpin, Hil⟩ := Hpi
      rw [pinned_sole log ilog hlen Hpin]
      iapply Hl
      ipureintro; exact Hil
    imodintro
    iintro %ilog ⟨%Hpin, %Hn⟩
    rw [pinned_sole log ilog hlen Hpin] at Hn ⊢
    iapply Hcok; ipureintro; exact Hn
  inext
  iintro %resp %trace %err ⟨Hrd, Htoks, Hu, %Ht, Htrc, %Hteq, Hout⟩
  ihave Hsw : soleWriterOpen γ log $$ [Htoks]
  · iunfold soleWriterOpen; iframe # ∗; ipureintro; exact Hl2
  iapply HΦ
  iframe Hrd Hu Htrc
  isplitl []
  · ipureintro; exact Ht
  isplitr
  · ipureintro; exact Hteq
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
    · ipureintro; exact Herr.1
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

theorem put_soleWriter_floor (hPut : Put.spec (GF := GF) (hG := hG)) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg : Loc)
    (le kv : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (p : Loc) (o : OpFull) (log : mvcc.Log)
    (P Pre Q Post : IProp GF) (f : val) (L : List w64) (ot : Option Loc) (te : Bool)
    (hlen : log.length + 4 ≤ 2 ^ 63) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
        isKV kv s γ ∗ mvcc.storeReader s γ ∗ soleWriter γ log ∗ mvcc.storeWT γ ∗
        isTxnLessor le γ.leases ∗ lease.lessorUser γ.leases L ∗
        putRequestIs p o ∗ mvcc.txnCtx ctx cd ∗ traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗
        □ (⌜o.ignoreLease = true⌝ -∗
          leaseOk L (putLeaseOf o (mvcc.findKey o.key (mvcc.stateAfter log)))) ∗
        □ (⌜needsPrev o = true → (mvcc.findKey o.key (mvcc.stateAfter log)).isSome⌝ -∗
          mvcc.certOk γ (log ++ [[putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))]])) ∗
        mvcc.csContract P f Pre Q Post ∗ mvcc.hookIs γ P f ∗ mvcc.idxCert γ.idx F }}
      (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.Put))
        (Val #(GoInterface.ok ctx))) (Val #lg)) (Val #le)) (Val #kv)) (Val #p))
    {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
        mvcc.storeReader s γ ∗ lease.lessorUser γ.leases L ∗ ⌜trace ≠ null⌝ ∗
        (∃ te' : Bool, traceutil.ownTrace trace te') ∗ ⌜∀ t0, ot = some t0 → te = false → trace = t0⌝ ∗
        ((⌜o.leaseID ≠ W64 0 ∧ resp = null⌝ ∗
            errVarIs go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound err ∗ soleWriter γ log ∗
            Pre) ∨
         (⌜needsPrev o = true ∧ mvcc.findKey o.key (mvcc.stateAfter log) = none ∧ resp = null⌝ ∗
            errVarIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrKeyNotFound err ∗
            soleWriter γ log ∗ Post) ∨
         (⌜err = GoInterface.nil ∧ F <+: log ∧
              (needsPrev o = true → (mvcc.findKey o.key (mvcc.stateAfter log)).isSome)⌝ ∗
            putResponseIs resp (W64 (log.length : Int))
              (if o.base.prevKV then mvcc.findKey o.key (mvcc.stateAfter log) else none) ∗
            respHdrOwn (structFieldRef go_etcd_io.etcd.api.v3.etcdserverpb.PutResponse go!"Header" resp) ∗
            soleWriter γ (log ++ [[putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))]]) ∗
            leaseOk L (putLeaseOf o (mvcc.findKey o.key (mvcc.stateAfter log))) ∗ Post ∗
            ⌜mvcc.stateAfter (log ++ [[putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))]]) =
              (applyTxnOp (W64 (log.length : Int)) (mvcc.stateAfter log) (putTxnOp o)).1⌝)) }} := by
  wp_start_folded as ⟨#Hkv, Hrd, Hsw, Hwt, #Hle, Hu, #Hp, #Hctx, #Hct, Hto, #Hl, #Hcok, Hcs, #Hhook, #HF⟩
  icases soleWriter_split γ log hlen $$ Hsw with ⟨Htok, Hsw⟩
  iunfold soleWriterOpen at Hsw
  icases Hsw with ⟨#Hc, Htoks, %Hl2⟩
  ihave ⟨%L0, #Hc0, %HL0⟩ := cert_join γ.idx log F $$ [$Hc $HF]
  iapply (hPut ctx cd lg le kv s γ p o (soleBudget log - 1) L0 P Pre Q Post f L ot te)
    $$ [Hrd Htok Hwt Htoks Hcs Hu Hto]
  · iframe # ∗
    isplitr
    · imodintro
      iintro %ilog %Hpi
      obtain ⟨Hpin, Hil⟩ := Hpi
      rw [(pinned_floor log F L0 ilog hlen HL0.1 HL0.2 Hpin).1]
      iapply Hl
      ipureintro; exact Hil
    imodintro
    iintro %ilog ⟨%Hpin, %Hn⟩
    rw [(pinned_floor log F L0 ilog hlen HL0.1 HL0.2 Hpin).1] at Hn ⊢
    iapply Hcok; ipureintro; exact Hn
  inext
  iintro %resp %trace %err ⟨Hrd, Htoks, Hu, %Ht, Htrc, %Hteq, Hout⟩
  ihave Hsw : soleWriterOpen γ log $$ [Htoks]
  · iunfold soleWriterOpen; iframe # ∗; ipureintro; exact Hl2
  iapply HΦ
  iframe Hrd Hu Htrc
  isplitl []
  · ipureintro; exact Ht
  isplitr
  · ipureintro; exact Hteq
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
  obtain ⟨hil, hFl⟩ := pinned_floor log F L0 ilog hlen HL0.1 HL0.2 Hpi.1
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
    · ipureintro; exact ⟨Herr.1, hFl, Herr.2⟩
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

/-- **`DeleteRange` at the sole writer of `log`** (fewer than `mvcc.putMax γ` keys in the range): the client's delete
on `log`'s state committed (no revision if nothing was deleted), the sole writer at the
committed log; or, with `PrevKv`, the range read's context error, the sole writer back. Under the
critical-section contract: `Post`. -/
theorem deleteRange_soleWriter_of (hDel : DeleteRange.spec (GF := GF) (hG := hG)) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (nd : Bool) (lg : Loc) (kv : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (dr : Loc) (o : OpFull)
    (log : mvcc.Log) (P Pre Q Post : IProp GF) (f : val) (ot : Option Loc) (te : Bool)
    (hlen : log.length + 4 ≤ 2 ^ 63)
    (hst : (rangeIn (mvcc.stateAfter log) o).length < mvcc.putMax γ) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
        isKV kv s γ ∗ mvcc.storeReader s γ ∗ soleWriter γ log ∗ mvcc.storeWT γ ∗
        deleteRangeRequestIs dr o ∗
        mvcc.txnCtx ctx cd ∗ traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗ (if nd then mvcc.neverDone cd else iprop(True)) ∗
        mvcc.certOkNext γ log (delChanges (mvcc.stateAfter log) o) ∗
        mvcc.csContract P f Pre Q Post ∗ mvcc.hookIs γ P f }}
      (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.DeleteRange))
        (Val #(GoInterface.ok ctx))) (Val #lg)) (Val #kv)) (Val #dr))
    {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
        mvcc.storeReader s γ ∗ ⌜trace ≠ null⌝ ∗ Post ∗
        (∃ te' : Bool, traceutil.ownTrace trace te') ∗ ⌜∀ t0, ot = some t0 → te = false → trace = t0⌝ ∗
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
  wp_start_folded as ⟨#Hkv, Hrd, Hsw, Hwt, #Hdr, #Hctx, #Hct, Hto, #Hnd, #Hcok, Hcs, #Hhook⟩
  icases soleWriter_split γ log hlen $$ Hsw with ⟨Htok, Hsw⟩
  iunfold soleWriterOpen at Hsw
  icases Hsw with ⟨#Hc, Htoks, %Hl2⟩
  iapply (hDel ctx cd nd lg kv s γ dr o (soleBudget log - 1) log P Pre Q Post f ot te)
    $$ [Hrd Htok Hwt Htoks Hcs Hto]
  · iframe # ∗
    isplitr
    · ipureintro
      intro ilog hp
      rw [pinned_sole log ilog hlen hp]
      exact hst
    imodintro
    iintro %ilog %Hpin
    rw [pinned_sole log ilog hlen Hpin]
    iexact Hcok
  inext
  iintro %resp %trace %err ⟨Hrd, Htoks, %Ht, HPost, Htrc, %Hteq, %ilog, %Hpi, Hout⟩
  have hil := pinned_sole log ilog hlen Hpi.1
  subst hil
  ihave Hsw : soleWriterOpen γ ilog $$ [Htoks]
  · iunfold soleWriterOpen; iframe # ∗; ipureintro; exact Hl2
  iapply HΦ
  iframe Hrd
  isplitl []
  · ipureintro; exact Ht
  iframe HPost Htrc
  isplitr
  · ipureintro; exact Hteq
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

theorem deleteRange_soleWriter_floor (hDel : DeleteRange.spec (GF := GF) (hG := hG)) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (nd : Bool) (lg : Loc) (kv : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (dr : Loc) (o : OpFull)
    (log : mvcc.Log) (P Pre Q Post : IProp GF) (f : val) (ot : Option Loc) (te : Bool)
    (hlen : log.length + 4 ≤ 2 ^ 63)
    (hst : (rangeIn (mvcc.stateAfter log) o).length < mvcc.putMax γ) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
        isKV kv s γ ∗ mvcc.storeReader s γ ∗ soleWriter γ log ∗ mvcc.storeWT γ ∗
        deleteRangeRequestIs dr o ∗
        mvcc.txnCtx ctx cd ∗ traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗ (if nd then mvcc.neverDone cd else iprop(True)) ∗
        mvcc.certOkNext γ log (delChanges (mvcc.stateAfter log) o) ∗
        mvcc.csContract P f Pre Q Post ∗ mvcc.hookIs γ P f ∗ mvcc.idxCert γ.idx F }}
      (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.DeleteRange))
        (Val #(GoInterface.ok ctx))) (Val #lg)) (Val #kv)) (Val #dr))
    {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
        mvcc.storeReader s γ ∗ ⌜trace ≠ null⌝ ∗ Post ∗
        (∃ te' : Bool, traceutil.ownTrace trace te') ∗ ⌜∀ t0, ot = some t0 → te = false → trace = t0⌝ ∗
        ((⌜err = GoInterface.nil ∧ F <+: log⌝ ∗
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
  wp_start_folded as ⟨#Hkv, Hrd, Hsw, Hwt, #Hdr, #Hctx, #Hct, Hto, #Hnd, #Hcok, Hcs, #Hhook, #HF⟩
  icases soleWriter_split γ log hlen $$ Hsw with ⟨Htok, Hsw⟩
  iunfold soleWriterOpen at Hsw
  icases Hsw with ⟨#Hc, Htoks, %Hl2⟩
  ihave ⟨%L0, #Hc0, %HL0⟩ := cert_join γ.idx log F $$ [$Hc $HF]
  iapply (hDel ctx cd nd lg kv s γ dr o (soleBudget log - 1) L0 P Pre Q Post f ot te)
    $$ [Hrd Htok Hwt Htoks Hcs Hto]
  · iframe # ∗
    isplitr
    · ipureintro
      intro ilog hp
      rw [(pinned_floor log F L0 ilog hlen HL0.1 HL0.2 hp).1]
      exact hst
    imodintro
    iintro %ilog %Hpin
    rw [(pinned_floor log F L0 ilog hlen HL0.1 HL0.2 Hpin).1]
    iexact Hcok
  inext
  iintro %resp %trace %err ⟨Hrd, Htoks, %Ht, HPost, Htrc, %Hteq, %ilog, %Hpi, Hout⟩
  obtain ⟨hil, hFl⟩ := pinned_floor log F L0 ilog hlen HL0.1 HL0.2 Hpi.1
  subst hil
  ihave Hsw : soleWriterOpen γ ilog $$ [Htoks]
  · iunfold soleWriterOpen; iframe # ∗; ipureintro; exact Hl2
  iapply HΦ
  iframe Hrd
  isplitl []
  · ipureintro; exact Ht
  iframe HPost Htrc
  isplitr
  · ipureintro; exact Hteq
  icases Hout with (⟨%Herr, #Hresp, Hhdr, #Hc', Htok⟩ | ⟨%Hn, Htok, -⟩)
  · -- deleted
    ileft
    isplitl []
    · ipureintro; exact ⟨Herr, hFl⟩
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
    (kv : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (r : Loc) (o : OpFull) (withTotal : Bool)
    (ot : Option Loc) (te : Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
        isKV kv s γ ∗ mvcc.storeReader s γ ∗ soleWriter γ log ∗
        rangeRequestIs r o ∗ mvcc.txnCtx ctx cd ∗ traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗
        (if nd then mvcc.neverDone cd else iprop(True)) ∗ ⌜lg ≠ null⌝ ∗
        ⌜validSortTarget o ∧ sortOk o log⌝ }}
      (App (App (App (App (App (Val (@! txn.Range)) (Val #(GoInterface.ok ctx))) (Val #lg))
        (Val #kv)) (Val #r)) (Val #withTotal))
    {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
        mvcc.storeReader s γ ∗ soleWriter γ log ∗ ⌜trace ≠ null⌝ ∗
        (∃ te' : Bool, traceutil.ownTrace trace te') ∗ ⌜∀ t0, ot = some t0 → te = false → trace = t0⌝ ∗
        rangeResult resp err log (W64 ((log.length : Int) - 1)) o withTotal ∗
        ⌜nd = true → err = GoInterface.nil ∨
          sint.Z (W64 ((log.length : Int) - 1)) < sint.Z o.base.rev⌝ }} := by
  wp_start_folded as ⟨#Hkv, Hrd, Hsw, #Hr, #Hctx, #Hct, Hto, #Hnd, %Hlg, %Hpre⟩
  iunfold soleWriter at Hsw
  icases Hsw with ⟨#Hc, Ht, %Hl2⟩
  iapply (hRange ctx cd nd lg kv s γ r o withTotal (soleBudget log) log ot te) $$ [Hrd Ht Hto]
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
  iintro %resp %tr %err ⟨Hrd, Ht, %Htr, Htrc, %Hteq, %log', %rev, -, -, %Hp, #Hres, -, %Hnd'⟩
  have heq := soleWriter_pins_read log log' hlen ⟨Hp.1, Hp.2.1⟩
  subst heq
  obtain ⟨-, -, -, hrev⟩ := Hp
  subst hrev
  iapply HΦ
  iframe Hrd Hres Htrc
  isplitl [Ht]
  · iunfold soleWriter; iframe Hc Ht; ipureintro; exact Hl2
  · ipureintro; exact ⟨Htr, Hteq, Hnd'⟩

end sole

end txn
end EtcdGrove
end Perennial
