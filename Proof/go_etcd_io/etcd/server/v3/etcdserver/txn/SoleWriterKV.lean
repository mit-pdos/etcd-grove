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
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Writer

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

/-- `put_soleWriter_of` with a floor `F` (a certified log): the put, if committed, met a log
extending `F` (`pinned_floor`). -/
theorem put_soleWriter_floor (hPut : Put.spec (GF := GF) (hG := hG)) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg : Loc)
    (le kv : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (p : Loc) (o : OpFull) (log : mvcc.Log)
    (P Pre Q Post : IProp GF) (f : val) (L : List w64) (ot : Option Loc) (te : Bool)
    (hlen : log.length + 4 ≤ 2 ^ 63) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
        isKV kv s γ ∗ mvcc.storeReader s γ ∗ kvWriter s γ log ∗ mvcc.storeWT γ ∗
        isTxnLessor le γ.leases ∗ lease.lessorUser γ.leases L (mvcc.leaseItemsOf (mvcc.stateAfter log)) ∗
        putRequestIs p o ∗ mvcc.txnCtx ctx cd ∗ traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗
        □ (⌜o.ignoreLease = true⌝ -∗
          leaseOk L (putLeaseOf o (mvcc.findKey o.key (mvcc.stateAfter log)))) ∗
        □ (⌜needsPrev o = true → (mvcc.findKey o.key (mvcc.stateAfter log)).isSome⌝ -∗
          mvcc.certOk γ (log ++ [[putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))]])) ∗
        mvcc.csContract P f Pre Q Post ∗ mvcc.hookOk γ P f ∗ mvcc.idxCert γ.idx F }}
      (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.Put))
        (Val #(GoInterface.ok ctx))) (Val #lg)) (Val #le)) (Val #kv)) (Val #p))
    {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
        mvcc.storeReader s γ ∗ ⌜trace ≠ null⌝ ∗
        (∃ te' : Bool, traceutil.ownTrace trace te') ∗ ⌜∀ t0, ot = some t0 → te = false → trace = t0⌝ ∗
        ((⌜o.leaseID ≠ W64 0 ∧ resp = null⌝ ∗
            errVarIs go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound err ∗ kvWriter s γ log ∗
            Pre ∗ lease.lessorUser γ.leases L (mvcc.leaseItemsOf (mvcc.stateAfter log))) ∨
         (⌜needsPrev o = true ∧ mvcc.findKey o.key (mvcc.stateAfter log) = none ∧ resp = null⌝ ∗
            errVarIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrKeyNotFound err ∗
            kvWriter s γ log ∗ Post ∗ lease.lessorUser γ.leases L (mvcc.leaseItemsOf (mvcc.stateAfter log))) ∨
         (⌜err = GoInterface.nil ∧ F <+: log ∧
              (needsPrev o = true → (mvcc.findKey o.key (mvcc.stateAfter log)).isSome)⌝ ∗
            putResponseIs resp (W64 (log.length : Int))
              (if o.base.prevKV then mvcc.findKey o.key (mvcc.stateAfter log) else none) ∗
            respHdrOwn (structFieldRef go_etcd_io.etcd.api.v3.etcdserverpb.PutResponse go!"Header" resp) ∗
            kvWriter s γ (log ++ [[putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))]]) ∗
            leaseOk L (putLeaseOf o (mvcc.findKey o.key (mvcc.stateAfter log))) ∗ Post ∗
            lease.lessorUser γ.leases L (mvcc.leaseItemsOf (mvcc.stateAfter
              (log ++ [[putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))]]))) ∗
            ⌜mvcc.stateAfter (log ++ [[putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))]]) =
              (applyTxnOp (W64 (log.length : Int)) (mvcc.stateAfter log) (putTxnOp o)).1⌝)) }} := by
  wp_start_folded as ⟨#Hkv, Hrd, Hsw, Hwt, #Hle, Hu, #Hp, #Hctx, #Hct, Hto, #Hl, #Hcok, Hcs, #Hhook, #HF⟩
  iunfold kvWriter at Hsw
  icases Hsw with ⟨Hsw, Hwl, Hfrag⟩
  icases soleWriter_split γ log hlen $$ Hsw with ⟨Htok, Hsw⟩
  -- the writer's hook: the hook's facts and the writer's fragment (D22 receiver epochs, S5b)
  ihave HhookW : mvcc.hookIs γ P f $$ [Hfrag]
  · iapply (mvcc.hookIs_split γ P f).2; iframe Hhook Hfrag
  iunfold soleWriterOpen at Hsw
  icases Hsw with ⟨#Hc, Htoks, %Hl2⟩
  have hsb : soleBudget log - 1 + 1 = soleBudget log := by unfold soleBudget; omega
  ihave ⟨%L0, #Hc0, %HL0⟩ := cert_join γ.idx log F $$ [$Hc $HF]
  iapply (hPut ctx cd lg le kv s γ p o (soleBudget log - 1) L0 P Pre Q Post f L _ ot te log)
    $$ [Hrd Htok Hwt Htoks Hcs Hu Hto Hwl HhookW]
  · iframe # ∗
    isplitr
    · ipureintro; exact fun _ => ⟨hsb, hlen⟩
    isplitr
    · imodintro
      iintro %ilog %Hpin
      rw [(pinned_floor log F L0 ilog hlen HL0.1 HL0.2 Hpin).1]
      ipureintro; rfl
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
  iintro %resp %trace %err ⟨Hrd, HhookW, Htoks, %Ht, Htrc, %Hteq, Hout⟩
  icases (mvcc.hookIs_split γ P f).1 $$ HhookW with ⟨-, Hfrag⟩
  ihave Hsw : soleWriterOpen γ log $$ [Htoks]
  · iunfold soleWriterOpen; iframe # ∗; ipureintro; exact Hl2
  iapply HΦ
  iframe Hrd Htrc
  isplitl []
  · ipureintro; exact Ht
  isplitr
  · ipureintro; exact Hteq
  icases Hout with (⟨%Hn, #He, Htok, Hwl, HPre, Hu⟩ | ⟨%ilog, %Hpi, HPost, Hout⟩)
  · -- the lease not found
    ileft
    isplitl []
    · ipureintro; exact Hn
    iframe He HPre Hu
    have h := soleWriter_close (GF := GF) γ log [] hlen
    simp only [mvcc.commitLog, ↓reduceIte] at h
    iunfold kvWriter
    iframe Hwl Hfrag
    iapply h
    iframe Hsw Htok Hc
  obtain ⟨hil, hFl⟩ := pinned_floor log F L0 ilog hlen HL0.1 HL0.2 Hpi.1
  subst hil
  icases Hout with (⟨%Hn, #He, Htok, -, Hwl, Hu⟩ | ⟨%Herr, #Hresp, Hhdr, #Hc', Hwl, #Hlok, Hu⟩)
  · -- the previous key-value missing
    iright; ileft
    isplitl []
    · ipureintro; exact Hn
    iframe He HPost Hu
    have h := soleWriter_close (GF := GF) γ ilog [] hlen
    simp only [mvcc.commitLog, ↓reduceIte] at h
    iunfold kvWriter
    iframe Hwl Hfrag
    iapply h
    iframe Hsw Htok Hc
  · -- the put committed
    iright; iright
    isplitl []
    · ipureintro; exact ⟨Herr.1, hFl, Herr.2⟩
    iframe Hresp Hhdr Hlok HPost Hu
    isplitl [Hsw Hwl Hfrag]
    · iunfold kvWriter
      have hc : mvcc.commitLog ilog [putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter ilog))] =
          ilog ++ [[putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter ilog))]] := by
        unfold mvcc.commitLog; simp
      rw [← hc]
      iframe Hwl Hfrag
      iapply soleWriter_close γ ilog _ hlen $$ [Hsw]
      rw [hc]
      iframe Hsw Hc'
      simp only [List.cons_ne_nil, ↓reduceIte]
      itrivial
    ipureintro; exact stateAfter_put ilog o

/-- **`Put` at the sole writer of `log`**: the lease not found or the previous key-value missing
(the sole writer back, nothing committed); or the put committed at `log`, as the client's put on
`log`'s state, the sole writer at the new log. Under the critical-section contract: `Pre` back if
the lease was not found (no transaction), else `Post`. `put_soleWriter_floor` at the floor
`log` itself (`kvWriter_cert`). -/
theorem put_soleWriter_of (hPut : Put.spec (GF := GF) (hG := hG)) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg : Loc)
    (le kv : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (p : Loc) (o : OpFull) (log : mvcc.Log)
    (P Pre Q Post : IProp GF) (f : val) (L : List w64) (ot : Option Loc) (te : Bool)
    (hlen : log.length + 4 ≤ 2 ^ 63) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
        isKV kv s γ ∗ mvcc.storeReader s γ ∗ kvWriter s γ log ∗ mvcc.storeWT γ ∗
        isTxnLessor le γ.leases ∗ lease.lessorUser γ.leases L (mvcc.leaseItemsOf (mvcc.stateAfter log)) ∗
        putRequestIs p o ∗ mvcc.txnCtx ctx cd ∗ traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗
        □ (⌜o.ignoreLease = true⌝ -∗
          leaseOk L (putLeaseOf o (mvcc.findKey o.key (mvcc.stateAfter log)))) ∗
        □ (⌜needsPrev o = true → (mvcc.findKey o.key (mvcc.stateAfter log)).isSome⌝ -∗
          mvcc.certOk γ (log ++ [[putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))]])) ∗
        mvcc.csContract P f Pre Q Post ∗ mvcc.hookOk γ P f }}
      (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.Put))
        (Val #(GoInterface.ok ctx))) (Val #lg)) (Val #le)) (Val #kv)) (Val #p))
    {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
        mvcc.storeReader s γ ∗ ⌜trace ≠ null⌝ ∗
        (∃ te' : Bool, traceutil.ownTrace trace te') ∗ ⌜∀ t0, ot = some t0 → te = false → trace = t0⌝ ∗
        ((⌜o.leaseID ≠ W64 0 ∧ resp = null⌝ ∗
            errVarIs go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound err ∗ kvWriter s γ log ∗
            Pre ∗ lease.lessorUser γ.leases L (mvcc.leaseItemsOf (mvcc.stateAfter log))) ∨
         (⌜needsPrev o = true ∧ mvcc.findKey o.key (mvcc.stateAfter log) = none ∧ resp = null⌝ ∗
            errVarIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrKeyNotFound err ∗
            kvWriter s γ log ∗ Post ∗ lease.lessorUser γ.leases L (mvcc.leaseItemsOf (mvcc.stateAfter log))) ∨
         (⌜err = GoInterface.nil⌝ ∗
            putResponseIs resp (W64 (log.length : Int))
              (if o.base.prevKV then mvcc.findKey o.key (mvcc.stateAfter log) else none) ∗
            respHdrOwn (structFieldRef go_etcd_io.etcd.api.v3.etcdserverpb.PutResponse go!"Header" resp) ∗
            kvWriter s γ (log ++ [[putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))]]) ∗
            leaseOk L (putLeaseOf o (mvcc.findKey o.key (mvcc.stateAfter log))) ∗ Post ∗
            lease.lessorUser γ.leases L (mvcc.leaseItemsOf (mvcc.stateAfter
              (log ++ [[putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))]]))) ∗
            ⌜mvcc.stateAfter (log ++ [[putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))]]) =
              (applyTxnOp (W64 (log.length : Int)) (mvcc.stateAfter log) (putTxnOp o)).1⌝)) }} := by
  wp_start_folded as ⟨#Hkv, Hrd, Hsw, Hwt, #Hle, Hu, #Hp, #Hctx, #Hct, Hto, #Hl, #Hcok, Hcs, #Hhook⟩
  icases kvWriter_cert s γ log $$ Hsw with ⟨Hsw, #HF⟩
  iapply (put_soleWriter_floor hPut ctx cd lg le kv s γ p o log P Pre Q Post f L ot te hlen log)
    $$ [Hrd Hsw Hwt Hu Hto Hcs]
  · iframe # ∗
  inext
  iintro %resp %trace %err ⟨Hrd, %Ht, Htrc, %Hteq, Hout⟩
  iapply HΦ
  iframe Hrd Htrc
  isplitl []
  · ipureintro; exact Ht
  isplitr
  · ipureintro; exact Hteq
  icases Hout with (Hout | Hout | ⟨%Herr, Hout⟩)
  · ileft; iexact Hout
  · iright; ileft; iexact Hout
  · iright; iright
    isplitl []
    · ipureintro; exact Herr.1
    iexact Hout

/-- `deleteRange_soleWriter_of` with a floor `F` (a certified log): the delete, if committed, met
a log extending `F` (`pinned_floor`). -/
theorem deleteRange_soleWriter_floor (hDel : DeleteRange.spec (GF := GF) (hG := hG)) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (nd : Bool) (lg : Loc) (kv : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (dr : Loc) (o : OpFull)
    (log : mvcc.Log) (P Pre Q Post : IProp GF) (f : val) (ot : Option Loc) (te : Bool) (L : List w64)
    (hlen : log.length + 4 ≤ 2 ^ 63)
    (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
        isKV kv s γ ∗ mvcc.storeReader s γ ∗ kvWriter s γ log ∗ mvcc.storeWT γ ∗
        deleteRangeRequestIs dr o ∗ lease.leaseOwn γ.leases L (mvcc.leaseItemsOf (mvcc.stateAfter log)) ∗
        mvcc.txnCtx ctx cd ∗ traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗ (if nd then mvcc.neverDone cd else iprop(True)) ∗
        mvcc.certOkNext γ log (delChanges (mvcc.stateAfter log) o) ∗
        mvcc.csContract P f Pre Q Post ∗ mvcc.hookOk γ P f ∗ mvcc.idxCert γ.idx F }}
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
            kvWriter s γ (mvcc.commitLog log (delChanges (mvcc.stateAfter log) o)) ∗
            lease.leaseOwn γ.leases L (mvcc.leaseItemsOf (mvcc.stateAfter
              (mvcc.commitLog log (delChanges (mvcc.stateAfter log) o)))) ∗
            ⌜mvcc.stateAfter (mvcc.commitLog log (delChanges (mvcc.stateAfter log) o)) =
              (applyTxnOp (W64 (log.length : Int)) (mvcc.stateAfter log) (.delete o)).1⌝) ∨
         (⌜err ≠ GoInterface.nil ∧ o.base.prevKV = true ∧ resp = null ∧ nd = false⌝ ∗
           kvWriter s γ log ∗ lease.leaseOwn γ.leases L (mvcc.leaseItemsOf (mvcc.stateAfter log)))) }} := by
  wp_start_folded as ⟨#Hkv, Hrd, Hsw, Hwt, #Hdr, Hown, #Hctx, #Hct, Hto, #Hnd, #Hcok, Hcs, #Hhook, #HF⟩
  iunfold kvWriter at Hsw
  icases Hsw with ⟨Hsw, Hwl, Hfrag⟩
  icases soleWriter_split γ log hlen $$ Hsw with ⟨Htok, Hsw⟩
  -- the writer's hook: the hook's facts and the writer's fragment (D22 receiver epochs, S5b)
  ihave HhookW : mvcc.hookIs γ P f $$ [Hfrag]
  · iapply (mvcc.hookIs_split γ P f).2; iframe Hhook Hfrag
  iunfold soleWriterOpen at Hsw
  icases Hsw with ⟨#Hc, Htoks, %Hl2⟩
  have hsb : soleBudget log - 1 + 1 = soleBudget log := by unfold soleBudget; omega
  ihave ⟨%L0, #Hc0, %HL0⟩ := cert_join γ.idx log F $$ [$Hc $HF]
  iapply (hDel ctx cd nd lg kv s γ dr o (soleBudget log - 1) L0 P Pre Q Post f ot te log L _)
    $$ [Hrd Htok Hwt Htoks Hcs Hto Hwl HhookW Hown]
  · iframe # ∗
    isplitr
    · ipureintro; exact fun _ => ⟨hsb, hlen⟩
    isplitr
    · imodintro
      iintro %ilog %Hpin
      rw [(pinned_floor log F L0 ilog hlen HL0.1 HL0.2 Hpin).1]
      ipureintro; rfl
    imodintro
    iintro %ilog %Hpin
    rw [(pinned_floor log F L0 ilog hlen HL0.1 HL0.2 Hpin).1]
    iexact Hcok
  inext
  iintro %resp %trace %err ⟨Hrd, HhookW, Htoks, %Ht, HPost, Htrc, %Hteq, %ilog, %Hpi, Hout⟩
  icases (mvcc.hookIs_split γ P f).1 $$ HhookW with ⟨-, Hfrag⟩
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
  icases Hout with (⟨%Herr, #Hresp, Hhdr, #Hc', Htok, Hwl, Hown⟩ | ⟨%Hn, Htok, -, Hwl, Hown⟩)
  · -- deleted
    ileft
    isplitl []
    · ipureintro; exact ⟨Herr, hFl⟩
    iframe Hresp Hhdr Hown
    isplitl [Hsw Htok Hwl Hfrag]
    · iunfold kvWriter
      iframe Hwl Hfrag
      iapply soleWriter_close γ ilog _ hlen
      iframe Hsw Hc' Htok
    ipureintro; exact stateAfter_commit_delete ilog o
  · -- the context error
    iright
    isplitl []
    · ipureintro; exact Hn
    iframe Hown
    have h := soleWriter_close (GF := GF) γ ilog [] hlen
    simp only [mvcc.commitLog, ↓reduceIte] at h
    iunfold kvWriter
    iframe Hwl Hfrag
    iapply h
    iframe Hsw Htok Hc

/-- **`DeleteRange` at the sole writer of `log`**: the client's delete
on `log`'s state committed (no revision if nothing was deleted), the sole writer at the
committed log; or, with `PrevKv`, the range read's context error, the sole writer back. Under the
critical-section contract: `Post`. `deleteRange_soleWriter_floor` at the floor `log` itself
(`kvWriter_cert`). -/
theorem deleteRange_soleWriter_of (hDel : DeleteRange.spec (GF := GF) (hG := hG)) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (nd : Bool) (lg : Loc) (kv : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (dr : Loc) (o : OpFull)
    (log : mvcc.Log) (P Pre Q Post : IProp GF) (f : val) (ot : Option Loc) (te : Bool) (L : List w64)
    (hlen : log.length + 4 ≤ 2 ^ 63) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
        isKV kv s γ ∗ mvcc.storeReader s γ ∗ kvWriter s γ log ∗ mvcc.storeWT γ ∗
        deleteRangeRequestIs dr o ∗ lease.leaseOwn γ.leases L (mvcc.leaseItemsOf (mvcc.stateAfter log)) ∗
        mvcc.txnCtx ctx cd ∗ traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗ (if nd then mvcc.neverDone cd else iprop(True)) ∗
        mvcc.certOkNext γ log (delChanges (mvcc.stateAfter log) o) ∗
        mvcc.csContract P f Pre Q Post ∗ mvcc.hookOk γ P f }}
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
            kvWriter s γ (mvcc.commitLog log (delChanges (mvcc.stateAfter log) o)) ∗
            lease.leaseOwn γ.leases L (mvcc.leaseItemsOf (mvcc.stateAfter
              (mvcc.commitLog log (delChanges (mvcc.stateAfter log) o)))) ∗
            ⌜mvcc.stateAfter (mvcc.commitLog log (delChanges (mvcc.stateAfter log) o)) =
              (applyTxnOp (W64 (log.length : Int)) (mvcc.stateAfter log) (.delete o)).1⌝) ∨
         (⌜err ≠ GoInterface.nil ∧ o.base.prevKV = true ∧ resp = null ∧ nd = false⌝ ∗
           kvWriter s γ log ∗ lease.leaseOwn γ.leases L (mvcc.leaseItemsOf (mvcc.stateAfter log)))) }} := by
  wp_start_folded as ⟨#Hkv, Hrd, Hsw, Hwt, #Hdr, Hown, #Hctx, #Hct, Hto, #Hnd, #Hcok, Hcs, #Hhook⟩
  icases kvWriter_cert s γ log $$ Hsw with ⟨Hsw, #HF⟩
  iapply (deleteRange_soleWriter_floor hDel ctx cd nd lg kv s γ dr o log P Pre Q Post f ot te L hlen
    log) $$ [Hrd Hsw Hwt Hto Hcs Hown]
  · iframe # ∗
  inext
  iintro %resp %trace %err ⟨Hrd, %Ht, HPost, Htrc, %Hteq, Hout⟩
  iapply HΦ
  iframe Hrd HPost Htrc
  isplitl []
  · ipureintro; exact Ht
  isplitr
  · ipureintro; exact Hteq
  icases Hout with (⟨%Herr, Hout⟩ | Hout)
  · ileft
    isplitl []
    · ipureintro; exact Herr.1
    iexact Hout
  · iright; iexact Hout

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
