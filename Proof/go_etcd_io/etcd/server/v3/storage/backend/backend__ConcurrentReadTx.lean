/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__ConcurrentReadTx.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__ConcurrentReadTx
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ReadLemmas
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.txReadBuffer__unsafeCopy

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- The read buffer a new `ConcurrentReadTx` copies: read-only for good, version 0, reading as
the readers' state `rv` (over its committed data). -/
def backend.crtBuf (P : BParams) (rv : RView) (bufp : Loc) : IProp GF :=
  iprop(∃ (c : txReadBuffer) (Pc : BksPhys) (bks : GMap w64 (List Ent)),
    bufp ↦□ c ∗ bksAt c.txBuffer'.buckets' DFrac.discard Pc bks ∗
    ⌜c.bufVersion' = W64 0 ∧ (⟨bks, W64 0⟩ : RBuf).Wf ∧ idsOk P bks ∧
      vData P (rv.1, ⟨bks, W64 0⟩) = vData P rv⌝)

instance backend.crtBuf_persistent (P : BParams) (rv : RView) (bufp : Loc) :
    Persistent (crtBuf (GF := GF) P rv bufp) := by
  unfold crtBuf; infer_instance

/-- The new transaction's copy, ready: a fresh copy made read-only for good and marked in the
cache, or the cache's own copy (of a state up to the current one, valid by `cacheValid`). -/
theorem backend.crtBuf_ready (γ : BNames) (P : BParams) (rv : RView) (idx : Nat) (win : Bool) (q : Qp)
    (vd : VData) (bufp : Loc) (hwf : rv.2.Wf ∧ idsOk P rv.2.bks) :
    cacheInv (GF := GF) γ ∗ ghostVar γ.cur sync.rfrac.half ((rv.2.ver, idx), win) ∗
      bView γ q vd ∗ histAt γ rv.2.ver idx rv ∗ cacheValid γ P rv idx ∗
      ((∃ (c : txReadBuffer) (Pc : BksPhys), bufp ↦ c ∗
          bksAt c.txBuffer'.buckets' (DFrac.own 1) Pc rv.2.bks ∗ ⌜c.bufVersion' = W64 0⌝) ∨
        cacheEnt γ P bufp rv.2.ver) ⊢
    |={⊤}=> (crtBuf P rv bufp ∗ cacheEnt γ P bufp rv.2.ver ∗
      ghostVar γ.cur sync.rfrac.half ((rv.2.ver, idx), win) ∗ bView γ q vd) := by
  iintro ⟨#Hci, Hcur, Hbv, #Hha, #Hcv, Hnew⟩
  icases Hnew with (⟨%c, %Pc, Hbp, Hbks, %Hc0⟩ | #Hce)
  · ipersist Hbp
    imod bksAt_persist _ _ _ $$ Hbks with #Hbks
    imod cache_mark γ sync.rfrac.half q rv.2.ver idx win vd $$ [$Hci $Hcur $Hbv]
      with ⟨#Hmk, Hcur, Hbv, %Hwin⟩
    imodintro
    iframe
    isplitr
    · unfold crtBuf
      iexists c, Pc, rv.2.bks
      iframe #
      ipureintro
      exact ⟨Hc0, fun id es h => hwf.1 id es h, hwf.2, rfl⟩
    unfold cacheEnt
    iexists c, Pc, idx, rv
    iframe #
    ipureintro; exact ⟨hwf.1, hwf.2, Hc0⟩
  · ihave #Hce' := Hce
    iunfold cacheEnt at Hce'
    icases Hce' with ⟨%c, %Pc, %i, %rvc, #Hbp, #Hbks, #Hh, #Hm, %Hfc⟩
    imod cache_lookup γ sync.rfrac.half rv.2.ver idx i win $$ [$Hci $Hcur $Hm] with ⟨Hcur, %Hi⟩
    iunfold cacheValid at Hcv
    ihave %Hval := Hcv $$ %i %rvc %Hi Hh Hm
    imodintro
    iframe
    iframe #
    unfold crtBuf
    iexists c, Pc, rvc.2.bks
    iframe #
    ipureintro
    exact ⟨Hfc.2.2, fun id es h => Hfc.1 id es h, Hfc.2.1, Hval⟩

theorem backend.backend.ConcurrentReadTx.wp_proof
    (hcopy : backend.txReadBuffer.unsafeCopy.spec (GF := GF) (hG := hG)) :
    backend.backend.ConcurrentReadTx.spec (GF := GF) (hG := hG) := by
  intro γ P WR b q qo vd
  wp_start as ⟨#Hb, Htok, Hbv, Hopen⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold rdTok
  icases Htok with ⟨%rt, #Hrt, Hmu, Hcr⟩
  ihave #Hb' := Hb
  unfold isBackend
  icases Hb' with ⟨%t, %rt2, %tm, %db, %lg, %h, -, #Hrt2, -, -, -, -, -, #Htm, -, -, -, #Hg,
    #Hcm, #Hci, -, -, -, %HPwf⟩
  icombine Hrt Hrt2 gives %Heq
  subst Heq
  wp_apply wp_with_defer as %defer defer
  -- `b.readTx.RLock()`
  wp_method_call
  wp_auto
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$Hmu] as ⟨Hrl, HP⟩
  wp_pure
  unfold rtRes rtResAt rtRest rtCore rtIntv
  icases HP with ⟨%rd, %rv, %H, %m, %Pb, %cm, Hrb, %Hok, Hcmf, Hview, Hrd, Hrvs, Hcur, Hhist,
    Hrtxf, Hwgf, %Hf, #Hha, #Hcv, Hpo, #Hauth, Hiv⟩
  cases hl : rd.live
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hiv with ⟨-, #Hst⟩
    iexfalso
    iapply bOpen_stopped γ qo $$ [$Hopen $Hst]
  simp only [↓reduceIte]
  icases Hiv with ⟨Hlive, #Hsnap, #Hintv, #Hwgi, Hwo, Htk⟩
  wp_auto
  -- `b.readTx.txWg.Add(1)`
  unfold crTok
  icases Hcr with ⟨%rt3, %tm3, #Hrt3, #Htm3, Hown, Hrdt⟩
  icombine Hrt Hrt3 gives %Heq
  subst Heq
  icombine Htm Htm3 gives %Heq
  subst Heq
  wp_apply wp_rdAdd γ rd.rtx rd.wg rd.γw rd.γo rd.γt sync.rfrac $$ [$Hwgi $Hwo $Hrdt]
    as ⟨%k, %qr, Hwo, Hsh⟩
  -- the cache
  wp_apply sync.Mutex.wp_Lock $$ [$Hcm] as ⟨Hml, HC⟩
  unfold cacheRes
  icases HC with ⟨%bp, %cver, Hcb, Hcv0, HCc⟩
  unfold rbAt
  icases Hrb with ⟨Hrbt, Hrbv, Hrbb⟩
  wp_auto
  wp_join iprop(∃ (bufp bpc : Loc) (vc : w64), buf_ptr ↦ bufp ∗
      ((∃ (c : txReadBuffer) (Pc : BksPhys), bufp ↦ c ∗
          bksAt c.txBuffer'.buckets' (DFrac.own 1) Pc rv.2.bks ∗ ⌜c.bufVersion' = W64 0⌝) ∨
        cacheEnt γ P bufp rv.2.ver) ∗
      cbufOf b ↦ bpc ∗ cverOf b ↦ vc ∗
      (⌜bpc = Loc.null⌝ ∨ cacheEnt γ P bpc vc) ∗ sync.ownMutex (cmuOf b) ∗
      rbAt (rbufOf (baseOf rt)) (DFrac.own sync.rfrac) m Pb rv.2 ∗ b_ptr ↦ b)
    with [buf Hcb Hcv0 HCc Hml Hrbt Hrbv Hrbb b isStaleCache curCache]
    as ⟨%bufp, %bpc, %vc, buf, Hnew, Hcb, Hcv0, HCc, Hml, Hrb, b⟩
  · -- an empty cache: a copy of the read buffer
    ihave Hrb : rbAt (rbufOf (baseOf rt)) (DFrac.own sync.rfrac) m Pb rv.2 $$ [Hrbt Hrbv Hrbb]
    · unfold rbAt; iframe
    wp_apply hcopy $$ [$Hrb] as %c ⟨Hrb, %Hc0, %Pc, Hbks⟩
    wp_join_done
    iexists curBuf_ptr, bp, cver
    iframe
    ileft
    iexists c, Pc
    iframe
    ipureintro; exact Hc0
  · have Hnull := Hif
    wp_if_destruct
    · -- a stale cache: a copy, outside the cache's lock
      wp_apply sync.Mutex.wp_Unlock $$ [$Hcm $Hml Hcb Hcv0 HCc]
      · iexists bp, cver; iframe
      ihave Hrb : rbAt (rbufOf (baseOf rt)) (DFrac.own sync.rfrac) m Pb rv.2 $$ [Hrbt Hrbv Hrbb]
      · unfold rbAt; iframe
      wp_apply hcopy $$ [$Hrb] as %c ⟨Hrb, %Hc0, %Pc, Hbks⟩
      wp_apply sync.Mutex.wp_Lock $$ [$Hcm] as ⟨Hml, HC⟩
      icases HC with ⟨%bp2, %cver2, Hcb, Hcv0, HCc⟩
      wp_join_done
      iexists curBuf_ptr, bp2, cver2
      iframe
      ileft
      iexists c, Pc
      iframe
      ipureintro; exact Hc0
    · -- the cache is current
      have hbp : bp ≠ Loc.null := by intro h; apply Hnull; simp [h]
      have hcv : cver = rv.2.ver := by
        cases h : decide (cver = rv.2.ver)
        · rw [h] at Hif; simp at Hif
        · exact of_decide_eq_true h
      icases HCc with (%Hn | #HCe)
      · exact absurd Hn hbp
      wp_join_done
      iexists bp, bp, cver
      iframe
      isplitr
      · iright; rw [← hcv]; iexact HCe
      isplitl []
      · iright; iexact HCe
      unfold rbAt; iframe
  imod crtBuf_ready γ P rv rd.idx rd.win q vd bufp ⟨Hf.1, Hf.2.1⟩
    $$ [$Hci $Hcur $Hbv $Hha $Hcv $Hnew] with ⟨#Hcrt, #Hce, Hcur, Hbv⟩
  -- the cache updated, if no one changed it meanwhile
  wp_join iprop(∃ (bpc : Loc) (vc : w64), cbufOf b ↦ bpc ∗ cverOf b ↦ vc ∗
      (⌜bpc = Loc.null⌝ ∨ cacheEnt γ P bpc vc) ∗ b_ptr ↦ b ∗ buf_ptr ↦ bufp)
    with [Hcb Hcv0 HCc buf b curBufVer curCacheVer]
    as ⟨%bpc', %vc', Hcb, Hcv0, HCc, b, buf⟩
  · iexists bufp, rv.2.ver
    iframe
    iright; iexact Hce
  · wp_if_destruct
    · wp_join_done
      iexists bufp, rv.2.ver
      iframe
      iright; iexact Hce
    · wp_join_done
  wp_apply sync.Mutex.wp_Unlock $$ [$Hcm $Hml Hcb Hcv0 HCc]
  · iexists bpc', vc'; iframe
  -- the new transaction
  iunfold crtBuf at Hcrt
  icases Hcrt with ⟨%c, %Pc, %bks, #Hbp, #Hbks, %Hcf⟩
  wp_auto
  wp_alloc crt as Hcrt
  -- the transaction's fields, read-only for good
  iStructNamed Hcrt
  iStructNamed baseReadTx
  iStructNamed buf
  ipersist txBuffer
  ipersist bufVersion
  ipersist txMu
  ipersist tx
  ipersist buckets
  ipersist txWg
  wp_auto
  -- the deferred `b.readTx.RUnlock()`
  wp_method_call
  wp_auto
  unfold bView
  icases Hbv with ⟨Hbv, Hcw⟩
  icombine Hbv Hview gives %Hvd0
  have Hvd := Hvd0.2
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hrb Hcmf Hview Hrd Hrvs Hcur Hhist Hrtxf Hwgf Hpo
      Hlive Hwo Htk] as Hmu
  · inext
    iexists rd, rv, H, m, Pb, cm
    rw [hl]
    simp only [↓reduceIte]
    unfold rbAt at *
    iframe; iframe #
    ipureintro; exact ⟨Hok, Hf⟩
  obtain ⟨Hc0, Hbwf, Hbids, Hbv'⟩ := Hcf
  iapply HΦ
  iframe Hopen
  isplitl [Hown Hsh]
  · unfold crtSnap
    iexists c.txBuffer'.buckets', Pc, cm, tm, rd.wg, rd.γw, rd.γo, rd.γt, k, qr, rt
    unfold rbAt
    rw [show ((rv.1, (⟨bks, W64 0⟩ : RBuf)) : RView).2.ver = c.bufVersion' by rw [Hc0]]
    iframe; iframe #
    ipureintro; exact ⟨Hbwf, Hbids, HPwf⟩
  isplitr
  · ipureintro; rw [Hbv']; exact Hvd.symm
  isplitl [Hmu]
  · iintro Hcr
    iexists rt
    iframe; iframe #
  iframe


end proof

end EtcdGrove
end Perennial
