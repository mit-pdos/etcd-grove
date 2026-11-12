/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart). (Strict M1, 2026-11-05: over
mvcc's API, `KV.Compact.contract` and `KV.Range.contract` at the KV's type, from `shapes.law`.)
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__Compaction
public import Spec.context.TODO
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.EnsureTrace
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.WriteLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ApiLemmas
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.EtcdBackend

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3
open mvcc.api (MvccState)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- A range's result that is not `nil` is owned (whichever outcome; `CountOnly` false). -/
private theorem rangeOutcomeC_res (r : Loc) (err : GoInterface) (log : mvcc.Log) (rev : w64) (c : Int)
    (en : Bool) (k e : GoString) (ro : go_etcd_io.etcd.server.v3.storage.mvcc.RangeOptions)
    (hro : ro.CountOnly' = false) (hr : r ≠ null) :
    mvcc.rangeOutcomeC (GF := GF) r err log rev c en k e ro ⊢
      ∃ v : go_etcd_io.etcd.server.v3.storage.mvcc.RangeResult, r ↦ v := by
  unfold mvcc.rangeOutcomeC mvcc.rangeOutcome
  simp only [hro, Bool.false_eq_true, ↓reduceIte]
  iintro (⟨-, -, H⟩ | ⟨-, (⟨-, -, H⟩ | ⟨-, -, %Hn, -⟩ | ⟨-, -, %kvs, H, -⟩)⟩)
  · iexists _; iexact H
  · iexists _; iexact H
  · exact absurd Hn hr
  · iexists _; iexact H

theorem apply.applierV3backend.Compaction.wp_proof
    (hTODO : context.TODO.spec (GF := GF) (hG := hG))
    (hEnsure : traceutil.EnsureTrace.spec (GF := GF) (hG := hG))
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG)) :
    apply.applierV3backend.Compaction.spec (GF := GF) (hG := hG) := by
  intro E p cr rev log crev Pre Q Post info
  wp_start as ⟨#Hb, #Hcr, %Hadm, HCp, Htt, Hpre, Hc⟩
  iunfold apply.applyTok at Htt
  icases Htt with Hmr
  iunfold apply.backendIs at Hb
  icases Hb with ⟨%opts, #Hopts, #Hok⟩
  ihave #Hok' := Hok
  iunfold apply.backendOptsOk at Hok'
  icases Hok' with ⟨#Hlg, #Hkv, %HkvE, #Haus, -⟩
  iunfold apply.mPre at Hpre
  icases Hpre with ⟨⟨%cr0, Hw⟩, Hll, Hrd, -, %B, Hbk, #Hhk, Htie, Hcs⟩
  iunfold apply.cmpOwn at Hc
  icases Hc with ⟨Hopen, Hcro⟩
  icases apply.wSt_crOwn_agree E.γs log cr0 crev $$ [$Hw $Hcro] with ⟨%Hcc, Hw, Hcro⟩
  subst cr0
  iunfold apply.envAus at Haus
  icases Haus with ⟨-, #HauR, -, #HauC, -⟩
  iunfold srvApi.csContractA at Hcs
  icases Hcs with ⟨HPre, Hhr, Hfin⟩
  iunfold apply.compactionIs at Hcr
  icases Hcr with ⟨%Hcrn, #Hrev⟩
  iStructNamed Hopts
  wp_auto
  ihave ⟨Hresp0, %Hrespn⟩ := typedPointsto_not_null_dup _ _ _ $$ «$r0»
  wp_apply hTODO
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨Hfl, Hflc⟩
  wp_auto
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  ihave #HlgN := zapLoggerOk_orNil _ $$ Hlg
  wp_apply hEnsure todoCtxVal mvcc.neverCd none false opts.Logger' _ _ $$ [Hfl Hflc $HlgN]
    as %ctx2 %trc ⟨⟨%Htrcnn, -⟩, Htrc, #Hct2, -, %vs2, #Hctx2t, -⟩
  · isplitr
    · iapply mvcc.txnCtx_todo
    isplitr
    · iapply traceutil.ctxTraceIs_todo
    isplitr
    · unfold traceutil.ownTraceOpt; itrivial
    iunfold traceutil.ownFields
    iexists _
    iframe Hfl Hflc
    ipureintro
    exact traceutil.fieldsWf_cons_int _ _ _ (.int64 _) _ traceutil.fieldsWf_nil
  -- `a.kv.Compact(trace, rev)`: `KV.Compact.contract` at the KV's type, by the builder's update
  iunfold apply.isApplyKV at Hkv
  icases Hkv with #Hkv
  icases txn.isMvcc_shape hsh opts.KV' E.γ $$ Hkv with ⟨%Hsh, -⟩
  obtain ⟨kty, kvv, Hkveq, -, -, -, -, hRangeC, -, -, hCompactC, -⟩ := Hsh
  ihave #Hmi : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  ihave Hinit : (go_etcd_io.etcd.server.v3.storage.mvcc.mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hmi
  icases Hinit with ⟨-, ⟨%ec, #HeC⟩, -⟩
  ihave Hau := HauC $$ %log %crev %rev %Hadm.2 Hw Hcro HCp
  iunfold srvApi.auCompact at Hau
  ihave #Hcq : mvcc.api.storageReq B (E.Pk B) iprop(True) iprop(True) $$ []
  · rw [mvcc.api.etcdStorage_req]; iapply backend.commitReq_true
  ihave Hkv' : □ mvcc.api.isMvcc (interface.mkOk kty kvv) E.γ $$ []
  · rw [← Hkveq]; imodintro; iexact Hkv
  icases Hkv' with #Hkv'
  rw [Hkveq]
  simp only [interface.mkOk]
  wp_apply (hCompactC E.γ trc false rev 1 B (E.Pk B) E.f Pre Q Post iprop(True) iprop(True) _)
    $$ [$Hkv' $Hopen $Htrc $Hbk $HPre $Hhr $Hfin $Hau]
    as %ch %err ⟨Hopen, Htrc, Hbk, %σ, ⟨%Hσ, Hw, Hcro⟩, Hout⟩
  · iframe #
    isplitr
    · ipureintro; exact Htrcnn
    ipureintro; exact Hadm.1
  subst Hσ
  have hrv : ((srvApi.stAt log crev).rev : Int) = (log.length : Int) - 1 := by
    have := Hadm.1; have := Hadm.2
    simp only [srvApi.stAt, mvcc.api.MvccState.rev]; omega
  have hcrv : (srvApi.stAt log crev).crev = crev := rfl
  icases Hout with (⟨⟨%Herr, %Hlt, -⟩, HPost, -, Hch⟩ | ⟨%Hle, #Herr, HPre, -, -⟩ |
    ⟨⟨%Hfut, -⟩, -, -, -⟩)
  · -- compacted: `KV.Range(ctx, "compaction", nil, {})` for the header
    subst Herr
    rw [hcrv] at Hlt
    wp_auto
    -- the context `EnsureTrace` returned is never done (`TODO`'s, with the trace)
    ihave #Hnd : mvcc.neverDone
        ({ Values := vs2, Deadline := none, Done_gn := ⟨0, 0⟩, PDone := iprop(False) } :
          context.ContextDesc (IProp GF)) $$ []
    · unfold mvcc.neverDone; imodintro; iintro H; iexact H
    ihave #Hnd' : iprop(if true = true then mvcc.neverDone
        ({ Values := vs2, Deadline := none, Done_gn := ⟨0, 0⟩, PDone := iprop(False) } :
          context.ContextDesc (IProp GF)) else iprop(True)) $$ []
    · simp only [↓reduceIte]; iexact Hnd
    ihave ⟨%td, %Htd, #Hrc⟩ := mvcc.txnCtx_rangeCtx true ctx2 _ $$ Hctx2t Hnd'
    have htd : td = true := Htd rfl
    subst htd
    have hra : apply.cmpRevAfter crev rev = sint.Z rev := by
      unfold apply.cmpRevAfter; simp [Hlt]
    ihave HauR' := HauR $$ %log %(apply.cmpRevAfter crev rev)
      %(srvApi.wSt E.γs log (apply.cmpRevAfter crev rev)) Hw []
    · iintro Hw; iexact Hw
    iunfold srvApi.auRead at HauR'
    wp_apply wp_string_to_bytes as %ksl ⟨Hks, -⟩
    imod ownSlice_persist _ _ _ $$ Hks with #Hks
    ihave #Hes : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
    · iapply ownSlice_nil
    wp_apply (hRangeC E.γ ctx2 _ true ksl slice.nil _ []
        (zero_val go_etcd_io.etcd.server.v3.storage.mvcc.RangeOptions) _)
      $$ [$Hkv' $Hmr $HauR']
      as %rr %rerr ⟨Hmr, %Hrrn, %σr, ⟨-, Hw⟩, Hrout, -⟩
    · iframe #
    ihave ⟨%rv0, Hrr⟩ := rangeOutcomeC_res rr rerr σr.log _ σr.crev _ _ _ _ rfl (Hrrn rfl) $$ Hrout
    wp_auto
    iapply HΦ
    iunfold apply.applyTok
    iframe Hmr
    isplitl [Hw Htie Hbk Hll Hrd]
    · iapply (apply.kvOwn_of_split E log B (apply.cmpRevAfter crev rev))
      iframe Hw Htie
      iunfold apply.kvRest; iframe Hbk Hll Hrd Hhk
    isplitl [HPost]
    · ileft; iexact HPost
    isplitl [Hopen Hcro]
    · iunfold apply.cmpOwn; iframe
    isplitl [Hresp0 «$r0» Htrc]
    · simp only [apply.cmpAnswerIs, apply.chainCompacts, ↓reduceIte]
      ileft
      isplitr
      · ipureintro; simp [Hlt]
      isplitr [Htrc]
      · iunfold apply.cmpRespOk
        isplitr
        · ipureintro; exact Hrespn
        iexists _
        iframe Hresp0
        iexists _
        iframe «$r0»
      · iunfold apply.traceRes; iright; iexists false; iexact Htrc
    · iunfold apply.cmpChan; iintro -; iexact Hch
  · -- `ErrCompacted`: no response, no trace
    rw [hcrv] at Hle
    icombine HeC Herr gives %Hee
    subst Hee
    wp_auto
    have hra : apply.cmpRevAfter crev rev = crev := by
      unfold apply.cmpRevAfter; split <;> omega
    iapply HΦ
    iunfold apply.applyTok
    iframe Hmr
    isplitl [Hw Htie Hbk Hll Hrd]
    · iapply (apply.kvOwn_of_split E log B (apply.cmpRevAfter crev rev))
      iframe Hw Htie
      iunfold apply.kvRest; iframe Hbk Hll Hrd Hhk
    isplitl [HPre]
    · iright; iexact HPre
    isplitl [Hopen Hcro]
    · iunfold apply.cmpOwn; iframe
    isplitr
    · simp only [apply.cmpAnswerIs, apply.chainCompacts, ↓reduceIte]
      iright
      isplitr
      · ipureintro; refine ⟨Hle, ?_, ?_, ?_⟩ <;> simp
      iunfold txn.errVarIs; iexists ec; iframe HeC; ipureintro; rfl
    · iunfold apply.cmpChan; iintro %Hlt; exact absurd Hlt (by omega)
  · -- `ErrFutureRev`: excluded, the revision is the log's
    exfalso
    rw [hrv] at Hfut
    have := Hadm.2
    have := Hadm.1
    omega

end proof

end EtcdGrove
end Perennial
