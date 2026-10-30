/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watcher__Watch.lean` (the watch slice's unit W-C).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watcher__Watch
public import Spec.go_etcd_io.etcd.client.v3.watcher__newWatcherGRPCStream
public import Spec.go_etcd_io.etcd.client.v3.streamKeyFromCtx
public import Spec.go_etcd_io.etcd.client.v3.OpWatch
public import Proof.go_etcd_io.etcd.client.v3.WatchApiLemmas
public import Proof.go_etcd_io.etcd.client.v3.WatchFire
public import Proof.go_etcd_io.etcd.client.v3.WatchCompl

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

set_option maxHeartbeats 0 in
theorem watcher.Watch.wp_proof
    (wp_OpWatch : OpWatch.spec (GF := GF) (hG := hG))
    (wp_key : streamKeyFromCtx.spec (GF := GF) (hG := hG))
    (wp_newStream : watcher.newWatcherGRPCStream.spec (GF := GF) (hG := hG)) :
    watcher.Watch.spec (GF := GF) (hG := hG) := by
  intro w V γ ctx cs key sl gs rev Q n
  wp_start as ⟨#Hw, %Hkst, #Hctx, #Hopts, %Hreq, #Hbound, #Hau⟩
  obtain ⟨Hrw, Hnp, Hrev1⟩ := Hreq
  have Hrev : 0 ≤ sint.Z rev := by omega
  -- (D47) a first firing of the read update (at the start log), for the responses that report nothing
  ihave #Hw0 := Hw
  iunfold isClientWatcher at Hw0
  icases Hw0 with ⟨%callSl0, %vs0, -, -, -, -, -, -, -, #Hf0, -⟩
  iunfold watchSrvFacts at Hf0
  icases Hf0 with ⟨-, #Hcf0⟩
  ihave ⟨#Hmf0, -⟩ := watchConnFacts_cur V $$ Hcf0
  iunfold watchMemberFacts at Hmf0
  icases Hmf0 with ⟨-, -, -, -, #Hkf0, -⟩
  iunfold srvKVFacts at Hkf0
  icases Hkf0 with ⟨%γr0, #Hinvs0, #H00, %Hkr0⟩
  imod (watch_fire V.R.E γr0 γ (by rw [Hkr0.1, Hkst]) Hkr0.2.1 [[], []] Q) $$ Hinvs0 H00 H00 [] Hau
    with ⟨%C0, #HQ0, -⟩
  · unfold mvcc.certOk; ileft; ipureintro; simp
  -- (G2) the watch's events are of its range with an empty key read as `"\x00"`, which the
  -- server registers exactly
  have hcpl : cplCond true (opWatchModel key gs).watchNorm rev = true := by
    rw [cplCond_iff]
    refine ⟨rfl, rangeExact_of_ne _ _ (OpFull.watchNorm_key_ne _), ?_⟩
    intro h; rw [h] at Hrev1; simp at Hrev1
  have HrwN : (opWatchModel key gs).watchNorm.isRangeWatch rev = true := by
    rw [isRangeWatch_watchNorm]; exact Hrw
  have HnpN : ¬ (opWatchModel key gs).watchNorm.watchPanics := by
    rw [OpFull.watchNorm_watchPanics]; exact Hnp
  have HbaseN := OpFull.watchNorm_base (opWatchModel key gs)
  ihave #Hsrd : startOk V true rev $$ []
  · unfold startOk; itrivial
  ihave #Hw' := Hw
  iunfold isClientWatcher at Hw'
  icases Hw' with ⟨%callSl, %vs, %Hwnn, #Hrem, #Hco, #Hvs, #Hok, #Hlg, #Hmu, #Hf, %Hlgb⟩
  obtain ⟨Hlgnn, Hb⟩ := Hlgb
  wp_auto
  wp_apply wp_OpWatch key sl gs $$ [] as %op #Hop
  · iframe #; ipureintro; exact Hnp
  iunfold opFullAt at Hop
  icases Hop with ⟨#Hopat, #Hkeysl, %Hof, #Hvalsl, #Hsort⟩
  iunfold opAt at Hopat
  icases Hopat with ⟨%Hfields, #Hendsl⟩
  have Hrw' := Hrw
  unfold OpFull.isRangeWatch at Hrw'
  simp only [decide_eq_true_eq] at Hrw'
  obtain ⟨Ht1, Hrv, Hpk, Hfr, Hfp, Hfd⟩ := Hrw'
  obtain ⟨-, Hfpk, -, -, -, -, -, -, Hffr, Hfcn, Hffp, Hffd, Hfrev, -, Hfpn⟩ := Hfields
  rw [Hffp, Hfp]
  wp_auto
  rw [Hffd, Hfd]
  wp_auto
  wp_apply wp_bytes_to_string op.key' (opWatchModel key gs).key DFrac.discard $$ [$Hkeysl] as -
  wp_apply wp_bytes_to_string op.end' (opWatchModel key gs).base.rangeEnd DFrac.discard $$ [$Hendsl] as -
  wp_apply chan.wp_make2 (V := Loc) (W64 1) as %retc %γret ⟨#Hretc, %Hcap, Hreto⟩
  · ipureintro; word
  -- the watch's values: its events' range, the request's own key and range end, the bound
  let P0 : WsPrm GF := ⟨(opWatchModel key gs).watchNorm, rev, ctx, cs, (opWatchModel key gs).key,
    (opWatchModel key gs).base.rangeEnd, op.createdNotify', op.progressNotify',
    op.watchBufLogEnabled', zero_val GoSlice, retc, γret, null, ⟨⟨γret, 0, 0⟩, 0, 0, false⟩, null,
    null, ⟨γret, 0, 0⟩, 0, 0, 0, true, 0, γ, Q, n, if V.nm = 1 then n else 0⟩
  imod wsBdOk_intro V P0 rfl $$ Hbound with #Hbd
  -- the spec's row is the watch's (`wsRow_eq`)
  have hrow : iprop(□ (⌜V.nm = 1⌝ → watchCheckOk (V.mem 0).2.γ (V.mem 0).2.s V.conn
      (GoInterface.ok ctx) n (opWatchModel key gs).key (opWatchModel key gs).base.rangeEnd)) =
      wsRow (GF := GF) V P0 := (wsRow_eq V P0).symm
  imod start_bag (retcP V (opWatchModel key gs).watchNorm rev true Q (wsRow V P0)) _ retc γret
    (by trivial) $$ Hretc Hreto with #Hbret
  irename ctx => Hctxp
  icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨«$r0», %Hwrnn⟩
  iStructNamed «$r0»
  irename : iprop("_" ∷ True) => Hjunk
  iclear Hjunk
  ipersist ctx
  ipersist key
  ipersist end'
  ipersist rev
  ipersist createdNotify
  ipersist progressNotify
  ipersist fragment
  ipersist watchBufLogEnabled
  ipersist filters
  ipersist prevKV
  ipersist retc
  have HrevEq : op.rev' = rev := Hfrev.trans Hrv
  rw [HrevEq] at *
  rw [Hffr, Hfr] at *
  rw [Hfpk, Hpk] at *
  ihave #HreqP : reqP V (streamKeyOf (metadata.outgoingOf (GoInterface.ok ctx)))
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.watchRequest.ty)
      #«$r0_ptr») $$ []
  · unfold reqP
    ileft
    iexists «$r0_ptr», P0
    isplitr
    · ipureintro; exact ⟨rfl, Hwrnn⟩
    unfold wrRO
    iframe #
    isplitr
    · iapply ownSlice_nil
    isplitr
    · ipureintro
      refine ⟨HrwN, HnpN, Hrev, (OpFull.watchNorm_key _).symm, by rw [HbaseN], ?_, ?_⟩
      · rw [HbaseN]; exact Hfcn
      · rw [HbaseN]; exact Hfpn
    isplitr
    · unfold wsAu; iexact Hau
    isplitr
    · ipureintro; exact ⟨Hkst.symm, hcpl⟩
    ipureintro; rfl
  wp_apply wp_key ctx cs
  · iexact Hctx
  ihave Hinv : iprop(∃ (b : Bool) (cc : Loc), "ok" ∷ ok_ptr ↦ b ∗
      "closeCh" ∷ closeCh_ptr ↦ cc ∗
      "Hcc" ∷ closeChRes (opWatchModel key gs).watchNorm Q (wsRow V P0) rev
        (cplCond true (opWatchModel key gs).watchNorm rev) cc) $$ [ok closeCh]
  · iexists false, _
    iframe
    unfold closeChRes
    ileft; ipureintro; rfl
  wp_for
  icases Hinv with ⟨%b, %cc, ok, closeCh, Hcc⟩
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold watcherMu at HR
  icases HR with ⟨%m, Hst, HM⟩
  wp_auto
  icases HM with (%Hnil | ⟨%M, HM, #HMs⟩)
  · subst Hnil
    simp only [show (null : Loc) = map.nil from rfl, _root_.decide_true]
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hst]
    · inext; unfold watcherMu; iexists map.nil; iframe Hst; ileft; ipureintro; rfl
    wp_apply chan.wp_make1 (V := go_etcd_io.etcd.client.v3.WatchResponse) as %ch %γch ⟨#Hch, %-, Hcho⟩
    imod watch_spsc_alloc (opWatchModel key gs).watchNorm Q (wsRow V P0) rev
      (cplCond true (opWatchModel key gs).watchNorm rev) ch γch $$ Hch [Hcho]
      with ⟨%γw, #Hs, Hp, -, Hc, #Hi0, #Hi02, %Hc2⟩
    · ileft; iexact Hcho
    wp_apply wp_spsc_close γw.spsc ch _ (fun _ => iprop(True)) [] $$ [$Hs $Hp]
    wp_for_post
    iapply HΦ
    rw [hrow]
    iapply watch_post
    iframe Hc
    iframe #
  by_cases hm : m = map.nil
  · simp only [hm, _root_.decide_true]
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hst HM]
    · inext; unfold watcherMu; iexists map.nil; iframe Hst; iright; iexists M; iframe HM; iframe #
    wp_apply chan.wp_make1 (V := go_etcd_io.etcd.client.v3.WatchResponse) as %ch %γch ⟨#Hch, %-, Hcho⟩
    imod watch_spsc_alloc (opWatchModel key gs).watchNorm Q (wsRow V P0) rev
      (cplCond true (opWatchModel key gs).watchNorm rev) ch γch $$ Hch [Hcho]
      with ⟨%γw, #Hs, Hp, -, Hc, #Hi0, #Hi02, %Hc2⟩
    · ileft; iexact Hcho
    wp_apply wp_spsc_close γw.spsc ch _ (fun _ => iprop(True)) [] $$ [$Hs $Hp]
    wp_for_post
    iapply HΦ
    rw [hrow]
    iapply watch_post
    iframe Hc
    iframe #
  simp only [hm, _root_.decide_false]
  wp_auto
  wp_apply wp_map_lookup1 go.string go_etcd_io.etcd.client.v3.watchGRPCStream.ty.PointerType m M
    (streamKeyOf (metadata.outgoingOf (GoInterface.ok ctx))) (DFrac.own 1) $$ [$HM] as HM
  wp_join iprop(∃ (G : WgsPrm GF) (M' : GMap GoString Loc), wgs_ptr ↦ G.wgs ∗ m ↦$ M' ∗
      (□ [∗map] k ↦ x ∈ M', ∃ G' : WgsPrm GF, ⌜G'.wgs = x ∧ G'.w = w ∧
        streamKeyOf (metadata.outgoingOf (GoInterface.ok G'.ctx)) = k⌝ ∗ isWGS V G' callSl) ∗
      ⌜G.w = w ∧ streamKeyOf (metadata.outgoingOf (GoInterface.ok G.ctx)) = (streamKeyOf (metadata.outgoingOf (GoInterface.ok ctx)))⌝ ∗
      isWGS V G callSl ∗ w_ptr ↦ w ∗ ctx_ptr ↦ GoInterface.ok ctx ∗
      ctxKey_ptr ↦ (streamKeyOf (metadata.outgoingOf (GoInterface.ok ctx))) ∗ watcherF w go!"streams" ↦ m)
    with [wgs HM w Hctxp ctxKey Hst] as ⟨%G, %M', wgs, HM, #HMs', %HGw, #HG, w, Hctxp, ctxKey, Hst⟩
  · wp_apply wp_newStream V w ctx cs $$ [] as %wgs' ⟨%G, %callSl', %HGeq, #Hco', #HG, %HGo⟩
    · iframe #; ipureintro; exact Hb
    icombine Hco Hco' gives %Hcs
    obtain ⟨-, rfl⟩ := Hcs
    wp_apply wp_mapInsert go.string m M (streamKeyOf (metadata.outgoingOf (GoInterface.ok ctx))) wgs' $$ [$HM] as HM
    have HGk : streamKeyOf (metadata.outgoingOf (GoInterface.ok G.ctx)) = (streamKeyOf (metadata.outgoingOf (GoInterface.ok ctx))) := by
      rw [HGo.1]
    wp_join_done
    iexists G, _
    iframe
    rw [← HGeq.1]
    iframe
    iframe #
    isplitr
    · iintro !>
      iapply BigSepM.bigSepM_insert_elim $$ [] HMs
      iexists G
      iframe #
      ipureintro; exact ⟨rfl, HGeq.2, HGk⟩
    ipureintro; exact ⟨HGeq.2, HGk⟩
  · cases h : M !! (streamKeyOf (metadata.outgoingOf (GoInterface.ok ctx))) with
    | none => exact absurd (by simp [h]; rfl) Hif
    | some x =>
      simp only [h, Option.getD_some] at Hif ⊢
      ihave ⟨%G, %HGx, #HG⟩ := BigSepM.bigSepM_lookup h $$ HMs
      iexists G, M
      rw [HGx.1]
      iframe
      iframe #
      ipureintro; exact HGx.2
  obtain ⟨HGw, HGk⟩ := HGw
  -- (G2) the request is at the stream's key
  ihave #HreqG : reqP V (streamKeyOf (metadata.outgoingOf (GoInterface.ok G.ctx)))
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.watchRequest.ty)
      #«$r0_ptr») $$ []
  · rw [HGk]; iexact HreqP
  iunfold isWGS at HG
  icases HG with ⟨%Hgnn, #Hcv, #Hsf, %Hlg', #Howner, #Hremote, #Hcallo, #Hgctx, #Hckey, #Hcancel,
    #Hreqc, #Hrespc, #Hdonec, #Herrc, #Hclosingc, #Hglg, #HisCtx, #Hcspec, #Hbreq, #Hberr, #Hbcl,
    #Hbdone, -⟩
  wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hst HM]
  · inext
    unfold watcherMu
    iexists m
    iframe Hst
    iright
    iexists M'
    iframe HM
    iframe #
  wp_join iprop(∃ (cc' : Loc) (γw : EtcdWatchNames), closeCh_ptr ↦ cc' ∗
      isSpsc γw.spsc cc' (outcElem γw (opWatchModel key gs).watchNorm Q (wsRow V P0))
        (fun _ => iprop(True)) ∗
      spscProducer γw.spsc ([] : List go_etcd_io.etcd.client.v3.WatchResponse) ∗
      monoListAuthOwn γw.cur 1 [rev - W64 1] ∗
      spscConsumer γw.spsc ([] : List go_etcd_io.etcd.client.v3.WatchResponse) ∗
      monoListIdxOwn γw.cur 0 (rev - W64 1) ∗ monoListIdxOwn γw.cur2 0 (rev - W64 1) ∗
      ⌜γw.cur2 = γw.cur ∧ γw.cpl = cplCond true (opWatchModel key gs).watchNorm rev⌝)
    with [closeCh Hcc] as ⟨%cc', %γw, closeCh, #Hs, Hp, Ha, Hc, #Hi0, #Hi02, %Hc2⟩
  · wp_apply +noauto chan.wp_make2 (V := go_etcd_io.etcd.client.v3.WatchResponse) (W64 1)
      as %ch %γch ⟨#Hch, %-, Hcho⟩
    · ipureintro; word
    imod watch_spsc_alloc (opWatchModel key gs).watchNorm Q (wsRow V P0) rev
      (cplCond true (opWatchModel key gs).watchNorm rev) ch γch $$ Hch [Hcho]
      with ⟨%γw, #Hs, Hp, Ha, Hc, #Hi0, #Hi02, %Hc2⟩
    · iright; iexact Hcho
    wp_auto
    wp_join_done
    iexists ch, γw
    iframe
    iframe #
    ipureintro; exact Hc2
  · unfold closeChRes
    icases Hcc with (%Hn | ⟨%γw, #Hs, Hp, Ha, Hc, #Hi0, %Hc2⟩)
    · exact absurd Hn Hif
    iexists cc, γw
    iframe
    iframe #
    isplitr
    · rw [Hc2.1]; iexact Hi0
    ipureintro; exact Hc2
  ihave #Hctx1 := Hctx
  iNamed Hctx1
  wp_apply +noauto HDone as %dch %dγ #Hdone
  wp_auto_lc 3
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, G.reqc, G.γreq,
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.watchRequest.ty) #«$r0_ptr»)
    isplit
    · -- the request converted to `watchStreamRequest` (the fork's Gooseable commit: Goose's
      -- `select` send case does not convert the sent value to the channel's element type)
      ipureintro; exact ⟨rfl, rfl⟩
    isplit
    · iapply is_bag_is_chan $$ Hbreq
    iapply bag_send_au $$ [$Hlc1 $Hlc2] Hbreq HreqG
    inext
    wp_auto
    wp_apply +noauto HDone as %dch' %dγ' #Hdone'
    wp_auto_lc 2
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, retc, γret
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ Hbret
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hbret
      inext
      iintro %ret Hret
      wp_auto
      wp_for_post
      iunfold retcP at Hret
      icases Hret with ⟨%γr, #Hrs, Hrc, #Hri, #Hri2, %Hcpl⟩
      iapply HΦ
      rw [hrow]
      iapply watch_post
      iframe Hrc
      iframe #
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch', dγ'
      isplit
      · ipureintro; rfl
      isplit
      · iapply context.isContextDone_is_chan $$ Hdone'
      iapply context.isContextDone_receive _ _ _ _ $$ Hdone'
      iintro -
      wp_auto
      wp_for_post
      wp_apply wp_spsc_close γw.spsc cc' _ (fun _ => iprop(True)) [] $$ [$Hs $Hp]
      iapply HΦ
      rw [hrow]
      iapply watch_post
      iframe Hc
      iframe #
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, G.donec, G.γdone
      isplit
      · ipureintro; rfl
      isplit
      · iapply ownBroadcastChan_is_chan $$ Hbdone
      iapply broadcast_chan_receive $$ Hbdone
      iintro ⟨#Hpub, -⟩
      iunfold closeErrPub at Hpub
      icases Hpub with ⟨%e, #Hce, #Hse⟩
      wp_auto
      cases e with
      | nil =>
        wp_auto
        wp_for_post
        iframe
        iexists true, cc'
        iframe
        unfold closeChRes
        iright
        iexists γw
        iframe
        iframe #
        ipureintro; exact Hc2
      | ok i =>
        wp_auto
        ihave ⟨H0, %Hhn⟩ := typedPointsto_not_null_dup _ _ _ $$ «$v0»
        iStructNamedPrefix H0 "H"
        ipersist HRevision
        imod monoListAuthOwn_update_app (GF := GF) [rev - W64 1] $$ Ha with ⟨Ha, #Hlb⟩
        ihave #Hi1 := monoListIdxOwn_get (GF := GF) 1 (rev - W64 1) rfl $$ Hlb
        ihave Hel := outcElem_canceled γw (opWatchModel key gs).watchNorm Q (wsRow V P0) (kvStateOf C0) 0
          (rev - W64 1) ⟨«$v0_ptr», slice.nil, 0, true, false, GoInterface.ok i, []⟩ ⟨rfl, rfl, rfl, rfl, Hhn⟩ $$ [HRevision]
        · rw [Hc2.1]
          iframe #
          rw [show (W64 0 : w64) = (zero_val etcdserverpb.ResponseHeader).Revision' from rfl]
          iexact HRevision
        wp_apply wp_spsc_send γw.spsc cc' _ (fun _ => iprop(True)) [] $$ [$Hs $Hp $Hel] as Hp
        wp_for_post
        wp_apply wp_spsc_close γw.spsc cc' _ (fun _ => iprop(True)) _ $$ [$Hs $Hp]
        iapply HΦ
        rw [hrow]
        iapply watch_post
        iframe Hc
        iframe #
    iapply BigAndL.bigAndL_nil.2
    itrivial
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch, dγ
    isplit
    · ipureintro; rfl
    isplit
    · iapply context.isContextDone_is_chan $$ Hdone
    iapply context.isContextDone_receive _ _ _ _ $$ Hdone
    iintro -
    wp_auto
    wp_for_post
    wp_apply wp_spsc_close γw.spsc cc' _ (fun _ => iprop(True)) [] $$ [$Hs $Hp]
    iapply HΦ
    rw [hrow]
    iapply watch_post
    iframe Hc
    iframe #
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, G.donec, G.γdone
    isplit
    · ipureintro; rfl
    isplit
    · iapply ownBroadcastChan_is_chan $$ Hbdone
    iapply broadcast_chan_receive $$ Hbdone
    iintro ⟨#Hpub, -⟩
    iunfold closeErrPub at Hpub
    icases Hpub with ⟨%e, #Hce, #Hse⟩
    wp_auto
    cases e with
    | nil =>
      wp_auto
      wp_for_post
      iframe
      iexists false, cc'
      iframe
      unfold closeChRes
      iright
      iexists γw
      iframe
      iframe #
      ipureintro; exact Hc2
    | ok i =>
      wp_auto
      ihave ⟨H0, %Hhn⟩ := typedPointsto_not_null_dup _ _ _ $$ «$v0»
      iStructNamedPrefix H0 "H"
      ipersist HRevision
      imod monoListAuthOwn_update_app (GF := GF) [rev - W64 1] $$ Ha with ⟨Ha, #Hlb⟩
      ihave #Hi1 := monoListIdxOwn_get (GF := GF) 1 (rev - W64 1) rfl $$ Hlb
      ihave Hel := outcElem_canceled γw (opWatchModel key gs).watchNorm Q (wsRow V P0) (kvStateOf C0) 0
        (rev - W64 1) ⟨«$v0_ptr», slice.nil, 0, true, false, GoInterface.ok i, []⟩ ⟨rfl, rfl, rfl, rfl, Hhn⟩ $$ [HRevision]
      · rw [Hc2.1]
        iframe #
        rw [show (W64 0 : w64) = (zero_val etcdserverpb.ResponseHeader).Revision' from rfl]
        iexact HRevision
      wp_apply wp_spsc_send γw.spsc cc' _ (fun _ => iprop(True)) [] $$ [$Hs $Hp $Hel] as Hp
      wp_for_post
      wp_apply wp_spsc_close γw.spsc cc' _ (fun _ => iprop(True)) _ $$ [$Hs $Hp]
      iapply HΦ
      rw [hrow]
      iapply watch_post
      iframe Hc
      iframe #
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
