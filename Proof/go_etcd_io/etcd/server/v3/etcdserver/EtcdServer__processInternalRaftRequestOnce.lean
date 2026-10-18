/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__processInternalRaftRequestOnce.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__processInternalRaftRequestOnce
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__getAppliedIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__getCommittedIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__FeatureEnabled
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.exceedsRequestLimit
public import Spec.go_etcd_io.etcd.pkg.v3.idutil.Generator__Next
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AuthInfoFromCtx
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.getRequestType
public import Spec.google_golang_org.protobuf.proto.MarshalIRR
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__ReqTimeout
public import Spec.go_opentelemetry_io.otel.trace.SpanFromContext
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__parseProposeCtxErr
public import Spec.context.ErrDone
public import Spec.strconv.FormatBool
public import Spec.time.Duration__Seconds
public import Spec.github_com.prometheus.client_golang.prometheus.HistogramVec__WithLabelValues
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ProposerLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.UberLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.DispatchLemmas
public import GeneratedProof.go_etcd_io.raft.v3

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `getRequestType`'s names are valid UTF-8 (`requestDurationSec`'s label; D19l (iii)). -/
theorem reqTypeName_utf8 (rq : apply.IRRModel) : utf8Valid (reqTypeName rq) := by
  have hite : ∀ {c : Prop} [Decidable c] {a b : GoString}, utf8Valid a → utf8Valid b →
      utf8Valid (if c then a else b) := by
    intro c _ a b ha hb; by_cases h : c
    · rw [if_pos h]; exact ha
    · rw [if_neg h]; exact hb
  unfold reqTypeName; repeat' (first | decide | apply hite)

set_option hygiene false in
/-- The deferred metrics closure (`requestDurationSec.WithLabelValues(reqType,
strconv.FormatBool(success)).Observe(time.Since(start).Seconds())`). -/
local macro "run_metrics" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply time.wp_Since as %_ -
  (try wp_auto)
  wp_apply hSec as %_ -
  (try wp_auto)
  wp_apply hFB as %fb %Hfb
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %lsl ⟨Hlsl, -⟩
  (try wp_auto)
  wp_apply hWL hist _ [go!"type", go!"success"] _ _ $$ [Hlsl] as %_ ⟨%oi, %Hoi, #Hobs, -⟩
  · iframe #; iframe Hlsl; ipureintro
    refine ⟨Hhl, prometheus.labelValuesOk_two _ _ _ _ (by first | decide | exact reqTypeName_utf8 _) ?_⟩
    rw [Hfb]; split <;> decide
  subst Hoi
  iunfold prometheus.observerSpec at Hobs
  (try wp_auto)
  wp_apply Hobs
  (try wp_auto)))

set_option hygiene false in
/-- A return before the proposal: no result, the error (not nil), nothing deposited. -/
local macro "exit_nodep" : tactic => `(tactic| (
  iapply HΦ
  iframe Hrd Hard
  iright
  isplitr
  · ipureintro; exact ⟨rfl, by simp⟩
  isplitr
  · first | iexact HaE | iexact HaTMR | iexact HaRTL
  iunfold srvMaybeDeposited
  iexists false
  simp only [Bool.false_eq_true, ↓reduceIte]
  itrivial))

set_option hygiene false in
/-- A return after the proposal: no result, the error (not nil), the proposal deposited. -/
local macro "exit_dep" : tactic => `(tactic| (
  iapply HΦ
  iframe Hrd Hard
  iright
  isplitr
  · ipureintro; exact ⟨rfl, by first | assumption | simp⟩
  isplitr
  · first | iexact HaE | iexact HaStop
  iunfold srvMaybeDeposited
  iexists true
  simp only [↓reduceIte]
  iexists bs, ⟨id, hv.Username', hv.AuthRevision'⟩, rq'
  iframe Hdep
  ipureintro; exact ⟨Hdec, Hwire⟩))

set_option hygiene false in
/-- The rest of the function from `getRequestType(r)` on (after the header is set, `Hhv : «$r0_ptr» ↦ hv`, `Hhvid : hv.ID' = id`). -/
local macro "piro_tail" : tactic => `(tactic| (
  wp_apply hRT p rq $$ []
  · iframe #
  (try wp_auto)
  wp_apply time.wp_Now as %start -
  (try wp_auto)
  ihave ⟨Hhv, %Hhvn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hhv
  iStructNamed Hhv
  ipersist ID
  ipersist Username
  ipersist AuthRevision
  ipersist Hhdr
  ihave #Hirrh : iprop(apply.internalRaftRequestIs p
      (apply.withHeader rq ⟨id, hv.Username', hv.AuthRevision'⟩)) $$ []
  · iapply irrIs_of_noHdr
    iframe #
    iunfold apply.headerIs
    rw [← Hhvid]
    iframe #
    ipureintro; exact Hhvn
  wp_apply hM p (apply.withHeader rq ⟨id, hv.Username', hv.AuthRevision'⟩) $$ []
    as %dsl %merr Hmres
  · iframe #
  (try wp_auto)
  icases Hmres with (⟨%Hmerr, %bs, %rq', Hbs, Hbscap, %Hbsdec⟩ | ⟨%Hmerr, #HaE⟩)
  · subst Hmerr
    (try wp_auto)
    ihave %Hbslen := ownSlice_len _ _ _ $$ Hbs
    wp_if_destruct
    · run_metrics
      exit_nodep
    rw [Hid0]
    (try wp_auto)
    rw [Hhvid]
    obtain ⟨Hdec, Hwire, Hbsne⟩ := Hbsdec
    have Hidrq : apply.irrId rq' = some id := by
      obtain ⟨h1, h2, -, -⟩ := Hwire
      unfold apply.irrId
      rw [h1, h2]
      simp [apply.withHeader, Hid0]
    iunfold idFresh at Hfresh
    icases Hfresh with ⟨Hunc, Hslot⟩
    imod srv_claim_mint ρ E v.gen id bs rq' F Hdec Hidrq $$ HidGen Hmint Hunc HF
      with ⟨%γf, #Hclaim, #Hfl, Hpf⟩
    iunfold waitInv at Hwi
    icases Hwi with ⟨%RD, #Hwait⟩
    iunfold isWait at Hwait
    icases Hwait with ⟨%wi, %Hwi', #HReg, #HTrig, -⟩
    rw [Hwi']
    (try wp_auto)
    wp_apply HReg $$ %id %(resultΨ E ρ rq' F) [Hslot] as %ch ⟨%γh, Hrecv, #Hregd⟩
    · iframe Hslot
      imodintro
      iunfold reqWaitR
      iexists bs, rq', γf, F
      iframe Hclaim Hfl
      ipureintro; exact ⟨Hdec, rfl⟩
    (try wp_auto)
    wp_apply hTO (structFieldRef EtcdServer go!"Cfg" s) v.electionTicks v.tickMs $$ [] as %tmo -
    · iframe #
    (try wp_auto)
    wp_apply context.wp_WithTimeout ctx cd tmo $$ [] as %cctx %γc %cancel %dl ⟨#Hcancel, #Hcctx⟩
    · iframe #
    (try wp_auto)
    wp_apply hSp ctx cd $$ [] as %sp #Hsp
    · iframe #
    (try wp_auto)
    iunfold trace.isSpan at Hsp
    icases Hsp with ⟨%si, %Hsi, #HEnd, #HAddEv, #HRecErr⟩
    subst Hsi
    (try wp_auto)
    wp_apply HAddEv
    (try wp_auto)
    imod ownSlice_persist dsl _ _ $$ Hbs with #Hbs
    iunfold srvRaftNode at Hrn
    icases Hrn with ⟨%nd, #Hnd, #Hprop⟩
    iunfold raftPropose at Hprop
    icases Hprop with ⟨%ni, %Hni, #HrLog, #HWits, #HPropose, -⟩
    ihave HokW := reqPropOk_wire ρ.kv rq rq' ⟨id, hv.Username', hv.AuthRevision'⟩ Qr Hwire $$ Hok
    imod kv_prop_au ρ.raft ρ.kv bs rq' Qr (Hbsne (by simp [apply.withHeader])) Hdec id γf Hidrq ⊤
      CoPset.subseteq_top $$ Hclog Hclaim HokW with #Hau
    rw [method_unfold (t := go.GoType.PointerType raftNode.ty) (m := go!"Propose")]
    (try wp_auto)
    rw [method_unfold (t := go.GoType.PointerType raftNodeConfig.ty) (m := go!"Propose")]
    wp_pures
    (try wp_auto)
    rw [Hni]
    (try wp_auto)
    wp_apply HPropose $$ %cctx %_ %dsl %bs %Qr %true [Hpf] as %perr Hpres
    · iframe Hbs
      isplitr
      · iunfold mvcc.txnCtx; iright; iexact Hcctx
      isplitr
      · ipureintro; exact Hbsne (by simp [apply.withHeader])
      iunfold srvPropArg
      simp only [↓reduceIte]
      iframe Hpf Hau
    (try wp_auto)
    iunfold srvPropRes at Hpres
    isimp only [↓reduceIte] at Hpres
    icases Hpres with ⟨⟨#Hdep, #HisP⟩, #HaE⟩
    iunfold waitRecv at Hrecv
    icases Hrecv with ⟨#Hho, Hcons⟩
    iunfold go_etcd_io.etcd.server.v3.storage.mvcc.counterSpec at Hpfcs
    icases Hpfcs with ⟨#HInc, -⟩
    cases perr with
    | ok pei =>
      (try wp_auto)
      wp_apply HInc
      (try wp_auto)
      wp_apply HTrig $$ %_ %_ [Hcons]
      · ileft; iexists γh; iframe Hcons Hregd; ipureintro; rfl
      (try wp_auto)
      wp_apply Hcancel
      run_metrics
      exit_dep
    | nil =>
      wp_auto_lc 1
      iunfold go_etcd_io.etcd.server.v3.storage.mvcc.gaugeSpec at Hppcs
      icases Hppcs with ⟨#HGInc, #HGDec, -⟩
      wp_apply HGInc
      (try wp_auto)
      ihave #Hcctx' := Hcctx
      iNamed Hcctx'
      wp_apply HDone as %chD %γD #HcD
      iunfold srvDoneChan at Hdonec
      icases Hdonec with ⟨%γdn, #Hdn⟩
      (try wp_auto)
      ihave #Hho' := Hho
      iunfold isHandoff at Hho'
      icases Hho' with ⟨#Hchan, -⟩
      wp_apply_core chan.wp_select_blocking
      iapply BigAndL.bigAndL_cons.2
      isplit
      · -- the result
        simp only [chan.blockingClausePre]
        iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, ch,
          γh.chanName
        isplitr
        · ipureintro; rfl
        isplitr
        · iexact Hchan
        iapply handoff_rcv_au γh ch (waitVal γh (resultΨ E ρ rq' F)) iprop(True) iprop(False) false _
          $$ Hho Hlc1 Hcons
        inext
        iintro %x %ok ⟨Hcons', Hgot⟩
        unfold handoffGot
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases ok
        · simp only [Bool.false_eq_true, ↓reduceIte]
          icases Hgot with ⟨-, Hf⟩
          iexfalso; iexact Hf
        simp only [↓reduceIte]
        icases Hgot with ⟨Hw, -⟩
        iunfold waitVal at Hw
        icases Hw with (Hres | ⟨-, Hc2⟩)
        rotate_left
        · iunfold handoffConsumer at Hcons' Hc2
          ihave %Hbad := dghostVar_agree _ _ _ _ _ $$ Hcons' Hc2
          cases Hbad
        iunfold resultΨ at Hres
        icases Hres with ⟨%ar, %lb, %Hx, HTr, Hri, #HeW⟩
        subst Hx
        wp_auto_lc 2
        iunfold entryWit at HeW
        icases HeW with ⟨%Lw, %mw, %ew, %idw, %γw, #HLw, #Hclw, %Hew⟩
        obtain ⟨hlk, het, hdecw, hidw, hlbw⟩ := Hew
        have hidd : idw = id := by rw [Hidrq] at hidw; cases hidw; rfl
        subst hidd
        ihave %Hdd := idClaim_agree ρ.ids idw ew.data bs γw γf $$ Hclw Hclaim
        replace Hdd := Hdd.1
        ihave #HWits' := HWits
        iunfold srvPropWits at HWits'
        imod HWits' $$ %bs %Qr %Lw %mw %ew HisP HLw [] [Hlc1 Hlc2] with #HQr
        · ipureintro; exact ⟨hlk, het, Hdd, Hbsne (by simp [apply.withHeader])⟩
        · iapply (lc_split (n := 1) (m := 1)).2; iframe
        ihave #HLt : iprop(srvRLogLb ρ.raft (Lw.take mw)) $$ []
        · iapply srvRLogLb_mono ρ.raft _ _ (List.take_prefix _ _) $$ HLw
        wp_apply HAddEv
        (try wp_auto)
        wp_apply HGDec
        (try wp_auto)
        wp_apply Hcancel
        run_metrics
        iapply HΦ
        iframe Hrd Hard
        ileft
        isplitr
        · ipureintro; rfl
        iexists ⟨idw, hv.Username', hv.AuthRevision'⟩, rq'
        iframe HTr
        isplitr
        · ipureintro; exact Hwire
        iexists lb
        iframe Hri
        iexists Lw.take mw
        iframe HLt HQr
        ipureintro; exact hlbw
      iapply BigAndL.bigAndL_cons.2
      isplit
      · -- the context done: give up
        simp only [chan.blockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, chD, γD
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply context.isContextDone_is_chan $$ HcD
        iapply context.isContextDone_receive _ _ _ _ $$ HcD
        iintro ⟨#HPD, #HCC⟩
        (try wp_auto)
        wp_apply HInc
        (try wp_auto)
        wp_apply HTrig $$ %_ %_ [Hcons]
        · ileft; iexists γh; iframe Hcons Hregd; ipureintro; rfl
        (try wp_auto)
        wp_apply hED cctx _ $$ [HCC] as %cerr ⟨%Hcerr, #Hcerrv⟩
        · iframe #
        (try wp_auto)
        wp_apply hPE s E ρ cerr start Hcerr $$ [Hrd] as %perr ⟨Hrd, %Hperr, #HaE⟩
        · iframe Hrd
          isplitl
          · iunfold isServerReq; iexists v; iexact Hv
          iexact Hcerrv
        (try wp_auto)
        wp_apply HGDec
        (try wp_auto)
        wp_apply Hcancel
        run_metrics
        exit_dep
      iapply BigAndL.bigAndL_cons.2
      isplit
      · -- the server stopped
        simp only [chan.blockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, v.done, γdn
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply ownBroadcastChan_is_chan $$ Hdn
        iapply broadcast_chan_receive _ _ _ _ _ $$ Hdn
        iintro ⟨-, -⟩
        (try wp_auto)
        wp_apply HGDec
        (try wp_auto)
        wp_apply Hcancel
        run_metrics
        exit_dep
      iapply BigAndL.bigAndL_nil.2
      itrivial
  · rcases merr with mei | _
    · run_metrics
      exit_nodep
    · exact absurd rfl Hmerr))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem EtcdServer.processInternalRaftRequestOnce.wp_proof
    (hAI : EtcdServer.getAppliedIndex.spec (GF := GF) (hG := hG))
    (hCI : EtcdServer.getCommittedIndex.spec (GF := GF) (hG := hG))
    (hFE : EtcdServer.FeatureEnabled.spec (GF := GF) (hG := hG))
    (hEx : exceedsRequestLimit.spec (GF := GF) (hG := hG))
    (hNext : idutil.Generator.Next.spec (GF := GF) (hG := hG))
    (hAuth : EtcdServer.AuthInfoFromCtx.spec (GF := GF) (hG := hG))
    (hRT : getRequestType.spec (GF := GF) (hG := hG))
    (hM : proto.MarshalIRR.spec (GF := GF) (hG := hG))
    (hTO : config.ServerConfig.ReqTimeout.spec (GF := GF) (hG := hG))
    (hSp : trace.SpanFromContext.spec (GF := GF) (hG := hG))
    (hPE : EtcdServer.parseProposeCtxErr.spec (GF := GF) (hG := hG))
    (hED : context.ErrDone.spec (GF := GF) (hG := hG))
    (hFB : strconv.FormatBool.spec (GF := GF) (hG := hG))
    (hSec : time.Duration.Seconds.spec (GF := GF) (hG := hG))
    (hWL : prometheus.HistogramVec.WithLabelValues.spec (GF := GF) (hG := hG)) :
    EtcdServer.processInternalRaftRequestOnce.spec (GF := GF) (hG := hG) := by
  intro s E ρ ctx cd p rq Qr F Hid0
  wp_start as ⟨#Hsrv, Hrd, Hard, Hcred, #Hctx, #Hirr, Hok, ⟨%h0, Hhdr⟩, #HF⟩
  wp_apply wp_with_defer as %defer defer
  iunfold isServerReq at Hsrv
  icases Hsrv with ⟨%v, #Hv⟩
  ihave #Hv' := Hv
  iunfold srvReqFieldsAt at Hv'
  icases Hv' with ⟨#Hgen, #HidGen, #Hw, #Hwi, #Hrn, #Hmrb, #Hfgf, #Hfg, #Hcca, #Het, #Htm,
    #Has, #Hras, #Hdone, #Hdonec, #Hmid, #Hlead, #Hcl, #Htr, #Hpeers, #Hidx, #Hmint, #Hclog, %Hcfgnn⟩
  ihave #Pidutil : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.idutil $$ []
  · iPkgInit
  ihave #Pproto : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  ihave #Pcfg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Ptrace : isPkgInit (PROP := IProp GF) pkg_id.go_opentelemetry_io.otel.trace $$ []
  · iPkgInit
  ihave #Ptime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Pstrconv : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  ihave #Pprom : isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus $$ []
  · iPkgInit
  iunfold srvIndexInvs at Hidx
  icases Hidx with ⟨%γr, #Hai, #Hci⟩
  wp_apply hAI s E γr $$ [] as %ai -
  · iframe #
  (try wp_auto)
  wp_apply hCI s γr none $$ [] as %ci -
  · iframe #; iunfold srvCommittedOwnOpt; itrivial
  (try wp_auto)
  wp_apply hFE s v.fg _ $$ [] as %en -
  · iframe #; ipureintro; simp [serverFeatures]
  ihave Hinit : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, ⟨⟨%hist, #Hhist, %Hhl⟩, ⟨%pfc, #Hpfc, #Hpfcs⟩, ⟨%ppc, #Hppc, #Hppcs⟩, -,
    ⟨#HTMR, #HRTL, #HStop, -⟩⟩, -⟩
  ihave ⟨%eTMR, #HeTMR, #HaTMR⟩ := errVarLeaf_get _ $$ HTMR
  ihave ⟨%eRTL, #HeRTL, #HaRTL⟩ := errVarLeaf_get _ $$ HRTL
  ihave ⟨%eStop, #HeStop, #HaStop⟩ := errVarLeaf_get _ $$ HStop
  wp_apply hEx ai ci p rq en $$ []
  · iframe #
  cases hx : exceedsLimit ai ci rq.leaseRevoke.isSome en
  · (try wp_auto)
    wp_apply hNext ρ.ids v.gen (srvFloorFact E) $$ [Hcred] as %id ⟨Hfresh, %pfx, %s0, %j, #Hpfx, %Hidshape⟩
    · iframe #; iframe Hcred
    (try wp_auto)
    ihave #Hirr' := Hirr
    iunfold irrNoHdrIs at Hirr'
    icases Hirr' with ⟨%Hpn, #HID, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%la, #Hla, Hla'⟩, -⟩
    ihave %Hlan := apply.optReqIs_nil la rq.authenticate _ apply.authenticateIs_nn $$ Hla'
    cases hau : rq.authenticate with
    | some am =>
      have hla : la ≠ null := fun h => by rw [Hlan.1 h] at hau; cases hau
      (try wp_auto)
      rw [decide_eq_false hla]
      (try wp_auto)
      ihave Hhv : iprop(∃ hv : etcdserverpb.RequestHeader, «$r0_ptr» ↦ hv ∗ ⌜hv.ID' = id⌝) $$ [«$r0»]
      · iexists _; iframe «$r0»; ipureintro; rfl
      icases Hhv with ⟨%hv, Hhv, %Hhvid⟩
      piro_tail
    | none =>
      have hla : la = null := Hlan.2 hau
      (try wp_auto)
      wp_if_destruct
      · wp_apply hAuth s v.auth E.RD v.cca ctx cd $$ [Hard] as %au %aerr ⟨Hard, Hau, #HaE⟩
        · iframe Hard; iframe #
          iunfold mvcc.txnCtx; iright; iexact Hctx
        (try wp_auto)
        cases aerr with
        | ok aei =>
          (try wp_auto)
          iapply HΦ
          iframe Hrd Hard
          iright
          isplitr
          · ipureintro; exact ⟨rfl, by simp⟩
          isplitr
          · iexact HaE
          iunfold srvMaybeDeposited
          iexists false
          simp only [Bool.false_eq_true, ↓reduceIte]
          itrivial
        | nil =>
          (try wp_auto)
          wp_join iprop(∃ hv : etcdserverpb.RequestHeader, «$r0_ptr» ↦ hv ∗ ⌜hv.ID' = id⌝ ∗
              structFieldRef etcdserverpb.InternalRaftRequest go!"Header" p ↦ «$r0_ptr» ∗ r_ptr ↦ p)
            with [«$r0» Hau authInfo Hhdr r] as ⟨%hv, Hhv, %Hhvid, Hhdr, r⟩
          · iexists _; iframe «$r0» Hhdr r; ipureintro; rfl
          · iunfold authInfoOpt at Hau
            icases Hau with (%Hn | ⟨%user, %rev, Hai⟩)
            · exfalso; simp_all
            iunfold authInfoIs at Hai
            icases Hai with ⟨-, #HU, #HR⟩
            (try wp_auto)
            wp_join_done
            iexists _; iframe «$r0» Hhdr r; ipureintro; rfl
          piro_tail
      · exact absurd hla Hif
  · (try wp_auto)
    iapply HΦ
    iframe Hrd Hard
    iright
    isplitr
    · ipureintro; exact ⟨rfl, by simp⟩
    isplitr
    · iexact HaTMR
    iunfold srvMaybeDeposited
    iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial

end proof

end EtcdGrove
end Perennial
