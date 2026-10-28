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
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
/-- `exit_dep` at the joined `select` (its postcondition, before the deferred calls). -/
local macro "exit_dep_q" : tactic => `(tactic| (
  iexists _, _
  isplitr
  · ipureintro; rfl
  iframe start Hrd Hard
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
    icases Hfresh with ⟨Hunc, Hslot, %Hpfx⟩
    imod srv_claim_mint ρ E v.gen id bs rq' F Hdec Hidrq Hpfx $$ HidGen Hmint Hunc HF
      with ⟨%γf, #Hclaim, #Hfl, Hpf⟩
    iunfold waitInvM at Hwi
    icases Hwi with ⟨⟨%RD, #Hwait⟩, #Hwn⟩
    iunfold isWait at Hwait
    icases Hwait with ⟨%wi, %Hwi', #HReg, #HTrig, -⟩
    rw [Hwi']
    (try wp_auto)
    wp_apply HReg $$ %id %(resultΨM on E ρ rq' F) [Hslot] as %ch ⟨%γh, Hrecv, #Hregd⟩
    · iframe Hslot
      imodintro
      iunfold reqWaitRM
      iexists bs, rq', γf, F
      iframe Hclaim Hfl
      ipureintro; exact ⟨Hdec, rfl, Hpfx⟩
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
    -- (linkv-txn stage B1) the id registered in this member's registry, before the proposal
    ihave #Hireg : iprop(idRegd ρ.ids id) $$ []
    · iunfold idRegd
      iexists ρ.wait, γh.takenName
      rw [Hpfx]
      iframe Hwn Hregd
    imod kv_prop_au_M on ρ.raft ρ.kv bs rq rq' ⟨id, hv.Username', hv.AuthRevision'⟩ Qh
      (Hbsne (by simp [apply.withHeader])) Hdec Hwire id γf Hidrq ⊤
      CoPset.subseteq_top $$ Hclog Hclaim Hireg Hok with ⟨Hau, #Hqi⟩
    rw [method_unfold (t := go.GoType.PointerType raftNode.ty) (m := go!"Propose")]
    -- (2026-10-27) a later credit for the node API's `Propose` (its registry's invariant)
    wp_auto_lc 1
    irename Hlc1 => HlcP
    rw [method_unfold (t := go.GoType.PointerType raftNodeConfig.ty) (m := go!"Propose")]
    wp_pures
    (try wp_auto)
    rw [Hni]
    (try wp_auto)
    wp_apply HPropose $$ %cctx %_ %dsl %bs %(Qh ⟨id, hv.Username', hv.AuthRevision'⟩) [Hpf Hau HlcP] as %perr Hpres
    · iframe Hbs
      isplitr
      · iunfold mvcc.txnCtx; iright; iexact Hcctx
      isplitr
      · ipureintro; exact Hbsne (by simp [apply.withHeader])
      iframe HlcP
      iunfold srvPropArg
      iframe Hpf Hau Hqi
    (try wp_auto)
    iunfold srvPropRes at Hpres
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
      · iright; ileft; iexists γh; iframe Hcons Hregd; ipureintro; rfl
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
      -- the `select`, joined (`wp_join`): its three ways out return, and the deferred
      -- `proposalsPending.Dec()`, `cancel()` and metrics after them are verified once
      wp_join (Q := fun v => iprop(∃ (res : Loc) (e : GoInterface),
          ⌜v = returnVal (PairV #res #e)⌝ ∗ start_ptr ↦ start ∗ srvLeadTimeReader s ∗ E.RD ∗
          ((⌜e = GoInterface.nil⌝ ∗ ∃ hm rq',
              ⌜irrWireOf (apply.withHeader rq hm) rq'⌝ ∗ apply.resTrace res ∗
              ∃ L, srvRLogLb ρ.raft L ∗ resPostM on E ρ rq' F res L ∗ pubAfterM on E ρ rq' L ∗
                □ Qh hm L ∗ hdrBoundM on s E (GoInterface.ok ctx) hm) ∨
            ⌜res = null ∧ e ≠ GoInterface.nil⌝ ∗ applyErrIs e ∗ srvMaybeDeposited ρ rq)))
        at (let: "$ch1" := _ in _) with [-HΦ defer reqType err]
      · ihave #Hcctx' := Hcctx
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
          iapply handoff_rcv_au γh ch (waitVal γh (resultΨM on E ρ rq' F)) iprop(True) iprop(False) false _
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
          cases on
          · -- the mode off: `resultΨ`, the mode-off model
            rw [resultΨM_false]
            iunfold resultΨ at Hres
            icases Hres with ⟨%ar, %lb, %Hx, HTr, Hri, #HeW⟩
            subst Hx
            wp_auto_lc 3
            iunfold entryWit at HeW
            icases HeW with ⟨%Lw, %mw, %ew, %idw, %γw, #HLw, #Hclw, %Hew⟩
            obtain ⟨hlk, het, hdecw, hidw, hlbw⟩ := Hew
            have hidd : idw = id := by rw [Hidrq] at hidw; cases hidw; rfl
            subst hidd
            ihave %Hdd := idClaim_agree ρ.ids idw ew.data bs γw γf $$ Hclw Hclaim
            replace Hdd := Hdd.1
            ihave #HWits' := HWits
            iunfold srvPropWits at HWits'
            imod HWits' $$ %bs %(Qh ⟨idw, hv.Username', hv.AuthRevision'⟩) %Lw %mw %ew HisP HLw [] [Hlc1 Hlc2 Hlc3] with #HQr
            · ipureintro; exact ⟨hlk, het, Hdd, Hbsne (by simp [apply.withHeader])⟩
            · iapply (lc_split (n := 2) (m := 1)).2; iframe Hlc3
              iapply (lc_split (n := 1) (m := 1)).2; iframe
            ihave #HLt : iprop(srvRLogLb ρ.raft (Lw.take mw)) $$ []
            · iapply srvRLogLb_mono ρ.raft _ _ (List.take_prefix _ _) $$ HLw
            wp_apply HAddEv
            (try wp_auto)
            iexists _, _
            isplitr
            · ipureintro; rfl
            iframe start Hrd Hard
            ileft
            isplitr
            · ipureintro; rfl
            iexists ⟨idw, hv.Username', hv.AuthRevision'⟩, rq'
            iframe HTr
            isplitr
            · ipureintro; exact Hwire
            iexists Lw.take mw
            iframe HLt HQr Hhb
            isplitl [Hri]
            rotate_left
            · unfold pubAfterM; itrivial
            iunfold resultIsW at Hri
            icases Hri with ⟨%Hnn, %y, %y', %out, %Hst, Hr1, Hr2, Hr3, Hr4, Hr5⟩
            iunfold resPostM
            isplitr
            · ipureintro; exact Hnn
            iexists y, y', out
            iframe Hr1 Hr2 Hr3 Hr4 Hr5
            isplitr
            · ipureintro
              refine ⟨Hst.1, Hst.2.1, Hst.2.2.2, ?_⟩
              show kvModel ρ.kv _ = _
              rw [Hst.2.2.1]; exact hlbw
            simp only [adminTieM]
            itrivial
          · -- the mode on: `resultΨOn`, the mode-`on` model and the auth layer's verdict
            rw [resultΨM_true]
            iunfold resultΨOn at Hres
            icases Hres with ⟨%ar, %lb, %st, %Hx, HTr, Hri, #HeW⟩
            subst Hx
            wp_auto_lc 3
            iunfold entryWitOn at HeW
            icases HeW with ⟨%Lw, %mw, %ew, %idw, %γw, #HLw, #Hclw, %Hew, #HpA⟩
            obtain ⟨hlk, het, hdecw, hidw, hlbw⟩ := Hew
            have hidd : idw = id := by rw [Hidrq] at hidw; cases hidw; rfl
            subst hidd
            ihave %Hdd := idClaim_agree ρ.ids idw ew.data bs γw γf $$ Hclw Hclaim
            replace Hdd := Hdd.1
            ihave #HWits' := HWits
            iunfold srvPropWits at HWits'
            imod HWits' $$ %bs %(Qh ⟨idw, hv.Username', hv.AuthRevision'⟩) %Lw %mw %ew HisP HLw [] [Hlc1 Hlc2 Hlc3] with #HQr
            · ipureintro; exact ⟨hlk, het, Hdd, Hbsne (by simp [apply.withHeader])⟩
            · iapply (lc_split (n := 2) (m := 1)).2; iframe Hlc3
              iapply (lc_split (n := 1) (m := 1)).2; iframe
            ihave #HLt : iprop(srvRLogLb ρ.raft (Lw.take mw)) $$ []
            · iapply srvRLogLb_mono ρ.raft _ _ (List.take_prefix _ _) $$ HLw
            wp_apply HAddEv
            (try wp_auto)
            iexists _, _
            isplitr
            · ipureintro; rfl
            iframe start Hrd Hard
            ileft
            isplitr
            · ipureintro; rfl
            iexists ⟨idw, hv.Username', hv.AuthRevision'⟩, rq'
            iframe HTr
            isplitr
            · ipureintro; exact Hwire
            iexists Lw.take mw
            iframe HLt HQr Hhb
            isplitl [Hri]
            rotate_left
            · -- (E3t) the auth state after the entry, published
              have htk : Lw.take mw ++ [ew] = Lw.take (mw + 1) := by
                rw [List.take_succ, hlk]; rfl
              unfold pubAfterM
              iexists ew
              isplitr
              · rw [htk]; iapply srvRLogLb_mono ρ.raft _ _ (List.take_prefix _ _) $$ HLw
              isplitr
              · ipureintro; exact ⟨het, hdecw⟩
              rw [htk]; iexact HpA
            iunfold resultIsWOn at Hri
            icases Hri with ⟨%Hnn, %y, %y', %out, %Hst, Hr1, Hr2, Hr3, Hr4, Hr5, #Hr6⟩
            iunfold resPostM
            isplitr
            · ipureintro; exact Hnn
            iexists y, y', out
            iframe Hr1 Hr2 Hr3 Hr4 Hr5
            isplitr
            · ipureintro
              refine ⟨Hst.1, Hst.2.1, Hst.2.2.2.1, st, ?_, Hst.2.2.2.2⟩
              rw [Hst.2.2.1]; exact hlbw
            -- (E3x) the admin result's tie, at the state the entry met
            simp only [adminTieM, hlbw]
            iexact Hr6
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
          · iright; ileft; iexists γh; iframe Hcons Hregd; ipureintro; rfl
          (try wp_auto)
          wp_apply hED cctx _ $$ [HCC] as %cerr ⟨%Hcerr, #Hcerrv⟩
          · iframe #
          (try wp_auto)
          wp_apply hPE s E ρ cerr start Hcerr $$ [Hrd] as %perr ⟨Hrd, %Hperr, #HaE⟩
          · iframe Hrd
            isplitl
            · iapply (isServerReqM_split _ _ _ _).2; iframe HsrvB; iexists v; iexact Hv
            iexact Hcerrv
          (try wp_auto)
          exit_dep_q
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
          exit_dep_q
        iapply BigAndL.bigAndL_nil.2
        itrivial
      iintro ⟨%res, %e, %Hv, start, Hrd, Hard, Hpost⟩
      subst Hv
      (try wp_auto)
      wp_apply HGDec
      (try wp_auto)
      wp_apply Hcancel
      run_metrics
      iapply HΦ
      iframe Hrd Hard Hpost
  · rcases merr with mei | _
    · run_metrics
      exit_nodep
    · exact absurd rfl Hmerr))

/-- **`AuthInfoFromCtx` in the auth mode `on`** (E3zb): its spec, and with auth on, over the
store's bound request side (`srvAuthBoundM`), the auth info bound to the context too
(`boundSpec`'s `ctxBoundOrTLS`). -/
theorem EtcdServer.AuthInfoFromCtx.wpM (on : Bool)
    (hAuth : EtcdServer.AuthInfoFromCtx.spec (GF := GF) (hG := hG))
    (hAuthB : on = true → EtcdServer.AuthInfoFromCtx.boundSpec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (st : GoInterface) (cca : Bool) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      structFieldRef EtcdServer go!"authStore" s ↦□ st ∗ isReqAuth st E.RD ∗
      srvAuthBoundM on s E ∗
      srvCfgFieldAddr s go!"ClientCertAuthEnabled" ↦□ cca ∗ mvcc.txnCtx ctx cd ∗ E.RD }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"AuthInfoFromCtx"))
      (Val #(GoInterface.ok ctx)))
  {{ (a : Loc) (err : GoInterface), RET (PairV #a #err); E.RD ∗ authInfoOpt a ∗ applyErrIs err ∗
      □ (⌜on = true⌝ → ctxBoundOrTLS s E.authMode (GoInterface.ok ctx) a) }} := by
  cases on
  · iintro %Φ ⟨#Hpkg, #Hst, #Hauth, -, #Hcca, #Hctx, Hrd⟩ HΦ
    iapply (hAuth s st E.RD cca ctx cd) $$ [Hrd] [HΦ]
    · iframe Hrd; iframe #
    · iintro !> %a %err ⟨Hrd, Ha, #Herr⟩
      iapply HΦ; iframe Hrd Ha Herr
      iintro !> %h; cases h
  · iintro %Φ ⟨#Hpkg, #Hst, #Hauth, #Hbd, #Hcca, #Hctx, Hrd⟩ HΦ
    unfold srvAuthBoundM
    iunfold srvAuthBound at Hbd
    icases Hbd with ⟨%st3, #Has3, #Hreqb⟩
    icombine Hst Has3 gives %Heq3
    subst Heq3
    iapply (hAuthB rfl s st E.RD E.authMode cca ctx cd) $$ [Hrd] [HΦ]
    · iframe Hrd; iframe #
    · iintro !> %a %err ⟨Hrd, Ha, #Herr, #Hb⟩
      iapply HΦ; iframe Hrd Ha Herr
      iintro !> -; iexact Hb

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem EtcdServer.processInternalRaftRequestOnce.wp_proofM (on : Bool)
    (hAI : EtcdServer.getAppliedIndex.specM (GF := GF) (hG := hG) on)
    (hCI : EtcdServer.getCommittedIndex.spec (GF := GF) (hG := hG))
    (hFE : EtcdServer.FeatureEnabled.spec (GF := GF) (hG := hG))
    (hEx : exceedsRequestLimit.spec (GF := GF) (hG := hG))
    (hNext : idutil.Generator.Next.spec (GF := GF) (hG := hG))
    (hAuth : EtcdServer.AuthInfoFromCtx.spec (GF := GF) (hG := hG))
    (hAuthB : on = true → EtcdServer.AuthInfoFromCtx.boundSpec (GF := GF) (hG := hG))
    (hRT : getRequestType.spec (GF := GF) (hG := hG))
    (hM : proto.MarshalIRR.spec (GF := GF) (hG := hG))
    (hTO : config.ServerConfig.ReqTimeout.spec (GF := GF) (hG := hG))
    (hSp : trace.SpanFromContext.spec (GF := GF) (hG := hG))
    (hPE : EtcdServer.parseProposeCtxErr.specM (GF := GF) (hG := hG) on)
    (hED : context.ErrDone.spec (GF := GF) (hG := hG))
    (hFB : strconv.FormatBool.spec (GF := GF) (hG := hG))
    (hSec : time.Duration.Seconds.spec (GF := GF) (hG := hG))
    (hWL : prometheus.HistogramVec.WithLabelValues.spec (GF := GF) (hG := hG)) :
    EtcdServer.processInternalRaftRequestOnce.specM (GF := GF) (hG := hG) on := by
  intro s E ρ ctx cd p rq Qh F Hid0
  wp_start as ⟨#Hsrv, Hrd, Hard, Hcred, #Hctx, #Hirr, Hok, ⟨%h0, Hhdr⟩, #HF⟩
  wp_apply wp_with_defer as %defer defer
  ihave ⟨⟨%v, #Hv⟩, #HsrvB⟩ := (isServerReqM_split _ _ _ _).1 $$ Hsrv
  ihave #Hv' := Hv
  iunfold srvReqFieldsAtM at Hv'
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
  iunfold srvIndexInvsM at Hidx
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
    -- `if r.Authenticate == nil { authInfo, err := s.AuthInfoFromCtx(ctx); if err != nil { return
    -- nil, err }; .. }`, joined (`wp_join`): falling through with the header set (`Hhv`), or
    -- returning the error; the rest (`piro_tail`) is verified once, not once per way (the
    -- receiver and the context, read-only from here on, for both)
    ipersist s
    ipersist ctx
    wp_join (Q := fun v => iprop(
        (⌜v = executeVal⌝ ∗ ∃ hv : etcdserverpb.RequestHeader, «$r0_ptr» ↦ hv ∗ ⌜hv.ID' = id⌝ ∗
          structFieldRef etcdserverpb.InternalRaftRequest go!"Header" p ↦ «$r0_ptr» ∗ r_ptr ↦ p ∗
          E.RD ∗ hdrBoundM on s E (GoInterface.ok ctx) ⟨id, hv.Username', hv.AuthRevision'⟩) ∨
        (∃ aei : GoInterfaceOk, ⌜v = returnVal (PairV #Loc.null #(GoInterface.ok aei))⌝ ∗ E.RD ∗
          applyErrIs (GoInterface.ok aei))))
      at next with [«$r0» Hhdr r Hard]
    · cases hau : rq.authenticate with
      | some am =>
        have hla : la ≠ null := fun h => by rw [Hlan.1 h] at hau; cases hau
        (try wp_auto)
        rw [decide_eq_false hla]
        (try wp_auto)
        ileft
        isplitr
        · ipureintro; rfl
        iexists _; iframe «$r0» Hhdr r Hard
        isplitr
        · ipureintro; rfl
        iapply hdrBoundM_empty _ _ _ _ _ rfl
      | none =>
        have hla : la = null := Hlan.2 hau
        (try wp_auto)
        wp_if_destruct
        · wp_apply EtcdServer.AuthInfoFromCtx.wpM on hAuth hAuthB s E v.auth v.cca ctx cd $$ [Hard]
            as %au %aerr ⟨Hard, Hau, #HaE, #Hab⟩
          · iframe Hard; iframe #
            iunfold mvcc.txnCtx; iright; iexact Hctx
          (try wp_auto)
          cases aerr with
          | ok aei =>
            (try wp_auto)
            iright
            iexists aei
            isplitr
            · ipureintro; rfl
            iframe Hard HaE
          | nil =>
            (try wp_auto)
            wp_join iprop(∃ hv : etcdserverpb.RequestHeader, «$r0_ptr» ↦ hv ∗ ⌜hv.ID' = id⌝ ∗
                structFieldRef etcdserverpb.InternalRaftRequest go!"Header" p ↦ «$r0_ptr» ∗ r_ptr ↦ p ∗
                hdrBoundM on s E (GoInterface.ok ctx) ⟨id, hv.Username', hv.AuthRevision'⟩)
              with [«$r0» Hau authInfo Hhdr r] as ⟨%hv, Hhv, %Hhvid, Hhdr, r, #Hhb⟩
            · iexists _; iframe «$r0» Hhdr r
              isplitr
              · ipureintro; rfl
              iapply hdrBoundM_empty _ _ _ _ _ rfl
            · iunfold authInfoOpt at Hau
              icases Hau with (%Hn | ⟨%user, %rev, #Hai⟩)
              · exfalso; simp_all
              ihave #Hhb := hdrBoundM_of_ctxBound on s E (GoInterface.ok ctx) _ id user rev $$ [Hab Hai]
              · iframe Hab Hai
              iunfold authInfoIs at Hai
              icases Hai with ⟨-, #HU, #HR⟩
              (try wp_auto)
              wp_join_done
              iexists _; iframe «$r0» Hhdr r Hhb; ipureintro; rfl
            ileft
            isplitr
            · ipureintro; rfl
            iexists hv; iframe Hhv Hhdr r Hard Hhb; ipureintro; exact Hhvid
        · exact absurd hla Hif
    iintro (⟨%Hv, %hv, Hhv, %Hhvid, Hhdr, r, Hard, #Hhb⟩ | ⟨%aei, %Hv, Hard, #HaE⟩)
    · subst Hv
      (try wp_auto)
      piro_tail
    · subst Hv
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

/-- **The mode-off spec, from the generic one** (a constant result: `reqPropOkM_of_false`). -/
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
  iintro %Φ Hpre HΦ
  iapply (EtcdServer.processInternalRaftRequestOnce.wp_proofM false hAI hCI hFE hEx hNext hAuth (fun h => by cases h)
    hRT hM hTO hSp hPE hED hFB hSec hWL s E ρ ctx cd p rq (fun _ => Qr) F Hid0) $$ [Hpre] [HΦ]
  · icases Hpre with ⟨Ha, Hb, Hc, Hd, He, Hf, Hg, Hok, Hi, Hj⟩
    ihave Hok' := reqPropOkM_of_false ρ.kv rq Qr $$ Hok
    rw [isServerReqM_false]
    iframe Ha Hb Hc Hd He Hf Hg Hok' Hi Hj
  · iintro !> %res %err ⟨Hrd, Hard, Hpost⟩
    iapply HΦ
    iframe Hrd Hard
    icases Hpost with (⟨%He, %hm, %rq', %Hw, HTr, %L, #HL, Hp, -, #HQ, -⟩ | Herr)
    · ileft
      isplitr
      · ipureintro; exact He
      iexists hm, rq'
      iframe HTr
      isplitr
      · ipureintro; exact Hw
      iunfold resPostM at Hp
      icases Hp with ⟨%Hnn, %y, %y', %out, %Hst, Hr1, Hr2, Hr3, Hr4, Hr5, -⟩
      iexists y.log
      iunfold resultIsW
      isplitl [Hr1 Hr2 Hr3 Hr4 Hr5]
      · isplitr
        · ipureintro; exact Hnn
        iexists y, y', out
        iframe Hr1 Hr2 Hr3 Hr4 Hr5
        ipureintro; exact ⟨Hst.1, Hst.2.1, rfl, Hst.2.2.1⟩
      iexists L
      iframe HL HQ
      ipureintro; exact Hst.2.2.2
    · iright; iexact Herr

end proof

end EtcdGrove
end Perennial
