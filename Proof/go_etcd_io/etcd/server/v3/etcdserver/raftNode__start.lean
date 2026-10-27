/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/raftNode__start.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__start
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftLoop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__tick
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__processMessages
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.updateCommittedIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__onStop
public import Spec.go_etcd_io.raft.v3.IsEmptySnap
public import Spec.go_etcd_io.raft.v3.IsEmptyHardState
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetCommit
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetType
public import Spec.google_golang_org.protobuf.proto.Clone
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Fatal
public import Spec.go_uber_org.zap.Duration
public import Spec.go_uber_org.zap.Logger__Warn
public import Proof.go_etcd_io.raft.v3.Linked

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open RaftLink

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

-- (2026-10-22) the unused-variables linter walks the proof's info tree: 8s of this module's CPU
set_option linter.unusedVariables false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem raftNode.start.wp_proof
    (wp_tick : raftNode.tick.spec (GF := GF) (hG := hG))
    (wp_processMessages : raftNode.processMessages.spec (GF := GF) (hG := hG))
    (wp_updateCommittedIndex : updateCommittedIndex.spec (GF := GF) (hG := hG))
    (wp_onStop : raftNode.onStop.spec (GF := GF) (hG := hG))
    (wp_IsEmptySnap : IsEmptySnap.spec (GF := GF) (hG := hG))
    (wp_IsEmptyHardState : IsEmptyHardState.spec (GF := GF) (hG := hG))
    (wp_GetCommit : raftpb.HardState.GetCommit.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.HardState.GetTerm.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Entry.GetType.spec (GF := GF) (hG := hG))
    (wp_Clone : proto.Clone.spec (GF := GF) (hG := hG))
    (wp_Error : zap.Error.spec (GF := GF) (hG := hG))
    (wp_Fatal : zap.Logger.Fatal.spec (GF := GF) (hG := hG))
    (wp_Duration : zap.Duration.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    raftNode.start.spec (GF := GF) (hG := hG) := by
  have wp_IsEmptySnap := wp_IsEmptySnap_nil wp_IsEmptySnap
  have wp_IsEmptyHardState := wp_hardStateAt_IsEmptyHardState wp_IsEmptyHardState
  have wp_GetCommit := wp_hardStateAt_GetCommit wp_GetCommit
  have wp_GetTerm := wp_hardStateAt_GetTerm wp_GetTerm
  have wp_GetType := wp_entryAt_GetType wp_GetType
  intro E γ r rh L R
  letI := srvStor (GF := GF) γ.node
  wp_start as ⟨#Hr, #Hrh, HR, Htok, Hdone, HS⟩
  ihave #Hr' := Hr
  iunfold isRaftNode at Hr'
  iNamed Hr'
  ihave #Henv0 := Henv
  iunfold rnEnvOk at Henv0
  icases Henv0 with ⟨-, %HEn, -⟩
  have HEai : uint.Z E.γr.raft.ai0 = γ.pre.length := HEn.2.2
  wp_auto
  simp only [time.Second]
  iunfold isRNTicker at Htki
  icases Htki with ⟨%tc, #Htc, #Htcb, #HtkStop⟩
  iunfold isRaftNodeIfc at Hni
  icases Hni with ⟨%ni, %Hnieq, -, #HReady, #HAdv, #HTick, #HStop, #HRI, #Hisn⟩
  subst Hnieq
  iunfold isRNTransport at Htri
  icases Htri with ⟨%ti, %Htieq, #HSend, #HTrStop⟩
  subst Htieq
  iunfold isRNWal at Hsti
  icases Hsti with ⟨%si, %Hsieq, #HSave, #HClose, #HSaveSnap, #HSync⟩
  subst Hsieq
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hrpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hpbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  iunfold rnStopBag at Hstci
  icases Hstci with ⟨%γst, #Hstb⟩
  ihave #Hrh0 := Hrh
  iunfold isReadyHandler at Hrh
  icases Hrh with ⟨%gl, %ul, %uls, %uci, #Hgl, #Hul, #Huls, #Huci, #Hglt, #Hult, #Hulst, #Hucit⟩
  iunfold isRNTimeoutDetector at Htdi
  icases Htdi with ⟨%Htdnn, #HtdReset, #HtdObserve⟩
  ihave Hsi : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iunfold srvInit at Hsi
  icases Hsi with ⟨⟨⟨%ghl, #Hghl, #Hghls⟩, ⟨%gil, #Hgil, #Hgils⟩, ⟨%gpc, #Hgpc, #Hgpcs⟩,
    ⟨%clc, #Hclc, #Hclcs⟩, -⟩, -⟩
  iunfold gaugeSetSpec at Hghls Hgils Hgpcs
  iunfold go_etcd_io.etcd.server.v3.storage.mvcc.counterSpec at Hclcs
  icases Hclcs with ⟨#HlcInc, -⟩
  wp_auto
  ipersist internalTimeout
  wp_apply wp_fork $$ [Htok Hdone r rh HR HS]
  · -- the goroutine
    wp_apply wp_with_defer as %defer defer
    -- (D22a) `raftTerm`, the latest non-empty `HardState`'s term, carried to the batches; (D22 S-b)
    -- `0` or a term raft handed out the witness of (`rnRtOk`); (D22l) `0` or the term of raft's
    -- `prevHardSt` `p`, the driver's (`rnLoopTokP`)
    iunfold rnLoopTok at Htok
    icases Htok with ⟨%p0, Htok⟩
    ihave HI : iprop(∃ (L' : List EntryModel) (b : Bool) (rt : w64) (p : HardStateM),
        "islead" ∷ islead_ptr ↦ b ∗ "raftTerm" ∷ raftTerm_ptr ↦ rt ∗
        "%Hrt" ∷ ⌜uint.Z rt = 0 ∨ rt = p.Term'⌝ ∗
        "Htok" ∷ rnLoopTokP γ L' p ∗ "HR" ∷ R ∗ "HS" ∷ E.S) $$ [islead raftTerm Htok HR HS]
    · iexists L, false, _, p0
      iframe
      ipureintro; left; rfl
    wp_for HI
    rw [method_unfold (t := go.GoType.PointerType raftNode.ty) (m := go!"Ready")]
    wp_auto_lc 4
    rw [method_unfold (t := go.GoType.PointerType raftNodeConfig.ty) (m := go!"Ready")]
    wp_auto
    wp_apply HReady as %rc #Hrc
    wp_apply_core chan.wp_select_blocking_nil
    -- `<-r.ticker.C`: a tick
    iapply BigAndL.bigAndL_cons.2
    isplit
    · icases Htcb with (%Htcn | ⟨%γt, #Htb⟩)
      · iright
        iapply chan.nilClausePre_recv time.Time _ _ Htcn
      ileft
      simp only [chan.blockingClausePre]
      iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tc, γt
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ Htb
      iapply bag_recv_au γt tc _ _ $$ [$Hlc1 $Hlc2] Htb
      inext
      iintro %t -
      wp_auto
      wp_apply wp_tick E γ r $$ [$Hpkg $Hr]
      wp_for_post
      iframe
      iexists L', b, rt, p
      iframe
      ipureintro; exact Hrt
    -- `rd := <-r.Ready()`
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      simp only [chan.blockingClausePre]
      iunfold rnLoopTokP at Htok
      icases Htok with ⟨%sent, %cums, Hdrv, Hprod, Hauth, %Hcums, %Hix⟩
      iunfold rnDrv at Hdrv
      icases Hdrv with ⟨Hdrv, Hcfg⟩
      icases Draft.isReadyChan_recvAu γ.nl rc γ.node.cl srvClusterN γ.id (rnDrvSt γ L' p) _ rfl
        $$ Hrc Hisn Hdrv with ⟨%γc, #Hch, Hau⟩
      iexists Ready, inferInstance, inferInstance, inferInstance, inferInstance, rc, γc
      isplitr
      · ipureintro; rfl
      isplitr
      · iexact Hch
      iapply Hau $$ [$Hlc1 $Hlc2]
      inext
      iintro %rd ⟨%ce0, %es0, %h0, %Lo, #Hcea0, #Hcom0, Hrs0, Hrest, Hdrv⟩
      -- (2026-10-27) the log's indices, at the start's index (`rnEnvOk`'s)
      have HLi : srvIdxOkW E.γr.raft.ai0 L' := by
        obtain ⟨ai, hai, hidx⟩ := Hix
        have h2 : uint.Z ai = uint.Z E.γr.raft.ai0 := by rw [hai, HEai]
        have hae : ai = E.γr.raft.ai0 := by word
        rw [← hae]; exact hidx
      imod rn_ready_recv E γ L' p rd ce0 es0 h0 Lo HLi $$ Henv Hrsb Hcfg Hcea0 Hcom0 Hrs0 Hrest
        Hdrv with ⟨%ce, %es, %p', Hdata, Hbusy, #Hdlb, %HidxN⟩
      -- (D43 M3) the driver's view after `L'`, apart
      iunfold rnBusy at Hbusy
      icases Hbusy with ⟨Hbusy, Hcv⟩
      iunfold rnReadyData at Hdata
      icases Hdata with ⟨%ceL, %esL, %msL, %hs, #Hce, #Hcea, #HC, #Hes, #Hesa, Happ, #Hms, Hmsok,
        #Hss, #Hhs, %Hp', ⟨%rsL, #Hrs, #Hrsok⟩, %Hsnapnil⟩
      wp_auto
      -- the `SoftState`: the leader, the gauges, the ready handler
      wp_join iprop(∃ b' : Bool, islead_ptr ↦ b' ∗ rd_ptr ↦ rd ∗ rh_ptr ↦ rh ∗ r_ptr ↦ r)
        at next with [islead rd rh r] as ⟨%b', islead, rd, rh, r⟩
      · wp_if_destruct
        · -- nil
          isplitr
          · itrivial
          iexists _; iframe islead rd rh r
        · iunfold softStateAt at Hss
          iunfold softStateRO at Hss
          icases Hss with (%Hssn | ⟨%lead, %rs, #Hlead, #Hrs⟩)
          · exact absurd Hssn Hif
          simp only [None']
          wp_auto
          -- `newLeader`
          wp_join (Q := fun v => iprop(∃ nl : Bool, ⌜v = #nl⌝ ∗ rh_ptr ↦ rh ∗ rd_ptr ↦ rd))
            with [rh rd]
          · iexists false
            iframe
            ipureintro; rfl
          · wp_apply Hglt as %gv -
            iexists _
            iframe
            ipureintro; rfl
          iintro ⟨%nl, %Hv, rh, rd⟩
          subst Hv
          wp_auto
          -- `leaderChanges.Inc()`
          wp_join with [rh rd]
          · wp_apply HlcInc
            wp_join_done
          -- `hasLeader.Set(0 or 1)`
          wp_join with [rh rd]
          · wp_apply Hghls
            wp_join_done
          · wp_apply Hghls
            wp_join_done
          wp_apply Hult
          -- `isLeader.Set(1 or 0)`
          wp_join with [rh rd]
          · wp_apply Hgils
            wp_join_done
          · wp_apply Hgils
            wp_join_done
          wp_apply Hulst
          wp_apply HtdReset
          isplitr
          · itrivial
          iexists _
          iframe islead rd rh r
      irename Hlc3 => HlcA
      irename Hlc4 => HlcB
      -- the read states: the last one to `readStateC` (or a timeout, or `<-r.stopped`: return)
      ihave %Hrsl := ownSlice_len _ _ _ $$ Hrs
      ihave #Hrsci' := Hrsci
      iunfold isRNReadStateC at Hrsci'
      iunfold isReadStateC at Hrsci'
      icases Hrsci' with ⟨%γrs, #Hrsb⟩
      wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∗ rd_ptr ↦ rd ∗ r_ptr ↦ r) ∨
          (⌜v = returnVal #()⌝ ∗ E.ST))) with [rd r]
      · -- no read states
        ileft
        iframe
        try (ipureintro; rfl)
      · -- `len(rd.ReadStates) != 0`: send the last one (or time out, or return on `r.stopped`)
        have hlen : 0 < rsL.length := by
          have h1 := Hrsl.1
          have hne : rd.ReadStates'.len ≠ W64 0 := by
            intro h; apply Hif; rw [h]
          have h3 : sint.Z rd.ReadStates'.len ≠ 0 := by
            intro h; apply hne; word
          have h2 := Hrsl.2
          have h4 : sint.nat rd.ReadStates'.len = (sint.Z rd.ReadStates'.len).toNat := rfl
          omega
        obtain ⟨rs, Hrs_lookup⟩ : ∃ rs, rsL[rsL.length - 1]? = some rs :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have hpos : 0 < sint.Z rd.ReadStates'.len := by
          have h4 : sint.nat rd.ReadStates'.len = (sint.Z rd.ReadStates'.len).toNat := rfl
          have h2 := Hrsl.2
          have h1 := Hrsl.1
          omega
        have hz : sint.Z (rd.ReadStates'.len - W64 1) = sint.Z rd.ReadStates'.len - 1 := by word
        rw [if_pos ⟨by omega, by omega⟩]
        wp_apply wp_load_slice_index rd.ReadStates' (sint.Z (rd.ReadStates'.len - W64 1)) rsL
          DFrac.discard rs (by omega) $$ [] as -
        · iframe Hrs
          ipureintro
          rw [← Hrs_lookup]
          congr 1
          have h4 : sint.nat rd.ReadStates'.len = (sint.Z rd.ReadStates'.len).toNat := rfl
          have h1 := Hrsl.1
          omega
        wp_apply (lc := 2) time.wp_After as %ach %γa #Ha
        ihave #Hrsk := (BigSepL.bigSepL_lookup (Φ := fun _ rs => srvReadStateOk (GF := GF) E.γr.raft E.RQ rs)
          Hrs_lookup) $$ Hrsok
        wp_apply_core chan.wp_select_blocking
        -- `r.readStateC <- rs`
        iapply BigAndL.bigAndL_cons.2
        isplit
        · simp only [chan.blockingClausePre]
          iexists ReadState, inferInstance, inferInstance, inferInstance, inferInstance, rsc, γrs, rs
          isplitr
          · ipureintro; exact ⟨rfl, rfl⟩
          isplitr
          · iapply is_bag_is_chan $$ Hrsb
          iapply bag_send_au γrs rsc _ rs _ $$ [$Hlc1 $Hlc2] Hrsb Hrsk
          inext
          try wp_auto
          ileft
          iframe
          try (ipureintro; rfl)
        -- `<-time.After(internalTimeout)`: a warning
        iapply BigAndL.bigAndL_cons.2
        isplit
        · simp only [chan.blockingClausePre]
          iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, ach, γa
          isplitr
          · ipureintro; rfl
          isplitr
          · iapply is_bag_is_chan $$ Ha
          iapply bag_recv_au γa ach _ _ $$ [$Hlc1 $Hlc2] Ha
          inext
          iintro %t -
          wp_auto
          wp_apply wp_Duration _ _ $$ [$Hzap] as %f1 -
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %fsl -
          wp_auto
          wp_apply wp_Warn lg _ _ $$ [$Hzap]
          · ipureintro; exact Hlgnn
          try wp_auto
          ileft
          iframe
          try (ipureintro; rfl)
        -- `<-r.stopped`: return
        iapply BigAndL.bigAndL_cons.2
        isplit
        · simp only [chan.blockingClausePre]
          iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stc, γst
          isplitr
          · ipureintro; rfl
          isplitr
          · iapply is_bag_is_chan $$ Hstb
          iapply bag_recv_au γst stc _ _ $$ [$Hlc1 $Hlc2] Hstb
          inext
          iintro %u HST
          try wp_auto
          iright
          iframe HST
          ipureintro; rfl
        iapply BigAndL.bigAndL_nil.2
        itrivial
      iintro (⟨%Hv, rd, r⟩ | ⟨%Hv, HST⟩)
      rotate_left
      · -- returned (`<-r.stopped`): the deferred `onStop`
        subst Hv
        wp_auto
        wp_for_post
        wp_apply wp_onStop E γ r $$ [$Hpkg $Hr $Hdone $HST]
        itrivial
      subst Hv
      wp_auto_lc 3
      -- (D22a) `if !raft.IsEmptyHardState(rd.HardState) { raftTerm = rd.HardState.GetTerm() }`
      wp_apply wp_IsEmptyHardState rd.HardState' hs $$ [$Hrpkg $Hhs] as %ehs0 %Hehs0
      -- (D22l) the term recorded is `0` or `prevHardSt`'s after the `Ready` (`p'`)
      wp_join iprop(∃ rt' : w64, raftTerm_ptr ↦ rt' ∗ rd_ptr ↦ rd ∗
          ⌜uint.Z rt' = 0 ∨ rt' = p'.Term'⌝) at next
        with [raftTerm rd] as ⟨%rt', raftTerm, rd, %Hrt'⟩
      · cases ehs0
        · -- a non-empty hard state: `prevHardSt`'s now, its term recorded
          have Hne : hs ≠ HardStateModel.empty := fun h => absurd (Hehs0.2 h) (by decide)
          wp_auto
          wp_apply wp_GetTerm rd.HardState' hs $$ [$Hpbpkg $Hhs]
          (try wp_auto)
          isplitr
          · itrivial
          iexists _
          iframe
          ipureintro; right
          rw [Hp', phsNext_toM_ne p hs Hne]; rfl
        · (try wp_auto)
          isplitr
          · itrivial
          iexists _
          iframe
          ipureintro
          rw [Hp', phsNext_toM_empty p hs (Hehs0.1 rfl)]; exact Hrt
      -- (D22 S-b, D22l) the batch's raft term, with the witness bounding the batch
      -- `notifyc` (D43 M3: the two-send idiom, depositing the view after the batch if it goes
      -- along, `rnApR`), `raftAdvancedC`
      wp_apply chan.wp_make2 (V := Unit) $$ [] as %nc %γnc0 ⟨#Hncch, %Hncap, Hncown⟩
      · ipureintro; decide
      imod start_notify (rnApR γ L' ce) nc γnc0 (by rw [Hncap]; rfl) $$ Hncch Hncown with
        ⟨%γnc, %Hγnc, #Hncb, Hnsnd, Hnrcv⟩
      -- (D43 M3) the view: with the batch if `rnHands` (with the committed log handed out), else
      -- kept
      ihave Hgive : iprop(rnApGive γ L' ce ∗ (if rnHands γ ce then iprop(True) else rnCfgAt γ L'))
        $$ [Hcv]
      · unfold rnApGive
        split
        · iframe Hcv Hdlb
        · iframe Hcv
      icases Hgive with ⟨Hgive, Hkeep⟩
      wp_apply chan.wp_make2 (V := Unit) $$ [] as %ac %γac ⟨#Hacch, -, Hacown⟩
      · ipureintro; decide
      -- (D19i part 1) `raftAdvancedC`: a broadcast channel, closed after `Advance`
      -- its close carries the storage's floor past the batch (`node.Advance`'s)
      imod alloc_stop_chan (E := ⊤) (memFloorAtLeast γ.ms γ.γs (γ.pre ++ L' ++ ce).length) γac ac
        $$ Hacch Hacown with Hacp
      icases ownStopChan_pending_unknown _ _ _ $$ Hacp with ⟨Hacp, #HacU⟩
      -- `proto.Clone(rd.Snapshot)` of the nil snapshot, twice
      rw [Hsnapnil]
      ihave #Hppkg : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
      · iPkgInit
      wp_apply wp_Clone.2 $$ [$Hppkg]
      rw [Hsnapnil]
      wp_apply wp_Clone.2 $$ [$Hppkg]
      irename notifyc => Hncl
      irename raftAdvancedC => Hacl
      irename raftTerm => Hrtl
      ipersist ap
      ihave #Hapf := ap
      iStructNamed Hapf
      -- (`wp_bind` then `iapply`: `wp_apply` fails silently here, framing the generic `R`)
      -- the batch's committed log and indices, from `E.C` (`rnEnvOk`)
      ihave #Henv' := Henv
      iunfold rnEnvOk at Henv'
      icases Henv' with ⟨-, -, -, -, -, -, -, #HCback, -⟩
      ihave #HCl := HCback $$ %(L' ++ ce) HC
      icases HCl with ⟨#HLb, %HidxOk⟩
      wp_bind (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.updateCommittedIndex))
        (Val #ap_ptr)) (Val #rh))
      iapply (wp_updateCommittedIndex ap_ptr rh rd.CommittedEntries' ceL L' ce R E.γr null) $$ [HR]
      · iframe HR; iframe #
        isplitr
        · ipureintro; exact HidxOk
        ileft; ipureintro; rfl
      inext
      iintro ⟨HR, #Hclast, -⟩
      wp_auto
      -- `cum` extended with the batch, then `applyc <- ap` (or `<-r.stopped`)
      imod cum_extend γ.cum cums L' ce sent.length Hcums.1 Hcums.2 $$ Hauth with ⟨Hauth, #Hcn, #Hcn1⟩
      wp_apply_core chan.wp_select_blocking_nil
      iapply BigAndL.bigAndL_cons.2
      isplit
      · ileft
        simp only [chan.blockingClausePre]
        iexists toApply, inferInstance, inferInstance, inferInstance, inferInstance, apc,
          γ.ap.chanName, _
        isplitr
        · ipureintro; exact ⟨rfl, rfl⟩
        ihave #Hsp := Hapci
        iunfold isRNApplyc at Hsp
        ihave #Hapci' := Hsp
        iunfold isSpsc at Hapci'
        icases Hapci' with ⟨#Hapch, -⟩
        isplitr
        · iexact Hapch
        iapply spsc_send_au γ.ap apc (rnApP E γ) _ sent _ _ $$ Hsp [$Hlc1 $Hlc2 $Hlc3]
          [$Hprod Hnrcv Hgive]
        · iunfold rnApP
          ileft
          iunfold rnApN
          iexists L', ce, ceL
          simp only [Int.toNat_natCast]
          iframe Hcn Hcn1 Hce Hcea HC
          isplitr
          · ipureintro; trivial
          isplitl [Hnrcv]
          · iexists γnc
            iframe Hncb Hnrcv
          isplitl [Hgive]
          · iexact Hgive
          isplitr
          · iunfold rnAdvChan
            iexists γac
            iexact HacU
          isplitr
          · iexact Hclast
          iunfold rnRtOk; itrivial
        inext
        iintro Hprod
        wp_auto
        -- `if islead { r.transport.Send(r.processMessages(rd.Messages)) }`
        -- (D21 stage M1) the messages' bundles go to the transport here, or stay for a follower's
        wp_join iprop(rh_ptr ↦ rh ∗ rd_ptr ↦ rd ∗ r_ptr ↦ r ∗ islead_ptr ↦ b' ∗ E.S ∗
            (⌜b' = true⌝ ∨ [∗list] m ∈ msL, rnMsgR E γ m))
          with [rh rd r islead HS Hmsok] as ⟨rh, rd, r, islead, HS, Hmsok⟩
        -- the cases that reach the join with nothing sent close by framing (`ileft` once the
        -- bundles went to the transport)
        all_goals first | (iframe; done) | (iframe; ileft; itrivial) | skip
        · wp_apply wp_processMessages E γ r _ msL $$ [$Hpkg $Hr $Hms $Hmsok] as %out ⟨%outL, Hout, Houtok⟩
          -- (`wp_apply HSend` here trips over an unknown free variable inside the join's case)
          wp_bind (App (Val #(methods ti.ty go!"Send" ti.v)) (Val #out))
          iapply HSend $$ [Hout Houtok HS]
          · iframe
          inext
          iintro HS
          (try wp_auto)
          wp_join_done
          all_goals first | (iframe; done) | (iframe; ileft; itrivial) | skip
        -- `if !raft.IsEmptySnap(raftSnap)`: the snapshot is nil
        wp_apply wp_IsEmptySnap $$ [$Hrpkg]
        -- `r.storage.Save(rd.HardState, rd.Entries)`, `lg.Fatal` on an error
        wp_apply HSave $$ [$Hhs $Hes $Hesa] as %err -
        rcases err with ei | _
        · wp_auto
          wp_apply wp_Error $$ [$Hzap] as %f -
          wp_apply wp_slice_literal
          try (isplitr; (ipureintro; rfl))
          try iintro %_ ⟨_, -⟩
          try wp_auto
          wp_apply wp_Fatal lg $$ [$Hzap] as %v Hf
          · ipureintro; exact Hlgnn
          iexfalso
          iexact Hf
        wp_auto
        -- `if !raft.IsEmptyHardState(rd.HardState) { proposalsCommitted.Set(..) }`
        wp_apply wp_IsEmptyHardState rd.HardState' hs $$ [$Hrpkg $Hhs] as %ehs -
        wp_join at next with [rh rd r islead]
        · cases ehs
          · wp_auto
            wp_apply wp_GetCommit rd.HardState' hs $$ [$Hpbpkg $Hhs]
            wp_apply Hgpcs
            wp_join_done
          · wp_auto
            wp_join_done
        -- the snapshot is nil: no `Sync`
        wp_apply wp_IsEmptySnap $$ [$Hrpkg]
        -- `r.raftStorage.Append(rd.Entries)`: the right becomes the receipt
        ihave #HApp := Hmsi
        iunfold isRNMemStor at HApp
        ispecialize HApp $$ %rd.Entries' %esL %es
        wp_apply HApp $$ [$Hes $Hesa $Happ] as Hrcpt
        -- the confChange scan (`confChanged` only decides an extra `notifyc` send)
        ihave %Hcelen := ownSlice_len _ _ _ $$ Hce
        ihave #Hcea' := Hcea
        iunfold entriesAt at Hcea'
        icases Hcea' with ⟨%Hcl, #Hcef⟩
        -- (D43 M3) its result: whether the batch has a `ConfChange` entry (`ccIn`)
        wp_join iprop(∃ cc : Bool, confChanged_ptr ↦ cc ∗ ⌜cc = ccIn ce⌝) at next
            with [i confChanged ent]
          as ⟨%cc, confChanged, %Hcc⟩
        · ihave IH : iprop(∃ (n : w64) (e : Loc),
              "i" ∷ i_ptr ↦ n ∗ "confChanged" ∷ confChanged_ptr ↦ false ∗ "ent" ∷ ent_ptr ↦ e ∗
              "%Hn" ∷ ⌜0 ≤ sint.Z n⌝ ∗
              "%Hnc" ∷ ⌜∀ (k : Nat) (m : EntryModel), k < sint.nat n → ce[k]? = some m →
                m.typ ≠ W32 1⌝) $$ [i confChanged ent]
          · iexists W64 0, _
            iframe
            ipureintro
            refine ⟨by decide, fun k m hk _ => absurd hk (by simp [sint.nat])⟩
          wp_for IH
          wp_if_destruct
          · rw [if_pos ⟨Hn, Hif⟩]
            have hlt : sint.nat n < ceL.length := by word
            obtain ⟨e, He⟩ : ∃ e, ceL[sint.nat n]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
            obtain ⟨m, Hm⟩ : ∃ m, ce[sint.nat n]? = some m :=
              ⟨_, List.getElem?_eq_getElem (by rw [← Hcl]; exact hlt)⟩
            wp_apply wp_load_slice_index rd.CommittedEntries' (sint.Z n) ceL DFrac.discard e Hn $$ [] as -
            · iframe Hce
              ipureintro; exact He
            ihave #He' := Hcef $$ %(sint.nat n) %e %m %He %Hm
            wp_apply wp_GetType e m $$ [$Hpbpkg $He']
            wp_if_destruct
            · -- a conf change: `confChanged = true; break`
              wp_for_post
              isplitr
              · itrivial
              iexists true
              iframe
              ipureintro
              symm
              unfold ccIn
              refine List.any_eq_true.2 ⟨m, List.mem_of_getElem? Hm, ?_⟩
              simp only [decide_eq_true_eq]
              first | exact Hif | (simp at Hif; exact Hif) | word
            · wp_for_post
              iframe
              iexists _, e
              iframe
              ipureintro
              refine ⟨by word, fun k m' hk hm' => ?_⟩
              have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by
                show (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1
                have : sint.Z (n + W64 1) = sint.Z n + 1 := by word
                rw [this]; omega
              rw [hn1] at hk
              rcases Nat.lt_or_ge k (sint.nat n) with hk' | hk'
              · exact Hnc k m' hk' hm'
              · have hkn : k = sint.nat n := by omega
                subst hkn
                rw [Hm] at hm'
                cases hm'
                intro hty
                apply Hif
                first | exact hty | (simp; exact hty) | (rw [hty]; rfl) | word
          · isplitr
            · itrivial
            iexists false
            iframe
            ipureintro
            symm
            unfold ccIn
            refine List.any_eq_false.2 fun m hm => ?_
            obtain ⟨k, hk⟩ := List.getElem?_of_mem hm
            have hkl : k < ce.length := (List.getElem?_eq_some_iff.1 hk).1
            have hge : ce.length ≤ sint.nat n := by
              have : ¬ (sint.Z n < sint.Z rd.CommittedEntries'.len) := by
                first | exact Hif | (intro h; exact Hif ⟨Hn, h⟩) | word
              rw [← Hcl]; word
            simpa using Hnc k m (by omega) hk
        -- `if !islead { .. } else { notifyc <- struct{}{} }`
        cases b'
        · -- a follower: `msgs := r.processMessages(rd.Messages)`, `notifyc <- `, then (on a conf
          -- change) a second `notifyc` send or `<-r.stopped`, `r.transport.Send(msgs)`
          wp_auto
          icases Hmsok with (%Hlead | Hmsok)
          · cases Hlead
          wp_apply wp_processMessages E γ r _ msL $$ [$Hpkg $Hr $Hms $Hmsok] as %out ⟨%outL, Hout, Houtok⟩
          wp_apply wp_notify_send1 γnc nc _ $$ [$Hncb $Hnsnd] as Hnsnd
          cases cc
          · wp_auto
            wp_bind (App (Val #(methods ti.ty go!"Send" ti.v)) (Val #out))
            iapply HSend $$ [Hout Houtok HS]
            · iframe
            inext
            iintro HS
            (try wp_auto)
            -- `r.Advance()`: the driver moves to `L' ++ ce`
            rw [method_unfold (t := go.GoType.PointerType raftNode.ty) (m := go!"Advance")]
            wp_auto
            rw [method_unfold (t := go.GoType.PointerType raftNodeConfig.ty) (m := go!"Advance")]
            wp_auto
            -- (D43 M3) the view after the batch: no conf entry, the loop's own
            ihave Hcv' := rnCfgAt_back_false γ _ L' ce HidxOk.2 Hcc.symm $$ Hkeep
            ihave HAdv' := HAdv $$ %L' %ce %es %p'
            wp_apply HAdv' $$ [$Hbusy $Hcv' $Hrcpt] as ⟨Hdrv, #Hfl⟩
            -- `close(raftAdvancedC)`, with the floor's witness
            wp_apply wp_stop_chan_close ac γac _ $$ [$Hacp] as -
            · imodintro; iexact Hfl
            (try wp_auto)
            wp_for_post
            iframe
            iexists (L' ++ ce), false, rt', p'
            iframe
            isplitr
            · ipureintro; exact Hrt'
            iunfold rnLoopTokP
            iexists _, cums ++ [L' ++ ce]
            iframe
            isplitr
            · ipureintro
              simp only [List.length_append, List.length_singleton, List.getLast?_append, List.getLast?_singleton]
              constructor
              · omega
              · rfl
            ipureintro; exact ⟨E.γr.raft.ai0, HEai, HidxN⟩
          · wp_auto
            wp_apply_core chan.wp_select_blocking_nil
            iapply BigAndL.bigAndL_cons.2
            isplit
            · ileft
              simp only [chan.blockingClausePre]
              iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nc, γnc.ch, ()
              isplitr
              · ipureintro; exact ⟨rfl, rfl⟩
              isplitr
              · iapply is_notify_is_chan γnc nc _ $$ Hncb
              iapply notify_send2_au γnc nc _ _ $$ [$HlcA $HlcB] Hncb Hnsnd
              inext
              iintro ⟨-, HRr⟩
              wp_auto
              wp_bind (App (Val #(methods ti.ty go!"Send" ti.v)) (Val #out))
              iapply HSend $$ [Hout Houtok HS]
              · iframe
              inext
              iintro HS
              (try wp_auto)
              -- `r.Advance()`: the driver moves to `L' ++ ce`
              rw [method_unfold (t := go.GoType.PointerType raftNode.ty) (m := go!"Advance")]
              wp_auto
              rw [method_unfold (t := go.GoType.PointerType raftNodeConfig.ty) (m := go!"Advance")]
              wp_auto
              -- (D43 M3) the view after the batch: the second send's, or the loop's own (static)
              ihave Hcv' := rnCfgAt_back_true γ L' ce Hcc.symm $$ [$Hkeep $HRr]
              ihave HAdv' := HAdv $$ %L' %ce %es %p'
              wp_apply HAdv' $$ [$Hbusy $Hcv' $Hrcpt] as ⟨Hdrv, #Hfl⟩
              -- `close(raftAdvancedC)`, with the floor's witness
              wp_apply wp_stop_chan_close ac γac _ $$ [$Hacp] as -
              · imodintro; iexact Hfl
              (try wp_auto)
              wp_for_post
              iframe
              iexists (L' ++ ce), false, rt', p'
              iframe
              isplitr
              · ipureintro; exact Hrt'
              iunfold rnLoopTokP
              iexists _, cums ++ [L' ++ ce]
              iframe
              isplitr
              · ipureintro
                simp only [List.length_append, List.length_singleton, List.getLast?_append, List.getLast?_singleton]
                constructor
                · omega
                · rfl
              ipureintro; exact ⟨E.γr.raft.ai0, HEai, HidxN⟩
            iapply BigAndL.bigAndL_cons.2
            isplit
            · ileft
              simp only [chan.blockingClausePre]
              iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stc, γst
              isplitr
              · ipureintro; rfl
              isplitr
              · iapply is_bag_is_chan $$ Hstb
              iapply bag_recv_au γst stc _ _ $$ [$HlcA $HlcB] Hstb
              inext
              iintro %u HST
              wp_auto
              wp_for_post
              wp_apply wp_onStop E γ r $$ [$Hpkg $Hr $Hdone $HST]
              itrivial
            iapply BigAndL.bigAndL_nil.2
            itrivial
        · -- the leader: `notifyc <- struct{}{}`, then (on a conf change, D43 M3: the fork's
          -- leader wait) a second `notifyc` send or `<-r.stopped`
          wp_auto
          wp_apply wp_notify_send1 γnc nc _ $$ [$Hncb $Hnsnd] as Hnsnd
          cases cc
          · wp_auto
            -- `r.Advance()`: the driver moves to `L' ++ ce`
            rw [method_unfold (t := go.GoType.PointerType raftNode.ty) (m := go!"Advance")]
            wp_auto
            rw [method_unfold (t := go.GoType.PointerType raftNodeConfig.ty) (m := go!"Advance")]
            wp_auto
            -- (D43 M3) the view after the batch: no conf entry, the loop's own
            ihave Hcv' := rnCfgAt_back_false γ _ L' ce HidxOk.2 Hcc.symm $$ Hkeep
            ihave HAdv' := HAdv $$ %L' %ce %es %p'
            wp_apply HAdv' $$ [$Hbusy $Hcv' $Hrcpt] as ⟨Hdrv, #Hfl⟩
            -- `close(raftAdvancedC)`, with the floor's witness
            wp_apply wp_stop_chan_close ac γac _ $$ [$Hacp] as -
            · imodintro; iexact Hfl
            (try wp_auto)
            wp_for_post
            iframe
            iexists (L' ++ ce), true, rt', p'
            iframe
            isplitr
            · ipureintro; exact Hrt'
            iunfold rnLoopTokP
            iexists _, cums ++ [L' ++ ce]
            iframe
            isplitr
            · ipureintro
              simp only [List.length_append, List.length_singleton, List.getLast?_append, List.getLast?_singleton]
              constructor
              · omega
              · rfl
            ipureintro; exact ⟨E.γr.raft.ai0, HEai, HidxN⟩
          · wp_auto
            wp_apply_core chan.wp_select_blocking_nil
            iapply BigAndL.bigAndL_cons.2
            isplit
            · ileft
              simp only [chan.blockingClausePre]
              iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nc, γnc.ch, ()
              isplitr
              · ipureintro; exact ⟨rfl, rfl⟩
              isplitr
              · iapply is_notify_is_chan γnc nc _ $$ Hncb
              iapply notify_send2_au γnc nc _ _ $$ [$HlcA $HlcB] Hncb Hnsnd
              inext
              iintro ⟨-, HRr⟩
              wp_auto
              -- `r.Advance()`: the driver moves to `L' ++ ce`
              rw [method_unfold (t := go.GoType.PointerType raftNode.ty) (m := go!"Advance")]
              wp_auto
              rw [method_unfold (t := go.GoType.PointerType raftNodeConfig.ty) (m := go!"Advance")]
              wp_auto
              -- (D43 M3) the view after the batch: the second send's, or the loop's own (static)
              ihave Hcv' := rnCfgAt_back_true γ L' ce Hcc.symm $$ [$Hkeep $HRr]
              ihave HAdv' := HAdv $$ %L' %ce %es %p'
              wp_apply HAdv' $$ [$Hbusy $Hcv' $Hrcpt] as ⟨Hdrv, #Hfl⟩
              -- `close(raftAdvancedC)`, with the floor's witness
              wp_apply wp_stop_chan_close ac γac _ $$ [$Hacp] as -
              · imodintro; iexact Hfl
              (try wp_auto)
              wp_for_post
              iframe
              iexists (L' ++ ce), true, rt', p'
              iframe
              isplitr
              · ipureintro; exact Hrt'
              iunfold rnLoopTokP
              iexists _, cums ++ [L' ++ ce]
              iframe
              isplitr
              · ipureintro
                simp only [List.length_append, List.length_singleton, List.getLast?_append, List.getLast?_singleton]
                constructor
                · omega
                · rfl
              ipureintro; exact ⟨E.γr.raft.ai0, HEai, HidxN⟩
            iapply BigAndL.bigAndL_cons.2
            isplit
            · ileft
              simp only [chan.blockingClausePre]
              iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stc, γst
              isplitr
              · ipureintro; rfl
              isplitr
              · iapply is_bag_is_chan $$ Hstb
              iapply bag_recv_au γst stc _ _ $$ [$HlcA $HlcB] Hstb
              inext
              iintro %u HST
              wp_auto
              wp_for_post
              wp_apply wp_onStop E γ r $$ [$Hpkg $Hr $Hdone $HST]
              itrivial
            iapply BigAndL.bigAndL_nil.2
            itrivial
      iapply BigAndL.bigAndL_cons.2
      isplit
      · ileft
        simp only [chan.blockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stc, γst
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply is_bag_is_chan $$ Hstb
        iapply bag_recv_au γst stc _ _ $$ [$HlcA $HlcB] Hstb
        inext
        iintro %u HST
        wp_auto
        wp_for_post
        wp_apply wp_onStop E γ r $$ [$Hpkg $Hr $Hdone $HST]
        itrivial
      iapply BigAndL.bigAndL_nil.2
      itrivial
    -- `<-r.stopped`: return (the deferred `onStop`)
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stc, γst
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ Hstb
      iapply bag_recv_au γst stc _ _ $$ [$Hlc1 $Hlc2] Hstb
      inext
      iintro %u HST
      wp_auto
      wp_for_post
      wp_apply wp_onStop E γ r $$ [$Hpkg $Hr $Hdone $HST]
      itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
