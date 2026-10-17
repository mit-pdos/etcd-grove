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
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__persistRaftData
public import Spec.go_etcd_io.raft.v3.IsEmptySnap
public import Spec.go_etcd_io.raft.v3.IsEmptyHardState
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetCommit
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Fatal
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetType
public import Spec.google_golang_org.protobuf.proto.Clone
public import Spec.go_uber_org.zap.Duration
public import Spec.go_uber_org.zap.Logger__Warn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option hygiene false in
/-- A return of the loop's goroutine (etcd-io/etcd#22223): its deferred closure, with
asynchronous storage writes off (`"#Hasync"`): `r.cancelStorageResponses()`, then `r.onStop()`. -/
local macro "rn_stop" : tactic => `(tactic| (
  (try wp_auto)
  wp_bind (App (Val #csr) (Val #()))
  iapply Hcsri $$ Htrue
  inext
  iintro -
  (try wp_auto)
  wp_apply wp_onStop E γ r $$ [Hdone]
  · iframe #; iexact Hdone
  itrivial))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem raftNode.start.wp_proof
    (wp_tick : raftNode.tick.spec (GF := GF) (hG := hG))
    (wp_processMessages : raftNode.processMessages.spec (GF := GF) (hG := hG))
    (wp_updateCommittedIndex : updateCommittedIndex.spec (GF := GF) (hG := hG))
    (wp_onStop : raftNode.onStop.spec (GF := GF) (hG := hG))
    (wp_persist : raftNode.persistRaftData.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Entry.GetType.spec (GF := GF) (hG := hG))
    (wp_Clone : proto.Clone.spec (GF := GF) (hG := hG))
    (wp_Duration : zap.Duration.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    raftNode.start.spec (GF := GF) (hG := hG) := by
  have wp_GetType := wp_entryAt_GetType wp_GetType
  intro E γ r rh L R
  wp_start as ⟨#Hr, #Hrh, HR, Htok, Hdone⟩
  ihave #Hr' := Hr
  iunfold isRaftNode at Hr'
  iNamed Hr'
  ihave #Htrue : iprop(□ (True : IProp GF)) $$ []
  · iintro !>; itrivial
  iunfold context.cancelSpec at Hcsri
  wp_auto
  simp only [time.Second]
  iunfold isRNTicker at Htki
  icases Htki with ⟨%tc, #Htc, #Htcb, #HtkStop⟩
  iunfold isRaftNodeIfc at Hni
  icases Hni with ⟨%ni, %Hnieq, #HReady, #HAdv, #HTick, #HStop, #HRI⟩
  subst Hnieq
  iunfold isRNTransport at Htri
  icases Htri with ⟨%ti, %Htieq, #HSend, #HTrStop⟩
  subst Htieq
  iunfold isRNWal at Hsti
  icases Hsti with ⟨%si, %Hsieq, #HSave, #HClose⟩
  subst Hsieq
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hrpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hpbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  iunfold isUnitBag at Hstci
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
  wp_apply wp_fork $$ [Htok Hdone r rh HR]
  · -- the goroutine
    wp_apply wp_with_defer as %defer defer
    ihave HI : iprop(∃ (L' : List EntryModel) (b : Bool),
        "islead" ∷ islead_ptr ↦ b ∗ "Htok" ∷ rnLoopTok γ L' ∗ "HR" ∷ R) $$ [islead Htok HR]
    · iexists L, false
      iframe
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
      iintro %t HT1
      wp_auto
      wp_apply wp_tick E γ r $$ [$Hpkg $Hr $HT1]
      wp_for_post
      iframe
      iexists L', b
      iframe
    -- `rd := <-r.Ready()`
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      simp only [chan.blockingClausePre]
      iexists Ready, inferInstance, inferInstance, inferInstance, inferInstance, rc, γ.node.readyc
      isplitr
      · ipureintro; rfl
      isplitr
      · unfold isHandshake
        icases Hrc with ⟨$, -⟩
      iapply handshake_receive_au γ.node.readyc rc (rnReadyP E γ) iprop(True) _ $$ [$Hlc1 $Hlc2] Hrc []
      · itrivial
      inext
      iintro %rd HP
      iunfold rnLoopTok at Htok
      icases Htok with ⟨%sent, %cums, Hdrv, Hprod, Hauth, %Hcums⟩
      imod rn_ready_recv E γ L' rd $$ Henv Hfits Hrsb Hdrv HP with ⟨%ce, %es, Hdata, Hbusy⟩
      iunfold rnReadyData at Hdata
      icases Hdata with ⟨%ceL, %esL, %msL, %hs, #Hce, #Hcea, #HC, #Hes, #Hesa, Happ, #Hms, #Hmsok,
        #Hss, #Hhs, ⟨%rsL, #Hrs, #Hrsok⟩, %Hsnapnil⟩
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
          (⌜v = returnVal #()⌝ ∗ r_ptr ↦ r))) with [rd r]
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
          iintro %u -
          try wp_auto
          iright
          iframe r
          ipureintro; rfl
        iapply BigAndL.bigAndL_nil.2
        itrivial
      iintro (⟨%Hv, rd, r⟩ | ⟨%Hv, r⟩)
      rotate_left
      · -- returned (`<-r.stopped`): the deferred `onStop`
        subst Hv
        wp_auto
        wp_for_post
        rn_stop
      subst Hv
      wp_auto_lc 3
      -- (etcd-io/etcd#22223) `snapshotPersistedC` (unused: no snapshot), `raftStorageReadyC`
      -- (the loop closes it, `Hncb`; the apply side's view `HncU`), `applyCompletedC` (the apply
      -- side closes it, `Hdcb`; the loop's view `HdcU`): broadcast channels; `raftAdvancedC`: a
      -- unit bag
      wp_apply chan.wp_make1 (V := Unit) as %spc %γspc ⟨#Hspch, %Hspcap, -⟩
      wp_apply chan.wp_make1 (V := Unit) as %nc %γnc ⟨#Hncch, %Hnccap, Hncown⟩
      imod alloc_broadcast_chan (E := ⊤) iprop(True) γnc nc $$ Hncch Hncown with Hncb
      ihave #HncU := ownBroadcastChan_Unknown _ _ _ _ $$ Hncb
      wp_apply chan.wp_make1 (V := Unit) as %dc %γdc ⟨#Hdcch, %Hdccap, Hdcown⟩
      imod alloc_broadcast_chan (E := ⊤) iprop(True) γdc dc $$ Hdcch Hdcown with Hdcb
      ihave #HdcU := ownBroadcastChan_Unknown _ _ _ _ $$ Hdcb
      wp_apply chan.wp_make2 (V := Unit) $$ [] as %ac %γac ⟨#Hacch, -, Hacown⟩
      · ipureintro; decide
      imod start_bag (fun _ => iprop(True)) _ ac γac trivial $$ Hacch Hacown with #Hacb
      -- `proto.Clone(rd.Snapshot)` of the nil snapshot, twice
      rw [Hsnapnil]
      ihave #Hppkg : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
      · iPkgInit
      wp_apply wp_Clone.2 $$ [$Hppkg]
      rw [Hsnapnil]
      wp_apply wp_Clone.2 $$ [$Hppkg]
      irename raftAdvancedC => Hacl
      ipersist ap
      ihave #Hapf := ap
      iStructNamed Hapf
      -- (`wp_bind` then `iapply`: `wp_apply` fails silently here, framing the generic `R`)
      -- the batch's committed log and indices, from `E.C` (`rnEnvOk`)
      ihave #Henv' := Henv
      iunfold rnEnvOk at Henv'
      icases Henv' with ⟨-, -, -, -, -, #HCback, -⟩
      ihave #HCl := HCback $$ %(L' ++ ce) HC
      icases HCl with ⟨#HLb, %HidxOk⟩
      wp_bind (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.updateCommittedIndex))
        (Val #ap_ptr)) (Val #rh))
      iapply (wp_updateCommittedIndex ap_ptr rh rd.CommittedEntries' ceL L' ce R E.γr) $$ [HR]
      · iframe HR; iframe #
        ipureintro; exact HidxOk
      inext
      iintro ⟨HR, #Hclast⟩
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
        iapply spsc_send_au γ.ap apc (rnApP E γ) _ sent _ _ $$ Hsp [$Hlc1 $Hlc2 $Hlc3] [$Hprod Hdcb]
        · iunfold rnApP
          iexists L', ce, ceL
          simp only [Int.toNat_natCast]
          iframe Hcn Hcn1 Hce Hcea HC
          isplitr
          · ipureintro; trivial
          isplitl [Hdcb]
          · iunfold rnApChans
            isplitr
            · ipureintro; exact ⟨rfl, rfl⟩
            isplitr
            · iexists γnc; iexact HncU
            isplitl [Hdcb]
            · iexists γdc; iexact Hdcb
            iunfold isUnitBag
            iexists γac
            iexact Hacb
          iexact Hclast
        inext
        iintro Hprod
        wp_auto
        -- `if islead { r.transport.Send(r.processMessages(rd.Messages)) }`
        wp_join with [rh rd r islead]
        · wp_apply wp_processMessages E γ r _ msL $$ [$Hpkg $Hr $Hms $Hmsok] as %out ⟨%outL, Hout, Houtok⟩
          wp_apply HSend $$ [$Hout $Houtok]
          wp_join_done
        -- (etcd-io/etcd#22223) `r.persistRaftData(rd.HardState, rd.Entries, raftSnap,
        -- snapshotPersistedC)`: the WAL, the gauge, the `MemoryStorage`'s append
        wp_apply wp_persist E γ r rd.HardState' hs rd.Entries' esL es spc
          $$ [$Hpkg $Hr $Hhs $Hes $Hesa $Happ] as Hrcpt
        -- the confChange scan (`confChanged` only decides an extra `notifyc` send)
        ihave %Hcelen := ownSlice_len _ _ _ $$ Hce
        ihave #Hcea' := Hcea
        iunfold entriesAt at Hcea'
        icases Hcea' with ⟨%Hcl, #Hcef⟩
        wp_join iprop(∃ cc : Bool, confChanged_ptr ↦ cc) at next with [i confChanged ent]
          as ⟨%cc, confChanged⟩
        · ihave IH : iprop(∃ (n : w64) (cc : Bool) (e : Loc),
              "i" ∷ i_ptr ↦ n ∗ "confChanged" ∷ confChanged_ptr ↦ cc ∗ "ent" ∷ ent_ptr ↦ e ∗
              "%Hn" ∷ ⌜0 ≤ sint.Z n⌝) $$ [i confChanged ent]
          · iexists W64 0, false, _
            iframe
            ipureintro; decide
          wp_for IH
          wp_if_destruct
          · have Hif' : sint.Z n < sint.Z rd.CommittedEntries'.len := by
              first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
            rw [if_pos ⟨Hn, Hif'⟩]
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
            · wp_for_post
              iframe
              iexists _, cc, e
              iframe
              ipureintro; word
          · isplitr
            · itrivial
            iexists cc
            iframe
        -- `if !islead { .. } else { notifyc <- struct{}{} }`
        cases b'
        · -- a follower: `msgs := r.processMessages(rd.Messages)`, `notifyc <- `, then (on a conf
          -- change) a second `notifyc` send or `<-r.stopped`, `r.transport.Send(msgs)`
          wp_auto
          wp_apply wp_processMessages E γ r _ msL $$ [$Hpkg $Hr $Hms $Hmsok] as %out ⟨%outL, Hout, Houtok⟩
          -- `close(raftStorageReadyC)`
          wp_apply wp_broadcast_chan_close (ty := go.ChannelType go.ChanDir.sendrecv (go.StructType []))
            nc γnc iprop(True) $$ [$Hncb $Htrue] as -
          cases cc
          · wp_auto
            wp_apply HSend $$ [$Hout $Houtok]
            -- `r.Advance()`: the driver moves to `L' ++ ce`
            rw [method_unfold (t := go.GoType.PointerType raftNode.ty) (m := go!"Advance")]
            wp_auto
            rw [method_unfold (t := go.GoType.PointerType raftNodeConfig.ty) (m := go!"Advance")]
            wp_auto
            ihave HAdv' := HAdv $$ %L' %ce %es
            wp_apply HAdv' $$ [$Hbusy $Hrcpt] as Hdrv
            -- no conf change
            wp_for_post
            iframe
            iexists (L' ++ ce), false
            iframe
            iunfold rnLoopTok
            iexists _, cums ++ [L' ++ ce]
            iframe
            ipureintro
            simp only [List.length_append, List.length_singleton, List.getLast?_append, List.getLast?_singleton]
            constructor
            · omega
            · rfl
          · wp_auto
            wp_apply_core chan.wp_select_blocking_nil
            iapply BigAndL.bigAndL_cons.2
            isplit
            · ileft
              simp only [chan.blockingClausePre]
              -- (etcd-io/etcd#22223) `<-applyCompletedC`
              iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dc, γdc
              isplitr
              · ipureintro; rfl
              isplitr
              · iapply ownBroadcastChan_is_chan $$ HdcU
              iapply broadcast_chan_receive _ _ _ _ _ $$ HdcU
              iintro -
              wp_auto
              wp_apply HSend $$ [$Hout $Houtok]
              -- `r.Advance()`: the driver moves to `L' ++ ce`
              rw [method_unfold (t := go.GoType.PointerType raftNode.ty) (m := go!"Advance")]
              wp_auto
              rw [method_unfold (t := go.GoType.PointerType raftNodeConfig.ty) (m := go!"Advance")]
              wp_auto
              ihave HAdv' := HAdv $$ %L' %ce %es
              wp_apply HAdv' $$ [$Hbusy $Hrcpt] as Hdrv
              -- a conf change: `raftAdvancedC <- struct{}{}`
              wp_apply wp_bag_send γac ac () (fun _ => iprop(True)) $$ [$Hacb]
              wp_for_post
              iframe
              iexists (L' ++ ce), false
              iframe
              iunfold rnLoopTok
              iexists _, cums ++ [L' ++ ce]
              iframe
              ipureintro
              simp only [List.length_append, List.length_singleton, List.getLast?_append, List.getLast?_singleton]
              constructor
              · omega
              · rfl
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
              iintro %u -
              wp_auto
              wp_for_post
              rn_stop
            iapply BigAndL.bigAndL_nil.2
            itrivial
        · -- the leader: `notifyc <- struct{}{}`
          wp_auto
          -- `close(raftStorageReadyC)`
          wp_apply wp_broadcast_chan_close (ty := go.ChannelType go.ChanDir.sendrecv (go.StructType []))
            nc γnc iprop(True) $$ [$Hncb $Htrue] as -
          -- `r.Advance()`: the driver moves to `L' ++ ce`
          rw [method_unfold (t := go.GoType.PointerType raftNode.ty) (m := go!"Advance")]
          wp_auto
          rw [method_unfold (t := go.GoType.PointerType raftNodeConfig.ty) (m := go!"Advance")]
          wp_auto
          ihave HAdv' := HAdv $$ %L' %ce %es
          wp_apply HAdv' $$ [$Hbusy $Hrcpt] as Hdrv
          -- `if confChanged { raftAdvancedC <- struct{}{} }`
          wp_join with [islead Hacl]
          · wp_apply wp_bag_send γac ac _ (fun _ => iprop(True)) $$ [$Hacb]
            wp_join_done
          wp_for_post
          iframe
          iexists (L' ++ ce), true
          iframe
          iunfold rnLoopTok
          iexists _, cums ++ [L' ++ ce]
          iframe
          ipureintro
          simp only [List.length_append, List.length_singleton, List.getLast?_append, List.getLast?_singleton]
          constructor
          · omega
          · rfl
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
        iintro %u -
        wp_auto
        wp_for_post
        rn_stop
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
      iintro %u -
      wp_auto
      wp_for_post
      rn_stop
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
