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
public import EtcdDeps.Spec.go_etcd_io.raft.v3.IsEmptySnap
public import EtcdDeps.Spec.go_etcd_io.raft.v3.IsEmptyHardState
public import EtcdDeps.Spec.go_etcd_io.raft.v3.raftpb.HardState__GetCommit
public import EtcdDeps.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetType
public import Spec.google_golang_org.protobuf.proto.Clone
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Fatal

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
    (wp_GetType : raftpb.Entry.GetType.spec (GF := GF) (hG := hG))
    (wp_Clone : proto.Clone.spec (GF := GF) (hG := hG))
    (wp_Error : zap.Error.spec (GF := GF) (hG := hG))
    (wp_Fatal : zap.Logger.Fatal.spec (GF := GF) (hG := hG)) :
    raftNode.start.spec (GF := GF) (hG := hG) := by
  intro E γ r rh L
  wp_start as ⟨#Hr, #Hrh, Htok, Hdone, #HT⟩
  ihave #Hr' := Hr
  iunfold isRaftNode at Hr'
  iNamed Hr'
  wp_auto
  simp only [time.Second]
  iunfold isRNTicker at Htki
  icases Htki with ⟨%tc, #Htc, #Htcb, #HtkStop⟩
  iunfold isRaftNodeIfc at Hni
  icases Hni with ⟨%ni, %Hnieq, #HReady, #HAdv, #HTick, #HStop⟩
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
  wp_apply wp_fork $$ [Htok Hdone r rh]
  · -- the goroutine
    wp_apply wp_with_defer as %defer defer
    ihave HI : iprop(∃ (L' : List EntryModel) (b : Bool),
        "islead" ∷ islead_ptr ↦ b ∗ "Htok" ∷ rnLoopTok γ L') $$ [islead Htok]
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
      iintro %t -
      wp_auto
      ihave HT1 := HT
      imod HT1
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
      iexists Ready, inferInstance, inferInstance, inferInstance, inferInstance, rc, γ.readyc
      isplitr
      · ipureintro; rfl
      isplitr
      · unfold isHandshake
        icases Hrc with ⟨$, -⟩
      iapply handshake_receive_au γ.readyc rc (rnReadyP E γ) iprop(True) _ $$ [$Hlc1 $Hlc2] Hrc []
      · itrivial
      inext
      iintro %rd HP
      iunfold rnLoopTok at Htok
      icases Htok with ⟨%sent, %cums, Hdrv, Hprod, Hauth, %Hcums⟩
      icases rn_ready_recv E γ L' rd $$ Hdrv HP with ⟨%ce, %es, Hdata, Hbusy⟩
      iunfold rnReadyData at Hdata
      icases Hdata with ⟨%ceL, %esL, %msL, %hs, #Hce, #Hcea, #HC, #Hes, #Hesa, Happ, #Hms, #Hmsok,
        #Hss, #Hhs, %Hsnap⟩
      obtain ⟨Hsnapnil, Hrsnil⟩ := Hsnap
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
      -- no read states (`rd.ReadStates` is nil)
      rw [Hrsnil]
      irename Hlc3 => HlcA
      irename Hlc4 => HlcB
      wp_auto_lc 3
      -- `notifyc`, `raftAdvancedC`: unit bags
      wp_apply chan.wp_make2 (V := Unit) $$ [] as %nc %γnc ⟨#Hncch, -, Hncown⟩
      · ipureintro; decide
      imod start_bag (fun _ => iprop(True)) _ nc γnc trivial $$ Hncch Hncown with #Hncb
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
      irename notifyc => Hncl
      irename raftAdvancedC => Hacl
      ipersist ap
      ihave #Hapf := ap
      iStructNamed Hapf
      wp_apply wp_updateCommittedIndex ap_ptr rh rd.CommittedEntries' ceL ce $$ [$Hpkg $entries $Hce $Hcea $snapshot $Hrh0]
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
        iapply spsc_send_au γ.ap apc (rnApP E γ) _ sent _ _ $$ Hsp [$Hlc1 $Hlc2 $Hlc3] [$Hprod]
        · iunfold rnApP
          iexists L', ce, ceL
          simp only [Int.toNat_natCast]
          iframe Hcn Hcn1 Hce Hcea HC
          isplitr
          · ipureintro; trivial
          isplitr
          · iunfold isUnitBag
            iexists γnc
            iexact Hncb
          iunfold isUnitBag
          iexists γac
          iexact Hacb
        inext
        iintro Hprod
        wp_auto
        -- `if islead { r.transport.Send(r.processMessages(rd.Messages)) }`
        wp_join with [rh rd r islead]
        · wp_apply wp_processMessages E γ r _ msL $$ [$Hpkg $Hr $Hms $Hmsok] as %out ⟨%outL, Hout, Houtok⟩
          wp_apply HSend $$ [$Hout $Houtok]
          wp_join_done
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
          wp_apply wp_bag_send γnc nc () (fun _ => iprop(True)) $$ [$Hncb]
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
              iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nc, γnc, ()
              isplitr
              · ipureintro; exact ⟨rfl, rfl⟩
              isplitr
              · iapply is_bag_is_chan $$ Hncb
              iapply bag_send_au γnc nc (fun _ => iprop(True)) () _ $$ [$HlcA $HlcB] Hncb []
              · itrivial
              inext
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
              wp_apply wp_onStop E γ r $$ [$Hpkg $Hr $Hdone]
              itrivial
            iapply BigAndL.bigAndL_nil.2
            itrivial
        · -- the leader: `notifyc <- struct{}{}`
          wp_auto
          wp_apply wp_bag_send γnc nc _ (fun _ => iprop(True)) $$ [$Hncb]
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
        wp_apply wp_onStop E γ r $$ [$Hpkg $Hr $Hdone]
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
      iintro %u -
      wp_auto
      wp_for_post
      wp_apply wp_onStop E γ r $$ [$Hpkg $Hr $Hdone]
      itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
