/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.node__run
public import Spec.go_etcd_io.raft.v3.RawNode__HasReady
public import Spec.go_etcd_io.raft.v3.RawNode__readyWithoutAccept
public import Spec.go_etcd_io.raft.v3.RawNode__acceptReady
public import Spec.go_etcd_io.raft.v3.RawNode__Advance
public import Spec.go_etcd_io.raft.v3.RawNode__Tick
public import Spec.go_etcd_io.raft.v3.raft__Step
public import Spec.go_etcd_io.raft.v3.raft__hasLeader
public import Spec.go_etcd_io.raft.v3.IsResponseMsg
public import Spec.go_etcd_io.raft.v3.IsLocalMsgTarget
public import Spec.go_etcd_io.raft.v3.raft__applyConfChange
public import Proof.go_etcd_io.raft.v3.InvNodeRun

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem node.run.wp_proof
    (wp_RawNode_HasReady : RawNode.HasReady.spec (GF := GF) (hG := hG))
    (wp_RawNode_readyWithoutAccept : RawNode.readyWithoutAccept.spec (GF := GF) (hG := hG))
    (wp_RawNode_acceptReady : RawNode.acceptReady.spec (GF := GF) (hG := hG))
    (wp_RawNode_Advance : RawNode.Advance.spec (GF := GF) (hG := hG))
    (wp_RawNode_Tick : RawNode.Tick.spec (GF := GF) (hG := hG))
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (wp_raft_hasLeader : raft.hasLeader.spec (GF := GF) (hG := hG))
    (wp_IsResponseMsg : IsResponseMsg.spec (GF := GF) (hG := hG))
    (wp_IsLocalMsgTarget : IsLocalMsgTarget.spec (GF := GF) (hG := hG))
    (wp_raft_applyConfChange : raft.applyConfChange.spec (GF := GF) (hG := hG)) :
    node.run.spec (GF := GF) (hG := hG) := by
  intro γ id n
  wp_start as ⟨#Hnode, Hpre⟩
  ihave #Hnode' := Hnode
  open_node Hnode'
  unfold runPre
  icases Hpre with ⟨%nv0, %rs, %x, #Hn0, Hrn, %Hrs, Hdlv, Hr1, Hr2, #Hlb⟩
  icombine Hn Hn0 gives %Heq
  subst Heq
  wp_auto
  simp only [None']
  wp_auto
  ihave HI : iprop(∃ (pc rc ac : GoChan) (rdv : Ready) (ld : w64),
      "propc" ∷ propc_ptr ↦ pc ∗ "readyc" ∷ readyc_ptr ↦ rc ∗ "advancec" ∷ advancec_ptr ↦ ac ∗
      "rd" ∷ rd_ptr ↦ rdv ∗ "lead" ∷ lead_ptr ↦ ld ∗
      "%Hpc" ∷ ⌜pc = chan.nil ∨ pc = nv.propc'⌝ ∗ "Hhead" ∷ runHead γ id nv ac rc rdv)
    $$ [propc readyc advancec rd lead Hrn Hdlv Hr1 Hr2]
  · iexists zero_val GoChan, zero_val GoChan, zero_val GoChan, zero_val Ready, _
    simp only [named]
    iframe propc readyc advancec rd
    isplitl [lead]
    · iexact lead
    isplitr
    · ipureintro; left; rfl
    unfold runHead
    iexists rs
    iframe Hrn
    unfold headRest
    iframe Hlb
    isplitr
    · ipureintro; exact Hrs.2.2
    ileft
    iframe Hdlv
    isplitr
    · ipureintro; exact ⟨rfl, Hrs.1, Hrs.2.1⟩
    isplitl [Hr1 Hr2]
    · unfold rofFull
      iexists x
      iframe Hr1 Hr2
    ileft; ipureintro; rfl
  ihave %Hadv_nn := isChan_not_null $$ [Hadvancec]
  · iapply isHandshake_isChan $$ Hadvancec
  ihave %Hrdy_nn := isChan_not_null $$ [Hreadyc]
  · iapply isHandshake_isChan $$ Hreadyc
  wp_for HI
  -- `if advancec == nil && n.rn.HasReady() { rd = n.rn.readyWithoutAccept(); ... }`
  wp_join iprop(∃ (rc' : GoChan) (rdv' : Ready), n_ptr ↦ n ∗ readyc_ptr ↦ rc' ∗
      rd_ptr ↦ rdv' ∗ runMid γ id nv ac rc' rdv')
    at next with [n readyc rd Hhead] as ⟨%rc', %rdv', n, readyc, rd, Hmid⟩
  · wp_if_destruct
    · -- no `Ready` outstanding
      iunfold runHead at Hhead
      icases Hhead with ⟨%rs, Hrn, Hrest⟩
      icases headRest_nil γ nv rs rc rdv Hadv_nn $$ Hrest with
        ⟨#Hlb, %Hrs, Hdlv, Hrof, Hrc⟩
      obtain ⟨Hst, Hsteps, Hunp⟩ := Hrs
      wp_apply wp_RawNode_HasReady γ.raft nv.rn' id rs $$ [$Hrn] as %b Hb
      icases Hb with (⟨%Hb, Hrn⟩ | ⟨%Hb, Hrn⟩) <;> subst Hb
      · wp_auto
        wp_apply wp_RawNode_readyWithoutAccept γ.raft nv.rn' id rs Hsteps Hunp $$ [$Hrn]
          as %rd' %ce %es %ms %sts H
        iNamed H
        wp_join_done
        iexists nv.readyc', rd'
        iframe n readyc rd
        unfold runMid
        iright
        isplitr
        · ipureintro; rfl
        iexists rs
        iframe Hlb Hdlv Hrof
        isplitr
        · ipureintro; exact ⟨Hst, Hsteps, Hunp⟩
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists ce, es, ms
        iframe Hrn
        unfold freshOk
        iframe Hce Hcommitted Hents Hmsgs Hmsgs_cap Hmsgs_ok
        isplitr
        · iexists sts
          iframe Hrs Hrs_ok
        ipureintro; exact ⟨Hmsgs_term, Hsnapz⟩
      · try wp_auto
        wp_join_done
        iexists rc, rdv
        iframe n readyc rd
        unfold runMid
        iright
        isplitr
        · ipureintro; rfl
        iexists rs
        iframe Hlb Hdlv Hrof
        isplitr
        · ipureintro; exact ⟨Hst, Hsteps, Hunp⟩
        icases Hrc with (%Hrc | ⟨%Hrc, Hstale⟩)
        · ileft
          isplitr
          · ipureintro; exact Hrc
          iapply ownRawNodeIdle_ownRawNode $$ Hrn
        · iright; iright
          isplitr
          · ipureintro; exact Hrc
          iframe Hrn Hstale
    · -- a `Ready` handed out: on to the `select`
      wp_join_done
      iexists rc, rdv
      iframe n readyc rd
      iapply runHead_mid_busy γ id nv ac rc rdv Hif $$ Hhead
  -- `if lead != r.lead { ... }`: the leader fields, out of whichever state the node is in
  ihave Hlf := runMid_lead γ id nv ac rc' rdv' r $$ Hmid Hrnraft
  iunfold leadFields at Hlf
  icases Hlf with ⟨%ldr, %tr, Hl, Ht, Hmidb⟩
  wp_join iprop(∃ (pc' : GoChan) (ld' : w64), propc_ptr ↦ pc' ∗ lead_ptr ↦ ld' ∗
      ⌜pc' = chan.nil ∨ pc' = nv.propc'⌝ ∗ r.[raft, go!"lead"] ↦ ldr ∗
      r.[raft, go!"Term"] ↦ tr ∗ r_ptr ↦ r ∗ n_ptr ↦ n)
    at next with [propc lead Hl Ht r n]
  · wp_auto
    wp_if_destruct
    · wp_join_done
      iexists pc, ld
      iframe
      ipureintro; exact Hpc
    · wp_apply wp_raft_hasLeader r ldr $$ [$Hl] as %b Hl
      cases b
      · -- lost the leader
        wp_auto
        wp_apply wp_slice_literal
        try (isplitr; (ipureintro; rfl))
        try iintro %_ ⟨_, -⟩
        try wp_auto
        wp_apply Logger.wp_logf lok _ _ _ (by decide) $$ Hlogger
        try wp_auto
        wp_join_done
        iexists chan.nil, ldr
        iframe
        ipureintro; left; rfl
      · wp_auto
        wp_if_destruct
        all_goals (
          wp_apply wp_slice_literal
          try (isplitr; (ipureintro; rfl))
          try iintro %_ ⟨_, -⟩
          try wp_auto
          wp_apply Logger.wp_logf lok _ _ _ (by decide) $$ Hlogger
          try wp_auto
          wp_join_done
          iexists nv.propc', ldr
          iframe
          ipureintro; right; rfl)
  iintro ⟨%pc', %ld', propc, lead, %Hpc', Hl, Ht, r, n⟩
  ihave Hmid := Hmidb $$ Hl Ht
  ihave %Hchans := runMid_chans γ id nv ac rc' rdv' $$ Hmid
  wp_auto_lc 4
  wp_apply_core chan.wp_select_blocking_nil
  -- `pm := <-propc`
  iapply BigAndL.bigAndL_cons.2
  isplit
  · rcases Hpc' with rfl | rfl
    · iright
      iapply chan.nilClausePre_recv msgWithResult _ _ rfl
    ileft
    simp only [chan.blockingClausePre]
    iexists msgWithResult, inferInstance, inferInstance, inferInstance, inferInstance,
      nv.propc', γ.propc
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply isHandshake_isChan $$ Hpropc
    iapply handshake_receive_au γ.propc nv.propc' (propP γ) iprop(True) _
      $$ [$Hlc1 $Hlc2] Hpropc []
    · itrivial
    inext
    iintro %pm HP
    iunfold propP at HP
    icases HP with (⟨%data_sl, %esl, %data, %γr, %Hpm, Hes, Hcap, #Hdata, #Hent, #Hho, Hprod⟩ |
      ⟨%Hres, Hfwd⟩)
    · wp_auto
      ihave Hhead := runMid_head γ id nv ac rc' rdv' $$ Hmid
      iunfold runHead at Hhead
      icases Hhead with ⟨%rs, Hrn, Hrest⟩
      rw [Hpm]
      ihave #Hm := isMessage_propMsg γ.raft esl data_sl $$ Hent
      ihave Hes : (propMsg esl).Entries' ↦* [propEntry data_sl] $$ [Hes]
      · rw [show (propMsg esl).Entries' = esl from rfl]; iexact Hes
      ihave Hcap : ownSliceCap raftpb.Entry (propMsg esl).Entries' (DFrac.own 1) $$ [Hcap]
      · rw [show (propMsg esl).Entries' = esl from rfl]; iexact Hcap
      ihave #Hpdi := isNode_propDataInv γ id n $$ Hnode
      wp_apply wp_rn_raft_Step_prop wp_raft_Step γ.raft nv.rn' id rs r (propMsg esl)
        [propEntry data_sl] rfl $$ [$Hpdi $Hrn $Hrnraft $Hes $Hcap $Hm]
        as %err Hrn
      · iexists []
        rw [show (propMsg esl).Context' = slice.nil from rfl]
        iapply ownSlice_nil
      ihave %Hrnn := isChan_not_null $$ [Hho]
      · unfold isHandoff
        icases Hho with ⟨$, -⟩
      wp_if_destruct
      · exact absurd Hif Hrnn
      wp_apply wp_handoff_send (t := go.error) γr pm.result' (fun (_ : GoInterface) => iprop(True))
        iprop(True) iprop(True) err $$ [$Hho $Hprod] as Hprod
      · isplitl <;> itrivial
      wp_apply wp_handoff_close (t := go.error) γr pm.result' (fun (_ : GoInterface) => iprop(True))
        iprop(True) iprop(True) true $$ [$Hho $Hprod]
      · simp only [↓reduceIte]
        itrivial
      wp_for_post
      iframe HΦ n r
      iexists nv.propc', rc', ac, rdv', ld'
      iframe propc readyc advancec rd lead
      isplitr
      · ipureintro; right; rfl
      unfold runHead
      iexists rs
      iframe Hrn Hrest
    · -- a proposal forwarded by a peer (2026-10-10): no result channel
      iunfold fwdP at Hfwd
      icases Hfwd with ⟨%Hty, %ents, %ctx, Hes, Hcap, #Hctx, #Hm⟩
      wp_auto
      ihave Hhead := runMid_head γ id nv ac rc' rdv' $$ Hmid
      iunfold runHead at Hhead
      icases Hhead with ⟨%rs, Hrn, Hrest⟩
      ihave #Hpdi := isNode_propDataInv γ id n $$ Hnode
      wp_apply wp_rn_raft_Step_prop wp_raft_Step γ.raft nv.rn' id rs r pm.m' ents Hty
        $$ [$Hpdi $Hrn $Hrnraft $Hes $Hcap $Hm] as %err Hrn
      · iexists ctx
        iframe Hctx
      rw [Hres]
      wp_if_destruct
      rotate_left
      · exact absurd rfl Hif
      wp_for_post
      iframe HΦ n r
      iexists nv.propc', rc', ac, rdv', ld'
      iframe propc readyc advancec rd lead
      isplitr
      · ipureintro; right; rfl
      unfold runHead
      iexists rs
      iframe Hrn Hrest
  -- `m := <-n.recvc`
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists raftpb.Message, inferInstance, inferInstance, inferInstance, inferInstance,
      nv.recvc', γ.recvc
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply isHandshake_isChan $$ Hrecvc
    iapply handshake_receive_au γ.recvc nv.recvc' (netP γ id) iprop(True) _
      $$ [$Hlc1 $Hlc2] Hrecvc []
    · itrivial
    inext
    iintro %m Hnet
    iunfold netP at Hnet
    icases Hnet with ⟨%Hok, %ents, %ctx, #Hents, Hents_cap, #Hctx, %Hsing, #Hmsg, #Hlbm,
      Hcred, Htc⟩
    have Hty0 : 0 ≤ sint.Z m.Type' := netStepTypes_nonneg Hok.1
    wp_auto
    ihave Hhead := runMid_head γ id nv ac rc' rdv' $$ Hmid
    iunfold runHead at Hhead
    icases Hhead with ⟨%rs, Hrn, Hrest⟩
    -- `IsResponseMsg(m.Type) && !IsLocalMsgTarget(m.From) && r.trk.Progress[m.From] == nil`
    wp_apply wp_IsResponseMsg _ Hty0 as %b2 _
    wp_if_destruct
    all_goals try (wp_apply wp_IsLocalMsgTarget m.From'; wp_if_destruct)
    all_goals try (
      icases ownRawNode_borrow γ.raft nv.rn' id rs r $$ Hrn Hrnraft with ⟨%s, Hphys, Hback⟩
      icases ownRaftPhys_tracker_same γ.raft.reCfg r id s $$ Hphys with
        ⟨%tv, Htrkf, Htrk, Hback2⟩
      icases ownTracker_progress_map γ.raft.reCfg tv _ $$ Htrk with ⟨#Hprs, %Hdom, Htrk⟩
      wp_auto
      wp_apply wp_map_lookup1 go.uint64 (go.GoType.PointerType tracker.Progress.ty) _ _ m.From' _
        $$ Hprs with -
      ihave Hphys := Hback2 $$ %tv Htrkf Htrk
      ihave Hrn := Hback $$ Hphys
      wp_if_destruct)
    -- filtered out: `break`
    all_goals try (
      wp_for_post
      iframe HΦ n r
      iexists pc', rc', ac, rdv', ld'
      iframe propc readyc advancec rd lead
      isplitr
      · ipureintro; exact Hpc'
      unfold runHead
      iexists rs
      iframe Hrn Hrest)
    -- `r.Step(m)`
    all_goals (
      try wp_auto
      icases headRest_termLB γ nv rs ac rc' rdv' $$ Hrest with ⟨#Hlb', Hrest⟩
      -- the budget covers the step: a `MsgTimeoutNow` spends its tick credit
      imod budget_step γ.bud rs.term m.Term' (m.Type' = MsgTimeoutNow) ⊤ (by solve_ndisj)
        $$ Hbud Hlb' Hlbm Htc with ⟨%Hbnd, %tb, #Hlbtb, %Htb⟩
      wp_apply wp_rn_raft_Step_net wp_raft_Step γ.raft nv.rn' id rs r m ents ctx Hok Hsing
        (fun _ => Hbnd) $$ [Hrn Hents_cap Hcred] as %err %t ⟨Hrn, %Ht⟩
      · iframe Hrn Hents_cap Hrnraft Hents Hctx Hmsg Hcred
      ihave #Hlbt : termLB γ.bud t $$ []
      · iapply termLB_le γ.bud tb t (Int.le_trans Ht.2 Htb) $$ Hlbtb
      ihave Hrest := headRest_term γ nv rs ac rc' rdv' t $$ Hrest Hlbt
      try wp_auto
      wp_for_post
      iframe HΦ n r
      iexists pc', rc', ac, rdv', ld'
      iframe propc readyc advancec rd lead
      isplitr
      · ipureintro; exact Hpc'
      unfold runHead
      iexists { rs with term := t }
      iframe Hrn Hrest)
  -- `cc := <-n.confc` (2026-10-13): a conf change that leaves the configuration unchanged
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists raftpb.ConfChangeV2, inferInstance, inferInstance, inferInstance, inferInstance,
      nv.confc', γ.confc
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply isHandshake_isChan $$ Hconfc
    iapply handshake_receive_au γ.confc nv.confc' (confcP γ) iprop(True) _
      $$ [$Hlc1 $Hlc2] Hconfc []
    · itrivial
    inext
    iintro %cc HP
    iunfold confcP at HP
    icases HP with ⟨%ccs, #Hccs, %Hn⟩
    wp_auto
    ihave Hhead := runMid_head γ id nv ac rc' rdv' $$ Hmid
    iunfold runHead at Hhead
    icases Hhead with ⟨%rs, Hrn, Hrest⟩
    -- `_, okBefore := r.trk.Progress[r.id]`: the node is a voter
    icases ownRawNode_borrow_in γ.raft nv.rn' id rs r $$ Hrn Hrnraft
      with ⟨%s, %Hin, Hphys, Hback⟩
    icases ownRaftPhys_tracker_same _ r id _ $$ Hphys with ⟨%tv, Htrkf, Htrk, Htb⟩
    icases ownTracker_progress_map _ _ _ $$ Htrk with ⟨#Hprs, %Hdom, Htrk⟩
    wp_auto
    wp_apply wp_map_lookup2 $$ Hprs as -
    ihave Hphys := Htb $$ %tv Htrkf Htrk
    ihave Hrn := Hback $$ Hphys
    have Hb : (s.progress !! id).isSome = true := by
      have := (GMap.elem_of_dom s.progress id).1 ((GMap.elem_of_subseteq _ _).1 Hdom _ Hin)
      obtain ⟨v, hv⟩ := this; rw [hv]; rfl
    rw [Hb]
    try wp_auto
    -- `cs := r.applyConfChange(cc)`
    wp_apply wp_rn_raft_applyConfChange wp_raft_applyConfChange γ.raft nv.rn' id rs r cc ccs Hn
      $$ [$Hrn $Hrnraft $Hccs] as %cs %xs %ls ⟨Hrn, Hvoters, Hls, %Hcs⟩
    -- `_, okAfter := r.trk.Progress[r.id]`: still a voter
    icases ownRawNode_borrow_in γ.raft nv.rn' id rs r $$ Hrn Hrnraft
      with ⟨%s2, %Hin2, Hphys, Hback⟩
    try wp_auto
    icases ownRaftPhys_tracker_same _ r id _ $$ Hphys with ⟨%tv2, Htrkf, Htrk, Htb⟩
    icases ownTracker_progress_map _ _ _ $$ Htrk with ⟨#Hprs2, %Hdom2, Htrk⟩
    wp_auto
    wp_apply wp_map_lookup2 $$ Hprs2 as -
    ihave Hphys := Htb $$ %tv2 Htrkf Htrk
    ihave Hrn := Hback $$ Hphys
    have Hb2 : (s2.progress !! id).isSome = true := by
      have := (GMap.elem_of_dom s2.progress id).1 ((GMap.elem_of_subseteq _ _).1 Hdom2 _ Hin2)
      obtain ⟨v, hv⟩ := this; rw [hv]; rfl
    rw [Hb2]
    imod ownSlice_persist $$ Hvoters with #Hvoters
    imod ownSlice_persist $$ Hls with #Hls
    wp_auto_lc 3
    -- `select { case n.confstatec <- cs: case <-n.done: }`
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists raftpb.ConfState, inferInstance, inferInstance, inferInstance, inferInstance,
        nv.confstatec', γ.confstatec, _
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · iapply isHandshake_isChan $$ Hconfstatec
      iapply handshake_send_au γ.confstatec nv.confstatec' _ (confstateP γ) iprop(True)
        $$ [$Hlc1 $Hlc2 $Hlc3] Hconfstatec []
      · unfold confstateP
        iexists xs, ls
        iframe Hvoters Hls
        ipureintro; exact Hcs
      inext
      iintro -
      wp_auto
      wp_for_post
      iframe HΦ n r
      iexists pc', rc', ac, rdv', ld'
      iframe propc readyc advancec rd lead
      isplitr
      · ipureintro; exact Hpc'
      unfold runHead
      iexists rs
      iframe Hrn Hrest
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.done', γ.done
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply isHandshake_isChan $$ Hdone
      iapply handshake_false_recv_au γ.done nv.done' $$ [$Hlc1 $Hlc2] Hdone
    iapply BigAndL.bigAndL_nil.2
    itrivial
  -- `<-n.tickc`
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.tickc', γ.tick
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact Htickc
    iapply tick_rcv_au γ _ $$ Htickinv Hlc1
    inext
    iintro Hcr
    wp_auto
    ihave Hhead := runMid_head γ id nv ac rc' rdv' $$ Hmid
    iunfold runHead at Hhead
    icases Hhead with ⟨%rs, Hrn, Hrest⟩
    icases headRest_termLB γ nv rs ac rc' rdv' $$ Hrest with ⟨#Hlb', Hrest⟩
    imod budget_spend γ.bud rs.term ⊤ (by solve_ndisj) $$ Hbud Hcr Hlb' with ⟨%Hb, #Hlb1⟩
    wp_apply wp_RawNode_Tick γ.raft nv.rn' id rs (by omega) $$ [$Hrn] as %t H
    iNamed H
    ihave #Hlbt := termLB_le γ.bud (rs.term + W64 1) t (by word) $$ Hlb1
    ihave Hrest := headRest_term γ nv rs ac rc' rdv' t $$ Hrest Hlbt
    wp_for_post
    iframe HΦ n r
    iexists pc', rc', ac, rdv', ld'
    iframe propc readyc advancec rd lead
    isplitr
    · ipureintro; exact Hpc'
    unfold runHead
    iexists { rs with term := t }
    iframe Hrn Hrest
  -- `readyc <- rd`
  iapply BigAndL.bigAndL_cons.2
  isplit
  · rcases Hchans.1 with Hrc | Hrc <;> subst Hrc
    · iright
      iapply chan.nilClausePre_send _ rdv' _ rfl
    ileft
    simp only [chan.blockingClausePre]
    iexists Ready, inferInstance, inferInstance, inferInstance, inferInstance,
      nv.readyc', γ.readyc, rdv'
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · iapply isHandshake_isChan $$ Hreadyc
    icases runMid_ready γ id nv ac rdv' Hrdy_nn Hadv_nn $$ Hmid with
      ⟨%Hac, %rs, #Hlb', %Hrs, Hdlv, Hrof, Hst⟩
    subst Hac
    obtain ⟨Hstor, Hsteps, Hunp⟩ := Hrs
    -- the `Ready` to send, fresh or stale (then it holds no messages and no entries)
    ihave Hg : iprop(∃ (ce es : List raftpb.Entry) (ms : List raftpb.Message),
        ownRawNodeReady γ.raft nv.rn' id rs rdv' ce es ms false ∗
        rdv'.CommittedEntries' ↦*□ ce ∗ isCommitted γ.raft (rs.delivered ++ ce) ∗
        rdv'.Entries' ↦*□ es ∗ rdv'.Messages' ↦* ms ∗ ([∗list] m ∈ ms, isRaftMsg γ.raft m) ∗
        (∃ sts : List ReadState, rdv'.ReadStates' ↦*□ sts ∗
          [∗list] st ∈ sts, readStateOk γ.raft st) ∗
        ⌜(∀ m ∈ ms, uint.Z m.Term' ≤ uint.Z rs.term) ∧
          rdv'.Snapshot' = zero_val raftpb.Snapshot⌝) $$ [Hst]
    · icases Hst with (⟨%ce, %es, %ms, Hrn, Hf⟩ | ⟨Hrn, Hstale⟩)
      · iunfold freshOk at Hf
        icases Hf with ⟨#Hce, #Hcommitted, #Hents, Hmsgs, -, #Hmsgs_ok, #Hrsts, %Hfacts⟩
        iexists ce, es, ms
        iframe Hrn Hce Hcommitted Hents Hmsgs Hmsgs_ok Hrsts
        ipureintro; exact Hfacts
      · icases ownRawNodeIdle_facts γ.raft nv.rn' id rs $$ Hrn with ⟨%Hidf, Hrn⟩
        iunfold staleOk at Hstale
        icases Hstale with
          ⟨%ce, %es, %k, #Hrdsoft, #Hce, Hce_cap, #Hcommitted, #Hents, #Hrsts, %Hsf⟩
        icases Hrsts with ⟨%sts, #Hrs, #Hrs_ok⟩
        obtain ⟨Hrdz, Hes, Hshape, Hk, Hce_ok⟩ := Hsf
        have Hes0 : es = [] := by
          by_cases h : es = []
          · exact h
          · have := Hes h
            rw [Hidf.2] at this
            exact absurd this (by simp)
        have Hk0 : k = 0 := by have := Hidf.1; omega
        subst Hes0 Hk0
        ihave Hrn := ownRawNodeIdle_ready γ.raft nv.rn' id rs rdv' ce sts Hsteps Hunp Hrdz
          Hce_ok $$ Hrdsoft Hce Hce_cap Hcommitted Hrs Hrn
        iexists ce, [], []
        iframe Hrn Hce Hcommitted Hents
        isplitl []
        · iapply ownSlice_of_shape rdv'.Messages' (DFrac.own 1) Hshape
        isplitl []
        · iapply BigSepL.bigSepL_nil.2
          iempintro
        isplitr
        · iexists sts
          iframe Hrs Hrs_ok
        ipureintro; exact ⟨by simp, Hrdz⟩
    icases Hg with
      ⟨%ce, %es, %ms, Hrn, #Hce, #Hcommitted, #Hents, Hmsgs, #Hmsgs_ok, #Hrsts, %Hfacts⟩
    iapply handshake_send_au_upd (t := Ready.ty) γ.readyc nv.readyc' rdv' (readyP γ) iprop(True) _
      $$ [$Hlc1 $Hlc2 $Hlc3] Hreadyc
    -- the append right goes with the `Ready`, and `rof` records it
    imod ownRawNodeReady_handout γ.raft nv.rn' id rs rdv' ce es ms $$ Hrn with ⟨Hrn, Happ, Hcr⟩
    iunfold rofFull at Hrof
    icases Hrof with ⟨%x, Hr1, Hr2⟩
    imod dghostVar_update_halves (rs.delivered, ce, es) γ.rof x x $$ Hr1 Hr2 with ⟨Hr1, Hr2⟩
    ihave Hmt := readyMsgs_termLB γ rs.term ms Hfacts.1 $$ Hmsgs_ok Hlb'
    imodintro
    isplitl [Hdlv Hr1 Happ Hmsgs Hmt Hcr]
    · unfold readyP
      iexists rs.delivered, ce, es, ms
      iframe Hdlv Hr1
      unfold readyData
      iframe Hce Hcommitted Hents Hmsgs Hmt Hcr Hrsts
      isplitl [Happ]
      · rw [← Hstor]
        iexact Happ
      ipureintro; exact Hfacts.2
    inext
    iintro -
    wp_auto
    wp_apply wp_RawNode_acceptReady γ.raft nv.rn' id rs rdv' ce es ms $$ [$Hrn] as %steps Hrn
    icases ownRawNode_async γ.raft nv.rn' id _ $$ Hrn with ⟨%rnv, Hrnown, %Hasync, Hrnback⟩
    wp_auto
    rw [Hasync]
    wp_auto
    ihave Hrn := Hrnback $$ Hrnown
    wp_for_post
    iframe HΦ n r
    iexists pc', chan.nil, nv.advancec', rdv', ld'
    iframe propc readyc advancec rd lead
    isplitr
    · ipureintro; exact Hpc'
    unfold runHead
    iexists { rs with delivered := rs.delivered ++ ce, unpersisted := es, steps := steps,
                      outlb := 0, unst := false }
    iframe Hrn
    unfold headRest
    iframe Hlb'
    isplitr
    · ipureintro; exact Hstor
    iright
    isplitr
    · ipureintro; exact ⟨rfl, rfl, rfl⟩
    iexists rs.delivered, ce
    iframe Hr2
    ipureintro; rfl
  -- `<-advancec`
  iapply BigAndL.bigAndL_cons.2
  isplit
  · rcases Hchans.2 with Hac | Hac <;> subst Hac
    · iright
      iapply chan.nilClausePre_recv Unit _ _ rfl
    ileft
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance,
      nv.advancec', γ.advancec
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply isHandshake_isChan $$ Hadvancec
    icases runMid_busy γ id nv rc' rdv' Hadv_nn $$ Hmid with
      ⟨%rs, %d, %ce, Hrn, #Hlb', %Hrs, Hrof⟩
    obtain ⟨Hstor, Hrc, Hunst, Hdel⟩ := Hrs
    iapply handshake_receive_au γ.advancec nv.advancec' (advanceP γ) iprop(True) _
      $$ [$Hlc1 $Hlc2] Hadvancec []
    · itrivial
    inext
    iintro %u HP
    iunfold advanceP at HP
    icases HP with ⟨%d', %ce', %es', Hdlv, Hrof', Hrcpt⟩
    ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hrof Hrof'
    simp only [Prod.mk.injEq] at Heq
    obtain ⟨rfl, rfl, rfl⟩ := Heq
    wp_auto
    -- the receipt: the `Ready`'s entries are appended
    ihave Hrcpt' : appendReceipt rs.storage rs.unpersisted $$ [Hrcpt]
    · rw [Hstor]
      iexact Hrcpt
    imod ownRawNode_appended γ.raft nv.rn' id rs $$ Hrn Hrcpt' with Hrn
    imod termLB_bound γ.bud rs.term ⊤ (by solve_ndisj) $$ Hbud Hlb' with %Hbnd
    wp_apply wp_RawNode_Advance γ.raft nv.rn' id { rs with unpersisted := [] } rdv' rfl
      (by simp only; omega) Hunst $$ [$Hrn] as %t ⟨Hrn, %Ht1, %Ht2⟩
    subst Ht2 Hrc
    wp_for_post
    iframe HΦ n r
    iexists pc', chan.nil, chan.nil, zero_val Ready, ld'
    iframe propc readyc advancec rd lead
    isplitr
    · ipureintro; exact Hpc'
    unfold runHead
    iexists _
    isplitl [Hrn]
    · iexact Hrn
    unfold headRest
    simp only
    iframe Hlb'
    isplitr
    · ipureintro; exact Hstor
    ileft
    isplitr
    · ipureintro; simp
    rw [Hdel]
    iframe Hdlv
    isplitl [Hrof Hrof']
    · unfold rofFull
      iexists (d, ce, rs.unpersisted)
      iframe Hrof Hrof'
    ileft; ipureintro; simp
  -- `<-n.status`: never
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists GoChan, inferInstance, inferInstance, inferInstance, inferInstance,
      nv.status', γ.status
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply isHandshake_isChan $$ Hstatus
    iapply handshake_false_recv_au γ.status nv.status' $$ [$Hlc1 $Hlc2] Hstatus
  -- `<-n.stop`: never
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.stop', γ.stop
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply isHandshake_isChan $$ Hstop
    iapply handshake_false_recv_au γ.stop nv.stop' $$ [$Hlc1 $Hlc2] Hstop
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
