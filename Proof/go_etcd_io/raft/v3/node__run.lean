/- Lean-first (no Rocq counterpart).

**Raft v3.7 (2026-10-16, stage R5 of the retarget).** Ported from the old proof. What changed:
the proposal from `propc` is a message pointer, owned (`propP`: `msgIn`), stamped by `run`
(`m.From = new(r.id)`: `cellRO_alloc`, `msgPtsC_store_From`) before `r.Step(m)`; a `recvc`
message is a pointer (`netP`: `msgIn ml □ st`) whose type and sender `run` reads through the
getters (`GetType`, `GetFrom`); `confc` carries a `*pb.ConfChangeV2` (`ownCCV2 v □ ccm`) and
`applyConfChange` returns a fresh `*pb.ConfState` (`csPts cs 1 c true`), whose `Voters` and
`VotersOutgoing` fields the removed-node check reads directly, and which goes to `confstatec`
whole (`confstateP`); a `Ready`'s messages are handed out (`QMsg`, D8). -/
module

public import Proof.go_etcd_io.raft.v3.InvAdvance
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
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import Proof.go_etcd_io.raft.v3.InvNodeRun
public import Proof.go_etcd_io.raft.v3.LemmasRunR

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

omit [FfiInterp ffi] [FfiSemantics ext ffi] [StorageModel GF] in
/-- A loop condition `wp_if_destruct` left as the value equation (D22 S-d3a), peeled. -/
private theorem hif_pos {P : Prop} [Decidable P] (h : (#(decide P) : val) = #true) : P :=
  of_decide_eq_true (GoGlobalContext.intoVal_inj_bool h)

omit [FfiInterp ffi] [FfiSemantics ext ffi] [StorageModel GF] in
private theorem hif_neg {P : Prop} [Decidable P] (h : ¬ ((#(decide P) : val) = #true)) : ¬ P :=
  fun hp => h (by rw [decide_eq_true hp])

set_option hygiene false in
/-- Peel `Hif` if `wp_if_destruct` left it as the value equation. -/
local macro "peel_hif" : tactic => `(tactic| first
  | (replace Hif := hif_pos Hif
     try simp only [if_decide_bool_eq_true, if_decide_bool_eq_false, decide_eq_true Hif,
       Bool.false_eq_true, ↓reduceIte]
     try wp_auto)
  | (replace Hif := hif_neg Hif
     try simp only [if_decide_bool_eq_true, if_decide_bool_eq_false, decide_eq_false Hif,
       Bool.false_eq_true, ↓reduceIte]
     try wp_auto)
  | skip)

set_option maxHeartbeats 1000000 in
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
    (wp_raft_applyConfChange : raft.applyConfChange.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG)) :
    node.run.spec (GF := GF) (hG := hG) := by
  intro γ id n
  wp_start as ⟨#Hnode, Hpre⟩
  ihave #Hnode' := Hnode
  open_node Hnode'
  unfold runPre
  icases Hpre with ⟨%nv0, %rs, %x, #Hn0, Hrn, %Hrs, Hdlv, Hr1, Hr2, #Hlb, Hcfg⟩
  icombine Hn Hn0 gives %Heq
  subst Heq
  wp_auto
  simp only [None']
  wp_auto
  ihave HI : iprop(∃ (pc rc ac : GoChan) (rdv : Ready) (ld : w64),
      "propc" ∷ propc_ptr ↦ pc ∗ "readyc" ∷ readyc_ptr ↦ rc ∗ "advancec" ∷ advancec_ptr ↦ ac ∗
      "rd" ∷ rd_ptr ↦ rdv ∗ "lead" ∷ lead_ptr ↦ ld ∗
      "%Hpc" ∷ ⌜pc = chan.nil ∨ pc = nv.propc'⌝ ∗ "Hhead" ∷ runHead γ id nv ac rc rdv)
    $$ [propc readyc advancec rd lead Hrn Hdlv Hr1 Hr2 Hcfg]
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
    iframe Hlb Hcfg
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
  · iapply isAdvChan_isChan $$ Hadvancec
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
        ⟨#Hlb, %Hrs, Hdlv, Hrof, Hcfg, Hrc⟩
      obtain ⟨Hst, Hsteps, Hunp⟩ := Hrs
      -- (2026-10-20, D22 S-c) no snapshot pending
      icases runCfg_psnap γ rs $$ Hcfg with ⟨%Hps, Hcfg⟩
      wp_apply wp_RawNode_HasReady γ.raft nv.rn' id rs $$ [$Hrn] as %b Hb
      icases Hb with (⟨%Hb, Hrn⟩ | ⟨%Hb, Hrn⟩) <;> subst Hb
      · wp_auto
        wp_apply wp_RawNode_readyWithoutAccept γ.raft nv.rn' id rs Hsteps Hunp $$ [$Hrn]
          as %rd' %ce %es %ms %sts %hrd %L H
        iNamed H
        -- (D22 S-d3a) no snapshot restored, none handed out
        have HL := Hpsn Hps
        subst HL
        iunfold rdSnapOut at Hsnapz
        icases Hsnapz with %Hsnapz
        wp_join_done
        iexists nv.readyc', rd'
        iframe n readyc rd
        unfold runMid
        iright
        isplitr
        · ipureintro; rfl
        iexists rs
        iframe Hlb Hdlv Hrof Hcfg
        isplitr
        · ipureintro; exact ⟨Hst, Hsteps, Hunp⟩
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists ce, es, ms
        iframe Hrn
        unfold freshOk
        iframe Hce Hcommitted Hents Hmsgs Hmsgs_cap Hmsgs_own Hmsgs_ok
        isplitr
        · iexists sts
          iframe Hrs Hrs_ok
        isplitr
        · iexists hrd
          iframe Hhard Hhsw
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
        iframe Hlb Hdlv Hrof Hcfg
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
    icases HP with (⟨%d, %γr, Hm, #Hent, Htk, #Hho, Hprod⟩ | ⟨%Hres, Hfwd⟩)
    · -- `m := pm.m; m.From = new(r.id)`
      icases msgPtsC_store_From _ _ _ _ $$ Hm with ⟨%pf, Hpf, Hback⟩
      wp_auto_lc 1
      imod cellRO_alloc $$ «$r0» with #c0
      ihave Hm := Hback $$ %_ %id Hpf c0
      ihave Hhead := runMid_head γ id nv ac rc' rdv' $$ Hmid
      iunfold runHead at Hhead
      icases Hhead with ⟨%rs, Hrn, Hrest⟩
      ihave #Hm0 := isMessage_propMsg γ.raft d $$ Hent
      ihave #Hm1 := isMessage_propose_from γ.raft propMsgM [propEntryM d] id $$ Hm0
      wp_apply wp_rn_raft_Step_prop wp_raft_Step γ.raft nv.rn' id rs r pm.m'
        ⟨{ propMsgM with From' := id }, [propEntryM d], none, [], []⟩ rfl rfl
        $$ [$Hrn $Hrnraft $Hm $Hm1 Htk $Hlc1] as %err ⟨Hrn, #Hstep⟩
      · iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => entTk (GF := GF) γ.raft e)).2
        iexact Htk
      ihave %Hrnn := isChan_not_null $$ [Hho]
      · unfold isHandoff
        icases Hho with ⟨$, -⟩
      wp_if_destruct
      · exact absurd Hif Hrnn
      wp_apply wp_handoff_send (t := go.error) γr pm.result' stepErr
        iprop(True) iprop(True) err $$ [$Hho $Hprod] as Hprod
      · iframe Hstep
      wp_apply wp_handoff_close (t := go.error) γr pm.result' stepErr
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
      icases Hfwd with ⟨%st, Hm, %Hty, #Hm0, Htk⟩
      icases msgPtsC_store_From _ _ _ _ $$ Hm with ⟨%pf, Hpf, Hback⟩
      wp_auto_lc 1
      imod cellRO_alloc $$ «$r0» with #c0
      ihave Hm := Hback $$ %_ %id Hpf c0
      ihave Hhead := runMid_head γ id nv ac rc' rdv' $$ Hmid
      iunfold runHead at Hhead
      icases Hhead with ⟨%rs, Hrn, Hrest⟩
      ihave #Hm1 := isMessage_propose_from γ.raft st.msg st.ents id $$ Hm0
      wp_apply wp_rn_raft_Step_prop wp_raft_Step γ.raft nv.rn' id rs r pm.m'
        { st with msg := { st.msg with From' := id } } Hty rfl
        $$ [$Hrn $Hrnraft $Hm $Hm1 $Htk $Hlc1] as %err ⟨Hrn, -⟩
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
    iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance,
      nv.recvc', γ.recvc
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply isHandshake_isChan $$ Hrecvc
    iapply handshake_receive_au γ.recvc nv.recvc' (netP γ id) iprop(True) _
      $$ [$Hlc1 $Hlc2] Hrecvc []
    · itrivial
    inext
    iintro %ml Hnet
    iunfold netP at Hnet
    icases Hnet with ⟨%st, Hm, %Hok, %Hpvb, #Hmsg, #Hlbm, Hcred, Htc⟩
    have Hty0 : 0 ≤ sint.Z st.msg.Type' := netStepTypes_nonneg Hok.1
    wp_auto_lc 1
    ihave Hhead := runMid_head γ id nv ac rc' rdv' $$ Hmid
    iunfold runHead at Hhead
    icases Hhead with ⟨%rs, Hrn, Hrest⟩
    -- `IsResponseMsg(m.GetType()) && !IsLocalMsgTarget(m.GetFrom()) &&
    -- r.trk.Progress[m.GetFrom()] == nil`
    wp_apply wp_GetType.1 ml _ _ _ _ $$ [$Hm] as Hm
    wp_apply wp_IsResponseMsg _ Hty0 as %b2 _
    wp_if_destruct
    all_goals try (
      wp_apply wp_GetFrom.1 ml _ _ _ _ $$ [$Hm] as Hm
      wp_apply wp_IsLocalMsgTarget st.msg.From'
      wp_if_destruct)
    all_goals try (
      icases ownRawNode_borrow γ.raft nv.rn' id rs r $$ Hrn Hrnraft with ⟨%cf, %s, Hphys, Hback⟩
      icases ownRaftPhysC_tracker_same cf r id s $$ Hphys with
        ⟨%tv, Htrkf, Htrk, Hback2⟩
      icases ownTrackerC_progress_map cf tv _ $$ Htrk with ⟨#Hprs, %Hdom, Htrk⟩
      try wp_auto
      wp_apply wp_GetFrom.1 ml _ _ _ _ $$ [$Hm] as Hm
      try wp_auto
      wp_apply wp_map_lookup1 go.uint64 (go.GoType.PointerType tracker.Progress.ty) _ _
        st.msg.From' _ $$ Hprs with -
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
      icases headRest_flw γ nv rs ac rc' rdv' $$ Hrest with ⟨%Hflw, Hrest⟩
      -- the budget covers the step: a `MsgTimeoutNow` spends its tick credit; (2026-10-17) the
      -- term ceiling raised to the bound, past the message's term (a granted pre-vote answers at
      -- it) and a transfer's campaign
      imod budget_step γ.bud rs.tc st.msg.Term' (st.msg.Type' = MsgTimeoutNow) ⊤ (by solve_ndisj)
        $$ Hbud Hlb' Hlbm Htc with ⟨%Hbnd, %tb, #Hlbtb, %Htb⟩
      have Htb1 := Int.le_max_left (uint.Z rs.tc) (uint.Z st.msg.Term')
      have Htb2 := Int.le_max_right (uint.Z rs.tc) (uint.Z st.msg.Term')
      have Hite : (0 : Int) ≤ (if st.msg.Type' = MsgTimeoutNow then 1 else 0) := by split <;> decide
      icases ownRawNode_term_tc γ.raft nv.rn' id rs $$ Hrn with ⟨%Htt, Hrn⟩
      ihave Hrn := ownRawNode_raise_tc γ.raft nv.rn' id rs tb (by omega) $$ Hrn
      icases ownRawNode_mode γ.raft nv.rn' id _ $$ Hrn with ⟨%Hmd, Hrn⟩
      wp_apply wp_rn_raft_Step_net wp_raft_Step γ.raft nv.rn' id { rs with tc := tb } r ml st Hok
        (by simp only; omega)
        (fun h => by simp only; rw [ite_eq_left h] at Htb; omega) Hpvb.1 Hflw Hpvb.2.1 Hpvb.2.2
        $$ [Hrn Hm Hcred Hlc1] as %err %t ⟨Hrn, %Ht⟩
      · iframe Hrn Hm Hrnraft Hmsg Hcred Hlc1
      ihave Hrest := headRest_term γ nv rs ac rc' rdv' t tb $$ Hrest Hlbtb
      try wp_auto
      wp_for_post
      iframe HΦ n r
      iexists pc', rc', ac, rdv', ld'
      iframe propc readyc advancec rd lead
      isplitr
      · ipureintro; exact Hpc'
      unfold runHead
      iexists { { rs with tc := tb } with term := t }
      iframe Hrn Hrest)
  -- `cc := <-n.confc` (2026-10-13): a conf change that leaves the configuration unchanged
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance,
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
    icases HP with ⟨%ccs, Hccs, HP⟩
    wp_auto_lc 1
    ihave Hhead := runMid_head γ id nv ac rc' rdv' $$ Hmid
    iunfold runHead at Hhead
    icases Hhead with ⟨%rs, Hrn, Hrest⟩
    icases headRest_mode γ nv rs ac rc' rdv' $$ Hrest with ⟨%Hrm, Hrest⟩
    icases ownRawNode_mode γ.raft nv.rn' id rs $$ Hrn with ⟨%Hmd, Hrn⟩
    icases HP with (%Hn | ⟨%ds, %ca, %cfg, %k, %e, %cs', %Hpre, #Hdlb, Hcap, Hccq⟩)
    · -- the static mode: a shrinking change (2026-10-13)
      have Hstatic : γ.raft.reDyn = none := Hmd.1 (Hrm.trans Hn.1)
      have Hgm := Hn.1
      have Hn := Hn.2
      -- `_, okBefore := r.trk.Progress[r.id]`: the node is a voter
      icases ownRawNode_borrow_in γ.raft nv.rn' id rs r Hstatic $$ Hrn Hrnraft
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
      wp_apply wp_rn_raft_applyConfChange wp_raft_applyConfChange γ.raft nv.rn' id rs r cc ccs
        Hstatic Hn
        $$ [$Hrn $Hrnraft $Hccs $Hlc1] as %cs %xs %ls ⟨Hrn, -, Hcsp, %Hcs⟩
      -- `_, okAfter := r.trk.Progress[r.id]`: still a voter
      icases ownRawNode_borrow_in γ.raft nv.rn' id rs r Hstatic $$ Hrn Hrnraft
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
      wp_auto_lc 3
      -- `select { case n.confstatec <- cs: case <-n.done: }`
      wp_apply_core chan.wp_select_blocking
      iapply BigAndL.bigAndL_cons.2
      isplit
      · simp only [chan.blockingClausePre]
        iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance,
          nv.confstatec', γ.confstatec, _
        isplitr
        · ipureintro; exact ⟨rfl, rfl⟩
        isplitr
        · iapply isHandshake_isChan $$ Hconfstatec
        iapply handshake_send_au γ.confstatec nv.confstatec' _ (confstateP γ) iprop(True)
          $$ [$Hlc1 $Hlc2 $Hlc3] Hconfstatec [Hcsp]
        · unfold confstateP
          iexists ConfStateM.mk xs ls [] [] false
          iframe Hcsp
          ileft
          ipureintro; exact ⟨Hgm, Hcs.1, Hcs.2, rfl, rfl, rfl⟩
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
    -- (2026-10-15, stage N) the dynamic mode: the next committed conf entry's change
    obtain ⟨Hdy, Hpre⟩ := Hpre
    obtain ⟨dec, c0, h0, h1, Hgm⟩ : ∃ dec c0 h0 h1, γ.mode = .dyn dec c0 h0 h1 := by
      cases h : γ.mode with
      | static => rw [h] at Hdy; cases Hdy
      | dyn dec c0 h0 h1 => exact ⟨dec, c0, h0, h1, rfl⟩
    have Hp := Hpre dec c0 h0 h1 Hgm
    have hm : rs.mode = .dyn dec c0 h0 h1 := Hrm.trans Hgm
    -- the driver's view agrees with `run`'s: the change's premises at the `RawNode`; the shared
    -- configuration moves to the entry applied
    icases headRest_cfg γ nv rs ac rc' rdv' cs' (k + 1) $$ Hrest with ⟨Hcfg, Hrestb⟩
    icases runCfg_confc γ rs ds ca cfg _ k e cs' dec Hp $$ Hcfg Hdlb Hcap with ⟨%Hp', Hupd⟩
    imod Hupd with ⟨Hcfg, Hcap, #Hcamlb⟩
    ihave Hrest := Hrestb $$ Hcfg
    -- `_, okBefore := r.trk.Progress[r.id]`
    icases ownRawNode_borrow γ.raft nv.rn' id rs r $$ Hrn Hrnraft with ⟨%cf, %s, Hphys, Hback⟩
    icases ownRaftPhysC_tracker_same cf r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback2⟩
    icases ownTrackerC_progress_map cf tv _ $$ Htrk with ⟨#Hprs, %Hdom, Htrk⟩
    wp_auto
    wp_apply wp_map_lookup2 $$ Hprs as -
    ihave Hphys := Hback2 $$ %tv Htrkf Htrk
    ihave Hrn := Hback $$ Hphys
    try wp_auto
    -- `cs := r.applyConfChange(cc)`
    wp_apply wp_rn_raft_applyConfChange_dyn wp_raft_applyConfChange γ.raft nv.rn' id rs r cc ccs
      dec c0 h0 h1 hm k e cs' Hp'
      $$ [$Hrn $Hrnraft $Hccs $Hlc1] as %cs %xs %os %ls %lns ⟨Hrn, -, Hcsp, %Hcs⟩
    -- `_, okAfter := r.trk.Progress[r.id]`
    icases ownRawNode_borrow γ.raft nv.rn' id _ r $$ Hrn Hrnraft with ⟨%cf2, %s2, Hphys, Hback⟩
    try wp_auto
    icases ownRaftPhysC_tracker_same cf2 r id s2 $$ Hphys with ⟨%tv2, Htrkf, Htrk, Hback2⟩
    icases ownTrackerC_progress_map cf2 tv2 _ $$ Htrk with ⟨#Hprs2, %Hdom2, Htrk⟩
    wp_auto
    wp_apply wp_map_lookup2 $$ Hprs2 as -
    ihave Hphys := Hback2 $$ %tv2 Htrkf Htrk
    ihave Hrn := Hback $$ Hphys
    try wp_auto
    -- `if okBefore && !okAfter { ... if !found { propc = nil } }`: the node removed
    wp_join iprop(∃ pc'' : GoChan, propc_ptr ↦ pc'' ∗ ⌜pc'' = chan.nil ∨ pc'' = nv.propc'⌝ ∗
        cs_ptr ↦ cs ∗ r_ptr ↦ r ∗
        csPts cs (DFrac.own 1) (ConfStateM.mk xs ls os lns cs'.cfg.autoLeave) true)
      at next with [propc cs r okAfter Hcsp]
    · by_cases Hb1 : (s.progress !! id).isSome = true
      · rw [decide_eq_true Hb1]
        wp_auto
        by_cases Hb2 : (s2.progress !! id).isSome = true
        · rw [decide_eq_true Hb2]
          wp_auto
          wp_join_done
          iexists pc'
          iframe propc cs r Hcsp
          ipureintro; exact Hpc'
        · rw [decide_eq_false Hb2]
          icases csPts_voters _ _ _ _ $$ Hcsp with ⟨%sv, %so, HV, Hv, HO, Ho, Hcsb⟩
          wp_auto
          -- `for _, sl := range [][]uint64{cs.Voters, cs.VotersOutgoing} { ... }`
          wp_apply wp_slice_literal (V := GoSlice) [sv, so]
          try (isplitr; (ipureintro; rfl))
          iintro %slp ⟨Hsl, -⟩
          simp only [go.arrayLiteralSize, List.foldl]
          rw [show (max (max ((0 : Int) + 1 + 1) 0) 0) = 2 by decide]
          wp_auto
          ihave IO : iprop(∃ (j : w64) (f : Bool) (slv : GoSlice),
              "i" ∷ i_ptr ↦ j ∗ "found" ∷ found_ptr ↦ f ∗ "sl" ∷ sl_ptr ↦ slv ∗
              "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 2⌝) $$ [i found sl]
          · iexists W64 0, _, _
            iframe i found sl
            ipureintro; decide
          wp_for IO
          wp_if_destruct
          all_goals try simp at Hif
          all_goals peel_hif
          · -- an iteration: `sl` is `cs.Voters` or `cs.VotersOutgoing`
            have Hj01 : j = W64 0 ∨ j = W64 1 := by
              have := Hj.1; revert Hif; word
            icases voters_pick sv so (DFrac.own 1) _ _ j Hj01 $$ Hv Ho with
              ⟨%v, %vs, %Hv, Hvs, Hpick⟩
            have Hbnd' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z (W64 2) := ⟨Hj.1, Hif⟩
            simp only [Hbnd', _root_.and_self]
            wp_apply wp_load_slice_index _ (sint.Z j) _ _ v Hbnd'.1 $$ [Hsl] with Hsl
            · iframe Hsl; ipureintro; exact Hv
            try wp_auto
            -- `for _, id := range sl { if id == r.id { found = true; break } }`
            ihave %Hvlen := ownSlice_len v (DFrac.own 1) vs $$ Hvs
            ihave II : iprop(∃ (j2 idv : w64) (f2 : Bool),
                "i" ∷ i_ptr ↦ j2 ∗ "id" ∷ id_ptr ↦ idv ∗ "found" ∷ found_ptr ↦ f2 ∗
                "%Hj2" ∷ ⌜0 ≤ sint.Z j2⌝) $$ [i id found]
            · iexists W64 0, _, _
              iframe i id found
              ipureintro; decide
            wp_for II
            wp_if_destruct
            all_goals try simp at Hif
            all_goals peel_hif
            · obtain ⟨x, Hx⟩ : ∃ x, vs[(sint.Z j2).toNat]? = some x :=
                ⟨_, List.getElem?_eq_getElem (by rw [Hvlen.1]; word)⟩
              have Hbnd2 : 0 ≤ sint.Z j2 ∧ sint.Z j2 < sint.Z v.len := ⟨Hj2, Hif⟩
              simp only [Hbnd2, _root_.and_self]
              wp_apply wp_load_slice_index v (sint.Z j2) vs (DFrac.own 1) x Hj2 $$ [Hvs] as Hvs
              · iframe Hvs; ipureintro; exact Hx
              try wp_auto
              wp_if_destruct
              · -- found: `break`, then the outer `break`
                wp_for_post
                wp_for_post
                wp_join_done
                icases Hpick $$ Hvs with ⟨Hv, Ho⟩
                ihave Hcsp := Hcsb $$ HV Hv HO Ho
                iexists pc'
                iframe propc cs r Hcsp
                ipureintro; exact Hpc'
              · wp_for_post
                iframe
                iexists j2 + W64 1, x, f2
                iframe
                ipureintro; word
            · -- the inner loop is done
              cases f2
              · wp_auto
                icases Hpick $$ Hvs with ⟨Hv, Ho⟩
                wp_for_post
                iframe
                iexists j + W64 1, false, v
                iframe
                ipureintro; word
              · wp_auto
                wp_for_post
                wp_join_done
                icases Hpick $$ Hvs with ⟨Hv, Ho⟩
                ihave Hcsp := Hcsb $$ HV Hv HO Ho
                iexists pc'
                iframe propc cs r Hcsp
                ipureintro; exact Hpc'
          · -- the outer loop is done
            ihave Hcsp := Hcsb $$ HV Hv HO Ho
            cases f <;> wp_auto
            · wp_join_done
              iexists chan.nil
              iframe propc cs r Hcsp
              ipureintro; left; rfl
            · wp_join_done
              iexists pc'
              iframe propc cs r Hcsp
              ipureintro; exact Hpc'
      · rw [decide_eq_false Hb1]
        wp_auto
        wp_join_done
        iexists pc'
        iframe propc cs r Hcsp
        ipureintro; exact Hpc'
    iintro ⟨%pc'', propc, %Hpc'', cs, r, Hcsp⟩
    wp_auto_lc 3
    -- `select { case n.confstatec <- cs: case <-n.done: }`
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance,
        nv.confstatec', γ.confstatec, _
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · iapply isHandshake_isChan $$ Hconfstatec
      iapply handshake_send_au γ.confstatec nv.confstatec' _ (confstateP γ) iprop(True)
        $$ [$Hlc1 $Hlc2 $Hlc3] Hconfstatec [Hcap Hccq Hcsp]
      · unfold confstateP
        iexists ConfStateM.mk xs ls os lns cs'.cfg.autoLeave
        iframe Hcsp
        iright
        isplitr
        · ipureintro; rw [Hgm]; rfl
        iexists (k + 1, cs')
        iframe Hcap Hccq Hcamlb
        ipureintro; exact ⟨Hcs.1, Hcs.2.1, Hcs.2.2.1, Hcs.2.2.2, rfl⟩
      inext
      iintro -
      wp_auto
      wp_for_post
      iframe HΦ n r
      iexists pc'', rc', ac, rdv', ld'
      iframe propc readyc advancec rd lead
      isplitr
      · ipureintro; exact Hpc''
      unfold runHead
      iexists { rs with cfg := cs', capplied := k + 1 }
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
    icases headRest_flw γ nv rs ac rc' rdv' $$ Hrest with ⟨%Hflw, Hrest⟩
    -- (2026-10-17) the tick credit raises the term ceiling by one: the tick may (pre-)campaign
    imod budget_spend γ.bud rs.tc ⊤ (by solve_ndisj) $$ Hbud Hcr Hlb' with ⟨%Hb, #Hlb1⟩
    icases ownRawNode_term_tc γ.raft nv.rn' id rs $$ Hrn with ⟨%Htt, Hrn⟩
    ihave Hrn := ownRawNode_raise_tc γ.raft nv.rn' id rs (rs.tc + W64 1) (by word) $$ Hrn
    wp_apply wp_RawNode_Tick γ.raft nv.rn' id { rs with tc := rs.tc + W64 1 } (by simp only; word)
      Hflw $$ [$Hrn] as %t H
    iNamed H
    ihave Hrest := headRest_term γ nv rs ac rc' rdv' t (rs.tc + W64 1) $$ Hrest Hlb1
    wp_for_post
    iframe HΦ n r
    iexists pc', rc', ac, rdv', ld'
    iframe propc readyc advancec rd lead
    isplitr
    · ipureintro; exact Hpc'
    unfold runHead
    iexists { { rs with tc := rs.tc + W64 1 } with term := t }
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
      ⟨%Hac, %rs, #Hlb', %Hrs, Hdlv, Hrof, Hcfg, Hst⟩
    subst Hac
    obtain ⟨Hstor, Hsteps, Hunp⟩ := Hrs
    -- (D22 S-d3a) no snapshot lent (`runCfg`)
    icases runCfg_slent γ rs $$ Hcfg with ⟨%Hsl0, Hcfg⟩
    -- the `Ready` to send, fresh or stale (then it holds no messages and no entries)
    ihave Hg : iprop(∃ (ce es : List EntryM) (ms : List QMsg),
        ownRawNodeReady γ.raft nv.rn' id rs rdv' ce es ms false ∗
        entsRO rdv'.CommittedEntries' ce ∗ isCommitted γ.raft (rs.delivered ++ ce) ∗
        entsRO rdv'.Entries' es ∗ rdv'.Messages' ↦* ms.map QMsg.loc ∗
        ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st) ∗
        ([∗list] q ∈ ms, isRaftMsg γ.raft q.st) ∗
        (∃ sts : List ReadStateM, readStatesPts rdv'.ReadStates' sts ∗
          [∗list] st ∈ sts, readStateOk γ.raft st) ∗
        (∃ h : HardStateM, hsOpt rdv'.HardState' h ∗
          hsWit γ.raft (phsNext rs.phs h) (rs.delivered ++ ce).length) ∗
        ⌜(∀ q ∈ ms, uint.Z q.st.msg.Term' ≤ uint.Z rs.tc) ∧ rdv'.Snapshot' = null⌝) $$ [Hst]
    · icases Hst with (⟨%ce, %es, %ms, Hrn, Hf⟩ | ⟨Hrn, Hstale⟩)
      · iunfold freshOk at Hf
        icases Hf with ⟨#Hce, #Hcommitted, #Hents, Hmsgs, -, Hown, #Hmsgs_ok, #Hrsts, #Hhd,
          %Hfacts⟩
        iexists ce, es, ms
        iframe Hrn Hce Hcommitted Hents Hmsgs Hown Hmsgs_ok Hrsts Hhd
        ipureintro; exact Hfacts
      · icases ownRawNodeIdle_facts γ.raft nv.rn' id rs Hsl0 $$ Hrn with ⟨%Hidf, Hrn⟩
        iunfold staleOk at Hstale
        icases Hstale with
          ⟨%ce, %es, %k, %hrd, #Hrdsoft, #Hrdh, #Hhsw, #Hce, Hce_cap, #Hcommitted, #Hents, #Hrsts,
            %Hsf⟩
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
        -- (D22l) its hard state's witness, for `prevHardSt`
        ihave #Hrdw := phsWit_of_hsWit_next γ.raft rs.phs hrd _ $$ Hhsw
        ihave Hrn := ownRawNodeIdle_ready γ.raft nv.rn' id rs rdv' ce sts hrd Hsteps Hunp Hrdz
          Hce_ok $$ Hrdsoft Hrdh Hrdw Hce Hce_cap Hents Hcommitted Hrs Hrn
        iexists ce, [], []
        iframe Hrn Hce Hcommitted Hents
        isplitl []
        · rw [List.map_nil]
          iapply ownSlice_of_shape (V := Loc) rdv'.Messages' (DFrac.own 1) Hshape
        isplitl []
        · iapply BigSepL.bigSepL_nil.2
          iempintro
        isplitl []
        · iapply BigSepL.bigSepL_nil.2
          iempintro
        isplitr
        · iexists sts
          iframe Hrs Hrs_ok
        isplitr
        · iexists hrd
          iframe Hrdh Hhsw
        ipureintro; exact ⟨by simp, Hrdz⟩
    icases Hg with
      ⟨%ce, %es, %ms, Hrn, #Hce, #Hcommitted, #Hents, Hmsgs, Hown, #Hmsgs_ok, #Hrsts,
        ⟨%h, #Hhh, #Hhw⟩, %Hfacts⟩
    iapply handshake_send_au_upd (t := Ready.ty) γ.readyc nv.readyc' rdv' (readyP γ) iprop(True) _
      $$ [$Hlc1 $Hlc2 $Hlc3] Hreadyc
    -- (2026-10-16, stage R7a) the `Ready`'s soft state, read-only for the application
    icases ownRawNodeReady_softStateRO γ.raft nv.rn' id rs rdv' ce es ms false $$ Hrn
      with ⟨#Hss, Hrn⟩
    -- the append right goes with the `Ready`, and `rof` records it
    imod ownRawNodeReady_handout γ.raft nv.rn' id rs rdv' ce es ms none $$ Hrn with ⟨Hrn, Happ, Hcr, Htk, #Hri⟩
    iunfold readyOut at Happ
    -- (2026-10-15, stage N) the committed log handed out grows, a lower bound for the driver
    imod runCfg_extend γ rs { rs with delivered := rs.delivered ++ ce } ce rfl rfl rfl rfl rfl $$ Hcfg
      with ⟨Hcfg, #Hdlb⟩
    iunfold rofFull at Hrof
    icases Hrof with ⟨%x, Hr1, Hr2⟩
    imod dghostVar_update_halves (rs.delivered, ce, es, phsNext rs.phs h) γ.rof x x $$ Hr1 Hr2
      with ⟨Hr1, Hr2⟩
    ihave Hmt := readyMsgs_termLB γ rs.tc ms Hfacts.1 $$ Hown Hmsgs_ok Hlb'
    imodintro
    isplitl [Hdlv Hr1 Happ Hmsgs Hmt Hcr Htk]
    · unfold readyP
      iexists rs.delivered, ce, es, ms, rs.phs, phsNext rs.phs h
      iframe Hdlv Hr1 Hdlb
      unfold readyData
      iframe Hce Hcommitted Hents Hmsgs Hmt Hcr Htk Hrsts Hhw Hss Hri
      isplitl [Happ]
      · rw [← Hstor]
        iexact Happ
      isplitr
      · iexists h; iframe Hhh; ipureintro; rfl
      ipureintro; exact Hfacts.2
    inext
    iintro -
    wp_auto
    -- (D22 S-d3a) no snapshot restored (`runCfg`): none handed out
    icases runCfg_psnap γ _ $$ Hcfg with ⟨%Hps0, Hcfg⟩
    icases runCfg_slent γ _ $$ Hcfg with ⟨%Hsl0, Hcfg⟩
    wp_apply wp_RawNode_acceptReady γ.raft nv.rn' id rs rdv' ce es ms h none $$ [$Hrn $Hhh]
      as %steps Hrn
    have Hrseq : ({ rs with
          delivered := rs.delivered ++ ce, unpersisted := es, steps := steps,
          outlb := 0, unst := false, phs := phsNext rs.phs h, psnap := false, slent := none } :
          RNState) =
        { rs with
          delivered := rs.delivered ++ ce, unpersisted := es, steps := steps,
          outlb := 0, unst := false, phs := phsNext rs.phs h } := by
      cases rs; simp only at Hps0 Hsl0; subst Hps0 Hsl0; rfl
    rw [Hrseq]
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
                      outlb := 0, unst := false, phs := phsNext rs.phs h }
    iframe Hrn
    unfold headRest
    iframe Hlb'
    isplitr
    · ipureintro; exact Hstor
    isplitl [Hcfg]
    · iExactEq Hcfg; rfl
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
    · iapply isAdvChan_isChan $$ Hadvancec
    icases runMid_busy γ id nv rc' rdv' Hadv_nn $$ Hmid with
      ⟨%rs, %d, %ce, Hrn, #Hlb', Hcfg, %Hrs, Hrof⟩
    obtain ⟨Hstor, Hrc, Hunst, Hdel⟩ := Hrs
    subst Hrc
    -- (D19i part 1) the rendezvous raises the floor (`advInv`): `run`'s node goes in, comes
    -- back appended and raised
    iapply adv_recv_au γ nv.rn' id nv.advancec' _ $$ [$Hlc1 $Hlc2] Hadvancec [Hrn Hcfg Hrof]
    · iunfold advDep
      iexists rs, d, ce
      iframe Hrn Hlb' Hcfg Hrof
      ipureintro; exact ⟨Hstor, Hunst, Hdel⟩
    inext
    iintro Hret
    iunfold advRet at Hret
    icases Hret with ⟨%rs1, %ca_d, Hrn, #Hlb1, Hcfg, Hdlv, Hrofs, #Hcamlb, %Hr1⟩
    obtain ⟨Hstor1, Hunst1, Hunp1, Hflw1, HA⟩ := Hr1
    wp_auto
    -- (2026-10-15, stage N) A1, from the driver's
    icases runCfg_a1 γ { rs1 with flw := false } ca_d $$ Hcfg Hcamlb [] with ⟨%HA1, Hcfg⟩
    · ipureintro; exact HA
    icases runCfg_slent γ { rs1 with flw := false } $$ Hcfg with ⟨%Hsl1, Hcfg⟩
    wp_apply wp_RawNode_Advance γ.raft nv.rn' id rs1 rdv' (fun _ => Hunp1) Hunst1 HA1
      $$ [$Hrn] as %t %ca ⟨Hrn, %Ht1, %Ht2, %Hca⟩
    · unfold loanRet; rw [show rs1.slent = none from Hsl1]; iempintro
    rw [advRS_none (rs := rs1) t ca Hsl1]
    ihave Hcfg := runCfg_advance γ { rs1 with flw := false }
      { rs1 with steps := [], term := t, capplied := ca, flw := false }
      rfl rfl rfl rfl Hca HA1 $$ Hcfg
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
    iframe Hlb1 Hcfg
    isplitr
    · ipureintro; exact Hstor1
    ileft
    isplitr
    · ipureintro; simp [Hunp1]
    iframe Hdlv
    isplitl [Hrofs]
    · unfold rofFull
      iexact Hrofs
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
