/-
Lean-first (no Rocq counterpart). **The traced `RawNode` functions** (2026-11-11, trace-check Q8 stage 1
slice 25n, `notes/decisions.md`, "Q8 stage 1 (slice 25n)"). Raft-internal (not on `etc/api/raft.txt`).

`ownRawNode` holds the node's trace capability (`rnTrace`, `InvRawnode.lean`: `emp` untraced; traced,
the configuration's scope, `TrNoSnap` and the capability idle at the node's state with any `booted`
flag). Here, each `RawNode` function the harness reaches gets a traced triple: the same `ownRawNode` in
and out, at a traced cluster (`γ.reTrace = some γd`), with what only the node API supplies (a received
message's token and facts, the bounds). Each takes `raft.Step`'s traced bundle as an explicit
hypothesis (`stepBundle_traced.on`, `TracedRaftStep.lean`, proved path by path in the path files and
not yet assembled), so that this layer does not wait for the path proofs. Done:

- `rnTrace_some`: the capability open at a traced node;
- `RawNode.Step.tracedTriple` (`RawNode.Step.traced`): a message of a traced network type
  (`TrNetTy`: `MsgApp`, `MsgAppResp`, `MsgVote`, `MsgVoteResp`, `MsgHeartbeat`, `MsgHeartbeatResp`,
  the types the harness's peers send with pre-vote and check-quorum off), its `isRaftMsg` (the
  transport's facts, which give the bundle's `isMessageC`, `MsgTrOk` and `TrRecvShape`:
  `isRaftMsg_trRecv`) and its token (`recvTokOf`), over the bundle on those types' paths.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedNodeRecv
public import Proof.go_etcd_io.raft.v3.TracedFamilies
public import Spec.go_etcd_io.raft.v3.RawNode__Step
public import Spec.go_etcd_io.raft.v3.raft__Step
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import Spec.go_etcd_io.raft.v3.IsLocalMsg
public import Spec.go_etcd_io.raft.v3.IsResponseMsg
public import Spec.go_etcd_io.raft.v3.IsLocalMsgTarget
public import Proof.go_etcd_io.raft.v3.Protocol.Facts
public import Proof.go_etcd_io.raft.v3.LemmasP3bXw
public import Proof.go_etcd_io.raft.v3.InvNodeRun
public import Proof.go_etcd_io.raft.v3.TracedRaftStepPropBundle

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

section pure
variable [GooseExts]

/-- **The network types a traced node steps** (`node.Step`'s, in the harness): the replication and
election messages of a cluster with pre-vote and check-quorum off, no snapshot, no read-index, no
leader transfer. -/
def TrNetTy (t : w32) : Prop :=
  t = MsgApp ∨ t = MsgAppResp ∨ t = MsgVote ∨ t = MsgVoteResp ∨ t = MsgHeartbeat ∨ t = MsgHeartbeatResp

theorem TrNetTy.stepEndTy {t : w32} (h : TrNetTy t) : StepEndTy t := by
  unfold StepEndTy
  rcases h with h | h | h | h | h | h <;> simp [h]

/-- A traced network type is none of the listed others. -/
theorem TrNetTy.ne {t : w32} (h : TrNetTy t) {u : w32}
    (hu : u ≠ MsgApp ∧ u ≠ MsgAppResp ∧ u ≠ MsgVote ∧ u ≠ MsgVoteResp ∧ u ≠ MsgHeartbeat ∧
      u ≠ MsgHeartbeatResp) : t ≠ u := by
  intro e; subst e
  rcases h with h | h | h | h | h | h
  · exact hu.1 h
  · exact hu.2.1 h
  · exact hu.2.2.1 h
  · exact hu.2.2.2.1 h
  · exact hu.2.2.2.2.1 h
  · exact hu.2.2.2.2.2 h

end pure

/-- `TrNetTy.ne` at a constant: the six inequalities by `decide`. -/
macro "trnet_ne" h:term:max : tactic =>
  `(tactic| exact TrNetTy.ne $h ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩)

section traced
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The capability, open at a traced node.** -/
theorem rnTrace_some (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (s : NState) (γd : GName)
    (h : s.gh.tr = some γd) :
    rnTrace (GF := GF) γ r id c s ⊣⊢
      ⌜s.prevote = false ∧ c.learners = ∅⌝ ∗ r.[raft, go!"checkQuorum"] ↦□ false ∗
        TrNoSnap s.gh.tr s.logst ∗ ∃ b : Bool, trCapB s.gh.tr γ r id c b (fun C => SimIdle C s) := by
  unfold rnTrace
  generalize hx : s.gh.tr = x
  subst hx
  rw [h]
  exact .rfl

/-- **`RawNode.Step` at a traced node** (see the file header): `RawNode.Step.spec`'s triple for a
message of a traced network type, at a traced cluster, with the message's `isRaftMsg` (in place of
the untraced spec's `"#Hmsg"`, `"#Hxfer"`, `"#Hsnap"`, `"Hcred"`, which it implies or which are vacuous
for these types) and its token. The premises beyond the untraced spec's: the term ceiling below the
traced numbers' bound (the step's terms are at most the ceiling, `RNPv`), the receipts' fit, and a
cluster started from a bootstrap log (`γ.reBoot ≠ []`: the harness's, `StartNode` with its peers). -/
abbrev RawNode.Step.tracedTriple : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (ml : Loc) (st : MsgSt) (γd : GName),
  NetMsgOk id st → TrNetTy st.msg.Type' →
  uint.Z st.msg.Term' ≤ uint.Z rs.tc →
  rs.flw = false →
  γ.reTrace = some γd →
  uint.Z rs.tc + 1 < traceNumBound →
  receiptBound GF + γ.reBoot.length ≤ traceNumBound →
  γ.reBoot ≠ [] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs ∗
      "Hm" ∷ msgIn ml DFrac.discard st ∗
      "#Hraft" ∷ isRaftMsg γ id st ∗
      "Htok" ∷ recvTokOf γd st.msg st.ents st.ctx }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"Step")) (Val #ml))
  {{ (err : GoInterface) (t : w64), RET #err;
      "Hrn" ∷ ownRawNode γ rn id { rs with term := t } ∗
      "%Ht" ∷ ⌜uint.Z rs.term ≤ uint.Z t ∧ uint.Z t ≤ uint.Z rs.tc ∧
               uint.Z t ≤ max (uint.Z rs.term) (uint.Z st.msg.Term')⌝ }}

set_option hygiene false in
/-- A message `RawNode.Step` does not step: the node as it was (the capability included). -/
local macro "early_return_tr" e:term : tactic => `(tactic| (
  try wp_auto
  iapply HΦ $$ %$e %rs.term
  isplitl
  · iapply ownRawNode_intro_tr γ rn id { rs with term := rs.term } s cf fp rnv sv
      hprev steps Hwf Hin Hasync Hdlen Hunp Hsnap Hstok Htrm Hstor Hpvoff
      Hrs_out Hrs_unst Hrs_clb Hrnfl Hloan
      Hsdt Hrole Hphs $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs Hloanc Hsloc Hdur Hrntr
  ipureintro
  refine ⟨Int.le_refl _, by rw [Htrm, Hpvoff.2.1]; exact Hpvoff.2.2.1, ?_⟩
  omega))

/-- See `RawNode.Step.tracedTriple`. As `RawNode.Step.wp_proof` (the two guards, then `raft.Step`),
with `raft.Step.spec` at the resources the traced bundle gives (`hb`) in place of its untraced
instance; the capability comes back idle at the end state. -/
theorem RawNode.Step.traced
    (wp_IsResponseMsg : IsResponseMsg.spec (GF := GF) (hG := hG))
    (wp_IsLocalMsg : IsLocalMsg.spec (GF := GF) (hG := hG))
    (wp_IsLocalMsgTarget : IsLocalMsgTarget.spec (GF := GF) (hG := hG))
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG))
    (hb : stepBundle_traced.on (GF := GF) (hG := hG) (fun _ m => TrNetTy m.Type')) :
    RawNode.Step.tracedTriple (GF := GF) (hG := hG) := by
  intro γ rn id rs ml st γd Hok Hnt Hmtc Hflw HtrG Htcb Hfit Hboot
  rcases st with ⟨m, ents, sn, ctx, rsp⟩
  simp only at Hok Hnt Hmtc ⊢
  have Hok0 := Hok
  obtain ⟨Hty, -⟩ := Hok0
  have Hty0 : 0 ≤ sint.Z m.Type' := netStepTypes_nonneg Hty
  have HnS : m.Type' ≠ MsgSnap := by trnet_ne Hnt
  have HnP : m.Type' ≠ MsgProp := by trnet_ne Hnt
  have HnT : m.Type' ≠ MsgTimeoutNow := by trnet_ne Hnt
  have HnX : m.Type' ≠ MsgTransferLeader := by trnet_ne Hnt
  have HnR : m.Type' ≠ MsgReadIndex := by trnet_ne Hnt
  have HnPR : m.Type' ≠ MsgPreVoteResp := by trnet_ne Hnt
  have HnA : m.Type' ≠ MsgStorageAppendResp := by trnet_ne Hnt
  have HnAp : m.Type' ≠ MsgStorageApplyResp := by trnet_ne Hnt
  wp_start as H
  iNamed H
  iNamed Hrn
  ihave #HI := isInitialized_access $$ Hpkg
  iNamed HI
  wp_auto_lc 1
  -- `IsLocalMsg(m.Type) && !IsLocalMsgTarget(m.From)`
  wp_apply wp_GetType.1 ml _ _ _ _ $$ [$Hm] as Hm
  wp_apply wp_IsLocalMsg _ Hty0 as %b1 _
  wp_if_destruct
  all_goals try (wp_apply wp_GetFrom.1 ml _ _ _ _ $$ [$Hm] as Hm
                 wp_apply wp_IsLocalMsgTarget m.From'; wp_if_destruct)
  all_goals try early_return_tr errStepLocal
  -- `IsResponseMsg(m.Type) && !IsLocalMsgTarget(m.From) && trk.Progress[m.From] == nil`
  all_goals (wp_apply wp_GetType.1 ml _ _ _ _ $$ [$Hm] as Hm
             wp_apply wp_IsResponseMsg _ Hty0 as %b2 _; wp_if_destruct)
  all_goals try (wp_apply wp_GetFrom.1 ml _ _ _ _ $$ [$Hm] as Hm
                 wp_apply wp_IsLocalMsgTarget m.From'; wp_if_destruct)
  all_goals try (
    icases ownRaftPhysC_tracker_same cf rnv.raft' id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
    icases ownTrackerC_progress_map cf tv _ $$ Htrk with ⟨#Hprs, %Hdom, Htrk⟩
    try wp_auto
    wp_apply wp_GetFrom.1 ml _ _ _ _ $$ [$Hm] as Hm
    wp_apply wp_map_lookup1 go.uint64 (go.GoType.PointerType tracker.Progress.ty) _ _ m.From' _
      $$ Hprs with -
    ihave Hphys := Hback $$ %tv Htrkf Htrk
    wp_if_destruct)
  all_goals try early_return_tr errStepPeer
  -- `rn.raft.Step(m)`
  all_goals (
      try wp_auto
      icases ownStepGhost_bootCommit γ _ cf id s $$ Hghost with ⟨%Hbc0, Hghost⟩
      icases ownStepGhost_term0 γ _ cf id s $$ Hghost
        with ⟨%Hb1, Hghost⟩
      icases ownRaftPhysC_sn cf rnv.raft' id s $$ Hphys with ⟨%Hns0, Hphys⟩
      icases ownRaftPhysC_preFacts cf rnv.raft' id s (Hpvoff.guard rs.capplied rs.cfg (ds := ds)) $$ Hphys with ⟨%Hpf, Hphys⟩
      icases ownRaftPhysC_persistRel cf rnv.raft' id s $$ Hphys with ⟨%Hpr, Hphys⟩
      icases ownRaftPhysC_gh cf rnv.raft' id s $$ Hphys with ⟨%Hgh0, Hphys⟩
      have Hrel := fun h => Hpr.2 (ack_snap_sip Hloan Hgh0.1.2.1 h)
      icases ownRaftPhysC_applying cf rnv.raft' id s $$ Hphys with ⟨%Hac0, Hphys⟩
      icases ownStepGhost_dlv_terms γ _ cf id s rs.delivered
        (by have := uint_Z_nonneg s.logst.applying; rw [Hdlen]; omega) Hac0 $$ Hdeliv Hghost
        with ⟨%Hdag, Hghost⟩
      -- (slice 25n) the capability, open; the bundle's premises from the node's state
      have Htr : s.gh.tr = some γd := Hgtr.trans HtrG
      icases (rnTrace_some γ rnv.raft' id cf s γd Htr).1 $$ Hrntr with ⟨%Hscope, #Hcqf, #Hnosnap, %bt, Hcap⟩
      icases ownRaftPhysC_cq cf rnv.raft' id s $$ Hphys with ⟨#Hcq, Hphys⟩
      icombine Hcqf Hcq gives %Hcqe
      icases ownRaftPhysC_dom cf rnv.raft' id s $$ Hphys with ⟨%Hsub, Hphys⟩
      icases ownRaftPhysC_precand cf rnv.raft' id s $$ Hphys with ⟨%Hpcd, Hphys⟩
      icases isRaftMsg_trRecv γ id ⟨m, ents, sn, ctx, rsp⟩ $$ Hraft with ⟨#Hmc, %Htrok, -, %Hshape⟩
      have Hst1 : uint.Z s.term ≤ uint.Z rs.tc := by rw [Hpvoff.2.1]; exact Hpvoff.2.2.1
      ihave Hpre : (trCapB s.gh.tr γ rnv.raft' id cf bt (fun C => SimIdle C s) (fun _ => True) ∗
          (recvTokOf γd m ents ctx ∗
            □ (∀ ty : MsgType, ⌜mtypeOf m.Type' = some ty ∧ ty.traced = true⌝ -∗
              isMessageC γ (absMsg ty m ents ctx))) ∗
          TrNoSnap s.gh.tr s.logst : IProp GF) $$ [Hcap Htok]
      · iframe Hcap Htok Hmc Hnosnap
      imod hb γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩) cf rnv.raft' id s m ents sn ctx rsp γd
          (fun _ => True) bt Hnt Htr Hscope.1 Hcqe.symm Hnt.stepEndTy Hwf
          (fun h => by rcases h with h | h | h <;> exact absurd h (by trnet_ne Hnt))
          (fun h => absurd h (by trnet_ne Hnt))
          (fun ty hty htr => (Hok.2.1 (fun hu => by
              rcases hu with h | h | h | h | h <;> exact absurd h (by trnet_ne Hnt))).1)
          (by omega) (by omega) Htrok Hfit Hscope.2 Hsub
          (fun h => by have := Hpcd h; rw [Hscope.1] at this; cases this)
          (Hshape (by rw [HtrG]; rfl)) (fun _ => Hboot) $$ Hpre
        with ⟨%R, HG, Hgates, Hclose⟩
      imod rdCred_zero_upd (GF := GF) γ with Hcred0
      ihave Hcred : rdCred γ (if m.Type' = MsgReadIndex then 1 else 0) $$ [Hcred0]
      · rw [ite_eq_right HnR]; iexact Hcred0
      wp_apply Hok.raftStep Hpvoff Htrm Hmtc (fun h => absurd h HnT) Hb1 (Hrnfl.1 Hflw)
          (wp_raft_Step cf _ γ _ id s ml m ents ctx sn rsp R
            (fun s' => iprop(⌜OutTyStep s s'⌝ ∗ ∃ bt' : Bool, ⌜bt = true → bt' = true⌝ ∗
              trCapB s.gh.tr γ rnv.raft' id cf bt' (fun C => SimIdle C s') (stepLastEv (fun _ => True)))))
          Hwf
        (RNMode.pre_net Hpf (fun h => absurd h (by trnet_ne Hnt))) (fun _ => Hns0.1)
        (fun h => absurd h (by trnet_ne Hnt)) (fun h => absurd h (by trnet_ne Hnt))
        (fun h => absurd h (by trnet_ne Hnt)) (fun h => absurd h (by trnet_ne Hnt)) $$ [$Hphys $Hghost $Hlc1 Hm Hcred HG Hgates Hclose]
      · simp only [HnP, ↓reduceIte, named]
        isplitr
        · imodintro; iintro %h; exact absurd h.1 HnX
        isplitl [Hm]
        · isplitl [Hm]
          · iexact Hm
          isplitr
          · iempintro
          isplitr
          · ipureintro; intro h; first | exact h.elim | exact absurd h HnP
          isplitr
          · ipureintro; intro _; exact Hok.resps
          isplitr
          · ipureintro; intro h; first | exact h.elim | exact absurd h HnAp
          imodintro
          iintro %ty %Hty' %Hne
          iapply isRaftMsg_isMessage γ id ⟨m, ents, sn, ctx, rsp⟩ ty Hty' Hne $$ Hraft
        isplitl [Hcred]
        · iexact Hcred
        isplitr
        · imodintro; iintro %h; exact absurd h HnS
        iframe HG Hgates Hclose
      simp only [HnP]
      iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hcc, -, %Hfr, %Hxwf, %Htm, %Hresp,
        -, %Htrc, -, HG⟩
      icases ownRaftPhysC_sn _ rnv.raft' id s' $$ Hphys with ⟨%Hsn1, Hphys⟩
      have Hc := Href.commit_mono
      have Hmtc' : uint.Z m.Term' ≤ uint.Z s.gh.tc := by rw [← Hpvoff.2.1]; exact Hmtc
      have Htc0 := Hpvoff.2.2.1
      have e1 := Href.keep (by trnet_ne Hnt) (by trnet_ne Hnt) (fun h => absurd h (by trnet_ne Hnt)); subst e1
      have e2 := Hcc (fun h => absurd h (by trnet_ne Hnt)); subst c'
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ :=
        Hfr (by trnet_ne Hnt) (by trnet_ne Hnt) (by trnet_ne Hnt) (fun h => absurd h (by trnet_ne Hnt))
      have HfrX : NetFrame s { s' with gh := s.gh } ∧ s'.gh = { s.gh with xw := s'.gh.xw } :=
        ⟨⟨a1, a2, a3, a4, a5, a6, a7, rfl, a9, a10⟩, by rw [a8]⟩
      obtain ⟨⟨Ha, Hsn, Hu, Hpv, Hsd, Hsg, Hpre, -, Hfl', Hap'⟩, Hgx⟩ := HfrX
      simp only at Ha Hsn Hu Hpv Hsd Hsg Hpre Hfl' Hap'
      have Hsneq : s'.gh.sn = s.gh.sn := by rw [Hgx]
      have Htceq : s'.gh.tc = s.gh.tc := by rw [Hgx]
      obtain ⟨Ht1, -, Ht3, Hip4, -, Hpcs⟩ := Htm HnS
      have Ht3' : uint.Z s'.term ≤ max (uint.Z s.term) (uint.Z m.Term') := by
        have := Ht3 (by trnet_ne Hnt) HnPR HnT; omega
      have Hle : uint.Z s'.term ≤ uint.Z s.gh.tc := by
        have := Int.max_le.2 ⟨Htc0, Hmtc'⟩; omega
      have Hstok' : StepsOk s' rs.steps :=
        stepsOk_mono_le s s' _ Ht1 ⟨Hpv, logStoreRec_stored Hsd⟩ Hc Ha (Int.le_of_eq (congrArg _ Htceq.symm)) Hstok
      ihave #Hstr' : ackInv γ { rs with term := s'.term } s' $$ []
      · by_cases Happ : m.Type' = MsgApp
        · ihave #Hm' := isRaftMsg_isMessage γ id ⟨m, ents, sn, ctx, rsp⟩ .app
            (by show mtypeOf m.Type' = _; rw [Happ]; exact mtypeOf_MsgApp) (by decide) $$ Hraft
          rw [isMessage_absMsg_ctx γ .app m ents ctx (And.intro (by decide) (by decide))]
          ihave #Hents := isMessage_app_leadFull γ m ents $$ Hm'
          iapply ackInv_app γ rfl Hstok Ht1 Hpv Hsn (logStoreRec_stored Hsd) (Htrc Happ) Hrel Hpr.1
            $$ Hstrecs Hents
        · iapply ackInv_keep γ rfl Hstok Ht1 Hpv Hsn (logStoreRec_stored Hsd) (Hip4 Happ) $$ Hstrecs
      ihave #Hsloc' : snapLocOk γ id s'.logst.snap $$ []
      · rw [Hsn]; iexact Hsloc
      -- (slice 25n) the capability back, idle at the end state
      have Htr' : s'.gh.tr = some γd := by rw [Hgx]; exact Htr
      ihave Hrntr : rnTrace γ rnv.raft' id cf s' $$ [HG]
      · iapply (rnTrace_some γ rnv.raft' id cf s' γd Htr').2
        isplitr
        · ipureintro; exact ⟨Hpre.trans Hscope.1, Hscope.2⟩
        isplitr
        · iexact Hcqf
        isplitr
        · iapply trNoSnap_logst s.gh.tr s'.gh.tr s.logst s'.logst (by rw [Htr', Htr]) Hpv.symm Hsg.symm
            $$ Hnosnap
        icases HG with ⟨-, %bt', -, HG⟩
        iexists bt'
        rw [show s'.gh.tr = s.gh.tr by rw [Htr', Htr]]
        iapply trCapB_monoΛ _ γ rnv.raft' id cf bt' _ _ _ (fun _ _ => trivial) $$ HG
      have HlO : LoanOk { rs with term := s'.term } s' := by
        have h := Hloan.step_gxw (b := false) s'.term Hgx
          (fun _ => ⟨.inl Hsn, Hfl', logStoreRec_stored Hsd, Hu, Ha, Hc⟩) ⟨Hsn, Hc⟩
        simpa only [Bool.or_false] using h
      wp_auto
      iapply HΦ $$ %err %s'.term
      isplitl
      · iapply ownRawNode_intro_tr γ rn id { rs with term := s'.term } s' cf fp
            rnv sv hprev steps Hwf' Hin
            Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp)
            (fun h => by rw [Hsn]; exact Hsnap h)
            Hstok' rfl (by rw [Hsg]; exact ⟨Hstor.1, by rw [Hsn1.2, Hsneq, ← Hns0.2]; exact Hstor.2⟩)
            (Hpvoff.step_gxw rfl rfl Hpre Hgx Hle Hpcs (fun h => absurd h (by trnet_ne Hnt)))
            (by rw [Hgx]; exact Hrs_out) (by rw [Hgx]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
            (RNFl.keep Hrnfl Hfl' Hap' Ha)
            HlO
            (Hsdt.ofRec Hsn Hsd) Hrole
            (Hphs.keep rfl rfl rfl (HsLe.of_step Href.voteLe Hc) Hsn (ip_of_step Hip4 Htrc))
            (by rw [Hgx]; exact Hgtr) (by rw [Hgx]; exact Hglq) $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr' Hloanc Hsloc' [Hdur] Hrntr
        · iapply durTie_congr γ (rs := rs) (s := s) (by rfl) (by rfl) Hsn Hpv (logStoreRec_stored Hsd) $$ Hdur
      ipureintro
      rw [Htrm]
      exact ⟨Ht1, by rw [Hpvoff.2.1]; exact Hle, Ht3'⟩)

set_option hygiene false in
/-- A premise of `Step` about another message type, for a proposal (`Hty` in context). -/
local macro "prop_ne" : tactic => `(tactic| (intro Hc; rw [Hty] at Hc; simp [MsgHup, MsgVote,
  MsgVoteResp, MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp,MsgCheckQuorum,
  MsgSnap, MsgBeat, MsgStorageAppendResp, MsgStorageApplyResp, MsgProp, MsgReadIndex,
  MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hc))

/-- **The paths of a traced node's proposal**: a `MsgProp` of a non-empty batch of normal entries, in a
cluster started from a bootstrap log, at any role (a leader appends it, `PropLead`; a follower forwards
it; a candidate drops it). The assembly's premises for `MsgProp` (`notes/decisions.md`, "Q8 stage 1
(slice 24a)"). -/
def PropAny (γ : RaftNames) (ents : List EntryM) (_s : NState) (m : MessageM) : Prop :=
  m.Type' = MsgProp ∧ ents ≠ [] ∧ (∀ e ∈ ents, e.Type' = EntryNormal) ∧ γ.reBoot ≠ []

/-- **`r.Step(m)` on a proposal at a traced node** (`node.run`'s `propc` arm: `node.Propose`'s
proposal, or one a follower forwarded, which `node.Step` hands to `propc`; `RawNode.Propose` is not on
the node API's path): `wp_rn_raft_Step_prop`'s triple at a traced cluster, over the traced bundle on
`PropAny`. Beyond the untraced premises: the batch's entries normal (the harness proposes no
configuration change, P3), the bounds, the bootstrap log. -/
theorem wp_rn_raft_Step_prop_traced (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (hb : stepBundle_traced.onG (GF := GF) (hG := hG) PropAny)
    (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : Loc) (ml : Loc) (st : MsgSt) (γd : GName)
    (Hty : st.msg.Type' = MsgProp) (Hfr : st.msg.From' = id) (Hrs : st.resps = [])
    (HtrG : γ.reTrace = some γd) (Hnorm : ∀ e ∈ st.ents, e.Type' = EntryNormal)
    (Htcb : uint.Z rs.tc + 1 < traceNumBound) (Hfit : receiptBound GF + γ.reBoot.length ≤ traceNumBound)
    (Hboot : γ.reBoot ≠ []) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        ownRawNode γ rn id rs ∗ rn.[RawNode, go!"raft"] ↦□ r ∗
        msgIn ml (DFrac.own 1) st ∗
        isMessage γ (absMsg .propose st.msg st.ents) ∗
        ([∗list] e ∈ st.ents, entTk γ e) ∗ £ 1 }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface), RET #err; ownRawNode γ rn id rs ∗ stepErr err }} := by
  rcases st with ⟨m, ents, sn, ctx, rsp⟩
  simp only at Hty Hfr Hrs Hnorm ⊢
  iintro %Φ ⟨#Hpkg, Hrn, #Hr, Hmin, #Hm, Htk, Hlc⟩ HΦ
  ihave #Hinit := isInitialized_access $$ Hpkg
  unfold isInitialized
  icases Hinit with ⟨%_, %_, %_, %_, %errPropDropped, %_, %_, %_, %_, %_, #Hinit⟩
  iNamed Hinit
  iNamed Hrn
  ihave #Hr' := rawNodeOwn_raft rn rnv $$ Hrn
  icombine Hr Hr' gives %Heq
  subst Heq
  icases ownRaftPhysC_sn cf rnv.raft' id s $$ Hphys with ⟨%Hns0, Hphys⟩
  ihave %Hpm := isMessage_propose_pure γ m ents $$ Hm
  obtain ⟨Hterm, Hne, Hlen⟩ := Hpm
  ihave #Hed : iprop([∗list] e ∈ ents, propData γ e) $$ []
  · iunfold isMessage at Hm
    simp only [absMsg, absMsgFrom]
    icases Hm with ⟨-, #Hed⟩
    iexact Hed
  icases propData_ccEnts γ ents $$ Hed with ⟨%cs, #Hcc⟩
  imod rdCred_zero_upd (GF := GF) γ with Hcr
  icases ownRaftPhysC_preFacts cf rnv.raft' id s (Hpvoff.guard rs.capplied rs.cfg (ds := ds)) $$ Hphys with ⟨%Hpf, Hphys⟩
  -- (slice 25n) the capability, open; the bundle's premises from the node's state
  have Htr : s.gh.tr = some γd := Hgtr.trans HtrG
  icases (rnTrace_some γ rnv.raft' id cf s γd Htr).1 $$ Hrntr with ⟨%Hscope, #Hcqf, #Hnosnap, %bt, Hcap⟩
  icases ownRaftPhysC_cq cf rnv.raft' id s $$ Hphys with ⟨#Hcq, Hphys⟩
  icombine Hcqf Hcq gives %Hcqe
  icases ownRaftPhysC_dom cf rnv.raft' id s $$ Hphys with ⟨%Hsub, Hphys⟩
  icases ownRaftPhysC_precand cf rnv.raft' id s $$ Hphys with ⟨%Hpcd, Hphys⟩
  have Hst1 : uint.Z s.term ≤ uint.Z rs.tc := by rw [Hpvoff.2.1]; exact Hpvoff.2.2.1
  have Hpt : mtypeOf m.Type' = some .propose := by rw [Hty]; rfl
  have Hpu : ∀ ty, mtypeOf m.Type' = some ty → ty.traced = false := by
    intro ty h; rw [Hpt] at h; cases h; rfl
  ihave Htok : recvTokOf γd m ents ctx $$ []
  · iunfold recvTokOf
    iintro %ty %h
    exact absurd h.2 (by rw [Hpu ty h.1]; simp)
  ihave Hpre : (trCapB s.gh.tr γ rnv.raft' id cf bt (fun C => SimIdle C s) (fun _ => True) ∗
      (recvTokOf γd m ents ctx ∗
        □ (∀ ty : MsgType, ⌜mtypeOf m.Type' = some ty ∧ ty.traced = true⌝ -∗
          isMessageC γ (absMsg ty m ents ctx))) ∗
      TrNoSnap s.gh.tr s.logst : IProp GF) $$ [Hcap Htok]
  · iframe Hcap Htok Hnosnap
    imodintro
    iintro %ty %h
    exact absurd h.2 (by rw [Hpu ty h.1]; simp)
  imod hb γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩) cf rnv.raft' id s m ents sn ctx rsp γd
      (fun _ => True) bt ⟨Hty, Hne, Hnorm, Hboot⟩ Htr Hscope.1 Hcqe.symm
      (by unfold StepEndTy; simp [Hty]) Hwf (fun _ => Hterm) (fun h => absurd h (by prop_ne))
      (fun ty h1 h2 => by rw [Hpu ty h1] at h2; cases h2)
      (by omega) (by rw [Hterm]; unfold traceNumBound; decide)
      (fun ty h => MsgTrOk.of_untraced γ (by
        have := Hpu ty h
        rw [Hpt] at h; cases h
        simpa [absMsg, absMsgFrom, Msg.mkV] using this))
      Hfit Hscope.2 Hsub
      (fun h => by have := Hpcd h; rw [Hscope.1] at this; cases this)
      ⟨fun h => absurd h (by prop_ne), fun h => absurd h (by prop_ne),
        fun h => by rcases h with h | h | h <;> exact absurd h (by prop_ne),
        fun ty h1 h2 => by rw [Hpu ty h1] at h2; cases h2⟩
      (fun _ => Hboot) $$ Hpre
    with ⟨%R, HG, Hgates, Hclose⟩
  wp_apply wp_raft_Step cf _ γ _ id s ml m ents ctx sn rsp R
    (fun s' => iprop(⌜OutTyStep s s'⌝ ∗ ∃ bt' : Bool, ⌜bt = true → bt' = true⌝ ∗
      trCapB s.gh.tr γ rnv.raft' id cf bt' (fun C => SimIdle C s') (stepLastEv (fun _ => True))))
    (by simp only [StepMsg, stepMsgTypes]; rw [Hty]; simp [MsgProp])
    (by prop_ne) (by prop_ne)
    (by prop_ne) (by prop_ne)
    (by prop_ne) (by prop_ne)
    (by prop_ne) (by prop_ne)
    (by prop_ne) (by prop_ne)
    (by prop_ne)
    (fun _ => ⟨Hterm, .inr Hfr⟩) (by prop_ne) (by prop_ne) (by prop_ne) (by prop_ne)
    (RestMsgOk.of_ne ⟨by prop_ne, by prop_ne, by prop_ne, by prop_ne, by prop_ne⟩) Hwf
    (GMode.Pre.of_facts Hpf (by prop_ne) (by prop_ne)) (fun h => absurd h (by prop_ne))
    (fun h => absurd h (by prop_ne)) (fun h => absurd h (by prop_ne)) (fun h => absurd h (by prop_ne))
    (fun _ _ e he hc => by
      have := Hnorm e he
      unfold IsConfEnt at hc; rw [this] at hc
      rcases hc with hc | hc <;> simp [EntryNormal] at hc)
    $$ [$Hphys $Hghost $Hlc Hmin Htk Hcr HG Hgates Hclose]
  · rw [Hty]
    simp only [ite_true]
    isplitr
    · imodintro
      iintro %h
      exact absurd h.1 (by simp [MsgProp, MsgTransferLeader])
    isplitl [Hmin Htk]
    · simp only [named]
      isplitl [Hmin]
      · iexact Hmin
      isplitl [Htk]
      · isplitr
        · iexists cs
          iexact Hcc
        iexact Htk
      isplitr
      · ipureintro
        intro _
        exact ⟨Hne, Hlen⟩
      isplitr
      · ipureintro; intro _; exact Hrs
      isplitr
      · ipureintro
        intro Hc
        simp [MsgProp, MsgStorageApplyResp] at Hc
      · imodintro
        iintro %ty %Hty2 _
        rw [show mtypeOf MsgProp = some .propose from rfl] at Hty2
        cases Hty2
        iapply isMessage_ctx_intro _ .propose _ _ _ ⟨nofun, nofun⟩
        iexact Hm
    isplitl [Hcr]
    · simp [MsgProp, MsgReadIndex]; iexact Hcr
    isplitr
    · imodintro
      iintro %Hc
      simp [MsgProp, MsgSnap] at Hc
    iframe HG Hgates Hclose
  iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hcc, %Hloc, %_, %_, %Htm, %_, -, -, Herr, HG⟩
  icases ownRaftPhysC_sn _ rnv.raft' id s' $$ Hphys with ⟨%Hsn1, Hphys⟩
  ihave #Hstep : stepErr err $$ [Herr]
  · unfold stepErr
    icases Herr with (%Hnil | ⟨-, #Hpd⟩)
    · ileft; ipureintro; exact Hnil
    · iright
      unfold errProposalDropped
      icombine Hpd ErrPropDropped gives %Heq
      subst Heq
      iframe Hpd
      ipureintro; exact HErrPropDropped
  have Hc := Href.commit_mono
  have e1 := Href.keep (by prop_ne) (by prop_ne) (fun h => absurd h (by prop_ne)); subst e1
  have e2 := Hcc (by prop_ne); subst c'
  obtain ⟨Hfr', Hap, -⟩ := Hloc.1 (fun h => absurd h (by prop_ne)) (.inl Hty)
  have Hap' := Hap (fun Hc => by rw [Hty] at Hc; simp [MsgProp, MsgStorageApplyResp] at Hc)
  ihave #Hstr' := ackInv_keep (rs' := rs) γ rfl Hstok (by rw [Hfr'.1]; exact Int.le_refl _)
    Hfr'.2.2.2.2.1 Hfr'.2.2.2.1 (logStoreRec_stored Hfr'.2.2.2.2.2.1) Hfr'.2.1 $$ Hstrecs
  ihave #Hsloc' := snapLocOk_keep γ id (.inl Hfr'.2.2.2.1) $$ Hsloc
  -- (slice 25n) the capability back, idle at the end state
  have Hgh' : s'.gh = s.gh := Hfr'.2.2.2.2.2.2.2.2.1
  have Htr' : s'.gh.tr = some γd := by rw [Hgh']; exact Htr
  ihave Hrntr : rnTrace γ rnv.raft' id cf s' $$ [HG]
  · iapply (rnTrace_some γ rnv.raft' id cf s' γd Htr').2
    isplitr
    · ipureintro; exact ⟨Hfr'.2.2.2.2.2.2.2.1.trans Hscope.1, Hscope.2⟩
    isplitr
    · iexact Hcqf
    isplitr
    · iapply trNoSnap_logst s.gh.tr s'.gh.tr s.logst s'.logst (by rw [Htr', Htr])
        Hfr'.2.2.2.2.1.symm Hfr'.2.2.2.2.2.2.1.symm $$ Hnosnap
    icases HG with ⟨-, %bt', -, HG⟩
    iexists bt'
    rw [show s'.gh.tr = s.gh.tr by rw [Htr', Htr]]
    iapply trCapB_monoΛ _ γ rnv.raft' id cf bt' _ _ _ (fun _ _ => trivial) $$ HG
  iapply HΦ
  isplitl
  rotate_left
  · iexact Hstep
  iapply ownRawNode_intro_tr γ rn id rs s' cf fp rnv sv hprev steps Hwf' Hin Hasync
    (by rw [Hap']; exact Hdlen) (by rw [Hfr'.2.2.1]; exact Hunp)
    (by rw [Hfr'.2.2.2.1]; exact Hsnap)
    (stepsOk_mono s s' _ Hfr'.1 ⟨Hfr'.2.2.2.2.1, (logStoreRec_stored Hfr'.2.2.2.2.2.1)⟩ Hc Hap'
      (tc_le_of_gh Hfr'.2.2.2.2.2.2.2.2.1) Hstok)
    (by rw [Hfr'.1]; exact Htrm)
    (by rw [Hfr'.2.2.2.2.2.2.1]
        exact ⟨Hstor.1, by rw [Hsn1.2, Hfr'.2.2.2.2.2.2.2.2.1, ← Hns0.2]; exact Hstor.2⟩)
    (Hpvoff.keep rfl rfl Hfr'.2.2.2.2.2.2.2.1 Hfr'.2.2.2.2.2.2.2.2.1 Hfr'.1 Hfr'.2.2.2.2.2.2.2.2.2.1
      Hfr'.2.2.2.1 (PreGuardF.step (Htm (by prop_ne))))
    (by rw [Hfr'.2.2.2.2.2.2.2.2.1]; exact Hrs_out) (by rw [Hfr'.2.2.2.2.2.2.2.2.1]; exact Hrs_unst)
    (Int.le_trans Hrs_clb Hc)
    (RNFl.keep Hrnfl Hfr'.2.2.2.2.2.2.2.2.2.2.1 Hfr'.2.2.2.2.2.2.2.2.2.2.2 Hap')
    (Hloan.keep Hfr'.2.2.2.2.2.2.2.2.1 Hfr'.2.2.2.1 Hfr'.2.2.2.2.2.2.2.2.2.2.1 (logStoreRec_stored Hfr'.2.2.2.2.2.1)
      Hfr'.2.2.1 Hap' Hc)
    (Hsdt.ofRec Hfr'.2.2.2.1 Hfr'.2.2.2.2.2.1) Hrole
    (Hphs.keep rfl rfl rfl (HsLe.of_step Href.voteLe Hc) Hfr'.2.2.2.1 (.inl Hfr'.2.1))
    (by rw [LocalFrame.ns Hfr']; exact Hgtr) (by rw [LocalFrame.ns Hfr']; exact Hglq) $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr' Hloanc Hsloc' [Hdur] Hrntr
  · iapply durTie_congr γ (rs := rs) (s := s) (by rfl) (by rfl) Hfr'.2.2.2.1 Hfr'.2.2.2.2.1 (logStoreRec_stored Hfr'.2.2.2.2.2.1) $$ Hdur

/-- **`RawNode.Tick` at a traced node** (2026-11-11, slice 26n): `RawNode.Tick.spec`'s triple at a traced
cluster (`γ.reTrace = some γd`) in place of its premise `γ.reTrace = none`. The premises beyond the
untraced spec's: the term ceiling below the traced numbers' bound (the tick's campaign is at most the
ceiling, as `RawNode.Step.tracedTriple`'s), the receipts' fit. -/
abbrev RawNode.Tick.tracedTriple : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (γd : GName),
  uint.Z rs.term + 1 ≤ uint.Z rs.tc →
  rs.flw = false →
  γ.reTrace = some γd →
  uint.Z rs.tc + 1 < traceNumBound →
  receiptBound GF + γ.reBoot.length ≤ traceNumBound →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"Tick")) (Val #()))
  {{ (t : w64), RET #();
      "Hrn" ∷ ownRawNode γ rn id { rs with term := t } ∗
      "%Ht" ∷ ⌜uint.Z rs.term ≤ uint.Z t ∧ uint.Z t ≤ uint.Z rs.term + 1⌝ }}

/-- See `RawNode.Tick.tracedTriple`. As `RawNode.Tick.wp_proof`, with the ticks' traced instances
(`raft.tickElection.traced`, at any role since Q25 (a): `r.tick` is either function whatever the role,
`TickFnOk`; `raft.tickHeartbeat.traced`) at the capability `rnTrace` holds; the capability comes back
idle at the end state. -/
theorem RawNode.Tick.traced
    (wp_tickElection : raft.tickElection.spec (GF := GF) (hG := hG))
    (wp_tickHeartbeat : raft.tickHeartbeat.spec (GF := GF) (hG := hG)) :
    RawNode.Tick.tracedTriple (GF := GF) (hG := hG) := by
  have wp_tickElection := raft.tickElection.traced wp_tickElection
  have wp_tickHeartbeat := raft.tickHeartbeat.traced wp_tickHeartbeat
  intro γ rn id rs γd Hterm Hflw HtrG Htcb Hfit
  wp_start as H
  iNamed H
  iNamed Hrn
  wp_auto
  have Htc1 : uint.Z s.term + 1 ≤ uint.Z s.gh.tc := by rw [← Htrm, ← Hpvoff.2.1]; exact Hterm
  have HT : uint.Z s.term + 1 < traceNumBound := by rw [← Htrm]; omega
  wp_apply raft.wp_load_tickC cf rnv.raft' id s Hwf.2 $$ Hphys as %f ⟨Hphys, %Hf⟩
  icases ownRaftPhysC_preFacts cf rnv.raft' id s (Hpvoff.guard rs.capplied rs.cfg (ds := ds)) $$ Hphys with ⟨%Hpf, Hphys⟩
  icases ownRaftPhysC_sn cf rnv.raft' id s $$ Hphys with ⟨%Hns0, Hphys⟩
  -- the capability, open; the ticks' premises from the node's state
  have Htr : s.gh.tr = some γd := Hgtr.trans HtrG
  icases (rnTrace_some γ rnv.raft' id cf s γd Htr).1 $$ Hrntr with ⟨%Hscope, #Hcqf, #Hnosnap, %bt, Hcap⟩
  icases ownRaftPhysC_cq cf rnv.raft' id s $$ Hphys with ⟨#Hcq, Hphys⟩
  icombine Hcqf Hcq gives %Hcqe
  rcases Hf with rfl | rfl
  all_goals first
    | wp_apply wp_tickElection cf _ γ rnv.raft' id s γd (fun _ => True) bt Hwf Hpf.1 (Hrnfl.1 Hflw)
        Htr Hscope.1 Hcqe.symm HT Hfit Hscope.2
        $$ [$Hphys $Hghost $Hcap $Hnosnap] as %s' ⟨Hphys, Hghost, %Hwf', %Hcv, %Htk, -, Hcap⟩
    | wp_apply wp_tickHeartbeat cf _ γ rnv.raft' id s γd (fun _ => True) bt Hwf Hpf.1
        Htr Hscope.1 Hcqe.symm HT Hfit Hscope.2
        $$ [$Hphys $Hghost $Hcap $Hnosnap] as %s' ⟨Hphys, Hghost, %Hwf', %Hcv, %Htk, -, Hcap⟩
  all_goals (
    have Hc := Hcv.1
    obtain ⟨⟨Ha, Hsn, Hu, Hpv, Hsd, Hsg, Hpre, Hgh, Hfl', Hap'⟩, Ht1, Ht2, Hip4, Htpc, Hgd, Hsrb⟩ := Htk
    icases ownRaftPhysC_sn cf rnv.raft' id s' $$ Hphys with ⟨%Hsn1, Hphys⟩
    ihave #Hstr' := ackInv_keep (rs' := rs) γ rfl Hstok Ht1 Hpv Hsn (logStoreRec_stored Hsd) Hip4 $$ Hstrecs
    -- the capability back, idle at the end state
    have Htr' : s'.gh.tr = some γd := by rw [Hgh]; exact Htr
    ihave Hrntr : rnTrace γ rnv.raft' id cf s' $$ [Hcap]
    · iapply (rnTrace_some γ rnv.raft' id cf s' γd Htr').2
      isplitr
      · ipureintro; exact ⟨Hpre.trans Hscope.1, Hscope.2⟩
      isplitr
      · iexact Hcqf
      isplitr
      · iapply trNoSnap_logst s.gh.tr s'.gh.tr s.logst s'.logst (by rw [Htr', Htr]) Hpv.symm Hsg.symm
          $$ Hnosnap
      icases Hcap with ⟨%bt', -, Hcap⟩
      iexists bt'
      rw [show s'.gh.tr = s.gh.tr by rw [Htr', Htr]]
      iapply trCapB_monoΛ _ γ rnv.raft' id cf bt' _ _ _ (fun _ _ => trivial) $$ Hcap
    iapply HΦ $$ %s'.term
    isplitl
    ihave #Hsloc' := snapLocOk_keep γ id (.inl Hsn) $$ Hsloc
    · iapply ownRawNode_intro_tr γ rn id { rs with term := s'.term } s' cf fp rnv sv hprev steps
        Hwf' Hin
        Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp) (by rw [Hsn]; exact Hsnap)
        (stepsOk_mono_le s s' _ Ht1 ⟨Hpv, (logStoreRec_stored Hsd)⟩ Hc Ha (tc_le_of_gh Hgh) Hstok) rfl
        (by rw [Hsg]; exact ⟨Hstor.1, by rw [Hsn1.2, Hgh, ← Hns0.2]; exact Hstor.2⟩)
        ⟨fun h => Hgd fp (Hpvoff.1 h), by rw [Hgh]; exact Hpvoff.2.1,
          by rw [Hgh]; omega, fun hp => by rw [Hgh, Htpc hp]; exact Htc1, Hpvoff.2.2.2.2.step Hsrb⟩
        (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
        (RNFl.keep Hrnfl Hfl' Hap' Ha) (Hloan.keep Hgh Hsn Hfl' (logStoreRec_stored Hsd) Hu Ha Hc)
        (Hsdt.ofRec Hsn Hsd) Hrole
        (Hphs.keep rfl rfl rfl (HsLe.of_step Hcv.2 Hc) Hsn (.inl Hip4))
        (by rw [Hgh]; exact Hgtr) (by rw [Hgh]; exact Hglq)
        $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr' Hloanc Hsloc' [Hdur] Hrntr
      · iapply durTie_congr γ (rs := rs) (s := s) (by rfl) (by rfl) Hsn Hpv (logStoreRec_stored Hsd) $$ Hdur
    ipureintro
    rw [Htrm]
    exact ⟨Ht1, Ht2⟩)

end traced

end EtcdGrove
end Perennial
