/-
Lean-first (no Rocq counterpart). **Step 4 of the trace-check design (2026-11-12): the lemmas of the
gated `node.run`** (`node__run_gated.lean`, `node.run.gated_of`; `notes/trace-check-design.md`, "Step 4
(2026-11-12): the statements"). Raft-internal (not on `etc/api/raft.txt`).

Each callee `run` calls gets a triple **for both modes**: its untraced triple at an untraced node (the
one today's `node.run.wp_proof` calls), its traced triple at a traced node, with the traced premises
gated (`γ.reTrace ≠ none → …`), so that `run`'s arms read the same in both modes:

- `termLB_rb`: a term within the budget is at most `receiptBound GF` (the ceiling's bound);
- `ownRawNode_trNoLoan`: at a traced node nothing is lent (`rs.slent = none`: a lent snapshot would be the
  log's boundary, past `0`, which `TrNoSnap` refutes) and the cluster has a bootstrap log;
- `isCommitted_trNoConf`: G3 (a) over a committed log (route (A) of the design's step-4 section);
- `wp_rn_raft_Step_prop_g`: the `propc` arm's step.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRunSpecs
public import Proof.go_etcd_io.raft.v3.TracedRawNode
public import Proof.go_etcd_io.raft.v3.TracedRaftStepBundle
public import Proof.go_etcd_io.raft.v3.TracedConfExcl
public import Proof.go_etcd_io.raft.v3.TracedReady
public import Proof.go_etcd_io.raft.v3.InvNodeRun
public import Proof.go_etcd_io.raft.v3.InvNodeRunHup
public import Proof.go_etcd_io.raft.v3.Protocol.SnapCertDyn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A term within the budget is at most the receipts' bound** (`budgetInv`: the bound `M` is at most
one past the receipts spent, which are below `receiptBound GF`): the term ceiling's bound at a traced
node, with `RunTracedOk`'s `receiptBound GF + 2 ≤ traceNumBound`. -/
theorem termLB_rb (bud : BudgetNames) (t : w64) (E : CoPset) (HE : ↑budgetN ⊆ E) :
    ⊢ inv budgetN (budgetInv (GF := GF) bud) -∗ termLB bud t ={E}=∗ ⌜uint.nat t ≤ receiptBound GF⌝ := by
  iintro #Hinv #Hlb
  iinv Hinv with >Hi Hclose
  unfold budgetInv
  icases Hi with ⟨%M, %k, HM, Hk, %Hb⟩
  unfold termLB
  ihave %Hle := monoNatLbOwn_valid bud.bound 1 M (uint.nat t) $$ HM Hlb
  imod receipt_snapshot k $$ Hk with ⟨Hk, #Hp⟩
  ihave %Hkl := preceipt_lt k $$ Hp
  imod Hclose $$ [HM Hk] with -
  · inext; iexists M, k; iframe HM Hk; ipureintro; exact Hb
  imodintro
  ipureintro
  unfold receiptBound
  omega

/-- **At a traced node nothing is lent, and the cluster has a bootstrap log** (`ownRawNode_trNoLoan`,
the design's step-4 lemma): a lent snapshot (`LoanOk`) is pending or past a pending one, so the log has a
snapshot, which is its boundary (`ownRaftLog_snap_facts`), past index `0`, which `TrNoSnap` refutes
(`trNoSnap_prev0`); the bootstrap log from the capability (`trCapB_reBoot`). -/
theorem ownRawNode_trNoLoan (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (γd : GName)
    (HtrG : γ.reTrace = some γd) :
    ownRawNode (GF := GF) γ rn id rs ⊢
      |={⊤}=> (⌜rs.slent = none ∧ γ.reBoot ≠ []⌝ ∗ ownRawNode γ rn id rs) := by
  iintro H
  iNamed H
  have Htr : s.gh.tr = some γd := Hgtr.trans HtrG
  icases (rnTrace_some γ rnv.raft' id cf rs.delivered s γd Htr).1 $$ Hrntr with
    ⟨%Hscope, %Hpure, #Hcqf, #Hnosnap, %bt, %Hbt, Hcap⟩
  icases trCapB_reBoot Htr γ rnv.raft' id cf bt _ _ $$ Hcap with ⟨%Hboot, Hcap⟩
  imod trNoSnap_prev0 s.gh.tr s.logst (by rw [Htr]; simp) $$ Hnosnap with %Hprev0
  icases ownRaftPhysC_log_same cf rnv.raft' id s $$ Hphys with ⟨Hlog, Hback⟩
  icases ownRaftLog_snap_facts _ _ $$ Hlog with ⟨%Hsf, Hlog⟩
  ihave Hphys := Hback $$ Hlog
  have Hsl : rs.slent = none := by
    cases h : rs.slent with
    | none => rfl
    | some l =>
      exfalso
      obtain ⟨-, Hsn, -⟩ := Hloan.2.2.1 l h
      obtain ⟨sid, hsid⟩ : ∃ sid, s.logst.snap = some sid := by
        rcases Hsn with h1 | ⟨s2, h2, -⟩
        · exact ⟨_, h1⟩
        · exact ⟨_, h2⟩
      obtain ⟨hp, -, hpos⟩ := Hsf.2.2.2 sid hsid
      rw [← hp] at hpos
      omega
  ihave Hrntr : rnTrace γ rnv.raft' id cf rs.delivered s $$ [Hcap]
  · iapply (rnTrace_some γ rnv.raft' id cf rs.delivered s γd Htr).2
    iframe Hcqf Hnosnap
    isplitr
    · ipureintro; exact Hscope
    isplitr
    · ipureintro; exact Hpure
    iexists bt
    iframe Hcap
    ipureintro; exact Hbt
  imodintro
  isplitr
  · ipureintro; exact ⟨Hsl, Hboot⟩
  iapply ownRawNode_intro_tr γ rn id rs s cf fp rnv sv hprev steps Hwf Hin Hasync Hdlen Hunp Hsnap
    Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl Hloan
    Hsdt Hrole Hphs $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs Hloanc Hsloc Hdur Hrntr

/-- **G3 (a) over a committed log** (`isCommitted_trNoConf`, route (A) of the design's step-4 section):
at a traced cluster a committed log's conf entries lie within the bootstrap log: the committed log is
the bootstrap log's prefix, or a log with records (`isCommitted_recs`), whose conf entries are at most
at index `|γ.reBoot|` (`logRecs_trNoConf`, base `0`). -/
theorem isCommitted_trNoConf (γ : RaftNames) (E : CoPset) (L : List EntryM) (htr : γ.reTrace ≠ none)
    (HE : ↑(raftLogN γ) ⊆ E) :
    ⊢ raftCommitInv (GF := GF) γ -∗ isCommitted γ L ={E}=∗
      ⌜∀ (k : Nat) (e : EntryM), L[k]? = some e → IsConfEnt e → k < γ.reBoot.length⌝ := by
  iintro #Hinv #HL
  imod isCommitted_recs γ E L HE $$ Hinv HL with HR
  unfold committedRecs
  icases HR with (%Hb | ⟨%Hwf, #Hr⟩)
  · imodintro
    ipureintro
    intro k e hk _
    have h1 := (List.getElem?_eq_some_iff.mp hk).1
    have h2 := Hb.length_le
    omega
  · ihave %H := logRecs_trNoConf γ base0 L htr Hwf $$ Hr
    imodintro
    ipureintro
    intro k e hk hc
    have := H k e hk hc
    have h0 : uint.Z base0.index' = 0 := rfl
    omega

/-- **`r.Step(m)` on a proposal, in both modes** (`node.run`'s `propc` arm): `wp_rn_raft_Step_prop` at
an untraced node, `wp_rn_raft_Step_prop_traced` at a traced one (its bundle on the proposal's paths with
the node's `StepNodeOk`, from the assembly, `stepBundle_traced.onG_of_statement`; the bootstrap log from
`ownRawNode_trNoLoan`), whose premises are gated: the batch's entries normal, the term ceiling's bound,
the receipts' fit. -/
theorem wp_rn_raft_Step_prop_g (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (hb : stepBundle_traced.statement (GF := GF) (hG := hG))
    (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : Loc) (ml : Loc) (st : MsgSt)
    (Hty : st.msg.Type' = MsgProp) (Hfr : st.msg.From' = id) (Hrs : st.resps = [])
    (Htr : γ.reTrace ≠ none → (∀ e ∈ st.ents, e.Type' = EntryNormal) ∧
      uint.Z rs.tc + 1 < traceNumBound ∧ traceReadyFits GF γ) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        ownRawNode γ rn id rs ∗ rn.[RawNode, go!"raft"] ↦□ r ∗
        msgIn ml (DFrac.own 1) st ∗
        isMessage γ (absMsg .propose st.msg st.ents) ∗
        ([∗list] e ∈ st.ents, entTk γ e) ∗ £ 1 }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface), RET #err; ownRawNode γ rn id rs ∗ stepErr err }} := by
  cases HtrG : γ.reTrace with
  | none => exact wp_rn_raft_Step_prop wp_raft_Step γ rn id rs r ml st Hty Hfr Hrs HtrG
  | some γd =>
    obtain ⟨Hnorm, Htcb, Hfit⟩ := Htr (by rw [HtrG]; simp)
    iintro %Φ ⟨#Hpkg, Hrn, #Hr, Hm, #Hmsg, Htk, Hlc⟩ HΦ
    imod ownRawNode_trNoLoan γ rn id rs γd HtrG $$ Hrn with ⟨%Hfacts, Hrn⟩
    have hb' : stepBundle_traced.onG (GF := GF) (hG := hG)
        (fun γ ents s m => PropAny γ ents s m ∧ StepNodeOk s m) :=
      stepBundle_traced.onG_of_statement hb (fun _ _ _ m hp =>
        ⟨hp.2, fun _ => ⟨hp.1.2.1, hp.1.2.2.1⟩, fun h => absurd (hp.1.1.symm.trans h)
          (by simp [MsgProp, MsgUnreachable])⟩)
    iapply wp_rn_raft_Step_prop_traced wp_raft_Step hb' γ rn id rs r ml st γd Hty Hfr Hrs HtrG Hnorm
      Htcb Hfit.le Hfacts.2 $$ [$Hpkg $Hrn $Hr $Hm $Hmsg $Htk $Hlc]
    iexact HΦ

/-- (step 4) **The types `run`'s `recvc` arm steps at a traced node from the network**: a traced network
type (`netGate`'s first disjunct), or `ReportUnreachable`'s `MsgUnreachable`. -/
def TrRcv (t : w32) : Prop := TrNetTy t ∨ t = MsgUnreachable

theorem TrRcv.ne {t : w32} (h : TrRcv t) {u : w32}
    (hu : u ≠ MsgApp ∧ u ≠ MsgAppResp ∧ u ≠ MsgVote ∧ u ≠ MsgVoteResp ∧ u ≠ MsgHeartbeat ∧
      u ≠ MsgHeartbeatResp) (hu' : MsgUnreachable ≠ u) : t ≠ u := by
  rcases h with h | h
  · exact TrNetTy.ne h hu
  · rw [h]; exact hu'

theorem TrRcv.stepEndTy {t : w32} (h : TrRcv t) : StepEndTy t := by
  rcases h with h | h
  · exact h.stepEndTy
  · unfold StepEndTy; simp [h, MsgUnreachable]

/-- `TrRcv.ne` at a constant. -/
local macro "trrcv_ne" h:term:max : tactic =>
  `(tactic| exact TrRcv.ne $h ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩ (by decide))

/-- (step 4) The capability's trace directory, whose voters are the configuration's. -/
theorem trCapB_voters (γd : GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (b : Bool)
    (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ : Option TraceEv → Prop) :
    trCapB (GF := GF) (some γd) γ r id c b Φ Λ ⊢
      (∃ tn : TraceNames, traceDir γd tn ∗ ⌜(elements c.incoming).Perm tn.voters⌝) ∗
        trCapB (some γd) γ r id c b Φ Λ := by
  apply persistent_entails_right
  iintro H
  iunfold trCapB at H
  icases H with ⟨%tn, %C, %tl, %cs, %P, #Hdir, %Hpf, -⟩
  iexists tn
  iframe Hdir
  ipureintro
  rw [Hpf.1]; exact Hpf.2.1

/-- **`r.Step(m)` on a network message at a traced node** (`node.run`'s `recvc` arm, after its guard;
step 4): as `RawNode.Step.traced` after its guards, for a message of a traced network type or
`MsgUnreachable` (`TrRcv`), with `netP`'s facts and its traced gate's: the token, the certified
abstraction, the numbers and shape (`isRaftMsg_trRecv`'s), an append response's sender a voter
(`trFromOk`), which with the tracker's keys gives `StepNodeOk` (`run`'s guard does not: it keeps a
response from a local target id). -/
theorem wp_rn_raft_Step_net_tr (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (hb0 : stepBundle_traced.statement (GF := GF) (hG := hG))
    (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : Loc) (ml : Loc) (st : MsgSt) (γd : GName)
    (Hok : NetMsgOk id st) (Hnt : TrRcv st.msg.Type')
    (Hmtc : uint.Z st.msg.Term' ≤ uint.Z rs.tc) (Hflw : rs.flw = false)
    (HtrG : γ.reTrace = some γd) (Htcb : uint.Z rs.tc + 1 < traceNumBound)
    (Hfit : receiptBound GF + γ.reBoot.length ≤ traceNumBound) (Hboot : γ.reBoot ≠ []) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        ownRawNode γ rn id rs ∗ rn.[RawNode, go!"raft"] ↦□ r ∗
        msgIn ml DFrac.discard st ∗
        □ (∀ ty, ⌜mtypeOf st.msg.Type' = some ty⌝ -∗ ⌜ty ≠ .snap⌝ -∗
          isMessage γ (absMsg ty st.msg st.ents st.ctx)) ∗
        rdCred γ (if st.msg.Type' = MsgReadIndex then 1 else 0) ∗ £ 1 ∗
        recvTokOf γd st.msg st.ents st.ctx ∗
        □ (∀ ty : MsgType, ⌜mtypeOf st.msg.Type' = some ty ∧ ty.traced = true⌝ -∗
          isMessageC γ (absMsg ty st.msg st.ents st.ctx)) ∗
        ⌜(∀ ty, mtypeOf st.msg.Type' = some ty → MsgTrOk γ (absMsg ty st.msg st.ents st.ctx)) ∧
          TrRecvShape st.msg st.ents⌝ ∗
        □ (⌜st.msg.Type' = MsgAppResp⌝ -∗ ∃ tn : TraceNames, traceDir γd tn ∗ ⌜st.msg.From' ∈ tn.voters⌝) }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (t : w64), RET #err;
        ownRawNode γ rn id { rs with term := t } ∗
        ⌜uint.Z rs.term ≤ uint.Z t ∧ uint.Z t ≤ uint.Z rs.tc ∧
          uint.Z t ≤ max (uint.Z rs.term) (uint.Z st.msg.Term')⌝ }} := by
  have hb : stepBundle_traced.on (GF := GF) (hG := hG) (fun s m => TrRcv m.Type' ∧ PrvalsOk s ∧
      domSet s.prvals = domSet s.progress ∧ (m.Type' = MsgAppResp → m.From' ∈ domSet s.progress) ∧
      (m.Type' = MsgUnreachable → m.Term' = W64 0)) :=
    stepBundle_traced.on_of_statement hb0 (fun _ _ hp =>
      ⟨⟨hp.2.1, hp.2.2.1, hp.2.2.2.1⟩, TrRcv.ne hp.1 ⟨by decide, by decide, by decide, by decide,
        by decide, by decide⟩ (by decide), hp.2.2.2.2⟩)
  rcases st with ⟨m, ents, sn, ctx, rsp⟩
  simp only at Hok Hnt Hmtc ⊢
  have Hty0 : 0 ≤ sint.Z m.Type' := netStepTypes_nonneg Hok.1
  have HnS : m.Type' ≠ MsgSnap := by trrcv_ne Hnt
  have HnP : m.Type' ≠ MsgProp := by trrcv_ne Hnt
  have HnT : m.Type' ≠ MsgTimeoutNow := by trrcv_ne Hnt
  have HnX : m.Type' ≠ MsgTransferLeader := by trrcv_ne Hnt
  have HnR : m.Type' ≠ MsgReadIndex := by trrcv_ne Hnt
  have HnPR : m.Type' ≠ MsgPreVoteResp := by trrcv_ne Hnt
  have HnA : m.Type' ≠ MsgStorageAppendResp := by trrcv_ne Hnt
  have HnAp : m.Type' ≠ MsgStorageApplyResp := by trrcv_ne Hnt
  have Hto' : ∀ ty, mtypeOf m.Type' = some ty → ty.traced = true → m.To' = id := by
    intro ty hty htr
    rcases Hnt with Hn | Hu
    · exact (Hok.2.1 (fun hu => by
        rcases hu with h | h | h | h | h <;> exact absurd h (TrNetTy.ne Hn ⟨by decide, by decide,
          by decide, by decide, by decide, by decide⟩))).1
    · rw [Hu] at hty; cases hty
  have Hut : m.Type' = MsgUnreachable → m.Term' = W64 0 := fun h =>
    Hok.2.2.1 (by unfold UnstampedType; simp [h]) (by rw [h]; decide)
  iintro %Φ ⟨#Hpkg, Hrn, #Hr, Hm, #Hmsg, Hcred, Hlc, Htok, #Hmc, %Hrf, #Hfrom⟩ HΦ
  obtain ⟨Htrok, Hshape⟩ := Hrf
  iNamed Hrn
  ihave #Hr' := rawNodeOwn_raft rn rnv $$ Hrn
  icombine Hr Hr' gives %Heq
  subst Heq
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
  icases (rnTrace_some γ rnv.raft' id cf rs.delivered s γd Htr).1 $$ Hrntr with
    ⟨%Hscope, %Hpure, #Hcqf, #Hnosnap, %bt, %Hbt, Hcap⟩
  icases ownRaftPhysC_cq cf rnv.raft' id s $$ Hphys with ⟨#Hcq, Hphys⟩
  icombine Hcqf Hcq gives %Hcqe
  icases ownRaftPhysC_dom cf rnv.raft' id s $$ Hphys with ⟨%Hsub, Hphys⟩
  icases ownRaftPhysC_precand cf rnv.raft' id s $$ Hphys with ⟨%Hpcd, Hphys⟩
  -- (step 4) `StepNodeOk`: the struct's `Progress` facts; an append response's sender a voter
  -- (`trFromOk`), so tracked
  icases ownRaftPhysC_prvalsDom cf rnv.raft' id s $$ Hphys with ⟨%Hsno, Hphys⟩
  icases trCapB_voters γd γ rnv.raft' id cf bt _ _ $$ [Hcap] with ⟨⟨%tn0, #Hdir0, %Hperm0⟩, Hcap⟩
  · rw [← Htr]; iexact Hcap
  icases ownRaftPhysC_tracker_same cf rnv.raft' id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback2⟩
  icases ownTrackerC_progress_map cf tv _ $$ Htrk with ⟨#Hprs, %Hdom, Htrk⟩
  ihave Hphys := Hback2 $$ %tv Htrkf Htrk
  ihave %Hfromp : ⌜m.Type' = MsgAppResp → m.From' ∈ domSet s.progress⌝ $$ []
  · iintro %h
    icases Hfrom $$ %h with ⟨%tn, #Hd, %Hin⟩
    icases traceDir_agree γd tn tn0 $$ [$Hd $Hdir0] with %Htn
    subst Htn
    ipureintro
    have h1 : m.From' ∈ cf.incoming := (GMap.elem_of_elements _ _).1 (Hperm0.mem_iff.2 Hin)
    rw [show domSet s.progress = cf.ids from Hdom]
    exact (GMap.elem_of_subseteq _ _).1 (incoming_sub_ids _) _ h1
  ihave Hcap : trCapB s.gh.tr γ rnv.raft' id cf bt (fun C => SimIdle C s) $$ [Hcap]
  · rw [Htr]; iexact Hcap
  have Hst1 : uint.Z s.term ≤ uint.Z rs.tc := by rw [Hpvoff.2.1]; exact Hpvoff.2.2.1
  ihave Hpre : (trCapB s.gh.tr γ rnv.raft' id cf bt (fun C => SimIdle C s) (fun _ => True) ∗
      (recvTokOf γd m ents ctx ∗
        □ (∀ ty : MsgType, ⌜mtypeOf m.Type' = some ty ∧ ty.traced = true⌝ -∗
          isMessageC γ (absMsg ty m ents ctx))) ∗
      TrNoSnap s.gh.tr s.logst : IProp GF) $$ [Hcap Htok]
  · iframe Hcap Htok Hmc Hnosnap
  imod hb γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩) cf rnv.raft' id s m ents sn ctx rsp γd
      (fun _ => True) bt ⟨Hnt, Hsno.1, Hsno.2, Hfromp, Hut⟩ Htr Hscope.1 Hcqe.symm (TrRcv.stepEndTy Hnt) Hwf
      (fun h => by rcases h with h | h | h <;> exact absurd h (by trrcv_ne Hnt))
      (fun h => absurd h (by trrcv_ne Hnt))
      Hto'
      (by omega) (by omega) Htrok Hfit Hscope.2 Hsub
      (fun h => by have := Hpcd h; rw [Hscope.1] at this; cases this)
      Hshape (fun _ => Hboot) $$ Hpre
    with ⟨%R, HG, Hgates, Hclose⟩
  wp_apply Hok.raftStep Hpvoff Htrm Hmtc (fun h => absurd h HnT) Hb1 (Hrnfl.1 Hflw)
      (wp_raft_Step cf _ γ _ id s ml m ents ctx sn rsp R
        (fun s' => iprop(⌜OutTyStep s s'⌝ ∗ ∃ bt' : Bool, ⌜bt = true → bt' = true⌝ ∗
          trCapB s.gh.tr γ rnv.raft' id cf bt' (fun C => SimIdle C s') (stepLastEv (fun _ => True)))))
      Hwf
    (RNMode.pre_net Hpf (fun h => absurd h (by trrcv_ne Hnt))) (fun _ => Hns0.1)
    (fun h => absurd h (by trrcv_ne Hnt)) (fun h => absurd h (by trrcv_ne Hnt))
    (fun h => absurd h (by trrcv_ne Hnt)) (fun h => absurd h (by trrcv_ne Hnt))
    -- (2026-11-12, implementation step 3) no transfer stepped; no transferee (`rnTrace`'s (b))
    (fun h => absurd h (by trrcv_ne Hnt)) (fun _ _ => Hpure.1.1) $$ [$Hphys $Hghost $Hlc Hm Hcred HG Hgates Hclose]
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
      iapply Hmsg $$ %ty %Hty' %Hne
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
  have e1 := Href.keep (by trrcv_ne Hnt) (by trrcv_ne Hnt) (fun h => absurd h (by trrcv_ne Hnt)); subst e1
  have e2 := Hcc (fun h => absurd h (by trrcv_ne Hnt)); subst c'
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ :=
    Hfr (by trrcv_ne Hnt) (by trrcv_ne Hnt) (by trrcv_ne Hnt) (fun h => absurd h (by trrcv_ne Hnt))
  have HfrX : NetFrame s { s' with gh := s.gh } ∧ s'.gh = { s.gh with xw := s'.gh.xw } :=
    ⟨⟨a1, a2, a3, a4, a5, a6, a7, rfl, a9, a10⟩, by rw [a8]⟩
  obtain ⟨⟨Ha, Hsn, Hu, Hpv, Hsd, Hsg, Hpre, -, Hfl', Hap'⟩, Hgx⟩ := HfrX
  simp only at Ha Hsn Hu Hpv Hsd Hsg Hpre Hfl' Hap'
  have Hsneq : s'.gh.sn = s.gh.sn := by rw [Hgx]
  have Htceq : s'.gh.tc = s.gh.tc := by rw [Hgx]
  obtain ⟨Ht1, -, Ht3, Hip4, -, Hpcs⟩ := Htm HnS
  have Ht3' : uint.Z s'.term ≤ max (uint.Z s.term) (uint.Z m.Term') := by
    have := Ht3 (by trrcv_ne Hnt) HnPR HnT; omega
  have Hle : uint.Z s'.term ≤ uint.Z s.gh.tc := by
    have := Int.max_le.2 ⟨Htc0, Hmtc'⟩; omega
  have Hstok' : StepsOk s' rs.steps :=
    stepsOk_mono_le s s' _ Ht1 ⟨Hpv, logStoreRec_stored Hsd⟩ Hc Ha (Int.le_of_eq (congrArg _ Htceq.symm)) Hstok
  ihave #Hstr' : ackInv γ { rs with term := s'.term } s' $$ []
  · by_cases Happ : m.Type' = MsgApp
    · ihave #Hm' := Hmsg $$ %MsgType.app %(by show mtypeOf m.Type' = _; rw [Happ]; exact mtypeOf_MsgApp)
        %(by decide)
      rw [isMessage_absMsg_ctx γ .app m ents ctx (And.intro (by decide) (by decide))]
      ihave #Hents := isMessage_app_leadFull γ m ents $$ Hm'
      iapply ackInv_app γ rfl Hstok Ht1 Hpv Hsn (logStoreRec_stored Hsd) (Htrc Happ) Hrel Hpr.1
        $$ Hstrecs Hents
    · iapply ackInv_keep γ rfl Hstok Ht1 Hpv Hsn (logStoreRec_stored Hsd) (Hip4 Happ) $$ Hstrecs
  ihave #Hsloc' : snapLocOk γ id s'.logst.snap $$ []
  · rw [Hsn]; iexact Hsloc
  -- (slice 25n) the capability back, idle at the end state
  have Htr' : s'.gh.tr = some γd := by rw [Hgx]; exact Htr
  -- (2026-11-12, implementation step 3) the leader exclusion's clause at the end state
  icases ownStepGhost_bootCommit γ _ cf id s' $$ Hghost with ⟨%Hbc', Hghost⟩
  icases ownStepGhost_bootPrefix γ _ cf id s' $$ Hghost with ⟨%Hbp', Hghost⟩
  ihave #Hnosnap' := trNoSnap_logst s.gh.tr s'.gh.tr s.logst s'.logst (by rw [Htr', Htr])
    Hpv.symm Hsg.symm $$ Hnosnap
  imod trNoSnap_prev0 s'.gh.tr s'.logst (by rw [Htr']; simp) $$ Hnosnap' with %Hprev'
  have Hboot' := RnTrBoot.step Hpure.2.2.2 Hpcs.2.2.hup Hap' Hprev' (Hbp' Hprev') Hbc'
  icases HG with ⟨%Houtty, %bt', %Hmono, HG⟩
  ihave Hrntr : rnTrace γ rnv.raft' id cf rs.delivered s' $$ [HG]
  · iapply (rnTrace_some γ rnv.raft' id cf rs.delivered s' γd Htr').2
    isplitr
    · ipureintro; exact ⟨Hpre.trans Hscope.1, Hscope.2⟩
    isplitr
    · ipureintro; exact Hpure.step (by rw [Htr]; rfl) Houtty Hboot'
    isplitr
    · iexact Hcqf
    isplitr
    · iapply trNoSnap_logst s.gh.tr s'.gh.tr s.logst s'.logst (by rw [Htr', Htr]) Hpv.symm Hsg.symm
        $$ Hnosnap
    iexists bt'
    isplitr
    · ipureintro; exact fun h => Hmono (Hbt h)
    rw [show s'.gh.tr = s.gh.tr by rw [Htr', Htr]]
    iapply trCapB_monoΛ _ γ rnv.raft' id cf bt' _ _ _ (fun _ _ => trivial) $$ HG
  have HlO : LoanOk { rs with term := s'.term } s' := by
    have h := Hloan.step_gxw (b := false) s'.term Hgx
      (fun _ => ⟨.inl Hsn, Hfl', logStoreRec_stored Hsd, Hu, Ha, Hc⟩) ⟨Hsn, Hc⟩
    simpa only [Bool.or_false] using h
  try wp_auto
  iapply HΦ $$ %err %s'.term
  isplitl
  · iapply ownRawNode_intro_tr γ rn id { rs with term := s'.term } s' cf fp
        rnv sv hprev steps Hwf' Hin
        Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp)
        (fun h => by rw [Hsn]; exact Hsnap h)
        Hstok' rfl (by rw [Hsg]; exact ⟨Hstor.1, by rw [Hsn1.2, Hsneq, ← Hns0.2]; exact Hstor.2⟩)
        (Hpvoff.step_gxw rfl rfl Hpre Hgx Hle Hpcs (fun h => absurd h (by trrcv_ne Hnt)))
        (by rw [Hgx]; exact Hrs_out) (by rw [Hgx]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
        (RNFl.keep Hrnfl Hfl' Hap' Ha)
        HlO
        (Hsdt.ofRec Hsn Hsd) Hrole
        (Hphs.keep rfl rfl rfl (HsLe.of_step Href.voteLe Hc) Hsn (ip_of_step Hip4 Htrc))
        (by rw [Hgx]; exact Hgtr) (by rw [Hgx]; exact Hglq) $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr' Hloanc Hsloc' [Hdur] Hrntr
    · iapply durTie_congr γ (rs := rs) (s := s) (by rfl) (by rfl) Hsn Hpv (logStoreRec_stored Hsd) $$ Hdur
  ipureintro
  rw [Htrm]
  exact ⟨Ht1, by rw [Hpvoff.2.1]; exact Hle, Ht3'⟩

/-- A premise of `Step` about another message type (for `MsgHup`). -/
local macro "hup_ne" : tactic => `(tactic| (intro Hc; simp [MsgHup, MsgVote, MsgVoteResp,
  MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp,MsgCheckQuorum, MsgSnap,
  MsgBeat, MsgProp, MsgStorageAppendResp, MsgStorageApplyResp, MsgReadIndex,
  MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hc))

/-- **`r.Step(m)` on `Campaign`'s `MsgHup` at a traced node** (`node.run`'s `recvc` arm, `hupP`; step 4):
`wp_rn_raft_Step_hup`'s triple at a traced cluster, with the assembly's resources (`MsgHup` is local, at
term `0`, of no abstraction: no token, no certificate); the capability closed idle at the end state. -/
theorem wp_rn_raft_Step_hup_tr (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (hb0 : stepBundle_traced.statement (GF := GF) (hG := hG))
    (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : Loc) (ml : Loc) (st : MsgSt) (γd : GName)
    (Hst : st = hupSt) (Hterm : uint.Z rs.term + 1 ≤ uint.Z rs.tc) (Hflw : rs.flw = false)
    (HtrG : γ.reTrace = some γd) (Htcb : uint.Z rs.tc + 1 < traceNumBound)
    (Hfit : receiptBound GF + γ.reBoot.length ≤ traceNumBound) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        ownRawNode γ rn id rs ∗ rn.[RawNode, go!"raft"] ↦□ r ∗
        msgIn ml DFrac.discard st ∗ £ 1 }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (t : w64), RET #err;
        ownRawNode γ rn id { rs with term := t } ∗
        ⌜uint.Z rs.term ≤ uint.Z t ∧ uint.Z t ≤ uint.Z rs.term + 1⌝ }} := by
  subst Hst
  iintro %Φ ⟨#Hpkg, Hrn, #Hr, Hm, Hlc1⟩ HΦ
  unfold hupSt
  iNamed Hrn
  ihave #Hr' := rawNodeOwn_raft rn rnv $$ Hrn
  icombine Hr Hr' gives %Heq
  subst Heq
  have Htc1 : uint.Z s.term + 1 ≤ uint.Z s.gh.tc := by rw [← Htrm, ← Hpvoff.2.1]; exact Hterm
  have Hnw : uint.Z s.term + 1 < 2 ^ 64 := by have : uint.Z s.gh.tc < 2 ^ 64 := by word
                                              omega
  imod rdCred_zero_upd (GF := GF) γ with Hcr
  icases ownRaftPhysC_sn cf rnv.raft' id s $$ Hphys with ⟨%Hns0, Hphys⟩
  icases ownRaftPhysC_preFacts cf rnv.raft' id s (Hpvoff.guard rs.capplied rs.cfg (ds := ds)) $$ Hphys with ⟨%Hpf, Hphys⟩
  -- the capability, open; the assembly's premises from the node's state
  have Htr : s.gh.tr = some γd := Hgtr.trans HtrG
  icases (rnTrace_some γ rnv.raft' id cf rs.delivered s γd Htr).1 $$ Hrntr with
    ⟨%Hscope, %Hpure, #Hcqf, #Hnosnap, %bt, %Hbt, Hcap⟩
  imod trNoSnap_prev0 s.gh.tr s.logst (by rw [Htr]; simp) $$ Hnosnap with %Hprev0
  icases ownRaftPhysC_cq cf rnv.raft' id s $$ Hphys with ⟨#Hcq, Hphys⟩
  icombine Hcqf Hcq gives %Hcqe
  icases ownRaftPhysC_dom cf rnv.raft' id s $$ Hphys with ⟨%Hsub, Hphys⟩
  icases ownRaftPhysC_precand cf rnv.raft' id s $$ Hphys with ⟨%Hpcd, Hphys⟩
  icases ownRaftPhysC_prvalsDom cf rnv.raft' id s $$ Hphys with ⟨%Hsno, Hphys⟩
  have Hmt : mtypeOf (W32 0) = none := rfl
  ihave Hpre : (trCapB s.gh.tr γ rnv.raft' id cf bt (fun C => SimIdle C s) (fun _ => True) ∗
      (recvTokOf γd ({ (zero_val MessageM) with Type' := W32 0 } : MessageM) [] [] ∗
        □ (∀ ty : MsgType, ⌜mtypeOf (W32 0) = some ty ∧ ty.traced = true⌝ -∗
          isMessageC γ (absMsg ty ({ (zero_val MessageM) with Type' := W32 0 } : MessageM) [] []))) ∗
      TrNoSnap s.gh.tr s.logst : IProp GF) $$ [Hcap]
  · iframe Hcap Hnosnap
    isplitl
    · iunfold recvTokOf
      iintro %ty %h
      rw [Hmt] at h; cases h.1
    imodintro
    iintro %ty %h
    rw [Hmt] at h; cases h.1
  imod hb0 γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩) cf rnv.raft' id s
      ({ (zero_val MessageM) with Type' := W32 0 } : MessageM) [] none [] [] γd
      (fun _ => True) bt Htr Hscope.1 Hcqe.symm
      (.inl (by unfold StepEndTy; simp [MsgHup])) Hwf (fun _ => rfl) (fun h => absurd h (by hup_ne))
      (fun ty h => by rw [Hmt] at h; cases h)
      (by rw [← Htrm]; omega) (by show uint.Z (W64 0) < traceNumBound; unfold traceNumBound; decide)
      (fun ty h => by rw [Hmt] at h; cases h)
      Hfit Hscope.2 Hsub
      (fun h => by have := Hpcd h; rw [Hscope.1] at this; cases this)
      ⟨fun h => absurd h (by hup_ne), fun h => absurd h (by hup_ne),
        fun h => by rcases h with h | h | h <;> exact absurd h (by hup_ne),
        fun ty h => by rw [Hmt] at h; cases h⟩
      (fun h => absurd h (by hup_ne)) ⟨Hsno.1, Hsno.2, fun h => absurd h (by hup_ne)⟩ $$ Hpre
    with ⟨%R, HG, Hgates, Hclose⟩
  have hP : (W32 0 : w32) ≠ MsgProp := by simp [MsgProp]
  wp_apply wp_raft_Step cf _ γ _ id s ml ({ (zero_val MessageM) with Type' := W32 0 } : MessageM)
    [] [] none [] R
    (fun s' => iprop(⌜OutTyStep s s'⌝ ∗ ∃ bt' : Bool, ⌜bt = true → bt' = true⌝ ∗
      trCapB s.gh.tr γ rnv.raft' id cf bt' (fun C => SimIdle C s') (stepLastEv (fun _ => True))))
    (by simp [StepMsg, stepMsgTypes, MsgHup])
    (fun _ => ⟨rfl, Hnw, fun _ => Htc1, Hrnfl.1 Hflw⟩)
    (by hup_ne) (by hup_ne) (by hup_ne) (by hup_ne) (by hup_ne) (by hup_ne)
    (by hup_ne) (by hup_ne) (by hup_ne) (by hup_ne) (by hup_ne) (by hup_ne)
    (by hup_ne) (by hup_ne) (by hup_ne)
    (RestMsgOk.of_ne ⟨by hup_ne, by hup_ne, by hup_ne, by hup_ne, by hup_ne⟩) Hwf
    (GMode.Pre.of_facts Hpf (by hup_ne) (by hup_ne)) (fun h => absurd h (by hup_ne))
    (fun h => absurd h (by hup_ne)) (fun h => absurd h (by hup_ne)) (fun h => absurd h (by hup_ne))
    (fun h => absurd h (by hup_ne))
    (fun h => absurd h (by hup_ne)) (fun h => absurd h (by hup_ne))
    $$ [$Hphys $Hghost $Hlc1 Hcr Hm HG Hgates Hclose]
  · simp only [hP, ↓reduceIte, named]
    isplitr
    · imodintro
      iintro %h
      exact absurd h.1 (by hup_ne)
    isplitl [Hm]
    · iframe Hm
      repeat (isplitr; · first | iempintro | (ipureintro; simp) | (ipureintro; hup_ne))
      imodintro
      iintro %ty %Hty
      rw [Hmt] at Hty
      cases Hty
    isplitl [Hcr]
    · rw [ite_eq_right (by hup_ne)]; iexact Hcr
    isplitr
    · imodintro
      iintro %Hc
      simp [MsgSnap] at Hc
    iframe HG Hgates Hclose
  simp only [hP]
  iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hcc, -, %Hfr, -, %Htm, -, -, -, -, HG⟩
  have Hc := Href.commit_mono
  have e1 := Href.keep (by hup_ne) (by hup_ne) (fun h => absurd h (by hup_ne)); subst e1
  have e2 := Hcc (by hup_ne); subst c'
  obtain ⟨Ha, Hsn, Hu, Hpv, Hsd, Hsg, Hpre, Hgh, Hfl', Hap'⟩ := Hfr (by hup_ne) (by hup_ne) (by hup_ne) (fun h => absurd h (by hup_ne))
  obtain ⟨Ht1, Ht2, -, Hip4, -, Hpcs⟩ := Htm (by hup_ne)
  have Ht2' := Ht2 rfl
  icases ownRaftPhysC_sn cf rnv.raft' id s' $$ Hphys with ⟨%Hsn1, Hphys⟩
  have Hstor' : rs.storage = s'.logst.storage ∧ rs.sn = s'.logst.sn :=
    ⟨by rw [Hsg]; exact Hstor.1, by rw [Hsn1.2, Hgh, ← Hns0.2]; exact Hstor.2⟩
  ihave #Hstr' := ackInv_keep (rs' := rs) γ rfl Hstok Ht1 Hpv Hsn (logStoreRec_stored Hsd) (Hip4 (by hup_ne)) $$ Hstrecs
  -- the capability back, idle at the end state
  have Htr' : s'.gh.tr = some γd := by rw [Hgh]; exact Htr
  icases ownStepGhost_bootCommit γ _ cf id s' $$ Hghost with ⟨%Hbc', Hghost⟩
  icases ownStepGhost_bootPrefix γ _ cf id s' $$ Hghost with ⟨%Hbp', Hghost⟩
  have Hprev' : uint.Z s'.logst.prev.index' = 0 := by rw [Hpv]; exact Hprev0
  have Hboot' := RnTrBoot.step Hpure.2.2.2 Hpcs.2.2.hup Hap' Hprev' (Hbp' Hprev') Hbc'
  icases HG with ⟨%Houtty, %bt', %Hmono, HG⟩
  ihave Hrntr : rnTrace γ rnv.raft' id cf rs.delivered s' $$ [HG]
  · iapply (rnTrace_some γ rnv.raft' id cf rs.delivered s' γd Htr').2
    isplitr
    · ipureintro; exact ⟨Hpre.trans Hscope.1, Hscope.2⟩
    isplitr
    · ipureintro; exact Hpure.step (by rw [Htr]; rfl) Houtty Hboot'
    isplitr
    · iexact Hcqf
    isplitr
    · iapply trNoSnap_logst s.gh.tr s'.gh.tr s.logst s'.logst (by rw [Htr', Htr]) Hpv.symm Hsg.symm
        $$ Hnosnap
    iexists bt'
    isplitr
    · ipureintro; exact fun h => Hmono (Hbt h)
    rw [show s'.gh.tr = s.gh.tr by rw [Htr', Htr]]
    iapply trCapB_monoΛ _ γ rnv.raft' id cf bt' _ _ _ (fun _ _ => trivial) $$ HG
  iapply HΦ $$ %err %s'.term
  ihave #Hsloc' := snapLocOk_keep γ id (.inl Hsn) $$ Hsloc
  isplitl
  · iapply ownRawNode_intro_tr γ rn id { rs with term := s'.term } s' cf fp rnv sv hprev steps Hwf' Hin
      Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp) (by rw [Hsn]; exact Hsnap)
      (stepsOk_mono_le s s' _ Ht1 ⟨Hpv, (logStoreRec_stored Hsd)⟩ Hc Ha (tc_le_of_gh Hgh) Hstok) rfl Hstor'
      (Hpvoff.step rfl rfl Hpre Hgh (by have := Ht2 rfl; omega) Hpcs (fun _ => Htc1))
      (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
      (RNFl.keep Hrnfl Hfl' Hap' Ha) (Hloan.keep Hgh Hsn Hfl' (logStoreRec_stored Hsd) Hu Ha Hc)
      (Hsdt.ofRec Hsn Hsd) Hrole
      (Hphs.keep rfl rfl rfl (HsLe.of_step Href.voteLe Hc) Hsn (.inl (Hip4 (by hup_ne))))
      (by rw [Hgh]; exact Hgtr) (by rw [Hgh]; exact Hglq)
      $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr' Hloanc Hsloc' [Hdur] Hrntr
    · iapply durTie_congr γ (rs := rs) (s := s) (by rfl) (by rfl) Hsn Hpv (logStoreRec_stored Hsd) $$ Hdur
  ipureintro
  rw [Htrm]
  exact ⟨Ht1, Ht2'⟩

end lemmas

end EtcdGrove
end Perennial
