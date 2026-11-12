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
public import Proof.go_etcd_io.raft.v3.InvRtk
public import Proof.go_etcd_io.raft.v3.TracedEscrow
public import Proof.go_etcd_io.raft.v3.TracedApplyConfChange
import all Proof.go_etcd_io.raft.v3.InvNodeChan

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim
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
  have h3 : k < receiptBound GF := Hkl
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
    Hok.2.2.1 (by unfold UnstampedType; simp [h]) (by rw [h]; simp [MsgUnreachable, MsgTransferLeader])
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
  imod trNoSnap_prev0 s.gh.tr s.logst (by rw [Htr]; simp) $$ Hnosnap with %Hprev0
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

/-! ### The `confc` arm (step 4) -/

/-- A follower's `applyConfChange` (`ApplyCCOkC`'s non-leader arm) changes only its tracker. -/
theorem applyCCOkC_follower {c' : CfgM} {id : w64} {s s' : NState} (H : ApplyCCOkC c' id s s')
    (hf : s.role = .follower) :
    ∃ prs pvs b, s' = { s with progress := prs, prvals := pvs, isLearner := b } := by
  obtain ⟨prs, pvs, -, -, Hsw⟩ := H
  unfold SwitchOkC at Hsw
  rw [if_neg (by simp [hf])] at Hsw
  exact ⟨prs, pvs, _, Hsw⟩

/-- **The `ApplyConfChange` line's numbers** at a traced node (`hCC`'s premises): the commit index
within the log, both below the trace's bound (`LogOk`, `ownRaftGhost_traceBound`), gated. -/
theorem ownStepGhost_ccNums (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState)
    (hfit : γ.reTrace ≠ none → receiptBound GF + γ.reBoot.length ≤ traceNumBound) :
    ownStepGhost (GF := GF) γ md c id s ⊢
      |==> (⌜γ.reTrace ≠ none → uint.Z s.logst.committed ≤ uint.Z (plastIndex (toPState s)) ∧
        uint.nat s.logst.committed < traceNumBound ∧ uint.nat (plastIndex (toPState s)) < traceNumBound⌝ ∗
        ownStepGhost γ md c id s) := by
  by_cases hn : γ.reTrace = none
  · iintro H; imodintro; iframe H; ipureintro; intro h; exact absurd hn h
  iintro H
  iunfold ownStepGhost at H
  icases H with ⟨Hg, Hr⟩
  ihave %Hok := ownRaftGhost_logOk γ id (toPState s) $$ Hg
  imod ownRaftGhost_traceBound (GF := GF) γ id (toPState s) (hfit hn) $$ Hg with ⟨%Hb, Hg⟩
  imodintro
  iunfold ownStepGhost
  iframe Hg Hr
  ipureintro
  intro _
  obtain ⟨h1, h2⟩ := Hb
  have hcm : uint.Z s.logst.committed ≤ plogLastIndexZ (toPState s).base (toPState s).log := Hok.2.2
  have h0 : (0 : Int) ≤ plogLastIndexZ (toPState s).base (toPState s).log := by
    unfold plogLastIndexZ; have := uint_Z_nonneg (toPState s).base.index'; omega
  have hb : traceNumBound = 2 ^ 61 := rfl
  have h2' : uint.nat s.logst.committed < traceNumBound := by
    have h := h2; simp only [toPState] at h; have := uint_nat_eq s.logst.committed; omega
  unfold plastIndex
  generalize plogLastIndexZ (toPState s).base (toPState s).log = L at h1 h0 hcm ⊢
  rw [hb] at h1 h2' ⊢
  exact ⟨by word, h2', by word⟩

/-- `isCommitted_trNoConf`, gated (vacuous untraced). -/
theorem isCommitted_trNoConfG (γ : RaftNames) (E : CoPset) (L : List EntryM)
    (HE : ↑(raftLogN γ) ⊆ E) :
    ⊢ raftCommitInv (GF := GF) γ -∗ isCommitted γ L ={E}=∗
      ⌜γ.reTrace ≠ none → ∀ (k : Nat) (e : EntryM), L[k]? = some e → IsConfEnt e →
        k < γ.reBoot.length⌝ := by
  by_cases hn : γ.reTrace = none
  · iintro _ _; imodintro; ipureintro; intro h; exact absurd hn h
  iintro #Hi #HL
  imod isCommitted_trNoConf γ E L hn HE $$ Hi HL with %H
  imodintro; ipureintro; intro _; exact H

/-- **The capability across `applyConfChange`, in both modes** (`rnTrace`): at a traced node with
something delivered, booted (clause (a)); back at a state that keeps the trace mode, pre-vote, the log's
boundary and storage, at the configuration after, which at a traced node is the one before, with the
clauses `RnTrPure` there. -/
theorem rnTrace_cc (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (dl : List EntryM) (s : NState)
    (hdl : s.gh.tr ≠ none → dl ≠ []) :
    rnTrace (GF := GF) γ r id c dl s ⊢
      ⌜s.gh.tr ≠ none → RnTrPure γ c s⌝ ∗ trCapB s.gh.tr γ r id c true (fun C => SimIdle C s) ∗
      (∀ (s' : NState) (c2 : CfgM), ⌜s'.gh.tr = s.gh.tr ∧ s'.prevote = s.prevote ∧
          s'.logst.prev = s.logst.prev ∧ s'.logst.storage = s.logst.storage ∧
          (s.gh.tr ≠ none → c2 = c ∧ RnTrPure γ c s')⌝ -∗
        trCapB s.gh.tr γ r id c2 true (fun C => SimIdle C s') -∗ rnTrace γ r id c2 dl s') := by
  cases htr : s.gh.tr with
  | none =>
    iintro _
    isplitr; · ipureintro; intro h; exact absurd rfl h
    isplitr
    · unfold trCapB; iempintro
    iintro %s' %c2 %Hf -
    iapply rnTrace_none γ r id c2 dl s' (by rw [Hf.1])
  | some γd =>
    iintro H
    icases (rnTrace_some γ r id c dl s γd htr).1 $$ H with ⟨%Hscope, %Hpure, #Hcqf, #Hnosnap, %bt, %Hbt, Hcap⟩
    have hb : bt = true := Hbt (hdl (by rw [htr]; simp))
    subst hb
    isplitr; · ipureintro; intro _; exact Hpure
    rw [← htr]
    iframe Hcap
    iintro %s' %c2 %Hf Hcap
    obtain ⟨h1, h2, h3, h4, h5⟩ := Hf
    obtain ⟨hc, hp⟩ := h5 (by rw [htr]; simp)
    subst hc
    iapply (rnTrace_some γ r id c2 dl s' γd (h1.trans htr)).2
    iframe Hcqf
    isplitr; · ipureintro; exact ⟨h2.trans Hscope.1, Hscope.2⟩
    isplitr; · ipureintro; exact hp
    isplitr
    · iapply trNoSnap_logst s.gh.tr s'.gh.tr s.logst s'.logst h1.symm h3.symm h4.symm $$ Hnosnap
    iexists true
    isplitr; · ipureintro; intro _; rfl
    rw [h1]; iexact Hcap

/-- `InvNodeRun.lean`'s private `leadW_applyCC`, restated: the leader witness across `applyConfChange`. -/
theorem leadW_applyCC' (γ : RaftNames) {c' : CfgM} {id : w64} {s s' : NState}
    (H : ApplyCCOkC c' id s s') :
    leadW (GF := GF) γ id (toPState s) ⊢ leadW γ id (toPState s') := by
  rcases applyCCOkC_step (B := 0) c' id s s' H with ⟨Hst, -⟩ | ⟨-, -, -, ps1, -, Hps⟩
  · iintro #Hl
    iapply leadW_stepC γ c' id 0 _ [] _ Hst $$ [] Hl
    iapply (BigSepL.bigSepL_nil (Φ := fun _ m => isMessage (GF := GF) γ m)).2
    iempintro
  · iintro -
    iapply leadW_none
    rw [Hps]; rfl

theorem wp_applyConf_dyn_g
    (hCC : raft.applyConfChange.tracedSpec (GF := GF) (hG := hG))
    (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (dec : CCDec) (c0 : CCState)
    (h0 : CfgOk c0) (h1 : CCGood c0) (hm : rs.mode = .dyn dec c0 h0 h1) (k : Nat)
    (e : EntryM) (cs' : CCState)
    (cc : Loc) (ccm : ConfChangeV2M) (dq : DFrac)
    -- (2026-10-28, stage U3d) of a committed log `D` within the commit index: the committed log
    -- handed out (while a snapshot `Ready` is lent, the loan's)
    (D : List EntryM)
    (ds : DecMap) (Hpre : DynCCPreOp (effDec dec ds) D rs.capplied rs.cfg (ccm.transition, ccm.changes) k e cs')
    (s : NState) (cf : CfgM) (fp : List EntryM) (rnv : RawNode) (sv : SoftState)
    (hprev : HardStateM) (steps : List Loc)
    (Hwf : NStateWf s) (Hin : rs.mode = .static → id ∈ γ.reCfg) (Hasync : rnv.asyncStorageWrites' = false)
    (Hdlen : rs.delivered.length = (uint.Z s.logst.applying).toNat)
    (Hunp : rs.unpersisted = s.logst.unpersisted)
    (Hsnap : rs.psnap = false ∧ rs.slent = none → s.logst.snap = none)
    (Hstok : StepsOk s rs.steps)
    (Htrm : rs.term = s.term) (Hstor : rs.storage = s.logst.storage ∧ rs.sn = s.logst.sn)
    (Hpvoff : RNPv rs fp s) (Hrs_out : rs.outlb = s.gh.outlb)
    (Hrs_unst : rs.unst = s.gh.unst) (Hrs_clb : uint.Z rs.clb ≤ uint.Z s.logst.committed)
    (Hrnfl : RNFl rs s) (Hloan : LoanOk rs s) (Hsdt : SdtTie rs s)
    (Hrole : rs.role = sv.RaftState') (Hphs : PhsOk rs s)
    (HDc : (D.length : Int) ≤ uint.Z s.logst.committed)
    -- (2026-11-02, stage II (u)) `D` within the committed log handed out (`CapOk`)
    (HDl : ∀ l, rs.slent = some l → D.length ≤ l.dlv.length)
    (HDn : rs.slent = none → D.length ≤ rs.delivered.length)
    -- (2026-11-09, Q8 stage 0) the trace mode the cluster's, and the cluster untraced
    (Hgtr : s.gh.tr = γ.reTrace)
    -- (step 4) at a traced node, the change keeps the configuration (`confcP`'s clause), and the
    -- bounds and no loan (`RunTracedOk`, `ownRawNode_trNoLoan`)
    (Hkeep : γ.reTrace ≠ none → cs'.cfg = rs.cfg.cfg)
    (Htr : γ.reTrace ≠ none → uint.Z rs.tc + 1 < traceNumBound ∧ traceReadyFits GF γ ∧ rs.slent = none)
    -- (2026-11-09, Q8 stage 1 slice 5) no message recorded as just queued (`NGhost.lq`)
    (Hglq : s.gh.lq = [] := by tr_keep) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        rawNodeOwn rn rnv ∗ ownRaftPhysCV cf cf.voters rnv.raft' id s ∗
        ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩) cf id s ∗
        sdrOk rnv.raft' rs.mode ∗ rnv.prevSoftSt' ↦□ sv ∗ prevHS γ rnv.prevHardSt' hprev rs.phs ∗
        rnv.stepsOnAdvance' ↦* steps ∗
        ownSliceCap Loc rnv.stepsOnAdvance' (DFrac.own 1) ∗
        lentPend rs.slent (pendList γ id rs.bw steps rs.steps) ∗
        isCommitted γ rs.delivered ∗ ackInv γ rs s ∗
        loanCom γ rs.slent ∗ snapLocOk γ id s.logst.snap ∗ ownConfChangeV2 cc dq ccm ∗ £ 1 ∗
        isCommitted γ D ∗ durTie γ rs s ∗ rnTrace γ rnv.raft' id cf rs.delivered s }}
      (App (Val (rnv.raft' @!! go.GoType.PointerType raft.ty @!! go!"applyConfChange")) (Val #cc))
    {{ (cs : Loc) (xs os ls lns : List w64), RET #cs;
        ownRawNode γ rn id { rs with cfg := cs', capplied := k + 1 } ∗
        ownConfChangeV2 cc dq ccm ∗
        csPts cs (DFrac.own 1) (ConfStateM.mk xs ls os lns cs'.cfg.autoLeave) true ∗
        ⌜xs ≡ₚ elements cs'.cfg.incoming ∧ os ≡ₚ elements cs'.cfg.outgoing ∧
          ls ≡ₚ elements cs'.cfg.learners ∧ lns ≡ₚ elements cs'.cfg.learnersNext⌝ }} := by
  obtain ⟨Hk1, Hk2, Hke, Hconf, Hnoc, ⟨op', Hdec, Hstep'⟩, Hstep⟩ := Hpre
  iintro %Φ ⟨#Hpkg, Hrn, Hphys, Hghost, #Hsdrf, #Hsoft, #Hhard, Hsteps, Hcap0, Hpend, #Hdeliv,
    #Hstrecs, #Hloanc, #Hsloc, Hch, Hlc, #HDd, #Hdur, Hrntr⟩ HΦ
  -- (step 4) the traced facts, while the ghost state is whole
  icases ownStepGhost_bootCommit γ _ cf id s $$ Hghost with ⟨%Hbc0, Hghost⟩
  icases ownStepGhost_applied_capplied γ rs.mode rs.capplied rs.cfg fp ds cf id s $$ Hghost with ⟨%Hapc, Hghost⟩
  imod ownStepGhost_ccNums γ _ cf id s (fun h => (Htr h).2.1.le) $$ Hghost with ⟨%Hnums, Hghost⟩
  icases (entails_wand (persistent_entails_left (ownStepGhost_inv γ _ cf id s))) $$ Hghost with ⟨Hghost, #Hci⟩
  imod isCommitted_trNoConfG γ ⊤ D (fun _ _ => CoPset.mem_full) $$ Hci HDd with %Hg3
  icases rnTrace_cc γ rnv.raft' id cf rs.delivered s (fun hs => by
      obtain ⟨-, -, hsl⟩ := Htr (Hgtr ▸ hs)
      have := HDn hsl
      intro h; rw [h] at this; simp only [List.length_nil] at this; omega) $$ Hrntr with ⟨%HrtP, Hcap, Hrtback⟩
  let g : RGh := ⟨rs.capplied, rs.cfg, fp, ds⟩
  ihave Hghost : ownStepGhost γ (.dyn dec c0 h0 g) cf id s $$ [Hghost]
  · rw [show (GMode.dyn dec c0 h0 g) = rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩ by rw [hm]; rfl]
    iexact Hghost
  icases ownRaftPhysC_logwf cf rnv.raft' id s $$ Hphys with ⟨%Hlw, Hphys⟩
  icases ownStepGhost_deliv γ dec c0 h0 g cf id s D HDc $$ HDd Hghost
    with ⟨%Hdp, Hghost⟩
  icases ownStepGhost_ns_last γ _ cf id s $$ Hghost with ⟨%Hli2, Hghost⟩
  ihave %Hltz := ownStepGhost_leader_tnz γ _ cf id s $$ Hghost
  icases (ownStepGhost_dyn γ dec c0 h0 g cf id s).1 $$ Hghost with ⟨%HDc, #HM, Hgr, #Hcl⟩
  obtain ⟨HD, Hgc, Hnl⟩ := HDc
  iunfold ownRaftGhostR at Hgr
  icases Hgr with ⟨Hg, %HI, #Hfr⟩
  icases (entails_wand (persistent_entails_left (wand_entails
    (ownRaftGhost_logRecs (GF := GF) γ id (rOf s g).p true)))) $$ Hg with ⟨Hg, %-, #Hlr⟩
  icases ownRaftPhysC_preFacts cf rnv.raft' id s (Hpvoff.guard rs.capplied rs.cfg (ds := ds)) $$ Hphys with ⟨%Hpf, Hphys⟩
  -- the entry, in the node's full log
  have Hfull_k : (rOf s g).full[k]? = some e := by
    obtain ⟨t, ht⟩ := Hdp
    rw [← ht, List.getElem?_append_left Hk2]; exact Hke
  have Htake : (rOf s g).full.take k = D.take k := by
    obtain ⟨t, ht⟩ := Hdp
    rw [← ht, List.take_append_of_le_length (Nat.le_of_lt Hk2)]
  have Hkc : k < uint.nat s.logst.committed := by
    have := uint_nat_eq s.logst.committed; omega
  have Hnoc' : NoUndecConfIn (effDec dec ds) (rOf s g).full g.cidx k :=
    Hnoc.prefix Hdp (Nat.le_of_lt Hk2)
  -- the configuration the code sees is the model's
  have Hgood : CCGood rs.cfg := cfgFold_good h1 HI.cfg
  have Hcfg : cfgStateC cf = rs.cfg := by rw [← Hgc]; exact cfgStateC_of_good Hgood
  obtain ⟨Happ, Hsz⟩ := ccStepB_some Hstep
  -- no candidate: a candidate has no conf entry past `applied` (`RInv.cand`)
  have Hnc : s.role ≠ .candidate := by
    intro hc
    have hc' : (rOf s g).p.role = .candidate := by simp [rOf, toPState, hc, proleRole]
    obtain ⟨-, Hn⟩ := HI.cand hc'
    have Hac := HI.applied_cidx
    exact Hn k e (Nat.le_trans Hac Hk1) Hkc Hfull_k Hconf
  -- (2026-10-25, T-M M2b) no pre-candidate either: its campaign guard has no conf entry past
  -- `applied` (`PreGuardF`; until then pre-vote was off in the dynamic mode)
  have Hnpc : s.role ≠ .preCandidate := by
    intro hp
    have Hg : PreGuardF fp s := by have := Hpf.1; rw [hm] at this; exact this
    obtain ⟨-, Hn⟩ := Hg HI.full.1 hp
    have Hac := HI.applied_cidx
    exact Hn k e (Nat.le_trans Hac Hk1) Hkc Hfull_k Hconf
  -- (step 4) a traced node is a follower: otherwise it applied the bootstrap log (`RnTrBoot`), so
  -- `applied ≥ |boot|`, while `applied ≤ capplied ≤ k` and the entry at `k`, a conf entry, is within the
  -- bootstrap log (G3 (a))
  have Hfol : s.gh.tr ≠ none → s.role = .follower := by
    intro hs
    have hγ : γ.reTrace ≠ none := Hgtr ▸ hs
    refine Classical.byContradiction (fun hr => ?_)
    have h1 := (HrtP hs).2.2.2.2 hr
    have h2 := Hapc (by rw [hm]; rfl)
    have h3 := Hg3 hγ k e Hke Hconf
    have h4 : uint.Z s.logst.applied = (uint.nat s.logst.applied : Int) := by
      have := uint_nat_eq s.logst.applied; omega
    omega
  imod rdCred_zero_upd (GF := GF) γ with Hcr0
  iapply wp_fupd
  wp_apply +noauto hCC cf rnv.raft' id s cc ccm dq cs' γ
      (by rw [Hcfg]; exact Happ) (by have := Hsz; omega) Hltz
      (fun h => by
        rcases h with h | h
        · exact absurd h Hnc
        · exact absurd h Hnpc) Hli2
      (fun hs => by
        have hγ : γ.reTrace ≠ none := Hgtr ▸ hs
        obtain ⟨Htcb, -, -⟩ := Htr hγ
        obtain ⟨n1, n2, n3⟩ := Hnums hγ
        refine ⟨Hfol hs, by rw [Hkeep hγ, ← Hcfg]; rfl, Hbc0, n1, ?_, n2, n3⟩
        have h5 : uint.Z s.term ≤ uint.Z rs.tc := by rw [Hpvoff.2.1]; exact Hpvoff.2.2.1
        have hb : traceNumBound = 2 ^ 61 := rfl
        rw [hb] at Htcb ⊢
        have := uint_nat_eq s.term
        omega)
    $$ [$Hphys $Hch $Hcap] as %cs %xs %os %ls %lns %s' ⟨Hphys, Hch, Hcs, %Hcs0, %Hok, Hcap⟩
  -- the ghost step
  let g' : RGh := ⟨k + 1, cs', fp, ds⟩
  have Hadm : AdmS (effDec dec ds) c0 (fun l => l = (rOf s g).full.take (k + 1)) ((rOf s g).full.take (k + 1))
      cs' := by
    refine ⟨?_, rfl⟩
    unfold AdmFold
    have H0 := cfgFold_noUndec (effDec dec ds) c0 Hnoc' Hk1 HI.cfg
    rw [show (rOf s g).full.take (k + 1) = (rOf s g).full.take k ++ [e] by
      rw [List.take_add_one, Hfull_k]; rfl, cfgFold_snoc, H0, Option.bind_some]
    unfold entStep
    rw [ite_eq_left Hconf, Htake, Hdec, Option.bind_some]
    exact Hstep'
  have HR1 : StepR (AdmS (effDec dec ds) c0 (fun l => l = (rOf s g).full.take (k + 1))) (effDec dec ds) id 0 (rOf s g) []
      (rOf s g') :=
    StepR.applyConf (rOf s g) k e op' cs' Hk1 Hkc Hfull_k Hconf
      Hnoc' (by rw [Htake]; exact Hdec) Hstep' Hadm
  have HR2 := applyCCOkC_stepR (B := 0) (Adm := AdmS (effDec dec ds) c0 (fun l => l = (rOf s g).full.take (k + 1)))
    (dec := effDec dec ds) cs'.cfg id s s' g' Hok rfl
  have HR := StepR.trans _ _ _ _ _ HR1 HR2
  ihave #Hrecs : □ ∀ (fp' : List EntryM), ⌜fp' = (rOf s g).full.take (k + 1)⌝ -∗
      logRecs (GF := GF) γ base0 fp' $$ []
  · ihave #Hfl := logRecs_full γ (rOf s g).p.base (rOf s g).fp (rOf s g).p.log HI.full $$ Hfr Hlr
    imodintro
    iintro %fp' %Hfp'
    subst Hfp'
    rw [show (rOf s g).full = (rOf s g).fp ++ (rOf s g).p.log from rfl]
    iapply logRecs_take γ _ (k + 1) $$ Hfl
  ihave Hgr : ownRaftGhostR γ (effDec dec ds) c0 id (rOf s g) $$ [Hg]
  · iunfold ownRaftGhostR
    iframe Hg Hfr
    ipureintro; exact HI
  imod (preceipt_zero_bound (GF := GF) γ.reBoot.length) with #Hrc0
  imod ownRaftGhostR_stepR γ dec ds c0 h0 HD _ id 0 (by decide) _ _ _ HR $$ Hrc0 HM Hrecs [] [Hcr0] []
    Hlc Hgr with Hgr
  · rw [List.nil_append]
    iapply (BigSepL.bigSepL_nil (Φ := fun _ m => isMessage (GF := GF) γ m)).2
    iempintro
  · rw [List.nil_append, show rdCount ([] : List Msg) = 0 from rfl]; iexact Hcr0
  · rw [List.nil_append]; iapply msgsTks_nil
  ihave Hghost : ownStepGhost γ (.dyn dec c0 h0 g') cs'.cfg id s' $$ [Hgr]
  · iapply (ownStepGhost_dyn γ dec c0 h0 g' cs'.cfg id s').2
    iframe Hgr HM
    isplitr
    · ipureintro
      refine ⟨HD, rfl, Hnl.step Hok.gh ?_⟩
      by_cases hs : s.gh.tr = none
      · exact OutTrStep.of_none hs
      · obtain ⟨prs, pvs, b, rfl⟩ := applyCCOkC_follower Hok (Hfol hs)
        exact fun _ m hm => .inl hm
    -- (raft-final phase 2) the certificate link and the transfer records over the kept ghost
    -- fields, the leader witness across the step (`leadW_applyCC`)
    icases Hcl with ⟨#Hcl1, #Hlw, #Hxw⟩
    isplitr
    · rw [Hok.gh]; iexact Hcl1
    isplitr
    · iapply leadW_applyCC' γ Hok $$ Hlw
    · iunfold xfW at Hxw
      iunfold xfW
      rw [Hok.gh]; iexact Hxw
  ihave Hghost : ownStepGhost γ (({ rs with cfg := cs', capplied := k + 1 } : RNState).mode.toG
      ⟨({ rs with cfg := cs', capplied := k + 1 } : RNState).capplied,
       ({ rs with cfg := cs', capplied := k + 1 } : RNState).cfg, fp, ds⟩) cs'.cfg id s' $$ [Hghost]
  · rw [show (({ rs with cfg := cs', capplied := k + 1 } : RNState).mode.toG
        ⟨({ rs with cfg := cs', capplied := k + 1 } : RNState).capplied,
         ({ rs with cfg := cs', capplied := k + 1 } : RNState).cfg, fp, ds⟩) = GMode.dyn dec c0 h0 g' by
      simp only; rw [hm]; rfl]
    iexact Hghost
  obtain ⟨Hwf', Ht', Hpv', Hgh', Hls', Hc', Hrl', Hfol'⟩ := applyCCOkC_frame Hok Hwf
  -- (2026-11-02, stage II (u)) the configuration index up to the entry applied, within `D`
  have Hcap' : CapOk { rs with cfg := cs', capplied := k + 1 } s' := by
    have H3 := Hloan.2.2.2.2.2
    refine ⟨?_, fun l hl => ?_, fun hl p hp => ?_⟩
    · show ((k + 1 : Nat) : Int) ≤ _; omega
    · show k + 1 ≤ l.dlv.length; have := HDl l hl; omega
    · rw [Hls'] at hp
      have h3 := H3 hl p hp
      have := HDn hl
      exact ⟨by show ((k + 1 : Nat) : Int) ≤ _; omega, h3.2⟩
  have HL := Hloan.keep (rs' := rs) Hgh' (by rw [Hls']) (by rw [Hls']) (by rw [Hls']) (by rw [Hls'])
    (by rw [Hls']) Hc'
  ihave #Hstr' := ackInv_keep (rs' := rs) γ rfl Hstok (by rw [Ht']; exact Int.le_refl _)
    (by rw [Hls']) (by rw [Hls']) (by rw [Hls']) (by rw [Hls']; exact Int.le_refl _) $$ Hstrecs
  ihave #Hsloc' := snapLocOk_keep γ id (o := s.logst.snap) (o' := s'.logst.snap) (.inl (by rw [Hls']))
    $$ Hsloc
  -- (step 4) the capability back, at the configuration after (the same at a traced node)
  ihave Hrntr := Hrtback $$ %s' %cs'.cfg %(⟨by rw [Hgh'], Hpv', by rw [Hls'], by rw [Hls'], fun hs => by
      refine ⟨by rw [Hkeep (Hgtr ▸ hs), ← Hcfg]; rfl, ?_⟩
      obtain ⟨prs, pvs, b, rfl⟩ := applyCCOkC_follower Hok (Hfol hs)
      exact (HrtP hs).congr rfl rfl rfl rfl rfl (Int.le_refl _)⟩) Hcap
  imodintro
  iapply HΦ $$ %cs %xs %os %ls %lns
  iframe Hch Hcs
  isplitl
  · iapply ownRawNode_intro_tr γ rn id { rs with cfg := cs', capplied := k + 1 } s' cs'.cfg fp rnv sv
      hprev steps Hwf' (fun h => by simp only at h; rw [hm] at h; cases h) Hasync
      (by rw [Hls']; exact Hdlen) (by rw [Hls']; exact Hunp) (by rw [Hls']; exact Hsnap)
      (Hgtr := by rw [Hgh']; exact Hgtr) (Hglq := by rw [Hgh']; exact Hglq)
      (stepsOk_mono s s' _ Ht' ⟨by rw [Hls'], by rw [Hls']⟩ Hc' (by rw [Hls']) (tc_le_of_gh Hgh') Hstok)
      (by rw [Ht']; exact Htrm) (by rw [Hls']; exact Hstor)
      ⟨fun _ _ hp => absurd (Hrl' hp) Hnpc, by rw [Hgh']; exact Hpvoff.2.1,
        by rw [Hgh', Ht']; exact Hpvoff.2.2.1, fun h => by rw [Hgh', Ht']; exact Hpvoff.2.2.2.1 (Hrl' h),
        fun h => Hfol' (Hpvoff.2.2.2.2 (by rw [Hls'] at h; exact h))⟩
      (by rw [Hgh']; exact Hrs_out) (by rw [Hgh']; exact Hrs_unst) (Int.le_trans Hrs_clb Hc')
      (by unfold RNFl; rw [Hls']; exact Hrnfl)
      ⟨HL.1, HL.2.1, HL.2.2.1, Hcap'⟩
      (by unfold SdtTie; rw [Hls']; exact Hsdt) Hrole
      (Hphs.keep rfl rfl rfl (HsLe.of_step (applyCCOkC_voteLe Hok) Hc') (by rw [Hls'])
        (.inl (by rw [Hls']; exact Int.le_refl _))) $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hcap0 Hpend Hdeliv Hstr' Hloanc Hsloc' [Hdur] Hrntr
    · iapply durTie_congr γ (rs := rs) (s := s) (by rfl) (by rfl) (by rw [Hls']) (by rw [Hls'])
        (by rw [Hls']) $$ Hdur
  ipureintro; exact Hcs0



theorem wp_rn_raft_applyConfChange_dyn_g
    (hCC : raft.applyConfChange.tracedSpec (GF := GF) (hG := hG))
    (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : Loc) (cc : Loc) (ccm : ConfChangeV2M)
    (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0)
    (h1 : CCGood c0) (hm : rs.mode = .dyn dec c0 h0 h1) (k : Nat) (e : EntryM)
    (cs' : CCState) (M : DecMap)
    -- (2026-10-28, stage U3d) of the committed log handed out (while a snapshot `Ready` is lent,
    -- the loan's: `rsDlv`); (2026-10-28, the decision switch) over the decisions `M`, which the
    -- node's ghost part absorbs
    (Hpre : DynCCPreOp (effDec dec M) (rsDlv rs) rs.capplied rs.cfg (ccm.transition, ccm.changes)
      k e cs')
    (Hkeep : γ.reTrace ≠ none → cs'.cfg = rs.cfg.cfg)
    (Htr : γ.reTrace ≠ none → uint.Z rs.tc + 1 < traceNumBound ∧ traceReadyFits GF γ ∧ rs.slent = none) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        ownRawNode γ rn id rs ∗ rn.[RawNode, go!"raft"] ↦□ r ∗ ownConfChangeV2 cc DFrac.discard ccm ∗
        £ 1 ∗ decLb γ M }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"applyConfChange")) (Val #cc))
    {{ (cs : Loc) (xs os ls lns : List w64), RET #cs;
        ownRawNode γ rn id { rs with cfg := cs', capplied := k + 1 } ∗
        ownConfChangeV2 cc DFrac.discard ccm ∗
        csPts cs (DFrac.own 1) (ConfStateM.mk xs ls os lns cs'.cfg.autoLeave) true ∗
        ⌜xs ≡ₚ elements cs'.cfg.incoming ∧ os ≡ₚ elements cs'.cfg.outgoing ∧
          ls ≡ₚ elements cs'.cfg.learners ∧ lns ≡ₚ elements cs'.cfg.learnersNext⌝ }} := by
  iintro %Φ ⟨#Hpkg, Hrn, #Hr, Hccs, Hlc, #HM⟩ HΦ
  iNamed Hrn
  -- (2026-10-28, the decision switch) the decisions join the ghost part
  icases ownStepGhost_absorbM γ rs.mode ⟨rs.capplied, rs.cfg, fp, ds⟩ cf id s M
    $$ [$HM $Hghost] with ⟨%Hsub, Hghost⟩
  have Hpre' : DynCCPreOp (effDec dec (ds ∪ M)) (rsDlv rs) rs.capplied rs.cfg
      (ccm.transition, ccm.changes) k e cs' := by
    rcases Hsub with h | h
    · exact Hpre.mono_dec (effDec_mono dec h)
    · rw [hm] at h; cases h
  generalize ds ∪ M = ds at Hpre' ⊢
  ihave #Hr' := rawNodeOwn_raft rn rnv $$ Hrn
  icombine Hr Hr' gives %Heq
  subst Heq
  -- the committed log handed out, committed and within the commit index
  ihave #HDd : isCommitted γ (rsDlv rs) $$ []
  · unfold rsDlv
    cases hs : rs.slent with
    | none => iexact Hdeliv
    | some l => icases Hloanc with ⟨#H, -⟩; iexact H
  icases ownRaftPhysC_logwf cf rnv.raft' id s $$ Hphys with ⟨%Hlw, Hphys⟩
  have HDc : ((rsDlv rs).length : Int) ≤ uint.Z s.logst.committed := by
    unfold rsDlv
    cases hs : rs.slent with
    | none => rw [Hdlen]; have := uint_Z_nonneg s.logst.applying; omega
    | some l =>
      obtain ⟨-, -, Hi, -, -, -, -, Hdl, -⟩ := Hloan.2.2.1 l hs
      simp only; rw [Hdl]; have := uint_Z_nonneg l.snap.Metadata'.Index'; omega
  iapply wp_applyConf_dyn_g hCC γ rn id rs dec c0 h0 h1 hm k e cs' cc ccm
      DFrac.discard (rsDlv rs) ds Hpre' s cf fp rnv sv hprev steps Hwf Hin Hasync Hdlen Hunp Hsnap Hstok
      Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl Hloan Hsdt Hrole Hphs HDc
      (fun l hl => by simp [rsDlv, hl])
      (fun hl => by simp [rsDlv, hl]) Hgtr Hkeep Htr
    $$ [$Hpkg $Hrn $Hphys $Hghost $Hsdrf $Hsoft $Hhard $Hsteps $Hsteps_cap $Hpend $Hdeliv
      $Hstrecs $Hloanc $Hsloc $Hccs $Hlc $HDd $Hdur $Hrntr]
  inext
  iintro %cs %xs %os %ls %lns ⟨Hrn, Hccs, Hcs, %Hcs⟩
  iapply HΦ $$ %cs %xs %os %ls %lns
  iframe Hrn Hccs Hcs
  ipureintro; exact Hcs


/-! ### Both modes: the wrappers `node.run.gated_of` calls -/

/-- The term ceiling's bound at a traced node, from the budget's (`termLB_rb`) and `RunTracedOk`'s. -/
theorem tc_bound {t : w64} (h1 : uint.nat t ≤ receiptBound GF) (h2 : receiptBound GF + 2 ≤ traceNumBound) :
    uint.Z t + 1 < traceNumBound := by
  have := uint_nat_eq t; omega

/-- `ownRawNode_trNoLoan`, gated (vacuous untraced). -/
theorem ownRawNode_trNoLoanG (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) :
    ownRawNode (GF := GF) γ rn id rs ⊢
      |={⊤}=> (⌜γ.reTrace ≠ none → rs.slent = none ∧ γ.reBoot ≠ []⌝ ∗ ownRawNode γ rn id rs) := by
  cases h : γ.reTrace with
  | none => iintro H; imodintro; iframe H; ipureintro; intro h'; exact absurd rfl h'
  | some γd =>
    iintro H
    imod ownRawNode_trNoLoan γ rn id rs γd h $$ H with ⟨%Hf, H⟩
    imodintro; iframe H; ipureintro; intro _; exact Hf

/-- The driver's view of the configuration is `run`'s (`runCfg`'s half of `cap`). -/
theorem runCfg_cap_agree (γ : NodeNames) (rs : RNState) (ca : Nat) (cfg : CCState) :
    ⊢ runCfg (GF := GF) γ rs -∗ dghostVar γ.cap (DFrac.own (1 : Qp).half) (ca, cfg) -∗
      ⌜cfg = rs.cfg⌝ ∗ runCfg γ rs ∗ dghostVar γ.cap (DFrac.own (1 : Qp).half) (ca, cfg) := by
  iintro Hcfg Hcap
  iunfold runCfg at Hcfg
  icases Hcfg with ⟨%Hm0, Hdlm, #Hdk, %ca_r, Hcap_r, Hcam, %Hinv, #Hinv2⟩
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hcap_r Hcap
  simp only [Prod.mk.injEq] at Heq
  iframe Hcap
  isplitr
  · ipureintro; exact Heq.2.symm
  iunfold runCfg
  iframe Hdlm Hdk
  isplitr
  · ipureintro; exact Hm0
  iexists ca_r
  iframe Hcap_r Hcam Hinv2
  ipureintro; exact Hinv

/-- The escrow's key, gated (the `readyc` commit). -/
theorem rtk_keyG (ρ : RaftNames) (γe : RtkNames) (ms : List QMsg) (E : CoPset) (hE : ↑rtkN ⊆ E) :
    ⊢ gateTr (GF := GF) ρ.reTrace (rtkInv ρ γe) -∗ gateTr ρ.reTrace (rtkRun γe none) ={E}=∗
      gateTr ρ.reTrace (rtkRun γe (some ms)) ∗ gateTr ρ.reTrace (rtkElem γe ms) := by
  unfold gateTr
  cases ρ.reTrace with
  | none => iintro _ _; imodintro; isplitr <;> itrivial
  | some _ =>
    iintro #Hi Hr
    imod rtk_key ρ γe ms E hE $$ Hi Hr with ⟨Hr, He⟩
    imodintro; iframe Hr He

/-- The escrow's deposit, gated (after `acceptReady`): the `Ready`'s tokens (`readyTok`, the escrow's
`trTokR`) in. -/
theorem rtk_depositG (ρ : RaftNames) (γe : RtkNames) (ms : List QMsg) (E : CoPset) (hE : ↑rtkN ⊆ E) :
    ⊢ gateTr (GF := GF) ρ.reTrace (rtkInv ρ γe) -∗ gateTr ρ.reTrace (rtkRun γe (some ms)) -∗
      ([∗list] q ∈ ms, readyTok ρ q.st) ={E}=∗ gateTr ρ.reTrace (rtkRun γe none) := by
  have hconv : ([∗list] q ∈ ms, readyTok (GF := GF) ρ q.st) ⊢ [∗list] q ∈ ms, trTokR ρ q.st := by
    apply BigSepL.bigSepL_mono
    intro k q _
    exact (readyTok_trTokR ρ q.st).1
  unfold gateTr
  cases ρ.reTrace with
  | none => iintro _ _ _; imodintro; itrivial
  | some _ =>
    iintro #Hi Hr Ht
    ihave Ht := hconv $$ Ht
    iapply rtk_deposit ρ γe ms E hE $$ Hi Hr Ht

/-- **`r.Step(m)` on `Campaign`'s `MsgHup`, in both modes** (`wp_rn_raft_Step_hup`, `wp_rn_raft_Step_hup_tr`). -/
theorem wp_rn_raft_Step_hup_g (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (hb0 : stepBundle_traced.statement (GF := GF) (hG := hG))
    (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : Loc) (ml : Loc) (st : MsgSt)
    (Hst : st = hupSt) (Hterm : uint.Z rs.term + 1 ≤ uint.Z rs.tc) (Hflw : rs.flw = false)
    (Htr : γ.reTrace ≠ none → uint.Z rs.tc + 1 < traceNumBound ∧ traceReadyFits GF γ) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        ownRawNode γ rn id rs ∗ rn.[RawNode, go!"raft"] ↦□ r ∗
        msgIn ml DFrac.discard st ∗ £ 1 }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (t : w64), RET #err;
        ownRawNode γ rn id { rs with term := t } ∗
        ⌜uint.Z rs.term ≤ uint.Z t ∧ uint.Z t ≤ uint.Z rs.term + 1⌝ }} := by
  cases HtrG : γ.reTrace with
  | none => exact wp_rn_raft_Step_hup wp_raft_Step γ rn id rs r ml st Hst Hterm Hflw HtrG
  | some γd =>
    obtain ⟨Htcb, Hfit⟩ := Htr (by rw [HtrG]; simp)
    exact wp_rn_raft_Step_hup_tr wp_raft_Step hb0 γ rn id rs r ml st γd Hst Hterm Hflw HtrG Htcb Hfit.le

/-- **`r.Step(m)` on a network message, in both modes** (`node.run`'s `recvc` arm): `wp_rn_raft_Step_net`
untraced; traced, `netP`'s gate (`netGate`) gives a `TrRcv` type and the traced step's facts
(`wp_rn_raft_Step_net_tr`), whose post reads as the untraced one's (no `MsgSnap`). -/
theorem wp_rn_raft_Step_net_g (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (hb0 : stepBundle_traced.statement (GF := GF) (hG := hG))
    (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : Loc) (ml : Loc) (st : MsgSt)
    (Hok : NetMsgOk id st)
    (Hmtc : uint.Z st.msg.Term' ≤ uint.Z rs.tc)
    (Htn : st.msg.Type' = MsgTimeoutNow →
      max (uint.Z rs.term) (uint.Z st.msg.Term') + 1 ≤ uint.Z rs.tc)
    (Hflw : rs.flw = false)
    (Htr : γ.reTrace ≠ none → uint.Z rs.tc + 1 < traceNumBound ∧ traceReadyFits GF γ) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        ownRawNode γ rn id rs ∗ rn.[RawNode, go!"raft"] ↦□ r ∗
        msgIn ml DFrac.discard st ∗
        □ (⌜st.msg.Type' = MsgTransferLeader ∧ st.msg.Term' ≠ W64 0⌝ -∗
          isLeader γ id st.msg.Term') ∗
        □ (∀ ty, ⌜mtypeOf st.msg.Type' = some ty⌝ -∗ ⌜ty ≠ .snap⌝ -∗
          isMessage γ (absMsg ty st.msg st.ents st.ctx)) ∗
        □ (⌜st.msg.Type' = MsgSnap⌝ -∗
           ∃ (sv : SnapshotM) (scfg : CSLists),
             ⌜st.snap = some sv ∧ scfg = sv.Metadata'.ConfState'.lists ∧
               uint.Z sv.Metadata'.Index' < 2^61⌝ ∗
             isMessageC γ (absSnap st.msg sv scfg) ∗ snapDataOk γ sv.Metadata'.Index' sv.Data' ∗
             snapLocal γ id sv.Metadata'.Index') ∗
        rdCred γ (if st.msg.Type' = MsgReadIndex then 1 else 0) ∗ £ 1 ∗ netGate γ st }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (t : w64), RET #err;
        ownRawNode γ rn id
          { rs with term := t, psnap := rs.psnap || decide (st.msg.Type' = MsgSnap) } ∗
        ⌜uint.Z rs.term ≤ uint.Z t ∧ uint.Z t ≤ uint.Z rs.tc ∧
          (st.msg.Type' ≠ MsgPreVoteResp →
            uint.Z t ≤ max (uint.Z rs.term) (uint.Z st.msg.Term') +
              (if st.msg.Type' = MsgTimeoutNow then 1 else 0))⌝ }} := by
  cases HtrG : γ.reTrace with
  | none =>
    iintro %Φ ⟨#Hpkg, Hrn, #Hr, Hm, #Hxf, #Hmsg, #Hsnap, Hcred, Hlc, -⟩ HΦ
    iapply wp_rn_raft_Step_net wp_raft_Step γ rn id rs r ml st Hok Hmtc Htn Hflw HtrG
      $$ [$Hpkg $Hrn $Hr $Hm $Hxf $Hmsg $Hsnap $Hcred $Hlc]
    iexact HΦ
  | some γd =>
    obtain ⟨Htcb, Hfit⟩ := Htr (by rw [HtrG]; simp)
    iintro %Φ ⟨#Hpkg, Hrn, #Hr, Hm, #Hxf, #Hmsg, #Hsnap, Hcred, Hlc, Hg⟩ HΦ
    imod ownRawNode_trNoLoan γ rn id rs γd HtrG $$ Hrn with ⟨%Hfacts, Hrn⟩
    unfold netGate
    rw [HtrG]
    -- the gate: a traced network type with its token, its sender's facts and its sender a voter, or
    -- `MsgUnreachable`
    ihave Hx : iprop(⌜TrRcv st.msg.Type'⌝ ∗ recvTokOf γd st.msg st.ents st.ctx ∗
        □ (∀ ty : MsgType, ⌜mtypeOf st.msg.Type' = some ty ∧ ty.traced = true⌝ -∗
          isMessageC γ (absMsg ty st.msg st.ents st.ctx)) ∗
        ⌜(∀ ty, mtypeOf st.msg.Type' = some ty → MsgTrOk γ (absMsg ty st.msg st.ents st.ctx)) ∧
          TrRecvShape st.msg st.ents⌝ ∗
        □ (⌜st.msg.Type' = MsgAppResp⌝ -∗ ∃ tn : TraceNames, traceDir γd tn ∗
          ⌜st.msg.From' ∈ tn.voters⌝)) $$ [Hg]
    · icases Hg with (⟨%Hn, Ht, ⟨%src, #Hraft⟩, #Hfr⟩ | %Hu)
      · icases isRaftMsg_trRecv γ src st $$ Hraft with ⟨#Hmc, %Htrok, -, %Hshape⟩
        iframe Ht Hmc
        isplitr; · ipureintro; exact .inl Hn
        isplitr; · ipureintro; exact ⟨Htrok, Hshape (by rw [HtrG]; rfl)⟩
        imodintro; iintro %h
        iunfold trFromOk at Hfr
        icases Hfr with ⟨%tn, #Hd, %Hin⟩
        iexists tn; iframe Hd; ipureintro; exact Hin h
      · have Hmt : mtypeOf st.msg.Type' = none := by rw [Hu]; rfl
        isplitr; · ipureintro; exact .inr Hu
        isplitl
        · iapply recvTokOf_untyped γd st.msg st.ents st.ctx Hmt
        isplitr
        · imodintro; iintro %ty %h; rw [Hmt] at h; cases h.1
        isplitr
        · ipureintro
          refine ⟨fun ty h => (by rw [Hmt] at h; cases h), fun h => ?_, fun h => ?_, fun h => ?_,
            fun ty h => (by rw [Hmt] at h; cases h)⟩
          · rw [Hu] at h; simp [MsgUnreachable, MsgHeartbeat] at h
          · rw [Hu] at h; simp [MsgUnreachable, MsgHeartbeatResp] at h
          · exfalso
            rcases h with h | h | h <;> rw [Hu] at h <;> simp [MsgUnreachable, MsgVote, MsgApp, MsgHeartbeat] at h
        imodintro; iintro %h; rw [Hu] at h; simp [MsgUnreachable, MsgAppResp] at h
    icases Hx with ⟨%Hnt, Htok, #Hmc, %Hrf, #Hfr⟩
    have HnS : st.msg.Type' ≠ MsgSnap := TrRcv.ne Hnt ⟨by decide, by decide, by decide, by decide,
      by decide, by decide⟩ (by decide)
    have HnT : st.msg.Type' ≠ MsgTimeoutNow := TrRcv.ne Hnt ⟨by decide, by decide, by decide, by decide,
      by decide, by decide⟩ (by decide)
    iapply wp_rn_raft_Step_net_tr wp_raft_Step hb0 γ rn id rs r ml st γd Hok Hnt Hmtc Hflw HtrG Htcb Hfit.le
      Hfacts.2 $$ [$Hpkg $Hrn $Hr $Hm $Hmsg $Hcred $Hlc $Htok $Hmc $Hfr]
    · ipureintro; exact Hrf
    iintro !> %err %t ⟨Hrn, %Ht⟩
    iapply HΦ $$ %err %t
    rw [decide_eq_false HnS, Bool.or_false]
    iframe Hrn
    ipureintro
    refine ⟨Ht.1, Ht.2.1, fun _ => ?_⟩
    rw [ite_eq_right HnT]; omega

-- (merge of `trace-check`) `raft.applyConfChange.spec_of_tracedSpec` is `TracedApplyConfChange.lean`'s.

/-- `fwdP`'s gate, as a gated pure fact. -/
theorem fwdGate_pure (ρ : RaftNames) (st : MsgSt) :
    fwdGate (GF := GF) ρ st ⊢ ⌜ρ.reTrace ≠ none → ∀ e ∈ st.ents, e.Type' = EntryNormal⌝ := by
  unfold fwdGate gateTr
  cases ρ.reTrace with
  | none => iintro _; ipureintro; intro h; exact absurd rfl h
  | some _ => iintro %H; ipureintro; intro _; exact H

end lemmas

end EtcdGrove
end Perennial
