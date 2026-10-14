/- Lean-first (no Rocq counterpart), 2026-10-13: reconfiguration stage D. -/
module

public import Spec.go_etcd_io.raft.v3.RawNode__ApplyConfChange
public import Spec.go_etcd_io.raft.v3.raft__applyConfChange
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChange__AsV2
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__AsV2
-- `rawNode_applyCC_reseal`
public import Proof.go_etcd_io.raft.v3.InvNodeRun
public import Proof.go_etcd_io.raft.v3.InvRawnodeC

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

/-- The dynamic model's reading of `ApplyCCOkC c'` (2026-10-14, stage B7 part 2): at a ghost part
over `c'`, a non-leader takes no step, a leader that stays a voter takes `reMatch`, `commit` by a
joint quorum of `c'` and `sendApps` (an `MsgApp` carrying its commit index, `ReplSends`), and a
removed or demoted leader takes `reMatch` and steps down (`StepR.stepDown`, with
`StepDownOnRemoval`). `applyCCOkC_step`'s `StepR` version: `StepR` has the step-down. -/
theorem applyCCOkC_stepR {Adm : List raftpb.Entry → CCState → Prop} {dec : CCDec} (c' : CfgM)
    (id : w64) (s s' : NState) (g : RGh) (H : ApplyCCOkC c' id s s') (hc : g.cfg.cfg = c') :
    StepR Adm dec id (rOf s g) [] (rOf s' g) := by
  obtain ⟨prs, pvs, -, Hmk, Hsw⟩ := H
  unfold SwitchOkC at Hsw
  by_cases Hl : s.role = .leader
  · rw [if_pos (show ({ s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id } :
        NState).role = .leader from Hl)] at Hsw
    have Hpl : (toPState s).role = .leader := by simp [toPState, Hl, proleRole]
    -- the new `Progress` values
    have H1 : StepCF c' id (toPState s) []
        (toPState { s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id }) := by
      have e : toPState { s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id } =
          { toPState s with matched := prvalsMatch pvs } := by simp [toPState, Hl]
      rw [e]
      refine .reMatch _ _ Hpl (fun v i hv => ?_)
      simp only [prvalsMatch, GMap.lookup_fmap'] at hv
      cases hp : pvs !! v with
      | none => rw [hp] at hv; cases hv
      | some p' =>
        rw [hp] at hv
        simp only [Option.map_some, Option.some.injEq] at hv
        subst hv
        rcases Hmk v p' hp with h0 | ⟨p, hp0, hm⟩
        · exact .inl h0
        · right
          simp [toPState, Hl, prvalsMatch, GMap.lookup_fmap', hp0, hm]
    have Hz := rOf_pci_zero s g
    by_cases Hv : id ∈ c'.voters
    · rw [if_pos Hv] at Hsw
      obtain ⟨c, ms, pvs2, lt', Hc, Hms, Hmm, rfl⟩ := Hsw
      generalize Hs1 : ({ s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id } :
        NState) = s1 at H1 Hc Hms Hmm
      have Hl1 : s1.role = .leader := by rw [← Hs1]; exact Hl
      have Hpl1 : (toPState s1).role = .leader := by simp [toPState, Hl1, proleRole]
      -- the commit
      have H2 : StepCF c' id (toPState s1) []
          (toPState { s1 with logst := { s1.logst with committed := c } }) := by
        rcases Hc with rfl | ⟨Hlt, Hle, Htm, Hq⟩
        · have e : ({ s1 with logst := { s1.logst with committed := s1.logst.committed } } : NState)
              = s1 := by cases s1; rfl
          rw [e]; exact .refl _
        · have e : toPState { s1 with logst := { s1.logst with committed := c } } =
              { toPState s1 with commit := c } := by simp [toPState, Hl1]
          rw [e]
          exact .commit _ c Hpl1 Hlt Hle Htm Hq
      generalize Hs2 : ({ s1 with logst := { s1.logst with committed := c } } : NState) = s2
        at H2 Hms
      have Hl2 : s2.role = .leader := by rw [← Hs2]; exact Hl1
      -- the appends
      have H3 : StepCF c' id (toPState s2) []
          (toPState { sendMsgs s2 ms with prvals := pvs2, lt := lt' }) := by
        have e : toPState { sendMsgs s2 ms with prvals := pvs2, lt := lt' } =
            toPState { sendMsgs s2 ms with prvals := pvs2 } := rfl
        rw [e, toPState_prvals (sendMsgs s2 ms) pvs2 (fun _ => by
          rw [Hmm]; rw [← Hs2]; rfl), toPState_sendMsgs]
        exact .sendApps _ ms (by simp [toPState, Hl2, proleRole]) Hms.replOk
          (fun m hm => (Hms m hm).2)
      have HF := StepCF.trans _ _ _ _ _ H1 (StepCF.trans _ _ _ _ _ H2 H3)
      have HR := HF.toR (Adm := Adm) (dec := dec) (rOf s g) rfl hc Hz
      have Hfr : RFrame s { sendMsgs s2 ms with prvals := pvs2, lt := lt' } := by
        refine ⟨?_, ?_, fun _ => ⟨Hl, ?_⟩⟩ <;> (rw [← Hs2, ← Hs1]; try rfl)
      rw [rOf_frame _ _ g Hfr]
      exact HR
    · -- removed or demoted: `reMatch`, then the step-down
      rw [if_neg Hv] at Hsw
      obtain ⟨pvs', rfl⟩ := Hsw
      generalize Hs1 : ({ s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id } :
        NState) = s1 at H1 ⊢
      have HR1 := H1.toR (Adm := Adm) (dec := dec) (rOf s g) rfl hc Hz
      have Hfr1 : RFrame s s1 := by
        refine ⟨?_, ?_, fun _ => ⟨Hl, ?_⟩⟩ <;> (rw [← Hs1]; try rfl)
      rw [← rOf_frame _ _ g Hfr1] at HR1
      have Hl1 : s1.role = .leader := by rw [← Hs1]; exact Hl
      have Hrl : (rOf s1 g).p.role = .leader := by simp [rOf, toPState, Hl1, proleRole]
      have HR2 := StepR.stepDown (Adm := Adm) (dec := dec) (id := id) (rOf s1 g) Hrl
        (by simp only [rOf]; rw [hc]; exact Hv)
      have Ht1 : s1.term = s.term := by rw [← Hs1]
      have e : RState.mk (pbecomeFollower (rOf s1 g).p (rOf s1 g).p.term (W64 0))
          (rOf s1 g).applied (W64 0) (rOf s1 g).snap (rOf s1 g).cidx (rOf s1 g).cfg (rOf s1 g).fp =
          rOf ({ becomeFollower s1 s1.term (W64 0) with prvals := pvs' } : NState) g := by
        have h1 := toPState_prvals (becomeFollower s1 s1.term (W64 0)) pvs'
          (fun h => by simp [becomeFollower] at h)
        have h2 := toPState_becomeFollower s1 s1.term (W64 0)
        unfold rOf
        rw [h1, h2]
        simp [pciR, becomeFollower, toPState, resetTo0, resetTo]
      rw [e] at HR2
      exact .trans _ _ _ _ _ HR1 HR2
  · rw [if_neg (show ¬ ({ s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id } :
        NState).role = .leader from Hl)] at Hsw
    subst Hsw
    have e : rOf { s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id } g =
        rOf s g := by
      unfold rOf pciR
      simp [toPState, Hl]
    rw [e]
    exact .refl _

/-- What `ApplyCCOkC` keeps of the physical state, the removed leader's step-down included. -/
theorem applyCCOkC_frame {c' : CfgM} {id : w64} {s s' : NState} (H : ApplyCCOkC c' id s s')
    (Hwf : NStateWf s) :
    NStateWf s' ∧ s'.term = s.term ∧ s'.prevote = s.prevote ∧ s'.gh = s.gh ∧
      s'.logst = { s.logst with committed := s'.logst.committed } ∧
      uint.Z s.logst.committed ≤ uint.Z s'.logst.committed := by
  rcases applyCCOkC_step c' id s s' H with ⟨-, Hr, Hsf, Htk, Ht, Hpv, Hg, Hl, Hc⟩ | ⟨Hl, Hv, -⟩
  · exact ⟨⟨by rw [Hsf, Hr]; exact Hwf.1, by rw [Htk]; exact Hwf.2⟩, Ht, Hpv, Hg, Hl, Hc⟩
  · obtain ⟨prs, pvs, -, -, Hsw⟩ := H
    unfold SwitchOkC at Hsw
    rw [if_pos (show ({ s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id } :
        NState).role = .leader from Hl), if_neg Hv] at Hsw
    obtain ⟨pvs', rfl⟩ := Hsw
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [becomeFollower, resetTo0, resetTo, stepFuncOf]

/-- `ccStepB`'s answer is `ccApplyM`'s, of fewer than `2^62` tracked ids. -/
theorem ccStepB_some {op : CCOp} {s s' : CCState} (h : ccStepB op s = some s') :
    ccApplyM op.1 op.2 s = some s' ∧ GMap.size s'.cfg.ids < 2 ^ 62 := by
  unfold ccStepB at h
  cases h1 : ccApplyM op.1 op.2 s with
  | none => rw [h1] at h; cases h
  | some s2 =>
    rw [h1] at h
    simp only [Option.bind_some] at h
    split at h
    · cases h; exact ⟨rfl, by assumption⟩
    · cases h


/-- `r.applyConfChange(cc)` at a dynamic node (2026-10-14, stage B7 part 2): the configuration
takes the next conf entry's change (`StepR.applyConf`), then `switchToConfig`'s effect
(`applyCCOkC_stepR`, a removed leader's step-down included); the node's ghost state follows
(`ownRaftGhostR_stepR`), and `ownRawNode` is re-sealed at the new configuration and
configuration index. The node is no candidate (a candidate has no conf entry to apply: `RInv`'s
`cand`), no pre-candidate (pre-vote off), and a removed leader steps down (`sdrOk`). -/
theorem wp_applyConf_dyn
    (wp_raft_applyConfChange : raft.applyConfChange.spec (GF := GF) (hG := hG))
    (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (dec : CCDec) (c0 : CCState)
    (h0 : CfgOk c0) (h1 : CCGood c0) (hm : rs.mode = .dyn dec c0 h0 h1) (o : CCMsg) (k : Nat)
    (e : raftpb.Entry) (cs' : CCState) (Hpre : DynCCPre dec rs o k e cs')
    (v2 : raftpb.ConfChangeV2) (ccs : List raftpb.ConfChangeSingle) (dq : DFrac)
    (Hv : (v2.Transition', ccs) = ccV2Of o)
    (s : NState) (cf : CfgM) (fp : List raftpb.Entry) (rnv : RawNode) (sv : SoftState)
    (steps : List raftpb.Message)
    (Hwf : NStateWf s) (Hin : rs.mode = .static → id ∈ γ.reCfg) (Hasync : rnv.asyncStorageWrites' = false)
    (Hdlen : rs.delivered.length = (uint.Z s.logst.applying).toNat)
    (Hunp : rs.unpersisted = s.logst.unpersisted) (Hsnap : s.logst.snap = none)
    (Hstok : StepsOk s rs.steps)
    (Htrm : rs.term = s.term) (Hstor : rs.storage = s.logst.storage)
    (Hpvoff : s.prevote = false) (Hrs_out : rs.outlb = s.gh.outlb)
    (Hrs_unst : rs.unst = s.gh.unst) (Hrs_clb : uint.Z rs.clb ≤ uint.Z s.logst.committed) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        rawNodeOwn rn rnv ∗ ownRaftPhysCV cf cf.voters rnv.raft' id s ∗
        ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp⟩) cf id s ∗
        sdrOk rnv.raft' rs.mode ∗ rnv.prevSoftSt' ↦□ sv ∗ rnv.stepsOnAdvance' ↦* steps ∗
        ownSliceCap raftpb.Message rnv.stepsOnAdvance' (DFrac.own 1) ∗
        ([∗list] _k ↦ m;p ∈ steps;rs.steps, pendingRel γ id m p) ∗
        ([∗list] _k ↦ m;p ∈ steps;rs.steps, pendingOwn m p) ∗
        isCommitted γ rs.delivered ∗ storedRecs γ s.logst.prev s.logst.stored ∗
        v2.Changes' ↦*{dq} ccs }}
      (App (Val (rnv.raft' @!! go.GoType.PointerType raft.ty @!! go!"applyConfChange")) (Val #v2))
    {{ (cs : raftpb.ConfState) (xs os ls lns : List w64), RET #cs;
        ownRawNode γ rn id { rs with cfg := cs', capplied := k + 1 } ∗
        v2.Changes' ↦*{dq} ccs ∗
        cs.Voters' ↦* xs ∗ cs.VotersOutgoing' ↦* os ∗ cs.Learners' ↦* ls ∗
        cs.LearnersNext' ↦* lns ∗
        ⌜xs ≡ₚ elements cs'.cfg.incoming ∧ os ≡ₚ elements cs'.cfg.outgoing ∧
          ls ≡ₚ elements cs'.cfg.learners ∧ lns ≡ₚ elements cs'.cfg.learnersNext ∧
          cs.AutoLeave' = cs'.cfg.autoLeave⌝ }} := by
  obtain ⟨Hk1, Hk2, Hke, Hconf, Hnoc, Hdec, Hstep, Hal'⟩ := Hpre
  iintro %Φ ⟨#Hpkg, Hrn, Hphys, Hghost, #Hsdrf, #Hsoft, Hsteps, Hcap, #Hpend, Hpown, #Hdeliv,
    #Hstrecs, Hch⟩ HΦ
  let g : RGh := ⟨rs.capplied, rs.cfg, fp⟩
  ihave Hghost : ownStepGhost γ (.dyn dec c0 h0 g) cf id s $$ [Hghost]
  · rw [show (GMode.dyn dec c0 h0 g) = rs.mode.toG ⟨rs.capplied, rs.cfg, fp⟩ by rw [hm]; rfl]
    iexact Hghost
  icases ownRaftPhysC_logwf cf rnv.raft' id s $$ Hphys with ⟨%Hlw, Hphys⟩
  icases ownStepGhost_deliv γ dec c0 h0 g cf id s rs.delivered
    (by rw [Hdlen]; have := uint_Z_nonneg s.logst.applying; omega) $$ Hdeliv Hghost
    with ⟨%Hdp, Hghost⟩
  icases (ownStepGhost_dyn γ dec c0 h0 g cf id s).1 $$ Hghost with ⟨%HDc, Hgr⟩
  obtain ⟨HD, Hgc⟩ := HDc
  iunfold ownRaftGhostR at Hgr
  icases Hgr with ⟨Hg, %HI, #Hfr, #Hcamp⟩
  icases (entails_wand (persistent_entails_left (wand_entails
    (ownRaftGhost_logRecs (GF := GF) γ id (rOf s g).p true)))) $$ Hg with ⟨Hg, %-, #Hlr⟩
  icases ownRaftPhysC_preFacts cf rnv.raft' id s Hpvoff $$ Hphys with ⟨%Hpf, Hphys⟩
  icases ownRaftPhysC_sdr cf rnv.raft' id s $$ Hphys with ⟨#Hsd, Hphys⟩
  ihave #Hsdrf' := Hsdrf
  iunfold sdrOk at Hsdrf'
  icases Hsdrf' with ⟨%b, #Hb, %Hbt⟩
  icombine Hb Hsd gives %Hbs
  have Hsdr : s.sdr = true := by rw [← Hbs]; exact Hbt (by rw [hm]; rfl)
  -- the entry, in the node's full log
  have Hfull_k : (rOf s g).full[k]? = some e := by
    obtain ⟨t, ht⟩ := Hdp
    rw [← ht, List.getElem?_append_left Hk2]; exact Hke
  have Htake : (rOf s g).full.take k = rs.delivered.take k := by
    obtain ⟨t, ht⟩ := Hdp
    rw [← ht, List.take_append_of_le_length (Nat.le_of_lt Hk2)]
  have Hkc : k < uint.nat s.logst.committed := by
    have := uint_nat_eq s.logst.committed; have := uint_nat_eq s.logst.applying; omega
  have Hnoc' : NoConfIn (rOf s g).full g.cidx k :=
    NoConfIn_prefix Hdp (Nat.le_of_lt Hk2) Hnoc
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
  rw [← Hv] at Happ
  imod rdCred_zero_upd (GF := GF) γ with Hcr0
  iapply wp_fupd
  wp_apply +noauto wp_raft_applyConfChange cf rnv.raft' id s v2 ccs dq cs'
      (by rw [Hcfg]; exact Happ) (by have := Hsz; omega) (fun _ _ => Hsdr)
      (fun h => by
        rcases h with h | h
        · exact absurd h Hnc
        · exact absurd h Hpf.1)
    $$ [$Hphys $Hch] as %cs %xs %os %ls %lns %s' ⟨Hphys, Hch, Hvoters, Hos, Hls, Hlns, %Hcs0, %Hok⟩
  -- the ghost step
  let g' : RGh := ⟨k + 1, cs', fp⟩
  have Hadm : AdmS dec c0 (fun l => l = (rOf s g).full.take (k + 1)) ((rOf s g).full.take (k + 1))
      cs' := by
    refine ⟨?_, rfl⟩
    unfold AdmFold
    have H0 := cfgFold_noConf dec c0 Hnoc' Hk1 HI.cfg
    rw [show (rOf s g).full.take (k + 1) = (rOf s g).full.take k ++ [e] by
      rw [List.take_succ, Hfull_k]; rfl, cfgFold_snoc, H0, Option.bind_some]
    unfold entStep
    rw [if_pos Hconf, Htake, Hdec, Option.bind_some]
    exact Hstep
  have HR1 : StepR (AdmS dec c0 (fun l => l = (rOf s g).full.take (k + 1))) dec id (rOf s g) []
      (rOf s g') :=
    StepR.applyConf (rOf s g) k e (ccV2Of o) cs' (by simp [rOf, Hsnap]) Hk1 Hkc Hfull_k Hconf
      Hnoc' (by rw [Htake]; exact Hdec) Hstep Hadm
  have HR2 := applyCCOkC_stepR (Adm := AdmS dec c0 (fun l => l = (rOf s g).full.take (k + 1)))
    (dec := dec) cs'.cfg id s s' g' Hok rfl
  have HR := StepR.trans _ _ _ _ _ HR1 HR2
  ihave #Hrecs : □ ∀ (fp' : List raftpb.Entry), ⌜fp' = (rOf s g).full.take (k + 1)⌝ -∗
      logRecs (GF := GF) γ base0 fp' $$ []
  · ihave #Hfl := logRecs_full γ (rOf s g).p.base (rOf s g).fp (rOf s g).p.log HI.full $$ Hfr Hlr
    imodintro
    iintro %fp' %Hfp'
    subst Hfp'
    rw [show (rOf s g).full = (rOf s g).fp ++ (rOf s g).p.log from rfl]
    iapply logRecs_take γ _ (k + 1) $$ Hfl
  ihave Hgr : ownRaftGhostR γ dec c0 id (rOf s g) $$ [Hg]
  · iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact HI
    iintro %hc; iapply Hcamp; exact hc
  imod ownRaftGhostR_stepR γ dec c0 h0 HD _ id _ _ _ HR $$ Hrecs [] [Hcr0] Hgr with Hgr
  · rw [List.nil_append]
    iapply (BigSepL.bigSepL_nil (Φ := fun _ m => isMessage (GF := GF) γ m)).2
    iempintro
  · rw [List.nil_append, show rdCount ([] : List Msg) = 0 from rfl]; iexact Hcr0
  ihave Hghost : ownStepGhost γ (.dyn dec c0 h0 g') cs'.cfg id s' $$ [Hgr]
  · iapply (ownStepGhost_dyn γ dec c0 h0 g' cs'.cfg id s').2
    iframe Hgr
    ipureintro; exact ⟨HD, rfl⟩
  ihave Hghost : ownStepGhost γ (({ rs with cfg := cs', capplied := k + 1 } : RNState).mode.toG
      ⟨({ rs with cfg := cs', capplied := k + 1 } : RNState).capplied,
       ({ rs with cfg := cs', capplied := k + 1 } : RNState).cfg, fp⟩) cs'.cfg id s' $$ [Hghost]
  · rw [show (({ rs with cfg := cs', capplied := k + 1 } : RNState).mode.toG
        ⟨({ rs with cfg := cs', capplied := k + 1 } : RNState).capplied,
         ({ rs with cfg := cs', capplied := k + 1 } : RNState).cfg, fp⟩) = GMode.dyn dec c0 h0 g' by
      simp only; rw [hm]; rfl]
    iexact Hghost
  obtain ⟨Hwf', Ht', Hpv', Hgh', Hls', Hc'⟩ := applyCCOkC_frame Hok Hwf
  ihave #Hstr' := storedRecs_eq γ _ s'.logst.prev _ s'.logst.stored (by rw [Hls'])
    (by rw [Hls']) $$ Hstrecs
  imodintro
  iapply HΦ $$ %cs %xs %os %ls %lns
  iframe Hch Hvoters Hos Hls Hlns
  isplitl
  · iapply ownRawNode_intro γ rn id { rs with cfg := cs', capplied := k + 1 } s' cs'.cfg fp rnv sv
      steps Hwf' (fun h => by simp only at h; rw [hm] at h; cases h) Hal' Hasync
      (by rw [Hls']; exact Hdlen) (by rw [Hls']; exact Hunp) (by rw [Hls']; exact Hsnap)
      (stepsOk_mono s s' _ Ht' ⟨by rw [Hls'], by rw [Hls']⟩ Hc' (by rw [Hls']) Hpv' Hstok)
      (by rw [Ht']; exact Htrm) (by rw [Hls']; exact Hstor) (by rw [Hpv']; exact Hpvoff)
      (by rw [Hgh']; exact Hrs_out) (by rw [Hgh']; exact Hrs_unst) (Int.le_trans Hrs_clb Hc')
      $$ Hrn Hphys Hghost Hsdrf Hsoft Hsteps Hcap Hpend Hpown Hdeliv Hstr'
  ipureintro; exact Hcs0

theorem RawNode.ApplyConfChange.wp_proof
    (wp_ConfChange_AsV2 : raftpb.ConfChange.AsV2.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_AsV2 : raftpb.ConfChangeV2.AsV2.spec (GF := GF) (hG := hG))
    (wp_raft_applyConfChange : raft.applyConfChange.spec (GF := GF) (hG := hG)) :
    RawNode.ApplyConfChange.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs c o dq k0 e0 cs0 Hap0 Hdyn
  wp_start as H
  iNamed H
  iNamed Hrn
  have Hmode : (∃ dec c0 h0 h1, rs.mode = .dyn dec c0 h0 h1) ∨ rs.mode = .static := by
    cases rs.mode with
    | static => exact .inr rfl
    | dyn dec c0 h0 h1 => exact .inl ⟨dec, c0, h0, h1, rfl⟩
  rcases Hmode with ⟨dec, c0, h0, h1, hm⟩ | hm
  · have Hpre := Hdyn dec c0 h0 h1 hm
    rcases o with m | m
    · simp only [ownCCI, ownCCV1]
      icases Hc with ⟨%v, %Hcv, %Hvm, Hctx⟩
      subst Hcv
      wp_auto
      wp_apply wp_ConfChange_AsV2 as %v2 ⟨%Hv2, Hch⟩
      obtain ⟨Hty, Hnid, Hid⟩ := Hvm
      wp_apply wp_applyConf_dyn wp_raft_applyConfChange γ rn id rs dec c0 h0 h1 hm (.v1 m) k0 e0
          cs0 Hpre v2 _ (DFrac.own 1) (by rw [Hv2.1, Hty, Hnid]; rfl) s cf fp rnv sv steps Hwf Hin
          Hasync Hdlen Hunp Hsnap Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb
        $$ [$Hrn $Hphys $Hghost $Hsdrf $Hsoft $Hsteps $Hsteps_cap $Hpend $Hpown $Hdeliv $Hstrecs
          $Hch] as %cs %xs %os %ls %lns ⟨Hrn, -, Hvoters, Hos, Hls, Hlns, %Hcs0⟩
      try wp_auto
      iapply HΦ
      simp only [named]
      iframe Hvoters Hls
      isplitl [Hctx]
      · try simp only [ownCCI, ownCCV1]
        iexists v
        isplitr
        · ipureintro; rfl
        iframe Hctx
        ipureintro; exact ⟨Hty, Hnid, Hid⟩
      iframe
      iright
      isplitr
      · ipureintro; rw [hm]; rfl
      iframe Hrn
      iexists os, lns
      iframe Hos Hlns
      ipureintro; exact Hcs0
    · simp only [ownCCI, ownCCV2]
      icases Hc with ⟨%v, %Hcv, %Htr, Hch, Hctx⟩
      subst Hcv
      wp_auto
      wp_apply wp_ConfChangeV2_AsV2
      wp_apply wp_applyConf_dyn wp_raft_applyConfChange γ rn id rs dec c0 h0 h1 hm (.v2 m) k0 e0
          cs0 Hpre v _ dq (by rw [Htr]; rfl) s cf fp rnv sv steps Hwf Hin
          Hasync Hdlen Hunp Hsnap Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb
        $$ [$Hrn $Hphys $Hghost $Hsdrf $Hsoft $Hsteps $Hsteps_cap $Hpend $Hpown $Hdeliv $Hstrecs
          $Hch] as %cs %xs %os %ls %lns ⟨Hrn, Hch, Hvoters, Hos, Hls, Hlns, %Hcs0⟩
      try wp_auto
      iapply HΦ
      simp only [named]
      iframe Hvoters Hls
      isplitl [Hch Hctx]
      · try simp only [ownCCI, ownCCV2]
        iexists v
        isplitr
        · ipureintro; rfl
        iframe Hch Hctx
        ipureintro; exact Htr
      iframe
      iright
      isplitr
      · ipureintro; rw [hm]; rfl
      iframe Hrn
      iexists os, lns
      iframe Hos Hlns
      ipureintro; exact Hcs0
  have Hm := hm
  have Hap0 := Hap0 hm
  icases ownRawNode_static_open γ rs Hm fp cf rnv.raft' id s $$ Hphys Hghost with ⟨Hphys, Hghost⟩
  have Hrel : NStateRel s (toPState s) := ⟨rfl, Hwf⟩
  have Hin := Hin Hm
  rcases o with m | m
  · -- a `ConfChange`: `AsV2` makes the one change
    simp only [ownCCI, ownCCV1]
    icases Hc with ⟨%v, %Hcv, %Hvm, Hctx⟩
    subst Hcv
    wp_auto
    wp_apply wp_ConfChange_AsV2 as %v2 ⟨%Hv2, Hch⟩
    obtain ⟨Hty, Hnid, Hid⟩ := Hvm
    have Hap : CCApplies γ.reCfg id v2.Transition' [({ Type' := v.Type', NodeId' := v.NodeId' } :
        raftpb.ConfChangeSingle)] := by
      rw [Hv2.1, Hty, Hnid]; exact Hap0
    by_cases Hsh : CCShrink γ.reCfg (ccV2Of (.v1 m)).1 (ccV2Of (.v1 m)).2
    · -- a shrinking change: as in stage L
      have Hn0 : CCShrink γ.reCfg v2.Transition' [({ Type' := v.Type', NodeId' := v.NodeId' } :
          raftpb.ConfChangeSingle)] := by
        rw [Hv2.1, Hty, Hnid]; exact Hsh
      icases ownRaftPhys_progress_dom γ.reCfg rnv.raft' id s $$ Hphys with ⟨%Hsub, Hphys⟩
      icases ownRaftPhys_progress_size γ.reCfg rnv.raft' id s $$ Hphys with ⟨%Hsz, Hphys⟩
      obtain ⟨lrn', Hd', Hsz', Hn⟩ := applyCC_of_shrink γ.reCfg s.progress _ _ Hn0 Hsub Hsz
      wp_apply +noauto (raft.applyConfChange.spec_simple wp_raft_applyConfChange) γ.reCfg rnv.raft' id s v2 _ (DFrac.own 1) lrn' Hd'
        Hsz' Hn
        $$ [$Hphys $Hch] as %cs %xs %ls %s' ⟨Hphys, -, Hvoters, Hls, %Hcs0, %Hok⟩
      imod rawNode_applyCC_reseal γ rn id rs s s' _ rnv sv steps Hm Hrel Hin Hasync Hdlen Hunp
        Hsnap Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hok
        $$ Hrn Hphys Hghost Hsdrf Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstrecs with Hrn
      try wp_auto
      iapply HΦ
      simp only [named]
      iframe Hvoters Hls
      isplitl [Hctx]
      · try simp only [ownCCI, ownCCV1]
        iexists v
        isplitr
        · ipureintro; rfl
        iframe Hctx
        ipureintro; exact ⟨Hty, Hnid, Hid⟩
      iframe
      ileft
      isplitr
      · ipureintro; exact Hm
      ileft
      iframe Hrn
      ipureintro
      exact ⟨Hsh, Hcs0.1, fun k hk => Hd' k ((GMap.elem_of_elements _ _).1 (Hcs0.2.1.mem_iff.1 hk)),
        Hcs0.2.2⟩
    · -- any other change: detached, at the new configuration
      icases ownRaftPhys_progress_dom γ.reCfg rnv.raft' id s $$ Hphys with ⟨%Hsub, Hphys⟩
      icases ownRaftPhys_progress_size γ.reCfg rnv.raft' id s $$ Hphys with ⟨%Hsz, Hphys⟩
      have HdL : ∀ k, k ∈ domSet s.progress \ γ.reCfg → k ∉ γ.reCfg :=
        fun k hk => ((GMap.elem_of_difference _ _ _).1 hk).2
      have HU : γ.reCfg ∪ (domSet s.progress \ γ.reCfg) = domSet s.progress := by
        apply GMap.set_eq; intro k
        rw [GMap.elem_of_union, GMap.elem_of_difference]
        constructor
        · rintro (h | ⟨h, -⟩)
          · exact (GMap.elem_of_subseteq _ _).1 Hsub k h
          · exact h
        · intro h
          by_cases hk : k ∈ γ.reCfg
          · exact .inl hk
          · exact .inr ⟨h, hk⟩
      have HszL : (GMap.size (γ.reCfg ∪ (domSet s.progress \ γ.reCfg)) : Int) ≤ 2 ^ 62 := by
        rw [HU, GMap.size_dom]; exact Hsz
      obtain ⟨c', Happ, Hsz', Hin'⟩ := Hap _ HdL HszL
      have Happ' := Happ
      rw [Hv2.1, Hty, Hnid] at Happ'
      ihave Hphys := ownRaftPhys_toC' $$ Hphys
      wp_apply +noauto wp_raft_applyConfChange (CfgM.simple γ.reCfg (domSet s.progress \ γ.reCfg))
          rnv.raft' id s v2 _ (DFrac.own 1) c' (by rw [cfgStateC_simple]; exact Happ) Hsz'
          (fun _ h => absurd Hin' h) (fun _ => Hin')
        $$ [$Hphys $Hch] as %cs %xs %os %ls %lns %s' ⟨Hphys, Hch, Hvoters, Hos, Hls, Hlns, %Hcs0, %Hok⟩
      try wp_auto
      iapply HΦ
      simp only [named]
      iframe Hvoters Hls
      isplitl [Hctx]
      · try simp only [ownCCI, ownCCV1]
        iexists v
        isplitr
        · ipureintro; rfl
        iframe Hctx
        ipureintro; exact ⟨Hty, Hnid, Hid⟩
      iframe
      ileft
      isplitr
      · ipureintro; exact Hm
      iright
      isplitr
      · ipureintro; exact Hsh
      iexists (domSet s.progress \ γ.reCfg), c', s, s', os, lns
      iframe Hos Hlns
      isplitl [Hrn Hphys Hsteps Hsteps_cap Hpown]
      · iapply ownRawNodeC_intro c'.cfg rn id s' rnv sv steps rs.steps Hasync
          $$ Hrn Hphys Hsoft Hsteps Hsteps_cap Hpown
      ipureintro
      exact ⟨HdL, Happ', Hcs0.1, Hcs0.2.1, Hcs0.2.2.1, Hcs0.2.2.2.1, Hcs0.2.2.2.2, Hok⟩
  · -- a `ConfChangeV2`: `AsV2` is itself
    simp only [ownCCI, ownCCV2]
    icases Hc with ⟨%v, %Hcv, %Htr, Hch, Hctx⟩
    subst Hcv
    wp_auto
    wp_apply wp_ConfChangeV2_AsV2
    have Hap : CCApplies γ.reCfg id v.Transition' m.changes := by rw [Htr]; exact Hap0
    by_cases Hsh : CCShrink γ.reCfg (ccV2Of (.v2 m)).1 (ccV2Of (.v2 m)).2
    · have Hn0 : CCShrink γ.reCfg v.Transition' m.changes := by rw [Htr]; exact Hsh
      icases ownRaftPhys_progress_dom γ.reCfg rnv.raft' id s $$ Hphys with ⟨%Hsub, Hphys⟩
      icases ownRaftPhys_progress_size γ.reCfg rnv.raft' id s $$ Hphys with ⟨%Hsz, Hphys⟩
      obtain ⟨lrn', Hd', Hsz', Hn⟩ := applyCC_of_shrink γ.reCfg s.progress _ _ Hn0 Hsub Hsz
      wp_apply +noauto (raft.applyConfChange.spec_simple wp_raft_applyConfChange) γ.reCfg rnv.raft' id s v _ dq lrn' Hd' Hsz' Hn
        $$ [$Hphys $Hch] as %cs %xs %ls %s' ⟨Hphys, Hch, Hvoters, Hls, %Hcs0, %Hok⟩
      imod rawNode_applyCC_reseal γ rn id rs s s' _ rnv sv steps Hm Hrel Hin Hasync Hdlen Hunp
        Hsnap Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hok
        $$ Hrn Hphys Hghost Hsdrf Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstrecs with Hrn
      try wp_auto
      iapply HΦ
      simp only [named]
      iframe Hvoters Hls
      isplitl [Hch Hctx]
      · try simp only [ownCCI, ownCCV2]
        iexists v
        isplitr
        · ipureintro; rfl
        iframe Hch Hctx
        ipureintro; exact Htr
      iframe
      ileft
      isplitr
      · ipureintro; exact Hm
      ileft
      iframe Hrn
      ipureintro
      exact ⟨Hsh, Hcs0.1, fun k hk => Hd' k ((GMap.elem_of_elements _ _).1 (Hcs0.2.1.mem_iff.1 hk)),
        Hcs0.2.2⟩
    · -- any other change: detached, at the new configuration
      icases ownRaftPhys_progress_dom γ.reCfg rnv.raft' id s $$ Hphys with ⟨%Hsub, Hphys⟩
      icases ownRaftPhys_progress_size γ.reCfg rnv.raft' id s $$ Hphys with ⟨%Hsz, Hphys⟩
      have HdL : ∀ k, k ∈ domSet s.progress \ γ.reCfg → k ∉ γ.reCfg :=
        fun k hk => ((GMap.elem_of_difference _ _ _).1 hk).2
      have HU : γ.reCfg ∪ (domSet s.progress \ γ.reCfg) = domSet s.progress := by
        apply GMap.set_eq; intro k
        rw [GMap.elem_of_union, GMap.elem_of_difference]
        constructor
        · rintro (h | ⟨h, -⟩)
          · exact (GMap.elem_of_subseteq _ _).1 Hsub k h
          · exact h
        · intro h
          by_cases hk : k ∈ γ.reCfg
          · exact .inl hk
          · exact .inr ⟨h, hk⟩
      have HszL : (GMap.size (γ.reCfg ∪ (domSet s.progress \ γ.reCfg)) : Int) ≤ 2 ^ 62 := by
        rw [HU, GMap.size_dom]; exact Hsz
      obtain ⟨c', Happ, Hsz', Hin'⟩ := Hap _ HdL HszL
      have Happ' := Happ
      rw [Htr] at Happ'
      ihave Hphys := ownRaftPhys_toC' $$ Hphys
      wp_apply +noauto wp_raft_applyConfChange (CfgM.simple γ.reCfg (domSet s.progress \ γ.reCfg))
          rnv.raft' id s v _ dq c' (by rw [cfgStateC_simple]; exact Happ) Hsz'
          (fun _ h => absurd Hin' h) (fun _ => Hin')
        $$ [$Hphys $Hch] as %cs %xs %os %ls %lns %s' ⟨Hphys, Hch, Hvoters, Hos, Hls, Hlns, %Hcs0, %Hok⟩
      try wp_auto
      iapply HΦ
      simp only [named]
      iframe Hvoters Hls
      isplitl [Hch Hctx]
      · try simp only [ownCCI, ownCCV2]
        iexists v
        isplitr
        · ipureintro; rfl
        iframe Hch Hctx
        ipureintro; exact Htr
      iframe
      ileft
      isplitr
      · ipureintro; exact Hm
      iright
      isplitr
      · ipureintro; exact Hsh
      iexists (domSet s.progress \ γ.reCfg), c', s, s', os, lns
      iframe Hos Hlns
      isplitl [Hrn Hphys Hsteps Hsteps_cap Hpown]
      · iapply ownRawNodeC_intro c'.cfg rn id s' rnv sv steps rs.steps Hasync
          $$ Hrn Hphys Hsoft Hsteps Hsteps_cap Hpown
      ipureintro
      exact ⟨HdL, Happ', Hcs0.1, Hcs0.2.1, Hcs0.2.2.1, Hcs0.2.2.2.1, Hcs0.2.2.2.2, Hok⟩

end proof

end EtcdGrove
end Perennial
