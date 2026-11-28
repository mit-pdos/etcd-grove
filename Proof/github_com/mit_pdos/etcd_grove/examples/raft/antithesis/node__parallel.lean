/-
Lean-first (no Rocq counterpart). #33 parity B2, driver group E: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__parallel.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__parallel
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.b2i
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.withByRole
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2ParWriteWp
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2Quiet
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2Holds
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2Loop
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1Ext
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MemView
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.RunInMaskB2
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2ParPre
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2ParReqWp
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2Shape

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- `RsView` reads only the view's disk, delivered and unreported committed entries, raft state and
pre-vote flag. -/
theorem rsView_congr {rs : RNState} {v v' : AntSim.NodeView} (h : RsView rs v)
    (hd : v'.dur = v.dur) (hdl : v'.delivered = v.delivered) (hce : v'.ce = v.ce) (hr : v'.r = v.r)
    (hpre : v'.pre = v.pre) : RsView rs v' := by
  unfold RsView AntSim.roleS AntSim.NodeView.ps at *
  rw [hd, hdl, hce, hr, hpre]; exact h

/-- B1's `RsView` is `RsViewB2`'s. -/
theorem rsViewB2_of {md : H.Mode} {rs : RNState} {v : AntSim.NodeView} (h : RsView rs v) :
    RsViewB2 md rs v := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h3, h4, h6, h7, fun _ => ⟨h1, h2, h5, h8⟩⟩

/-- `ViewNormal` reads only the view's full log and cause. -/
theorem viewNormal_congr {v v' : AntSim.NodeView} (h : ViewNormal v) (hr : v'.r.full = v.r.full)
    (hc : v'.cause = v.cause) : ViewNormal v' := by
  unfold ViewNormal at *
  rw [hr, hc]; exact h

instance hsNew_decP (h : HardStateM) : Decidable (HsNew h) := by unfold HsNew; infer_instance

/-- `ReachIn` starts from a view with no committed entries left to report. -/
theorem reachIn_ce {msk : AntSim.SimMask} {R : AntSim.RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {net : List Msg} {xnet : List XMsg} {n : Fin R.N}
    {v : AntSim.NodeView} {r₁ : RState} (h : AntSim.ReachIn msk R dec Adm net xnet n v r₁) :
    v.ce = [] := by
  cases h with
  | stay hI _ => exact hI.2.2.2.1
  | input inp r₁ h0 hI h1 h2 h3 h4 h5 h6 => exact hI.2.2.2.1
  | advance r₁ h1 h2 h3 h4 h5 h6 h7 => exact h3

/-- The view after `parallel`'s `mem` report (`memHstepD`'s), or after a quiet `Ready` (`w = false`,
the view's `told`: `quietPView`). -/
abbrev parMemV (v : AntSim.NodeView) (r₁ : RState) (rd : AntSim.ReadyD) (w : Bool) : AntSim.NodeView :=
  { (v.drainOf r₁ rd) with
    pend := rd.msgs.filter AntSim.isReqM ++ rd.msgs.filter (fun q => !AntSim.isReqM q),
    mems := if w then v.mems ++ [rd.memRec v] else v.mems }

/-- A `Ready`'s entries continue the disk's log (`ReadyOutP`'s first-entry equation, `LogIdx`). -/
theorem saveOk_ready {w : AntSim.DurW} {es l : List EntryM} (hl : AntSim.LogIdx l)
    (hd : ∀ e0 ∈ es.head?, l = w.log.take (uint.nat e0.Index' - 1) ++ es) : SaveOk w es := by
  intro e0 he0
  have h := hd e0 he0
  have hk : l[(w.log.take (uint.nat e0.Index' - 1)).length]? = some e0 := by
    rw [h, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    cases es with
    | nil => cases he0
    | cons a t => simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at he0; subst he0; rfl
  have h1 := hl _ _ hk
  simp only [List.length_take] at h1
  have : uint.nat e0.Index' = (uint.Z e0.Index').toNat := rfl
  constructor <;> omega

/-- The `Ready`'s entries, the log from the first one's index. -/
theorem ready_drop {w : AntSim.DurW} {es l : List EntryM} (hl : AntSim.LogIdx l)
    (hd : ∀ e0 ∈ es.head?, l = w.log.take (uint.nat e0.Index' - 1) ++ es) :
    ∀ e0 ∈ es.head?, l.drop (uint.nat e0.Index' - 1) = es := by
  intro e0 he0
  have hs := saveOk_ready hl hd e0 he0
  rw [hd e0 he0]
  exact List.drop_left' (by simp only [List.length_take]; omega)

theorem mskB2_refl : AntSim.mskB2 ≤ AntSim.mskB2 := by
  simp [LE.le, AntSim.SimMask.Le, AntSim.RnMode.Le, AntSim.NodeK.Le, AntSim.BLe]

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem entsRO_open_p (s : GoSlice) (es : List EntryM) :
    entsRO (GF := GF) s es ⊢ ∃ ls : List Loc, s ↦*{DFrac.discard} ls ∗ [∗list] l;e ∈ ls;es, entRO l e := by
  unfold entsRO entsPts; exact .rfl

/-- **`reportCause` at the head of `parallel`'s report** (`reportCause.specB2` with the cause cell
against the view): recorded (the view's `told` set as `Told` needs, the sent lists' lower bounds
grown), or killed now (nothing recorded); with no fuse burning, recorded. -/
theorem parCauseRep (h_vu : view_update.law (GF := GF))
    (wp_reportCause : node.reportCause.specB2 (GF := GF) (hG := hG))
    (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N) (q : Qp) (v : AntSim.NodeView)
    (net₀ : List Msg) (xnet₀ : List XMsg) (cl : Loc) (fuse : w64)
    (hbt : γ.R.drv.batch = false)
    (hinm : ∀ S V net xnet, AntSim.AntSimD γ.R γ.dec S V net xnet →
      AntSim.InMask AntSim.mskB2 γ.R net xnet) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ killOwn n false fuse ∗ n.[H.node, go!"cause"] ↦ cl ∗
      causeOwn γ.toAntNames j v cl ∗ sentLb γ.toAntNames net₀ ∗ xsentLb γ.toAntNames xnet₀ ∗
      viewFrag γ.toAntNames j v ∗ runLive γ q }}
    (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"reportCause")) (Val #()))
  {{ (d : Bool) (f : w64) (b : Bool) (net₁ : List Msg) (xnet₁ : List XMsg), RET #();
      killOwn n d f ∗ n.[H.node, go!"cause"] ↦ null ∗ viewFrag γ.toAntNames j { v with told := b } ∗
      runLive γ q ∗ parCauseB2 γ j d { v with told := b } null net₁ xnet₁ ∗
      ⌜(fuse = W64 0 → d = false ∧ f = W64 0) ∧ (d = false → v.byE = go!"recv" → b = true) ∧
        net₀ <+: net₁ ∧ xnet₀ <+: xnet₁⌝ }} := by
  wp_start_folded as ⟨#Hc, #Hn, Hk, Hcl, Hco, #Hlb, #Hxlb, Hv, Hl⟩
  by_cases hrec : (if decide (v.byE = go!"recv" ∧ v.told = false) then emitStep false fuse
      else (true, false, fuse)).1 = true
  · ihave Hrep := causeOwn_reportB2 h_vu AntSim.mskB2 mskB2_refl c γ j q v net₀ xnet₀ cl
      (parCauseQ γ j q v net₀ xnet₀) hbt hinm $$ [Hco Hv Hl]
    · iframe Hc Hlb Hxlb Hco Hv Hl
      iintro %b %net₂ %xnet₂ %Hb Hlb2 Hxlb2 Hv Hl
      iunfold parCauseQ
      iexists b, net₂, xnet₂
      iframe Hlb2 Hxlb2 Hv Hl
      ipureintro; exact Hb
    icases Hrep with ⟨%o, Hpco, %Ho, Hrep⟩
    have hcs := causeStep_isSome o _ Ho false fuse
    have hc1 : (causeStep o false fuse).1 = true := by rw [hcs]; exact hrec
    have hc2 : (causeStep o false fuse).2.1 = false := by
      rw [hcs]
      cases hb : decide (v.byE = go!"recv" ∧ v.told = false) <;> simp [hb] at hrec ⊢
      exact emitStep_rec hrec
    have hz : fuse = W64 0 → (causeStep o false fuse).2.2 = W64 0 := by
      intro h0; rw [causeStep_zero o fuse (by rw [h0]; rfl)]; exact h0
    ihave Hpre : (if (causeStep o false fuse).1 then reports γ.strm
        (o.toList.map (atNode (AntSim.nameOf (AntSim.nodeId j)))) (parCauseQ γ j q v net₀ xnet₀)
        else emp) $$ [Hrep]
    · iapply ite_true_intro hc1; iexact Hrep
    wp_apply wp_reportCause c γ n j cl o (parCauseQ γ j q v net₀ xnet₀) false fuse
      $$ [$Hpkg $Hc $Hn $Hk $Hcl $Hpco $Hpre] as ⟨Hk, Hcl, HQ⟩
    ihave HQ := ite_true_ent hc1 $$ HQ
    iunfold parCauseQ at HQ
    icases HQ with ⟨%b, %net₂, %xnet₂, %Hb, #Hlb2, #Hxlb2, Hv, Hl⟩
    rw [hc2] at *
    iapply HΦ
    iframe Hk Hcl Hv Hl
    isplitl
    · iapply (parCauseB2_alive γ j _ null net₂ xnet₂).2
      iframe Hlb2 Hxlb2
      iapply causeOwn_told γ.toAntNames j { v with told := b } Hb.1
    ipureintro
    exact ⟨fun h0 => ⟨rfl, hz h0⟩, fun _ => Hb.1, Hb.2.2.1, Hb.2.2.2⟩
  · icases causeOwn_pendingB2 γ.toAntNames j v cl $$ Hco with ⟨%o, Hpco, %Ho⟩
    have hcs := causeStep_isSome o _ Ho false fuse
    have hc1 : (causeStep o false fuse).1 = false := by rw [hcs]; simpa using hrec
    have hc2 : (causeStep o false fuse).2.1 = true := by
      rw [hcs]
      cases hb : decide (v.byE = go!"recv" ∧ v.told = false) <;> simp [hb] at hrec ⊢
      exact emitStep_kill hrec
    have hnz : fuse ≠ W64 0 := by
      intro h0; rw [causeStep_zero o fuse (by rw [h0]; rfl)] at hc1; cases hc1
    ihave Hpre : (if (causeStep o false fuse).1 then reports γ.strm
        (o.toList.map (atNode (AntSim.nameOf (AntSim.nodeId j)))) (emp : IProp GF)
        else emp) $$ []
    · iapply ite_false_intro hc1
      iempintro
    wp_apply wp_reportCause c γ n j cl o emp false fuse
      $$ [$Hpkg $Hc $Hn $Hk $Hcl $Hpco $Hpre] as ⟨Hk, Hcl, -⟩
    rw [hc2] at *
    iapply HΦ
    iframe Hk Hcl
    isplitl [Hv]
    · iExactEq Hv; rfl
    iframe Hl
    isplitl
    · iapply (parCauseB2_dead_null (GF := GF) γ j _ net₀ xnet₀)
    ipureintro
    exact ⟨fun h0 => absurd h0 hnz, fun h => Bool.noConfusion h, List.prefix_refl net₀,
      List.prefix_refl xnet₀⟩

theorem node.parallel.wp_proof
    (h_vu : view_update.law (GF := GF))
    (h_wf : rawNode_wf.law (GF := GF) (hG := hG))
    (h_recs : rawNode_logRecs.law (GF := GF) (hG := hG))
    (h_ld : rawNode_leader.law (GF := GF) (hG := hG))
    (h_vote : rawNode_vote.law (GF := GF) (hG := hG))
    (h_cm : rawNode_commit.law (GF := GF) (hG := hG))
    (h_cmd : rawNode_committed.law (GF := GF) (hG := hG))
    (h_inv : rawNode_commitInv.law (GF := GF) (hG := hG))
    (h_ttc : rawNode_term_tc.law (GF := GF) (hG := hG))
    (h_tlp : rnTermLB_persistent.law (GF := GF) (hG := hG))
    (h_app : rawNode_appended.law (GF := GF) (hG := hG))
    (h_mem : AntSim.antSim_memP_in.stmt)
    (wp_reportCause : node.reportCause.specB2 (GF := GF) (hG := hG))
    (wp_stateEv : node.stateEv.specB2 (GF := GF) (hG := hG))
    (wp_withByRole : withByRole.spec (GF := GF) (hG := hG))
    (wp_b2i : b2i.spec (GF := GF) (hG := hG))
    (wp_emit : node.emit.specB2 (GF := GF) (hG := hG))
    (h_req : parReqB2.stmt (GF := GF) (hG := hG))
    (h_write : parWriteB2.stmt (GF := GF) (hG := hG)) :
    node.parallel.spec (GF := GF) (hG := hG) := by
  intro _ c γ n j I x g net₀ xnet₀ hsl hp q has hbt hpar hsp hlead hhp1 hhp2 hhne
  haveI := h_tlp γ.raft I.rs.tc
  wp_start as ⟨#Hc, #Hn, %Hb2, Hpre, Hexit, Htok⟩
  ihave #Hc' := Hc
  iunfold antClusterB2 at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, -, -, %Hmode, -, -, -, -, -, -, -, -, -, -, -, -, -, %Hγ⟩
  iunfold drainPreB2 at Hpre
  icases Hpre with ⟨Hrn, Hraw, Hrest, Hgv, Hdur, Henter, #Hhard, #Hents, Hrout, #Hce, Hrs, #Hrsr,
    Hmsgs, Hcap, Hown, Hlead, %Hpure⟩
  iunfold loopRestB2 at Hrest
  icases Hrest with ⟨%d, %ms, %cl, %csl, %role, %applied, %fuse, %dk, %si, %hn, #Hd, Hms, Hrole, Hhs,
    Hcause, Happl, Hconf, Hkill, Hv, Hdisk, %Hvn, Hstor, %Hsto, #Htlb, Hbud, %Hhold, Hmem, #Hhsro,
    %Hpv, #Hcs, #Hrq, %Hc0, #Hlb, #Hxlb, Hco⟩
  iunfold nodeExitB2 at Hexit
  icases Hexit with ⟨Hl, Hadd⟩
  obtain ⟨hreach, hRO, hfull, hmok, hok⟩ := Hpure
  rw [has] at hreach
  simp only [Bool.false_eq_true, ↓reduceIte] at hreach
  have hinm := inMask_b2_run (dec := γ.dec) Hmode.2 Hb2 has hsp
  obtain ⟨hasR, hbtR⟩ := rMd_sync_b2 Hmode.2 has hbt
  obtain ⟨hn0, hdk0, hparts0⟩ := Hpv.2.2.2.2 has
  icases nodeMemB2_mems_nil γ j n I.v x g _ _ _ has hbt $$ Hmem with ⟨%Hmems0, Hmem⟩
  imod drain_peekRecsB2 h_vu AntSim.mskB2 c γ j q I.v net₀ xnet₀ hinm $$ [$Hc $Hlb $Hxlb $Hv $Hl]
    with ⟨%Hpk, #Hvrec, %Hvidx, Hv, Hl⟩
  obtain ⟨S₀, netS, xnetS, hn0', hx0', hin0, hnet0, hok0⟩ := Hpk
  obtain ⟨hs, hcc, hfw⟩ := rMd_flags_b2 Hmode.2 Hb2
  have hreach0 := hreach.mono hn0' hx0'
  have hdurv : I.v.dur = AntSim.durOf I.v.r := by
    have hdf : AntSim.DiskFold I.v := hok0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have := hdf hparts0; rw [Hmems0] at this; exact this
  have hout := hok.2.2.2.2.1
  have hrole : (readyDOf I.r (roleAfter I.rs.role I.ss) I.es I.ce I.ms I.qs I.sts).role = .leader := by
    simp only [readyDOf]; rw [← hout.1.1, hlead]; rfl
  have hlh := AntSim.leadHs_reachD mskB2_refl hin0 hasR hbtR hnet0 hok0 Hmems0 hparts0 hreach0 hRO hrole
  have hS : I.rs.dur.term = (rAccepted I.r).p.term ∧ I.rs.dur.vote = (rAccepted I.r).p.vote := by
    have h1 := Hhold.1.2.2.2.1
    have h2 := Hhold.1.2.2.2.2.1
    simp only [diskContents] at h1 h2
    rw [hdk0] at h1 h2
    simp only [rAccepted, pAccepted]
    exact ⟨h1.symm.trans hlh.1.symm, h2.symm.trans hlh.2.symm⟩
  obtain ⟨hsn0, -, -⟩ := AntSim.InMask.b2 mskB2_refl hin0
  have hfp : (rAccepted I.r).fp = [] :=
    (AntSim.reach_fpD mskB2_refl hin0 hbtR hok0 hreach0).trans ((AntSim.nodeOkD_factsS hok0).2.1 hsn0).2.1
  imod readyExt_b1 h_wf h_recs h_ld h_vote h_cm h_cmd h_inv γ.toAntNames j γ.R.md hs hcc hfw hasR I.rn
    I.rs₁ (rAccepted I.r) I.qs I.ip I.rs.dur hfp hS Hγ.2.2.2.1 Hγ.2.2.2.2 $$ [$Hraw $Hdur]
    with ⟨#Hext, Hraw, Hdur⟩
  icases h_ttc γ.R.md hs hcc hfw hasR _ _ _ _ _ _ _ $$ Hraw with ⟨%Httc, Hraw⟩
  ihave #Hents' := entsROz_entsRO _ _ _ $$ Hents
  ihave %Heslen := entsPts_len _ _ _ $$ Hents'
  obtain ⟨rdD, hrdD⟩ : ∃ y, y = readyDOf I.r (roleAfter I.rs.role I.ss) I.es I.ce I.ms I.qs I.sts :=
    ⟨_, rfl⟩
  rw [← hrdD] at hRO hrole
  imod drain_peekShapeB2 h_vu AntSim.mskB2 mskB2_refl c γ j q I.v I.r rdD net₀ xnet₀ hinm hasR hbtR
    Hmems0 hparts0 hreach hRO Hvn.1.1 (fun m h => (Hvn.1.2 m h).1) $$ [$Hc $Hlb $Hxlb $Hv $Hl]
    with ⟨%Hshape, Hv, Hl⟩
  imod commit_peekB2 h_vu AntSim.mskB2 mskB2_refl c γ j q I.v I.r net₀ xnet₀ hinm Hmems0 hparts0 hreach
    $$ [$Hc $Hlb $Hxlb $Hv $Hl] with ⟨%hcm, Hv, Hl⟩
  have hesMem : ∀ e ∈ I.es, e ∈ I.r.full := by
    intro e he
    obtain ⟨e0, he0⟩ : ∃ e0, I.es.head? = some e0 := by
      cases hes : I.es with
      | nil => rw [hes] at he; cases he
      | cons a _ => exact ⟨a, rfl⟩
    have h1 := (hRO.2.2.2.2.2.2.1 e0 (by rw [hrdD]; exact he0)).1
    rw [h1]; exact List.mem_append_right _ (by rw [hrdD]; exact he)
  have hesNorm : AllNormal I.es := fun e he => Hshape.1 e (hesMem e he)
  have hmsgN : ∀ m ∈ I.ms, isRequestTy m.st.msg.Type' = true → AllNormal m.st.ents := by
    intro m hm hr
    obtain ⟨q', habs, hrq⟩ := req_absMsgOf hr (hok.2.2.2.2.2.2.1 m hm)
    have hns : q'.ty ≠ .snap := (isReqM_ty hrq).2
    rw [(absMsgOf_st habs hns).2]
    exact Hshape.2 q' (by rw [hrdD]; exact List.mem_filterMap.2 ⟨m, hm, habs⟩)
  -- `write := hs != n.hs || len(rd.Entries) > 0`
  ihave %Hhpne : ⌜HsNew I.h → hp ≠ hsl⌝ $$ []
  · iintro %hE %Heq
    rw [hhp1 hE] at Heq
    ihave #Hhard' := Hhard
    iunfold hsOptC at Hhard'
    icases Hhard' with (%Hh0 | #Hhro)
    · exfalso; apply hE; rw [Hh0.2]; simp
    · ihave #Hhr : hsRO (GF := GF) hsl I.h $$ []
      · rw [← Heq]; iapply hsROC_hsRO _ _ $$ Hhro
      ihave %Hag := hsRO_agree hsl hn I.h $$ [$Hhsro $Hhr]
      exfalso
      apply hhne hE
      rw [hok.1.1, ← hn0, Hag]
  have hwr : decide (hp = hsl) = !decide (HsNew I.h) := by
    by_cases hE : HsNew I.h
    · simp [hE, Hhpne hE]
    · simp [hE, hhp2 hE]
  wp_auto
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun w => iprop(⌜w = #(decide (HsNew I.h ∨ I.es ≠ []))⌝ ∗ rd_ptr ↦ I.rd)))
    $$ [rd]
  · have hl : I.es ≠ [] ↔ 0 < I.es.length := by cases I.es <;> simp
    have h0 : sint.Z (W64 0) = 0 := by word
    rw [hwr]
    have h2 : sint.nat I.rd.Entries'.len = (sint.Z I.rd.Entries'.len).toNat := rfl
    have hlen := Heslen.1
    by_cases hE : HsNew I.h
    · rw [show decide (HsNew I.h) = true from decide_eq_true hE]
      simp only [Bool.not_true]
      wp_auto
      iframe
      ipureintro
      rw [show decide (HsNew I.h ∨ I.es ≠ []) = true from decide_eq_true (.inl hE)]
    · rw [show decide (HsNew I.h) = false from decide_eq_false hE]
      simp only [Bool.not_false]
      wp_auto
      iframe
      ipureintro
      have : (0 < sint.Z I.rd.Entries'.len) ↔ (HsNew I.h ∨ I.es ≠ []) := by
        rw [hl]; constructor
        · intro hh; right; omega
        · rintro (hh | hh)
          · exact absurd hh hE
          · omega
      rw [h0]
      simp only [this]
  iintro %w ⟨%Hw, rd⟩
  subst Hw
  wp_auto
  -- the report's facts
  have hrole0 : role = AntSim.roleS I.v := Hpv.2.1
  have hparR : γ.R.drv.parallel = true := by rw [Hmode.2.2.2.2.2.2]; exact hpar
  have hRepIff : (HsNew I.h ∨ ¬ I.es = [] ∨ roleStr (roleAfter I.rs.role I.ss) ≠ role) ↔
      AntSim.Reported I.v rdD := by
    rw [hrdD, hrole0]
    exact reported_iff hok.1 hout.2.1 hhne hout.1.1 rfl
  have hWIff : (HsNew I.h ∨ I.es ≠ []) ↔ AntSim.Writes I.v rdD := by
    rw [hrdD]; exact writes_iff hok.1 hout.2.1 hhne
  have hrdT : rdD.term = I.r.p.term ∧ rdD.vote = I.r.p.vote ∧ rdD.commit = I.r.p.commit ∧
      rdD.ents = I.es ∧ rdD.snap = none := by
    subst hrdD; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hrs : AntSim.roleStr rdD.pre rdD.role = roleStr (roleAfter I.rs.role I.ss) := by
    rw [hrdD]; exact readyDOf_roleStr hout.1.1
  have hsn := hok.2.2.2.2.2.2.2.2.2.2.2.1
  have htcb : uint.Z I.rs.tc < 2 ^ 61 := hok.2.2.2.2.2.2.2.2.2.2.1
  have htc' : uint.Z I.r.p.term < 2 ^ 61 := by
    have : uint.Z I.r.p.term ≤ uint.Z I.rs.tc := Httc
    omega
  have hesMemP : ∀ e ∈ I.es, e ∈ I.r.p.log := fun e he => hfull ▸ hesMem e he
  have hesN : ∀ e ∈ I.es, uint.Z e.Term' < 2 ^ 61 ∧ uint.Z e.Index' < 2 ^ 61 :=
    fun e he => hsn.2.2.2.2 e (hesMemP e he)
  have hevM : ∀ w : Bool, atNode (AntSim.nameOf (AntSim.nodeId j))
      { withByRoleM (stateEvM go!"mem" (HardStateM.mk I.r.p.term I.r.p.vote I.r.p.commit) I.es) I.v.byE
          (roleStr (roleAfter I.rs.role I.ss)) with w := some (sint.Z (W64 (if w then 1 else 0))) } =
      AntSim.evMem (AntSim.nodeId j) I.v.byE (AntSim.roleStr rdD.pre rdD.role) rdD.term rdD.vote
        rdD.commit rdD.ents none w := by
    intro w
    rw [hrs, hrdT.1, hrdT.2.1, hrdT.2.2.1, hrdT.2.2.2.1]
    exact stateEv_mem _ _ _ _ _ w (by simpa using htc') (by simpa using hsn.2.2.2.1) hesN
  have hH : phsNext I.rs.phs I.h = HardStateM.mk I.r.p.term I.r.p.vote I.r.p.commit := hout.2.1
  ihave #HhsH : hsRO (GF := GF) hp (HardStateM.mk I.r.p.term I.r.p.vote I.r.p.commit) $$ []
  · by_cases hE : HsNew I.h
    · rw [hhp1 hE, ← hH, phsNext_ne _ _ hE]
      ihave #Hhard' := Hhard
      iunfold hsOptC at Hhard'
      icases Hhard' with (%Hh0 | #Hhro)
      · exfalso; apply hE; rw [Hh0.2]; simp
      · iapply hsROC_hsRO _ _ $$ Hhro
    · rw [hhp2 hE, ← hH, phsNext_empty _ _ (Classical.not_not.mp hE), hok.1.1, ← hn0]
      iexact Hhsro
  haveI := h_tlp γ.raft I.rs₁.tc
  ihave #Htlb1 : rnTermLB (GF := GF) γ.raft I.rs₁.tc $$ []
  · iExactEq Htlb; rfl
  haveI := h_tlp γ.raft I.rs₂.tc
  ihave #Htlb2 : rnTermLB (GF := GF) γ.raft I.rs₂.tc $$ []
  · iExactEq Htlb; rfl
  ihave #Hext' : □ factsExt (GF := GF) γ.toAntNames (fun G0 G => FactsLe γ.R G0 G ∧ AntSim.RaftLaws G ∧
      AntSim.ReadyFacts G (AntSim.nodeId j) I.r) $$ []
  · imodintro; iExactEq Hext; rfl
  icases entsRO_open_p _ _ $$ Hents' with ⟨%els, #Hsl, #Hbig⟩
  -- `write || role != n.role`
  wp_bind (If (Val _) _ _)
  iapply (wp_wand (Φ := fun w => iprop(⌜w = #(decide (HsNew I.h ∨ ¬ I.es = [] ∨
      roleStr (roleAfter I.rs.role I.ss) ≠ role))⌝ ∗
      role_ptr ↦ roleStr (roleAfter I.rs.role I.ss) ∗ n_ptr ↦ n ∗
      n.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node, go!"role"] ↦ role)))
    $$ [role n Hrole]
  · by_cases hw : HsNew I.h ∨ ¬ I.es = []
    · rw [decide_eq_true hw]
      wp_auto
      iframe
      ipureintro
      have : HsNew I.h ∨ ¬ I.es = [] ∨ roleStr (roleAfter I.rs.role I.ss) ≠ role := by
        rcases hw with hw | hw
        · exact Or.inl hw
        · exact Or.inr (Or.inl hw)
      rw [decide_eq_true this]
    · rw [decide_eq_false hw]
      wp_auto
      iframe
      ipureintro
      simp only [not_or, Classical.not_not] at hw
      by_cases hc : roleStr (roleAfter I.rs.role I.ss) = role
      · simp [hc, hw]
      · simp [hc, hw]
  iintro %w ⟨%Hw, role, n, Hrole⟩
  subst Hw
  -- the report (`mem`), or a quiet `Ready`
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun w => iprop(⌜w = executeVal⌝ ∗ n_ptr ↦ n ∗ hs_ptr ↦ hp ∗
      role_ptr ↦ roleStr (roleAfter I.rs.role I.ss) ∗ by_ptr ↦ I.v.byE ∗ rd_ptr ↦ I.rd ∗
      write_ptr ↦ decide (HsNew I.h ∨ ¬I.es = []) ∗
      ∃ (d₁ : Bool) (f₁ : w64) (cl₁ : Loc) (b : Bool) (v₁ : AntSim.NodeView) (net₁ : List Msg)
        (xnet₁ : List XMsg),
        killOwn n d₁ f₁ ∗ n.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node, go!"cause"] ↦ cl₁ ∗
        viewFrag γ.toAntNames j v₁ ∗ runLive γ q ∗ parCauseB2 γ j d₁ v₁ cl₁ net₁ xnet₁ ∗
        ⌜(fuse = W64 0 → d₁ = false ∧ f₁ = W64 0) ∧ net₀ <+: net₁ ∧ xnet₀ <+: xnet₁ ∧
          (d₁ = true → v₁ = { I.v with told := b }) ∧
          (d₁ = false → v₁ = parMemV { I.v with told := b } I.r rdD
            (decide (HsNew I.h ∨ ¬I.es = [])))⌝)))
    $$ [n hs role «by» rd write Hkill Hcause Hco Hv Hl]
  · by_cases hrep : HsNew I.h ∨ ¬ I.es = [] ∨ roleStr (roleAfter I.rs.role I.ss) ≠ role
    · rw [decide_eq_true hrep]
      have hrepS : AntSim.Reported I.v rdD := hRepIff.1 hrep
      wp_auto
      wp_apply +noauto (parCauseRep h_vu wp_reportCause c γ n j q I.v net₀ xnet₀ cl fuse hbtR hinm)
        $$ [$Hpkg $Hc $Hn $Hkill $Hcause $Hco $Hlb $Hxlb $Hv $Hl]
        as %d2 %f2 %b %net₁ %xnet₁ ⟨Hkill, Hcause, Hv, Hl, Hpc, %Hrc⟩
      wp_take_receipt as Hr1
      wp_apply +noauto wp_stateEv c γ n j go!"mem" hp (HardStateM.mk I.r.p.term I.r.p.vote I.r.p.commit)
        I.rd.Entries' DFrac.discard els I.es hesNorm $$ [$Hpkg $Hc $Hn $HhsH $Hsl $Hbig]
        as %pe ⟨-, -, Hev, Hr3⟩
      wp_take_receipt as Hr2
      wp_apply wp_withByRole pe _ I.v.byE (roleStr (roleAfter I.rs.role I.ss)) $$ [$Hpkg $Hev] as Hev
      icases eventOwn_setW pe _ $$ Hev with ⟨%g, Hp, Hset⟩
      wp_auto
      wp_apply wp_b2i (decide (HsNew I.h ∨ ¬I.es = [])) $$ [$Hpkg]
      try wp_auto
      ihave Hev := Hset $$ %(W64 (if decide (HsNew I.h ∨ ¬I.es = []) then 1 else 0)) [Hp]
      · iExactEq Hp; rfl
      -- the `mem` report (`emit`), or a kill
      by_cases hrec2 : (emitStep d2 f2).1 = true
      · have hd2 := emitStep_rec_alive hrec2
        subst hd2
        have hd3 := emitStep_rec hrec2
        icases (parCauseB2_alive γ j _ null net₁ xnet₁).1 $$ Hpc with ⟨-, #Hlb1, #Hxlb1⟩
        have htold : AntSim.Told ({ I.v with told := b } : AntSim.NodeView) := fun h => Hrc.2.1 rfl h
        have hterm : AntSim.TermRoom ({ I.v with told := b } : AntSim.NodeView) := by
          show uint.Z I.v.ps.term + 1 < 2 ^ 64
          have h1 : I.v.ps.term = I.v.dur.term := by rw [hdurv]; rfl
          rw [h1, ← hlh.1]; omega
        have hwI : decide (HsNew I.h ∨ ¬I.es = []) = true ↔
            AntSim.Writes ({ I.v with told := b } : AntSim.NodeView) rdD := by
          rw [decide_eq_true_iff]; exact hWIff
        have hstep := memHstepD h_mem AntSim.mskB2 mskB2_refl j ({ I.v with told := b } : AntSim.NodeView)
          I.r rdD (decide (HsNew I.h ∨ ¬I.es = [])) net₁ xnet₁ hinm hasR hbtR hparR
          (reachIn_told_b2 b (hreach.mono Hrc.2.2.1 Hrc.2.2.2)) hRO hrole hrdT.2.2.2.2 hrepS hwI htold hterm
          Hmems0 hparts0
        ihave Hrc3 : ⧗ (AntSim.evMem (AntSim.nodeId j) I.v.byE (AntSim.roleStr rdD.pre rdD.role) rdD.term
            rdD.vote rdD.commit rdD.ents none (decide (HsNew I.h ∨ ¬I.es = []))).weight $$ [Hr1 Hr2 Hr3]
        · rw [evMem_weight, hrdT.2.2.2.1]
          iapply (receipt_add (GF := GF) (I.es.length + 1) 1).2
          iframe Hr2
          iapply (receipt_add (GF := GF) I.es.length 1).2
          iframe Hr3 Hr1
        ihave Hpre2 : (if (emitStep false f2).1 then reports γ.strm
            [atNode (AntSim.nameOf (AntSim.nodeId j))
              { withByRoleM (stateEvM go!"mem" (HardStateM.mk I.r.p.term I.r.p.vote I.r.p.commit) I.es)
                  I.v.byE (roleStr (roleAfter I.rs.role I.ss)) with
                w := some (sint.Z (W64 (if decide (HsNew I.h ∨ ¬I.es = []) then 1 else 0))) }]
            iprop(viewFrag γ.toAntNames j (parMemV { I.v with told := b } I.r rdD
                (decide (HsNew I.h ∨ ¬I.es = []))) ∗ runLive γ q ∗
              (∃ (net : List Msg) (xnet : List XMsg), sentLb γ.toAntNames net ∗ xsentLb γ.toAntNames xnet ∗
                ⌜net₁ <+: net ∧ (∀ m ∈ ([] : List Msg), m ∈ net) ∧ xnet₁ <+: xnet ∧
                  ∀ x ∈ ([] : List XMsg), x ∈ xnet⌝)) else emp) $$ [Hv Hl Hrc3]
        · iapply ite_true_intro hrec2
          rw [hevM]
          iapply report_updB2 h_vu c γ j q ({ I.v with told := b } : AntSim.NodeView)
            (parMemV { I.v with told := b } I.r rdD (decide (HsNew I.h ∨ ¬I.es = [])))
            (AntSim.evMem (AntSim.nodeId j) I.v.byE (AntSim.roleStr rdD.pre rdD.role) rdD.term rdD.vote
              rdD.commit rdD.ents none (decide (HsNew I.h ∨ ¬I.es = [])))
            net₁ [] xnet₁ []
            (fun G0 G => FactsLe γ.R G0 G ∧ AntSim.RaftLaws G ∧ AntSim.ReadyFacts G (AntSim.nodeId j) I.r) _
            (by rw [hrdT.1, hrdT.2.2.1, hrdT.2.2.2.1]; exact evMem_numsOk _ hsn htc' hesMemP)
            (evMem_chgOk _ _ _ _ _ _ _ _) hstep
          iframe Hc Hlb1 Hxlb1 Hext' Hrc3 Hv Hl
          iintro H
          iexact H
        wp_apply +noauto wp_emit c γ n j pe _ _ false f2 $$ [$Hpkg $Hc $Hn $Hkill $Hev $Hpre2]
          as %b' ⟨Hkill, %Hb', HQ⟩
        subst Hb'
        ihave HQ := ite_true_ent hrec2 $$ HQ
        icases HQ with ⟨Hv, Hl, %net₂, %xnet₂, #Hlb2, #Hxlb2, %Hn2⟩
        rw [hd3]
        wp_auto
        isplitr
        · ipureintro; rfl
        iframe n hs role «by» rd write
        iexists false, (emitStep false f2).2.2, null, b,
          parMemV { I.v with told := b } I.r rdD (decide (HsNew I.h ∨ ¬I.es = [])), net₂, xnet₂
        iframe Hkill Hcause Hv Hl
        isplitl
        · iapply (parCauseB2_alive γ j _ null net₂ xnet₂).2
          iframe Hlb2 Hxlb2
          iapply causeOwn_told γ.toAntNames j _ (Hrc.2.1 rfl)
        ipureintro
        refine ⟨fun h0 => ⟨rfl, ?_⟩, Hrc.2.2.1.trans Hn2.1, Hrc.2.2.2.trans Hn2.2.2.1,
          fun h => Bool.noConfusion h, fun _ => rfl⟩
        have hz : uint.Z f2 = 0 := by rw [(Hrc.1 h0).2]; rfl
        rw [emitStep_zero f2 hz]; exact (Hrc.1 h0).2
      · have hrec2' : (emitStep d2 f2).1 = false := by simpa using hrec2
        have hd3 := emitStep_norec_dead hrec2'
        ihave Hpre2 : (if (emitStep d2 f2).1 then reports γ.strm
            [atNode (AntSim.nameOf (AntSim.nodeId j))
              { withByRoleM (stateEvM go!"mem" (HardStateM.mk I.r.p.term I.r.p.vote I.r.p.commit) I.es)
                  I.v.byE (roleStr (roleAfter I.rs.role I.ss)) with
                w := some (sint.Z (W64 (if decide (HsNew I.h ∨ ¬I.es = []) then 1 else 0))) }]
            (emp : IProp GF) else emp) $$ []
        · iapply ite_false_intro hrec2'
          iempintro
        wp_apply +noauto wp_emit c γ n j pe _ _ d2 f2 $$ [$Hpkg $Hc $Hn $Hkill $Hev $Hpre2]
          as %b' ⟨Hkill, -, -⟩
        rw [hd3]
        wp_auto
        isplitr
        · ipureintro; rfl
        iframe n hs role «by» rd write
        iexists true, (emitStep d2 f2).2.2, null, b, ({ I.v with told := b } : AntSim.NodeView), net₁, xnet₁
        iframe Hkill Hcause Hv Hl
        isplitl
        · iapply (parCauseB2_dead_null (GF := GF) γ j _ net₁ xnet₁)
        ipureintro
        refine ⟨fun h0 => ?_, Hrc.2.2.1, Hrc.2.2.2, fun _ => rfl, fun h => Bool.noConfusion h⟩
        exfalso
        obtain ⟨h1, h2⟩ := Hrc.1 h0
        have hz : uint.Z f2 = 0 := by rw [h2]; rfl
        rw [h1, emitStep_zero f2 hz] at hrec2'
        cases hrec2'
    · rw [decide_eq_false hrep]
      have hnr : ¬ AntSim.Reported I.v rdD := fun h' => hrep (hRepIff.2 h')
      imod view_quietPB2 h_vu AntSim.mskB2 mskB2_refl c γ j q I.v I.r rdD net₀ xnet₀ hinm hasR hbtR
        hparR Hmems0 hparts0 hreach hRO hrole hrdT.2.2.2.2 hnr $$ [$Hc $Hlb $Hxlb $Hext' $Hv $Hl]
        with ⟨Hv, Hl⟩
      wp_auto
      isplitr
      · ipureintro; rfl
      iframe n hs role «by» rd write
      iexists false, fuse, cl, I.v.told, quietPView I.v I.r rdD, net₀, xnet₀
      iframe Hkill Hcause Hv Hl
      isplitl
      · iapply (parCauseB2_alive γ j _ cl net₀ xnet₀).2
        iframe Hlb Hxlb
        iExactEq Hco; rfl
      ipureintro
      have hw : decide (HsNew I.h ∨ ¬I.es = []) = false := by
        apply decide_eq_false
        intro h'
        rcases h' with h' | h'
        · exact hrep (Or.inl h')
        · exact hrep (Or.inr (Or.inl h'))
      refine ⟨fun h0 => ⟨rfl, h0⟩, List.prefix_refl _, List.prefix_refl _, fun h => Bool.noConfusion h,
        fun _ => ?_⟩
      rw [hw]
      rfl
  iintro %w ⟨%Hw, n, hs, role, «by», rd, write, %d₁, %f₁, %cl₁, %b, %v₁, %net₁, %xnet₁, Hkill, Hcause,
    Hv, Hl, Hpc, %Hmid⟩
  subst Hw
  wp_pures
  wp_load
  wp_pures
  wp_load
  wp_pures
  wp_store
  wp_pure
  wp_pure
  wp_pure
  wp_pure
  -- the requests (`parReqB2`)
  obtain ⟨hfz1, hn1, hx1, hd1, ha1⟩ := Hmid
  have hal : d₁ = false → v₁.pend = reqPend I.ms 0 ∧ v₁.parts = [] ∧ v₁.byE = I.v.byE := by
    intro hd
    rw [ha1 hd, reqPend_zero, hrdD]
    exact ⟨rfl, hparts0, rfl⟩
  wp_bind (App (App (Val exceptionSeq) _) _)
  have hrq := h_req n_ptr rd_ptr by_ptr c n γ j I AntSim.mskB2 v₁ net₁ xnet₁ d₁ f₁ cl₁ q
  unfold github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.parallel.reqE at hrq
  iapply hrq _ _ mskB2_refl hinm has hbt hok hmsgN hal
  clear hrq
  ihave Hrm := Hlead $$ %hlead
  iframe Hpkg Hc Hn n «by» rd Hkill Hcause Hv Hpc Htlb Hmsgs Hcap Hown Hrm Hl Hadd Htok
  isplitr
  · ipureintro; exact Hb2
  isplitr
  · ipureintro; exact hmok
  iintro %d₂ %f₂ %cl₂ %v₂ %net₂ %xnet₂ ⟨n, «by», rd, Hkill, Hcause, Hv, Hpc, %Hreq, Hmsgs, Hl, Hadd,
    Htok⟩
  subst hdk0 hn0
  have hce0 : I.v.ce = [] := reachIn_ce hreach
  have hLI : AntSim.LogIdx I.r.full := hRO.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hhead : ∀ e0 ∈ I.es.head?, I.r.full = I.v.dur.log.take (uint.nat e0.Index' - 1) ++ I.es := by
    intro e0 he0
    have := (hRO.2.2.2.2.2.2.1 e0 (by rw [hrdT.2.2.2.1]; exact he0)).1
    rw [hrdT.2.2.2.1] at this; exact this
  have hnil : I.es = [] → I.r.full = I.v.dur.log := fun hes =>
    hRO.2.2.2.2.2.1 hrdT.2.2.2.2 (by rw [hrdT.2.2.2.1]; exact hes)
  have hwm : I.v.dur.write (rdD.memRec I.v) = AntSim.durOf (AntSim.accepted I.r) :=
    AntSim.write_memRec hRO hrdT.2.2.2.2
  -- the views after the requests
  have hv1 : v₁.dur = I.v.dur ∧ v₁.cause = I.v.cause ∧ (v₁.r.full = I.v.r.full ∨ v₁.r.full = I.r.full) := by
    cases hd : d₁
    · rw [ha1 hd]; exact ⟨rfl, rfl, Or.inr rfl⟩
    · rw [hd1 hd]; exact ⟨rfl, rfl, Or.inl rfl⟩
  have hvn1 : ViewNormal v₁ := by
    rcases hv1.2.2 with h | h
    · exact viewNormal_congr Hvn.1 h hv1.2.1
    · exact ⟨fun e he => Hshape.1 e (h ▸ he), by rw [hv1.2.1]; exact Hvn.1.2⟩
  obtain ⟨P₂, T₂, U₂, M₂, hv2, hUM2, -, hP2⟩ := Hreq.2.2.2.2
  have hvn2 : ViewNormal v₂ := by rw [hv2]; exact viewNormal_congr hvn1 rfl rfl
  have hdur2 : v₂.dur = I.v.dur := by rw [hv2]; exact hv1.1
  have hRst : γ.mode.Restarts' = false → fuse = W64 0 := Hvn.2.2
  by_cases hW : HsNew I.h ∨ ¬I.es = []
  · -- the write (`parWriteB2`)
    have hWb : decide (HsNew I.h ∨ ¬I.es = []) = true := decide_eq_true hW
    iunfold nodeStor at Hstor
    icases Hstor with ⟨Hbr, %γs, #Hlock, Hmeta, #Hbridge, %Hsz⟩
    ihave #Hbridge' : antStorBridge (GF := GF) I.rs.storage γs $$ []
    · rw [Hsto]; iexact Hbridge
    ihave Happ : appendRight (GF := GF) I.rs.storage I.es $$ [Hrout]
    · iunfold readyOut at Hrout; iexact Hrout
    icases parStorPre I.rs.storage γs I.es I.r.full hLI (ready_drop hLI hhead)
      (fun e he => (hesN e he).2) $$ [$Hbridge' $Happ] with ⟨%k, %old, %Hk, %Hidx, %Hkb, Hpre⟩
    ihave #HentsZ : entsPtsZ (GF := GF) γs.sz I.rd.Entries' DFrac.discard I.es $$ []
    · rw [Hsz]; iexact Hents
    ihave ⟨%oh, %Hoh1, #Hoh⟩ : ∃ oh : Option HardStateM,
        ⌜oh.getD (HardStateM.mk I.v.dur.term I.v.dur.vote I.v.dur.commit) =
          HardStateM.mk I.r.p.term I.r.p.vote I.r.p.commit⌝ ∗
        hsOptRO (GF := GF) (if hp = hsl then null else hp) oh $$ []
    · by_cases hE : HsNew I.h
      · iexists some (HardStateM.mk I.r.p.term I.r.p.vote I.r.p.commit)
        rw [if_neg (Hhpne hE)]
        ihave %Hnn : ⌜hp ≠ null⌝ $$ []
        · ihave #HhsH' := HhsH
          iunfold hsRO at HhsH'
          icases HhsH' with ⟨%pt, %pv, %pc, %uf, %Hnn, -⟩
          ipureintro; exact Hnn
        isplitr
        · ipureintro; rfl
        iunfold hsOptRO; iright; iexists _; iframe HhsH; ipureintro; exact ⟨Hnn, rfl⟩
      · iexists none
        rw [if_pos (hhp2 hE)]
        isplitr
        · ipureintro
          rw [Option.getD_none, ← hH, phsNext_empty _ _ (Classical.not_not.mp hE), hok.1.1]
        iunfold hsOptRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
    have hsw : saveW I.v.dur oh I.es = AntSim.durOf (AntSim.accepted I.r) :=
      saveW_ready _ oh I.es _ I.r.full Hoh1 hnil hhead
    have hal2 : d₂ = false → v₂.mems = [rdD.memRec { I.v with told := b }] ∧
        (rdD.memRec { I.v with told := b }).snap = none ∧ (rdD.memRec { I.v with told := b }).ents = I.es ∧
        atNode (AntSim.nameOf (AntSim.nodeId j))
            (stateEvM go!"write" (HardStateM.mk I.r.p.term I.r.p.vote I.r.p.commit) I.es) =
          AntSim.evWrite (AntSim.nodeId j) (rdD.memRec { I.v with told := b }).term
            (rdD.memRec { I.v with told := b }).vote (rdD.memRec { I.v with told := b }).commit
            (rdD.memRec { I.v with told := b }).ents (rdD.memRec { I.v with told := b }).snap ∧
        (AntSim.evWrite (AntSim.nodeId j) (rdD.memRec { I.v with told := b }).term
            (rdD.memRec { I.v with told := b }).vote (rdD.memRec { I.v with told := b }).commit
            (rdD.memRec { I.v with told := b }).ents (rdD.memRec { I.v with told := b }).snap).NumsOk := by
      intro hd
      have hd1 : d₁ = false := by
        cases h : d₁
        · rfl
        · have := Hreq.2.1 h; rw [hd] at this; cases this
      obtain ⟨P, T, U, M, hv2, -⟩ := Hreq.2.2.2.2
      have hm2 : v₂.mems = [rdD.memRec { I.v with told := b }] := by
        rw [hv2, ha1 hd1]; simp [parMemV, hWb, Hmems0]
      refine ⟨hm2, hrdT.2.2.2.2, hrdT.2.2.2.1, ?_, ?_⟩
      · show _ = AntSim.evWrite _ rdD.term rdD.vote rdD.commit rdD.ents rdD.snap
        rw [hrdT.1, hrdT.2.1, hrdT.2.2.1, hrdT.2.2.2.1, hrdT.2.2.2.2]
        exact stateEv_write _ _ _ (by simpa using htc') (by simpa using hsn.2.2.2.1) hesN
      · show (AntSim.evWrite _ rdD.term rdD.vote rdD.commit rdD.ents rdD.snap).NumsOk
        rw [hrdT.1, hrdT.2.1, hrdT.2.2.1, hrdT.2.2.2.1, hrdT.2.2.2.2]
        exact evWrite_numsOk hsn htc' hesMemP
    ihave write : write_ptr ↦ true $$ [write]
    · iExactEq write; rw [hWb]
    have hwr := h_write n_ptr rd_ptr hs_ptr write_ptr c n γ j I AntSim.mskB2 v₂
      (rdD.memRec { I.v with told := b }) net₀ xnet₀ d₂ f₂ hp hsl
      (HardStateM.mk I.r.p.term I.r.p.vote I.r.p.commit)
      (HardStateM.mk I.v.dur.term I.v.dur.vote I.v.dur.commit) oh d I.v.dur els ms γs k old q
    unfold github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.parallel.writeE at hwr
    iapply hwr _ mskB2_refl hinm has hbt hpar hesNorm (saveOk_ready hLI hhead) Hidx Hkb hal2
    clear hwr
    iframe Hpkg Hc Hn n rd hs write Hhs HhsH Hoh Hd Hdisk Hkill Hsl Hbig Hms Hlock Hmeta Hpre HentsZ Hv Hl
      Hlb Hxlb
    iintro %d₃ %f₃ %wr %v₃ %net₃ %xnet₃ ⟨n, rd, hs, write, Hhs, Hkill, Hdisk, Hms, Hmeta, -, Hlog, Hv, Hl,
      #Hlb3, #Hxlb3, %Hfin⟩
    have hvn3 : ViewNormal v₃ := by
      rcases Hfin.2.2.2.1 with ⟨-, hv⟩ | ⟨-, hv⟩ | ⟨-, -, hv⟩ <;> (rw [hv]; exact viewNormal_congr hvn2 rfl rfl)
    have hDR : DiskRel v₃ (if wr = true then saveW I.v.dur oh I.es else I.v.dur) := by
      rcases Hfin.2.2.2.1 with ⟨hw0, hv⟩ | ⟨-, hv⟩ | ⟨-, hw1, hv⟩
      · rw [hw0, hv]; left; rw [hdur2]; rfl
      · rw [hv]
        by_cases hw : wr = true
        · left; rw [if_pos hw, hsw, ← hwm]; show _ = v₂.dur.write _; rw [hdur2]; rfl
        · right; rw [if_neg hw]; exact ⟨by show some v₂.dur = _; rw [hdur2], rfl⟩
      · rw [hw1, hv]; left; rw [if_pos rfl, hsw, ← hwm]; show _ = v₂.dur.write _; rw [hdur2]; rfl
    have hf3 : γ.mode.Restarts' = false → f₃ = W64 0 ∧ d₃ = false := fun hr => by
      obtain ⟨hd1', hf1⟩ := hfz1 (hRst hr)
      obtain ⟨hd2', hf2⟩ := Hreq.1 hf1
      obtain ⟨hd3', hf3'⟩ := Hfin.1 hf2
      exact ⟨hf3', by rw [hd3', hd2', hd1']⟩
    have hHold := DrainIterB1.holds_saveW γ.toAntNames j I oh hok Hhold.1 (Hoh1.trans hH.symm)
      (saveOk_ready hLI hhead) hcm Httc
    -- the enter promise, once the disk is written
    iapply (wp_ncfupd _ _ (by rfl))
    unfold ncfupd
    iintro Hnc
    iunfold readyEnterB2 at Henter
    by_cases hwr : wr = true
    · imod Henter $$ %⊤ %(1 : Qp) %CoPset.subseteq_top Hnc [$Hdur $Hgv] with
        ⟨Hnc, Hdur, Hgv, Hfree, Hdf, -⟩
      ihave Hrcpt := append_postB1 I.rs.storage γs I.es k Hk $$ [$Hbridge' $Hlog]
      ihave Hrcpt : appendReceipt (GF := GF) I.rs₁.storage I.rs₁.unpersisted [] $$ [Hrcpt]
      · iExactEq Hrcpt; rfl
      imod h_app γ.R.md hs hcc hfw hasR γ.raft.raftNames I.rn (AntSim.nodeId j) I.rs₁ (rAccepted I.r) I.qs
        I.ip [] rfl (fun hh => absurd rfl hh) $$ Hraw Hrcpt with Hraw
      imodintro
      iframe Hnc
      rw [if_pos hwr] at hDR ⊢
      wp_auto
      by_cases hd3 : d₃ = true
      · -- killed after the write
        have hre : γ.mode.Restarts' = true := by
          cases hr : γ.mode.Restarts'
          · have := (hf3 hr).2; rw [hd3] at this; cases this
          · rfl
        rw [hd3]
        ispecialize HΦ $$ %v₃ %net₀ %xnet₀
        iapply HΦ
        iunfold nodeExitB2
        iframe Hl Hadd Htok
        iright
        have hdi := nodeOwnB2HD_dead_intro (GF := GF) c γ j n v₃ d I.rn ms hp cl₂ csl
          (roleStr (roleAfter I.rs.role I.ss)) applied f₃ (saveW I.v.dur oh I.es) si
          { I.rs₁ with unpersisted := [] } I.qs I.ip
          (rAccepted I.r) x g I.rs₂.dur (oh.getD (HardStateM.mk I.v.dur.term I.v.dur.vote I.v.dur.commit))
          hvn3 hDR hre Hsto hHold
        iapply hdi
        iframe Hd Hrn Hms Hrole Hhs Hcause Happl Hconf Hkill Hv Hdisk Hraw Hgv Hdur Htlb1 Hbud
        isplitl [Hbr Hmeta]
        · iunfold nodeStor
          iframe Hbr
          iexists γs
          iframe Hlock Hmeta Hbridge
          ipureintro; exact Hsz
        isplitl [Hmem]
        · iapply (nodeMemB2_view (GF := GF) γ j n I.v v₃ x g I.rs.phs I.rs₁.phs I.rs.dur I.rs.dur
            I.rs₁.dur I.rs₂.dur true none has hbt (fun h => Bool.noConfusion h))
          iapply nodeMemB2_kill
          iexact Hmem
        rw [Hoh1]; iexact HhsH
      · -- alive
        have hd3' : d₃ = false := by simpa using hd3
        obtain ⟨-, hv3⟩ := Hfin.2.2.1 hd3'
        have hd2' : d₂ = false := by
          cases h : d₂
          · rfl
          · have := (Hfin.2.1 h).1; rw [hd3'] at this; cases this
        have hd1' : d₁ = false := by
          cases h : d₁
          · rfl
          · have := Hreq.2.1 h; rw [hd2'] at this; cases this
        have hPe := hP2 hd2'
        have hv1e := ha1 hd1'
        have hf3' : γ.mode.Restarts' = false → f₃ = W64 0 := fun hr => (hf3 hr).1
        have hdur3 : v₃.dur = AntSim.durOf (AntSim.accepted I.r) := by
          rw [hv3]; show v₂.dur.write (rdD.memRec { I.v with told := b }) = _; rw [hdur2]; exact hwm
        have hpend3 : v₃.pend = P₂ := by rw [hv3, hv2]
        ispecialize HΦ $$ %v₃ %net₃ %xnet₃
        subst hd3' hd2' hd1' hv3 hv2 hv1e hrdD
        icases (parCauseB2_alive γ j _ cl₂ net₂ xnet₂).1 $$ Hpc with ⟨Hco2, -, -⟩
        have hrv := drainView_rep (I := I) (id := AntSim.nodeId j) b hok.1 hce0 hout hfull Hvn.1 Hshape.1
        iapply HΦ
        iunfold nodeExitB2
        iframe Hl Hadd Htok
        ileft
        iframe Hmsgs
        isplitl
        · iunfold drainMidB2
          iexists x, g, hp
          iframe Hrn Hgv Hdur Hfree Hdf Hce Hrs Hrsr
          isplitl [Hraw]
          · iExactEq Hraw; rfl
          isplitl
          · iunfold loopRestB2
            iexists d, ms, cl₂, csl, roleStr (roleAfter I.rs.role I.ss), applied, f₃, saveW I.v.dur oh I.es,
              si, oh.getD (HardStateM.mk I.v.dur.term I.v.dur.vote I.v.dur.commit)
            iframe Hd Hms Hrole Hhs Hcause Happl Hconf Hkill Hv Hdisk Hbud Htlb2 Hcs Hlb3 Hxlb3
            isplitr
            · ipureintro; exact ⟨hvn3, hDR, hf3'⟩
            isplitl [Hbr Hmeta]
            · iunfold nodeStor
              iframe Hbr
              iexists γs
              iframe Hlock Hmeta Hbridge
              ipureintro; exact Hsz
            isplitr
            · ipureintro; exact Hsto
            isplitr
            · ipureintro; exact hHold
            isplitl [Hmem]
            · iapply (nodeMemB2_view (GF := GF) γ j n I.v _ x g I.rs.phs I.rs₂.phs I.rs.dur I.rs.dur
                I.rs₂.dur I.rs₂.dur false none has hbt (fun _ => ⟨rfl, rfl⟩))
              iexact Hmem
            isplitr
            · rw [Hoh1]; iexact HhsH
            isplitr
            · ipureintro
              refine ⟨Hpv.1, ?_, Hpv.2.2.1, hok.2.1, fun _ => ⟨?_, by rw [hdur3, hsw], hparts0⟩⟩
              · exact (roleS_drainOf (v := { I.v with told := b }) (qs := I.qs) (sts := I.sts) hout).symm
              · rw [Hoh1, hdur3]; rfl
            isplitr
            · iExactEq Hrq; rfl
            isplitr
            · ipureintro; exact Hc0
            iExactEq Hco2; rfl
          ipureintro
          refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, hok⟩
          exact rsViewB2_of (rsView_congr hrv.1 hdur3 rfl rfl rfl rfl)
        ipureintro
        rw [hpend3, hPe, reqPend_end]
        exact ⟨rfl, rfl⟩
    · imodintro
      iframe Hnc
      rw [if_neg hwr] at hDR ⊢
      wp_auto
      have hd3 : d₃ = true := by
        cases h : d₃
        · exact absurd (Hfin.2.2.1 h).1 hwr
        · rfl
      have hre : γ.mode.Restarts' = true := by
        cases hr : γ.mode.Restarts'
        · have := (hf3 hr).2; rw [hd3] at this; cases this
        · rfl
      rw [hd3]
      ispecialize HΦ $$ %v₃ %net₀ %xnet₀
      iapply HΦ
      iunfold nodeExitB2
      iframe Hl Hadd Htok
      iright
      have hdi := nodeOwnB2HD_dead_intro (GF := GF) c γ j n v₃ d I.rn ms hp cl₂ csl
        (roleStr (roleAfter I.rs.role I.ss)) applied f₃ I.v.dur si I.rs₁ I.qs I.ip
        (rAccepted I.r) x g I.rs.dur (oh.getD (HardStateM.mk I.v.dur.term I.v.dur.vote I.v.dur.commit))
        hvn3 hDR hre Hsto Hhold
      iapply hdi
      iframe Hd Hrn Hms Hrole Hhs Hcause Happl Hconf Hkill Hv Hdisk Hraw Hgv Hdur Htlb1 Hbud
      isplitl [Hbr Hmeta]
      · iunfold nodeStor
        iframe Hbr
        iexists γs
        iframe Hlock Hmeta Hbridge
        ipureintro; exact Hsz
      isplitl [Hmem]
      · iapply (nodeMemB2_view (GF := GF) γ j n I.v v₃ x g I.rs.phs I.rs₁.phs I.rs.dur I.rs.dur I.rs₁.dur
          I.rs.dur true none has hbt (fun h => Bool.noConfusion h))
        iapply nodeMemB2_kill
        iexact Hmem
      rw [Hoh1]; iexact HhsH
  · -- nothing to write
    have hWb : decide (HsNew I.h ∨ ¬I.es = []) = false := decide_eq_false hW
    simp only [not_or, Classical.not_not] at hW
    obtain ⟨hE, hes⟩ := hW
    have hoh0 : (none : Option HardStateM).getD (HardStateM.mk I.v.dur.term I.v.dur.vote I.v.dur.commit) =
        phsNext I.rs.phs I.h := by
      rw [Option.getD_none, phsNext_empty _ _ (Classical.not_not.mp hE), hok.1.1]
    have hsv0 : SaveOk I.v.dur I.es := by rw [hes]; intro e he; cases he
    have hHold0 := DrainIterB1.holds_saveW γ.toAntNames j I none hok Hhold.1 hoh0 hsv0 hcm Httc
    rw [hes] at hHold0
    have hf2 : γ.mode.Restarts' = false → f₂ = W64 0 ∧ d₂ = false := fun hr => by
      obtain ⟨hd1', hf1⟩ := hfz1 (hRst hr)
      obtain ⟨hd2', hf2'⟩ := Hreq.1 hf1
      exact ⟨hf2', by rw [hd2', hd1']⟩
    ihave write : write_ptr ↦ false $$ [write]
    · iExactEq write; rw [hWb]
    -- the enter promise (no write)
    iapply (wp_ncfupd _ _ (by rfl))
    unfold ncfupd
    iintro Hnc
    iunfold readyEnterB2 at Henter
    imod Henter $$ %⊤ %(1 : Qp) %CoPset.subseteq_top Hnc [$Hdur $Hgv] with
      ⟨Hnc, Hdur, Hgv, Hfree, Hdf, -⟩
    ihave Hrcpt : appendReceipt (GF := GF) I.rs₁.storage I.rs₁.unpersisted [] $$ []
    · iunfold appendReceipt; ileft; ipureintro; exact hes
    imod h_app γ.R.md hs hcc hfw hasR γ.raft.raftNames I.rn (AntSim.nodeId j) I.rs₁ (rAccepted I.r) I.qs
      I.ip [] rfl (fun hh => absurd rfl hh) $$ Hraw Hrcpt with Hraw
    imodintro
    iframe Hnc
    wp_auto
    have hDR2 : DiskRel v₂ I.v.dur := .inl hdur2.symm
    by_cases hd2 : d₂ = true
    · -- killed on the way
      have hre : γ.mode.Restarts' = true := by
        cases hr : γ.mode.Restarts'
        · have := (hf2 hr).2; rw [hd2] at this; cases this
        · rfl
      rw [hd2]
      ispecialize HΦ $$ %v₂ %net₀ %xnet₀
      iapply HΦ
      iunfold nodeExitB2
      iframe Hl Hadd Htok
      iright
      have hdi := nodeOwnB2HD_dead_intro (GF := GF) c γ j n v₂ d I.rn ms hsl cl₂ csl
        (roleStr (roleAfter I.rs.role I.ss)) applied f₂ I.v.dur si
        { I.rs₁ with unpersisted := [] } I.qs I.ip
        (rAccepted I.r) x g I.rs₂.dur (HardStateM.mk I.v.dur.term I.v.dur.vote I.v.dur.commit)
        hvn2 hDR2 hre Hsto hHold0
      iapply hdi
      iframe Hd Hrn Hms Hrole Hhs Hcause Happl Hconf Hkill Hv Hdisk Hraw Hgv Hdur Htlb1 Hbud Hstor
      isplitl [Hmem]
      · iapply (nodeMemB2_view (GF := GF) γ j n I.v v₂ x g I.rs.phs I.rs₁.phs I.rs.dur I.rs.dur
          I.rs₁.dur I.rs₂.dur true none has hbt (fun h => Bool.noConfusion h))
        iapply nodeMemB2_kill
        iexact Hmem
      iexact Hhsro
    · -- alive
      have hd2' : d₂ = false := by simpa using hd2
      have hd1' : d₁ = false := by
        cases h : d₁
        · rfl
        · have := Hreq.2.1 h; rw [hd2'] at this; cases this
      have hPe := hP2 hd2'
      have hv1e := ha1 hd1'
      have hf2' : γ.mode.Restarts' = false → f₂ = W64 0 := fun hr => (hf2 hr).1
      have hpend2 : v₂.pend = P₂ := by rw [hv2]
      have hm2 : v₂.mems = [] := by rw [hv2, hv1e]; simp [parMemV, hWb, Hmems0]
      ihave Hmem : nodeMemB2 γ j n v₂ x g I.rs₂.phs I.rs₂.dur I.rs₂.dur false none $$ [Hmem]
      · iapply (nodeMemB2_view (GF := GF) γ j n I.v v₂ x g I.rs.phs I.rs₂.phs I.rs.dur I.rs.dur
          I.rs₂.dur I.rs₂.dur false none has hbt (fun _ => ⟨hm2, rfl⟩))
        iexact Hmem
      ispecialize HΦ $$ %v₂ %net₂ %xnet₂
      subst hd2' hd1' hv2 hv1e hrdD
      icases (parCauseB2_alive γ j _ cl₂ net₂ xnet₂).1 $$ Hpc with ⟨Hco2, #Hlb2, #Hxlb2⟩
      have hfv : I.r.full = I.v.r.full := (hnil hes).trans (by rw [hdurv]; rfl)
      have hrv := drainView_silent (I := I) (id := AntSim.nodeId j) hok.1 hce0 hout hfv Hvn.1 hE hes
      iapply HΦ
      iunfold nodeExitB2
      iframe Hl Hadd Htok
      ileft
      iframe Hmsgs
      isplitl
      · iunfold drainMidB2
        iexists x, g, hsl
        iframe Hrn Hgv Hdur Hfree Hdf Hce Hrs Hrsr
        isplitl [Hraw]
        · iExactEq Hraw; rfl
        isplitl
        · iunfold loopRestB2
          iexists d, ms, cl₂, csl, roleStr (roleAfter I.rs.role I.ss), applied, f₂, I.v.dur, si,
            HardStateM.mk I.v.dur.term I.v.dur.vote I.v.dur.commit
          iframe Hd Hms Hrole Hhs Hcause Happl Hconf Hkill Hv Hdisk Hbud Htlb2 Hcs Hlb2 Hxlb2 Hstor Hhsro
          isplitr
          · ipureintro; exact ⟨hvn2, hDR2, hf2'⟩
          isplitr
          · ipureintro; exact Hsto
          isplitr
          · ipureintro; exact hHold0
          isplitl [Hmem]
          · iexact Hmem
          isplitr
          · ipureintro
            refine ⟨Hpv.1, ?_, Hpv.2.2.1, hok.2.1, fun _ => ⟨rfl, rfl, hparts0⟩⟩
            exact (roleS_drainOf (v := { I.v with told := b }) (qs := I.qs) (sts := I.sts) hout).symm
          isplitr
          · iExactEq Hrq; rfl
          isplitr
          · ipureintro; exact Hc0
          iExactEq Hco2; rfl
        ipureintro
        refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, hok⟩
        exact rsViewB2_of (rsView_congr hrv.1 rfl rfl rfl rfl rfl)
      ipureintro
      rw [hpend2, hPe, reqPend_end]
      exact ⟨rfl, rfl⟩

end proof

end AntHarness
end EtcdGrove
end Perennial
