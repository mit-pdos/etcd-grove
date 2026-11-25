/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H3/PrepareReply.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H3: `handlePrepareReply` (the recovering leader's handling of a Prepare reply).

In a section with one `HeapGS`; `handlePrepareReply_wp_frozen` is the frozen
`handlePrepareReply.wp`'s statement.
-/
module

public import Dsverify.Proof.gryff.H3.Env
public import Dsverify.Proof.gryff.H3.Bcast
public import Dsverify.Proof.gryff.H3.Recover
public import Dsverify.Proof.gryff.H2b.Phase1
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2.h3

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.replica2
open Perennial.gryff.model (RState Copy LB Proposal Msg Ev Out Cmd Deps)
open Perennial.gryff.replica (XS rowOwn nSlots)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF]
variable [strconvA : strconv.Assumptions] -- N-5


set_option goose.wp.extras true

/-- The bookkeeping struct's fields are the model's (`lbRep`'s pure part). -/
def lbOk (gl : src.gryff.LeaderBookkeeping) (b : LB) : Prop :=
  gl.maxRecvBallot' = b.maxRecvBallot ∧ gl.prepareOKs' = b.prepareOKs ∧
    gl.allEqual' = b.allEqual ∧ gl.preAcceptOKs' = b.preAcceptOKs ∧
    gl.acceptOKs' = b.acceptOKs ∧ gl.nacks' = b.nacks ∧ depsOf gl.originalDeps' = b.originalDeps ∧
    gl.preparing' = b.preparing ∧ gl.numReplicasExecuted' = b.numReplicasExecuted ∧
    gl.repliedClient' = b.repliedClient

theorem lbRep_some_open (ρ : Repl2Names) (l : Loc) (b : LB) :
    lbRep (GF := GF) ρ l (some b) ⊣⊢ ∃ gl : src.gryff.LeaderBookkeeping, l ↦ gl ∗
      proposalsRep ρ gl.clientProposals' b.clientProposals ∗
      gl.committedDeps' ↦* b.committedDeps ∗ riRep gl.recoveryInst' b.recoveryInst ∗ ⌜lbOk gl b⌝ := by
  unfold lbRep; exact .rfl

theorem riRep_some_open (l : Loc) (ri : model.RecoveryInstance) :
    riRep (GF := GF) l (some ri) ⊣⊢ ∃ g : src.gryff.RecoveryInstance, l ↦ g ∗ cmdsRep g.cmds' ri.cmds ∗
      ⌜g.status' = ri.status ∧ g.seq' = ri.seq ∧ depsOf g.deps' = ri.deps ∧ vtOf g.base' = ri.base ∧
        g.preAcceptCount' = ri.preAcceptCount ∧ g.leaderResponded' = ri.leaderResponded ∧
        g.vbal' = ri.vbal⌝ := by
  unfold riRep; exact .rfl

/-- A fresh recovery instance holding the reply's values. -/
theorem riRep_reply (rp : Loc) (g : wire.gryffproto.PrepareReply.Msg) (msl : GoSlice) (cnt : w64)
    (lr : Bool) (hcm : model.cmdsOk (g.Command.map cmdOf) = true) :
    rp ↦ ({ cmds' := msl, status' := g.Status, seq' := g.Seq, deps' := g.Deps, base' := g.Base, preAcceptCount' := cnt, leaderResponded' := lr, vbal' := g.VBallot } : src.gryff.RecoveryInstance) ∗
      msl ↦*□ g.Command ⊢ (riRep rp (some (model.riOf (prepareReplyOf g) cnt lr)) : IProp GF) := by
  iintro ⟨Hp, #Hs⟩
  iapply (riRep_some_open ..).2
  iexists _
  iframe Hp
  isplitr
  · iunfold cmdsRep; iexists g.Command; iframe Hs; ipureintro; exact ⟨rfl, hcm⟩
  ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The bookkeeping with a new recovery-instance pointer. -/
theorem lbRep_setRI (ρ : Repl2Names) (l rp : Loc) (gl : src.gryff.LeaderBookkeeping) (b : LB)
    (ri : Option model.RecoveryInstance) (hf : lbOk gl b) :
    l ↦ { gl with recoveryInst' := rp } ∗ proposalsRep ρ gl.clientProposals' b.clientProposals ∗
      gl.committedDeps' ↦* b.committedDeps ∗ riRep (GF := GF) rp ri ⊢
      lbRep ρ l (some { b with recoveryInst := ri }) := by
  iintro ⟨Hl, Hp, Hc, Hr⟩
  iapply (lbRep_some_open ..).2
  iexists _
  iframe Hl Hp Hc Hr
  ipureintro; exact hf

/-- After a pre-accepted reply, there is a candidate. -/
theorem prPre_ri (lb : LB) (m : model.PrepareReplyM) :
    ∃ ri, (prPre lb m).recoveryInst = some ri := by
  unfold prPre
  rcases h : lb.recoveryInst with _ | ri
  · exact ⟨_, rfl⟩
  · dsimp only
    by_cases h1 : (prUnchanged m && model.sgt ri.preAcceptCount 0) = true
    · rw [if_pos h1]; exact ⟨_, rfl⟩
    · rw [if_neg h1]
      by_cases h2 : prUnchanged m = true
      · rw [if_pos h2]; exact ⟨_, rfl⟩
      · rw [if_neg h2]; exact ⟨ri, h⟩

/-- The bookkeeping, no longer preparing. -/
theorem lbRep_unprep (ρ : Repl2Names) (l : Loc) (gl : src.gryff.LeaderBookkeeping) (b : LB)
    (ri : Option model.RecoveryInstance) (hri : b.recoveryInst = ri) (hf : lbOk gl b) :
    l ↦ { gl with preparing' := false } ∗ proposalsRep ρ gl.clientProposals' b.clientProposals ∗
      gl.committedDeps' ↦* b.committedDeps ∗ riRep (GF := GF) gl.recoveryInst' ri ⊢
      lbRep ρ l (some { b with preparing := false }) := by
  iintro ⟨Hl, Hp, Hc, Hr⟩
  iapply (lbRep_some_open ..).2
  iexists _
  iframe Hl Hp Hc
  rw [hri]
  iframe Hr
  ipureintro
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := hf
  exact ⟨f1, f2, f3, f4, f5, f6, f7, rfl, f9, f10⟩

/-- The bookkeeping, no longer preparing (its candidate named). -/
theorem lbRep_unprep' (ρ : Repl2Names) (l : Loc) (gl : src.gryff.LeaderBookkeeping) (b : LB)
    (ri : Option model.RecoveryInstance) (hf : lbOk gl b) :
    l ↦ { gl with preparing' := false } ∗ proposalsRep ρ gl.clientProposals' b.clientProposals ∗
      gl.committedDeps' ↦* b.committedDeps ∗ riRep (GF := GF) gl.recoveryInst' ri ⊢
      lbRep ρ l (some { b with preparing := false, recoveryInst := ri }) := by
  iintro ⟨Hl, Hp, Hc, Hr⟩
  iapply (lbRep_some_open ..).2
  iexists _
  iframe Hl Hp Hc Hr
  ipureintro
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := hf
  exact ⟨f1, f2, f3, f4, f5, f6, f7, rfl, f9, f10⟩

section uc
variable (s : RState) (cmds : List Cmd) (q i seq : w32)
/-! `updateConflicts` changes the conflict tables and `maxSeq` only. -/
theorem uc_maxN : (model.updateConflicts s cmds q i seq).maxN = s.maxN := by
  obtain ⟨cf, ms, h⟩ := h2b.updateConflicts_shape s cmds q i seq; rw [h]
theorem uc_rops : (model.updateConflicts s cmds q i seq).rops = s.rops := by
  obtain ⟨cf, ms, h⟩ := h2b.updateConflicts_shape s cmds q i seq; rw [h]
theorem uc_wops : (model.updateConflicts s cmds q i seq).wops = s.wops := by
  obtain ⟨cf, ms, h⟩ := h2b.updateConflicts_shape s cmds q i seq; rw [h]
theorem uc_ongoingReqs : (model.updateConflicts s cmds q i seq).ongoingReqs = s.ongoingReqs := by
  obtain ⟨cf, ms, h⟩ := h2b.updateConflicts_shape s cmds q i seq; rw [h]
theorem uc_id : (model.updateConflicts s cmds q i seq).id = s.id := by
  obtain ⟨cf, ms, h⟩ := h2b.updateConflicts_shape s cmds q i seq; rw [h]
theorem uc_tag : (model.updateConflicts s cmds q i seq).tag = s.tag := by
  obtain ⟨cf, ms, h⟩ := h2b.updateConflicts_shape s cmds q i seq; rw [h]
theorem uc_ongoing : (model.updateConflicts s cmds q i seq).ongoing = s.ongoing := by
  obtain ⟨cf, ms, h⟩ := h2b.updateConflicts_shape s cmds q i seq; rw [h]
theorem uc_val : (model.updateConflicts s cmds q i seq).val = s.val := by
  obtain ⟨cf, ms, h⟩ := h2b.updateConflicts_shape s cmds q i seq; rw [h]
theorem uc_proposeQ : (model.updateConflicts s cmds q i seq).proposeQ = s.proposeQ := by
  obtain ⟨cf, ms, h⟩ := h2b.updateConflicts_shape s cmds q i seq; rw [h]
end uc

set_option hygiene false in
/-- The copy keeps its struct, with the bookkeeping `LB` (`Hlb`): put it back (closing (a)),
close the replica (the goal: `|={⊤}=> Φ #()`, at `s.setInst q i { c with lb := some LB }`). -/
local macro "h3_pr_keep" : tactic => `(tactic| (
  ihave Hc : copyRep ρ xs (sint.Z g.Replica, sint.Z g.Instance) ptr { c with lb := some LB } $$ [Hiv Hlb]
  · iapply (copyRep_open ..).2; iexists iv; iframe Hiv Hcmds Hlb; ipureintro; exact Hivf
  icases Hclose with ⟨Ha, -⟩
  ihave Hep := Ha $$ %({ c with lb := some LB }) [] Hsq Hc
  · ipureintro
    refine ⟨rfl, fun hh => ?_⟩
    rw [coe_setInst _ _ _ _ hbox']
    rw [coe_slot _ _ _ hbox', hc] at hh
    exact hh
  imod Hep
  ihave Hco := coordOwn_congr ρ co _ k s (s.setInst g.Replica g.Instance { c with lb := some LB })
    rfl rfl rfl rfl $$ Hco
  imodintro
  iapply HΦ
  iframe Hpend
  iapply handler_close γ ρ k r gR h pa co xs
  iframe Henv
  iunfold parts
  simp only [setInst_tag, setInst_ongoing, setInst_val, setInst_proposeQ, setInst_id]
  iframe
  ipureintro; exact Hid))

set_option hygiene false in
/-- The reply changes nothing (`c` unchanged at `ptr`, `Hlb` its bookkeeping): put the copy
back, close the replica (the goal: `|={⊤}=> Φ #()`). -/
local macro "h3_pr_same" : tactic => `(tactic| (
  ihave Hc : copyRep ρ xs (sint.Z g.Replica, sint.Z g.Instance) ptr c $$ [Hiv Hlb]
  · iapply (copyRep_open ..).2; iexists iv; iframe Hiv Hcmds
    isplitl [Hlb]
    · first | iexact Hlb | (rw [‹c.lb = _›]; iexact Hlb)
    ipureintro; exact Hivf
  icases Hclose with ⟨Ha, -⟩
  ihave Hep := Ha $$ %c [] Hsq Hc
  · ipureintro; refine ⟨rfl, fun hh => ?_⟩; rw [setInst_self _ _ _ _ hc]; exact hh
  imod Hep
  rw [setInst_self _ _ _ _ hc]
  imodintro
  iapply HΦ
  iframe Hpend
  iapply handler_close γ ρ k r gR h pa co xs
  iframe Henv
  iunfold parts
  iframe
  ipureintro; exact Hid))

variable [pD : GryffPartiDeps (GF := GF)] in
set_option maxHeartbeats 4000000 in
theorem handlePrepareReply_wp' (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h p : Loc)
    (m : model.PrepareReplyM) (t : List Ev) (s s' : RState) (outs : List Out)
    (hstep : model.stepR k s (.msg (.prepareReply m)) = .ok (s', outs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r ∗
        replicaOwn ρ k r s ∗ pendingOuts γ ρ k r t outs ∗
        (handlerOf r h ∗ msgAt p (.prepareReply m)) }}
      (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!!
        go!"handlePrepareReply")) (Val #p))
    {{ RET #(); replicaOwn ρ k r s' ∗ pendingOuts γ ρ k r t [] }} := by
  wp_start as ⟨#Hrep, Hown, Hpend, ⟨Hh, Hmsg⟩⟩
  have hrec : model.stepPrepareReply s m = .ok (s', outs) := by
    simpa [model.stepR] using hstep
  ihave ⟨%gR, %pa, %co, %xs, #Henv, Hparts⟩ := handler_open γ ρ k r h s $$ [Hrep Hh Hown]
  · iframe # ∗
  iunfold parts at Hparts
  ihave #Henv' := Henv
  iunfold epEnv at Henv'
  icases Henv' with ⟨#HgR, #Hpa', #Hco', #Hh', #HR', #HId, #HN, #HDur, #Hok, #Hfix⟩
  icases Hparts with ⟨Hpa, Hval, Hco, Hep, Hxs, Hprop, Hscr, %Hid⟩
  iunfold msgAt at Hmsg
  icases Hmsg with ⟨%g, %msl, Hg, #Hmsl, %Hg⟩
  subst Hg
  obtain ⟨hbox, c, hc, hres⟩ := stepPrepareReply_guards s s' _ outs hrec
  simp only [prepareReplyOf] at hbox hc hres
  have hbox' := hbox
  icases epaxosOwn_inst_open' ρ h r xs s g.Replica g.Instance hbox $$ Hep with
    ⟨%ispS, %sq, %isp, %ptrs, %ptr, #HIS, #Hisp, %Hsl, Hsq, Hcase, %Hunc, Hclose⟩
  rw [hc]
  icases Hcase with ⟨%Hnn, Hc⟩
  icases (copyRep_open ..).1 $$ Hc with ⟨%iv, Hiv, #Hcmds, Hlb, %Hivf⟩
  simp only [model.inBox, decide_eq_true_eq] at hbox
  obtain ⟨hq0, hq3, hi0, hiS⟩ := hbox
  obtain ⟨hsq, hptr⟩ := Hsl
  ihave %HispL := ownSlice_len _ _ _ $$ Hisp
  ihave %HsqL := ownSlice_len _ _ _ $$ Hsq
  have hqZ : sint.Z (W64 (sint.Z g.Replica)) = sint.Z g.Replica := by word
  have hiZ : sint.Z (W64 (sint.Z g.Instance)) = sint.Z g.Instance := by word
  have hqlen : sint.Z g.Replica < sint.Z ispS.len := by
    have h0 := (List.getElem?_eq_some_iff.1 hsq).1
    have h1 := HispL.1; have h2 := HispL.2
    simp only [sint.nat, sint.Z] at h1 h2 hq0 h0 ⊢; omega
  have hilen : sint.Z g.Instance < sint.Z sq.len := by
    have h0 := (List.getElem?_eq_some_iff.1 hptr).1
    have h1 := HsqL.1; have h2 := HsqL.2
    simp only [sint.nat, sint.Z] at h1 h2 hi0 h0 ⊢; omega
  iapply wp_fupd
  wp_auto
  rw [hqZ, if_pos ⟨hq0, hqlen⟩]
  wp_apply wp_load_slice_index ispS _ isp _ sq hq0 $$ [Hisp] as -
  · iframe Hisp; ipureintro; exact hsq
  rw [hiZ, if_pos ⟨hi0, hilen⟩]
  wp_apply wp_load_slice_index sq _ ptrs _ ptr hi0 $$ [Hsq] as Hsq
  · iframe Hsq; ipureintro; exact hptr
  rcases hres with ⟨hg1, rfl, rfl⟩ | ⟨lb, hlb, hprep, hres⟩
  · -- no bookkeeping, or not preparing: ignored
    rcases hlb : c.lb with _ | lb
    · iunfold lbRep at Hlb
      icases Hlb with %Hnull
      ihave Hlb : lbRep ρ iv.lb' none $$ []
      · iunfold lbRep; ipureintro; exact Hnull
      wp_if_destruct
      · h3_pr_same
      · exact absurd Hnull ‹_›
    · have hnp : lb.preparing = false := by rw [hlb] at hg1; simpa using hg1
      iunfold lbRep at Hlb
      icases Hlb with ⟨%glb, Hglb, Hprops, Hcd, Hri, %Hgf⟩
      ihave %Hgn := typedPointsto_not_null _ _ _ $$ Hglb
      have hgp : glb.preparing' = false := Hgf.2.2.2.2.2.2.2.1.trans hnp
      wp_if_destruct
      · exact absurd ‹_› Hgn
      rw [hgp]
      wp_auto
      ihave Hlb : lbRep ρ iv.lb' (some lb) $$ [Hglb Hprops Hcd Hri]
      · iunfold lbRep; iexists glb; iframe; ipureintro; exact Hgf
      h3_pr_same
  -- preparing: the guards on the copy and the reply
  rw [hlb]
  iunfold lbRep at Hlb
  icases Hlb with ⟨%glb, Hglb, Hprops, Hcd, Hri, %Hgf⟩
  ihave %Hgn := typedPointsto_not_null _ _ _ $$ Hglb
  have hgp : glb.preparing' = true := Hgf.2.2.2.2.2.2.2.1.trans hprep
  wp_if_destruct
  · exact absurd ‹_› Hgn
  rw [hgp]
  wp_auto
  have hs0 := Hivf.2.1
  rcases hres with ⟨hcs, rfl, rfl⟩ | ⟨hncs, hres⟩
  · -- committed here: ignored
    wp_if_destruct
    · ihave Hlb : lbRep ρ iv.lb' (some lb) $$ [Hglb Hprops Hcd Hri]
      · iunfold lbRep; iexists glb; iframe; ipureintro; exact Hgf
      h3_pr_same
    wp_if_destruct
    · ihave Hlb : lbRep ρ iv.lb' (some lb) $$ [Hglb Hprops Hcd Hri]
      · iunfold lbRep; iexists glb; iframe; ipureintro; exact Hgf
      h3_pr_same
    exfalso
    rcases hcs with e | e
    · exact ‹¬iv.Status' = W8 4› (hs0.trans e)
    · exact ‹¬iv.Status' = W8 5› (hs0.trans e)
  wp_if_destruct
  · exact absurd (hs0.symm.trans ‹_›) (fun e => hncs (Or.inl e))
  wp_if_destruct
  · exact absurd (hs0.symm.trans ‹_›) (fun e => hncs (Or.inr e))
  rcases hres with ⟨hokf, rfl, rfl⟩ | ⟨hok, hres⟩
  · -- a nack: counted
    wp_if_destruct
    rotate_left
    · exact absurd hokf ‹_›
    let c' : Copy := { c with lb := some { lb with nacks := lb.nacks + 1 } }
    ihave Hc : copyRep ρ xs (sint.Z g.Replica, sint.Z g.Instance) ptr c' $$
        [Hiv Hglb Hprops Hcd Hri]
    · iapply (copyRep_open ..).2; iexists iv; iframe Hiv Hcmds
      isplitl
      · iunfold lbRep; iexists _; iframe Hglb Hprops Hcd Hri
        ipureintro
        obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := Hgf
        exact ⟨f1, f2, f3, f4, f5, by first | rfl | (rw [f6]; rfl) | (simp only [f6]; rfl), f7, f8, f9, f10⟩
      ipureintro; exact Hivf
    icases Hclose with ⟨Ha, -⟩
    ihave Hep := Ha $$ %c' [] Hsq Hc
    · ipureintro
      refine ⟨rfl, fun hh => ?_⟩
      rw [coe_setInst _ _ _ _ hbox']
      rw [coe_slot _ _ _ hbox', hc] at hh
      exact hh
    imod Hep
    ihave Hco := coordOwn_congr ρ co _ k s (s.setInst g.Replica g.Instance c') rfl rfl rfl rfl $$ Hco
    imodintro
    iapply HΦ
    iframe Hpend
    iapply handler_close γ ρ k r gR h pa co xs
    iframe Henv
    iunfold parts
    simp only [setInst_tag, setInst_ongoing, setInst_val, setInst_proposeQ, setInst_id]
    iframe
    ipureintro; exact Hid
  wp_if_destruct
  · exact absurd ‹_› hok
  rcases hres with ⟨hbn, rfl, rfl⟩ | ⟨hbe, hcm, hmain⟩
  · -- a promise for another ballot: ignored
    wp_if_destruct
    · exact absurd (Hif.trans Hivf.1) hbn
    · ihave Hlb : lbRep ρ iv.lb' (some lb) $$ [Hglb Hprops Hcd Hri]
      · iunfold lbRep; iexists glb; iframe; ipureintro; exact Hgf
      h3_pr_same
  wp_if_destruct
  rotate_left
  · exact absurd (hbe.trans Hivf.1.symm) Hif
  have hmC := hmain
  by_cases hC : g.Status = model.St.COMMITTED ∨ g.Status = model.St.EXECUTED
  · rw [prMain_committed _ _ _ _ hC] at hmC
    simp only [] at hmC
    split at hmC
    rotate_left
    · cases hmC
    rename_i outsC hbc
    simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hmC
    obtain ⟨rfl, rfl⟩ := hmC
    have hcoe : committedOrExecuted s (sint.Z g.Replica, sint.Z g.Instance) = false := by
      rw [coe_slot _ _ _ hbox', hc]; simp [hncs]
    obtain ⟨hnum, hlow, hnin⟩ := Hunc hcoe
    wp_if_destruct
    rotate_left
    wp_if_destruct
    rotate_left
    · exfalso
      rename_i h4
      rcases hC with h | h
      · exact h4 h
      · exact Hif h
    all_goals
      have hilt := (List.getElem?_eq_some_iff.1 hptr).1
      rw [hqZ, if_pos ⟨hq0, hqlen⟩]
      wp_apply wp_load_slice_index ispS _ isp _ sq hq0 $$ [Hisp] as -
      · iframe Hisp; ipureintro; exact hsq
      rw [hiZ, if_pos ⟨hi0, hilen⟩]
      wp_apply wp_store_slice_index sq _ ptrs «$r0_ptr» $$ [Hsq] as Hsq
      · iframe Hsq; ipureintro; omega
      irename «$r0» => HiI
      generalize «$r0_ptr» = pI
      ihave %HpInn := typedPointsto_not_null _ _ _ $$ HiI
      let c' : Copy := { cmds := g.Command.map cmdOf, ballot := c.ballot, status := model.St.COMMITTED, seq := g.Seq, deps := depsOf g.Deps, base := vtOf g.Base, lb := none, slot := g.Instance, leader := g.Replica, vbal := c.ballot }
      ihave Hc : copyRep ρ xs (sint.Z g.Replica, sint.Z g.Instance) pI c' $$ [HiI]
      · iapply (copyRep_open ..).2
        iexists _
        iframe HiI
        isplitr
        · iunfold cmdsRep
          iexists g.Command
          iframe Hmsl
          ipureintro; exact ⟨rfl, hcm⟩
        isplitr
        · iunfold lbRep; ipureintro; trivial
        ipureintro
        refine ⟨Hivf.1, rfl, rfl, rfl, rfl, rfl, rfl, Hivf.1, rfl, rfl, ?_, ?_, ?_⟩
        · rw [hnum]; rfl
        · rw [hlow]; rfl
        · constructor
          · intro e; cases e
          · intro e; exact absurd e hnin
      icases Hclose with ⟨-, -, Hcl⟩
      ihave Hep := Hcl $$ %pI %c' [] Hsq Hc
      · ipureintro; exact ⟨rfl, hcoe, HpInn⟩
      imod Hep
      wp_apply h2b.bcastCommit_wp' γ ρ k r gR h xs t (s.setInst g.Replica g.Instance c') g.Replica
        g.Instance g.Seq msl g.Command g.Deps g.Base outsC [] (by rw [setInst_id]; exact Hid) hcm
        hbc $$ [Hep Hpend] as ⟨Hep, Hpend⟩
      · rw [List.append_nil]
        iframe # ∗
        unfold h2b.bcFixed
        iframe #
      ihave Hco := coordOwn_congr ρ co _ k s (s.setInst g.Replica g.Instance c') rfl rfl rfl rfl $$ Hco
      imodintro
      iapply HΦ
      iframe Hpend
      iapply handler_close γ ρ k r gR h pa co xs
      iframe Henv
      iunfold parts
      simp only [setInst_tag, setInst_ongoing, setInst_val, setInst_proposeQ, setInst_id]
      iframe
      ipureintro; exact Hid
  · -- not committed: the candidate's updates, the quorum test, the choice
    rw [prMain_open _ _ _ _ hC] at hmC
    change prStage2 s (prepareReplyOf g) c
      (prAcc { lb with prepareOKs := lb.prepareOKs + 1, preparing := true } (prepareReplyOf g)) = _ at hmC
    generalize hm : prepareReplyOf g = m at hmC
    have hmst : m.status = g.Status := by rw [← hm]; rfl
    have hmvb : m.vbal = g.VBallot := by rw [← hm]; rfl
    have hmq : m.replica = g.Replica := by rw [← hm]; rfl
    have hmi : m.inst = g.Instance := by rw [← hm]; rfl
    have hmac : m.acceptorId = g.AcceptorId := by rw [← hm]; rfl
    have hmcm : m.cmds = g.Command.map cmdOf := by rw [← hm]; rfl
    generalize hlb1 : { lb with prepareOKs := lb.prepareOKs + 1, preparing := true } = lb1 at hmC
    ihave Hlb : lbRep ρ iv.lb' (some lb1) $$ [Hglb Hprops Hcd Hri]
    · iunfold lbRep; iexists _; iframe Hglb; rw [← hlb1]; iframe Hprops Hcd Hri
      ipureintro
      obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := Hgf
      exact ⟨f1, by rw [f2]; rfl, f3, f4, f5, f6, f7, hgp, f9, f10⟩
    wp_if_destruct
    · exact absurd (Or.inl Hif) hC
    wp_if_destruct
    · exact absurd (Or.inr Hif) hC
    -- the ACCEPTED reply's update (`prAcc`)
    wp_join iprop(lbRep ρ iv.lb' (some (prAcc lb1 m)) ∗ ptr ↦ iv ∗ inst_ptr ↦ ptr ∗
        preply_ptr ↦ p ∗ p ↦ wire.gryffproto.PrepareReply.goVal g msl)
      with [Hlb Hiv inst preply Hg] as ⟨Hlb, Hiv, inst, preply, Hg⟩
    · have hA : m.status = model.St.ACCEPTED := hmst.trans Hif
      iunfold lbRep at Hlb
      icases Hlb with ⟨%gl, Hgl, Hprops, Hcd, Hri, %Hglf⟩
      rcases hri : lb1.recoveryInst with _ | ri
      · iunfold riRep at Hri
        icases Hri with %Hnull
        wp_auto
        wp_if_destruct
        · ihave Hri := riRep_reply «$r0_ptr» g msl (W64 0) false hcm $$ [«$r0»]
          · iframe # ∗
          rw [hm]
          ihave Hlb := lbRep_setRI ρ iv.lb' «$r0_ptr» gl lb1 _ Hglf $$ [Hgl Hprops Hcd Hri]
          · iframe
          rw [show prAcc lb1 m = { lb1 with recoveryInst := some (model.riOf m 0 false) } by
            simp [prAcc, hA, prBetter, hri]]
          iframe
        · exact absurd Hnull ‹_›
      · iunfold riRep at Hri
        icases Hri with ⟨%gri, Hgri, #Hricmds, %Hrif⟩
        ihave %Hrinn := typedPointsto_not_null _ _ _ $$ Hgri
        wp_auto
        wp_if_destruct
        · exact absurd ‹_› Hrinn
        wp_if_destruct
        · -- an ACCEPTED candidate: replaced if of a smaller vbal
          have hst : ri.status = model.St.ACCEPTED := Hrif.1.symm.trans Hif
          try wp_auto
          wp_if_destruct
          · have hlt : model.slt ri.vbal m.vbal = true := by
              rw [← Hrif.2.2.2.2.2.2, hmvb]; simpa [model.slt] using ‹_›
            ihave Hri := riRep_reply «$r0_ptr» g msl (W64 0) false hcm $$ [«$r0»]
            · iframe # ∗
            rw [hm]
            ihave Hlb := lbRep_setRI ρ iv.lb' «$r0_ptr» gl lb1 _ Hglf $$ [Hgl Hprops Hcd Hri]
            · iframe
            rw [show prAcc lb1 m = { lb1 with recoveryInst := some (model.riOf m 0 false) } by
              simp [prAcc, hA, prBetter, hri, hlt]]
            iframe
          · -- kept
            have hnb : model.slt ri.vbal m.vbal = false := by
              rw [← Hrif.2.2.2.2.2.2, hmvb]; simpa [model.slt] using Hif
            rw [show prAcc lb1 m = lb1 by simp [prAcc, hA, prBetter, hri, hst, hnb]]
            ihave Hri : riRep gl.recoveryInst' (some ri) $$ [Hgri]
            · iapply (riRep_some_open ..).2; iexists gri; iframe Hgri Hricmds; ipureintro; exact Hrif
            ihave Hlb : lbRep ρ iv.lb' (some lb1) $$ [Hgl Hprops Hcd Hri]
            · iapply (lbRep_some_open ..).2; iexists gl; rw [hri]; iframe; ipureintro; exact Hglf
            iframe
        · -- the candidate is not ACCEPTED: replaced
          have hne : ri.status ≠ model.St.ACCEPTED := fun e => Hif (Hrif.1.trans e)
          ihave Hri := riRep_reply «$r0_ptr» g msl (W64 0) false hcm $$ [«$r0»]
          · iframe # ∗
          rw [hm]
          ihave Hlb := lbRep_setRI ρ iv.lb' «$r0_ptr» gl lb1 _ Hglf $$ [Hgl Hprops Hcd Hri]
          · iframe
          rw [show prAcc lb1 m = { lb1 with recoveryInst := some (model.riOf m 0 false) } by
            simp [prAcc, hA, prBetter, hri, hne]]
          iframe
    · rw [show prAcc lb1 m = lb1 by unfold prAcc; rw [if_neg]; rw [hmst]; exact Hif]
      iframe
    -- the pre-accepted reply's update and the leader's reply (`prStage2_eq`)
    generalize hLA : prAcc lb1 m = LA at hmC ⊢
    rw [prStage2_eq] at hmC
    wp_join (Q := fun v => iprop(∃ LB : LB, ⌜(v = returnVal #() ∧
          s' = s.setInst m.replica m.inst { c with lb := some LB } ∧ outs = []) ∨
        (v = executeVal ∧ prQuorum s m c LB = .ok (s', outs))⌝ ∗
        lbRep ρ iv.lb' (some LB) ∗ ptr ↦ iv ∗ inst_ptr ↦ ptr ∗ preply_ptr ↦ p ∗
        p ↦ wire.gryffproto.PrepareReply.goVal g msl))
      at (if: _ then _ else _) with [Hlb Hiv inst preply Hg] as ⟨%LB, %HLB, Hlb, Hiv, inst, preply, Hg⟩
    · wp_join (Q := fun v => iprop(⌜v = #(decide (prPreCond LA m))⌝ ∗ lbRep ρ iv.lb' (some LA) ∗
          ptr ↦ iv ∗ inst_ptr ↦ ptr ∗ preply_ptr ↦ p ∗ p ↦ wire.gryffproto.PrepareReply.goVal g msl))
        at (if: _ then _ else #false) with [Hlb Hiv inst preply Hg] as ⟨%Hv, Hlb, Hiv, inst, preply, Hg⟩
      · wp_if_destruct
        rotate_left
        wp_if_destruct
        rotate_left
        · -- not pre-accepted
          have hnP : ¬prPreCond LA m := by
            rintro ⟨h | h, -⟩
            · exact ‹¬g.Status = W8 1› (hmst.symm.trans h)
            · exact ‹¬g.Status = W8 2› (hmst.symm.trans h)
          iframe
          ipureintro
          simp [hnP]
        all_goals
          have hPA : m.status = model.St.PREACCEPTED ∨ m.status = model.St.PREACCEPTED_EQ := by
            rw [hmst]; first | exact Or.inl Hif | exact Or.inr Hif
          icases (lbRep_some_open ..).1 $$ Hlb with ⟨%gl, Hgl, Hprops, Hcd, Hri, %Hglf⟩
          rcases hri : LA.recoveryInst with _ | ri
          · iunfold riRep at Hri
            icases Hri with %Hnull
            try wp_auto
            wp_if_destruct
            · have hP : prPreCond LA m := ⟨hPA, by simp [hri]⟩
              ihave Hlb : lbRep ρ iv.lb' (some LA) $$ [Hgl Hprops Hcd]
              · iapply (lbRep_some_open ..).2; iexists gl; iframe; rw [hri]; iunfold riRep
                ipureintro; exact ⟨Hnull, Hglf⟩
              iframe
              ipureintro; simp [hP]
            · exact absurd Hnull ‹_›
          · icases (riRep_some_open ..).1 $$ Hri with ⟨%gri, Hgri, #Hricmds, %Hrif⟩
            ihave %Hrinn := typedPointsto_not_null _ _ _ $$ Hgri
            try wp_auto
            wp_if_destruct
            · exact absurd ‹_› Hrinn
            have hiff : prPreCond LA m ↔ sint.Z gri.status' < sint.Z (W8 3) := by
              simp only [prPreCond, hri, model.slt, decide_eq_true_eq, ← Hrif.1]
              exact ⟨fun h => h.2, fun h => ⟨hPA, h⟩⟩
            ihave Hri : riRep gl.recoveryInst' (some ri) $$ [Hgri]
            · iapply (riRep_some_open ..).2; iexists gri; iframe Hgri Hricmds; ipureintro; exact Hrif
            ihave Hlb : lbRep ρ iv.lb' (some LA) $$ [Hgl Hprops Hcd Hri]
            · iapply (lbRep_some_open ..).2; iexists gl; rw [hri]; iframe; ipureintro; exact Hglf
            iframe
            ipureintro
            rw [decide_eq_decide.mpr hiff]
      subst Hv
      wp_if_destruct
      · -- `unchanged`
        have hP := Hif
        wp_join (Q := fun v => iprop(⌜v = #(prUnchanged m)⌝ ∗ preply_ptr ↦ p ∗
            p ↦ wire.gryffproto.PrepareReply.goVal g msl))
          at (if: _ then _ else #false) with [preply Hg] as ⟨%Hv, preply, Hg⟩
        · wp_if_destruct
          · have h2 := Hif
            wp_if_destruct
            · have h0 := Hif
              try wp_auto
              iframe; ipureintro; congr 1
              simp [prUnchanged, hmst, hmvb, hmac, hmq, h2, h0, model.St.PREACCEPTED_EQ]
              by_cases e : g.AcceptorId = g.Replica <;> simp [e]
            · iframe; ipureintro; congr 1
              simp [prUnchanged, hmst, hmvb, h2, Hif, model.St.PREACCEPTED_EQ]
              intro h; exact absurd h Hif
          · iframe; ipureintro; congr 1
            simp [prUnchanged, hmst, Hif, model.St.PREACCEPTED_EQ]
            intro h; exact absurd h Hif
        subst Hv
        generalize hU : prUnchanged m = u
        wp_auto
        wp_join iprop(count_ptr ↦ (if u then W64 1 else W64 0)) with [count] as count
        all_goals try (simp only [Bool.false_eq_true, ↓reduceIte]; iframe)
        -- the candidate's update (`prPre`)
        wp_join iprop(lbRep ρ iv.lb' (some (prPre LA m)) ∗ ptr ↦ iv ∗ inst_ptr ↦ ptr ∗
            preply_ptr ↦ p ∗ p ↦ wire.gryffproto.PrepareReply.goVal g msl ∗ unchanged_ptr ↦ u ∗
            count_ptr ↦ (if u then W64 1 else W64 0))
          at (if: _ then _ else _) with [Hlb Hiv inst preply Hg unchanged count]
          as ⟨Hlb, Hiv, inst, preply, Hg, unchanged, count⟩
        · icases (lbRep_some_open ..).1 $$ Hlb with ⟨%gl, Hgl, Hprops, Hcd, Hri, %Hglf⟩
          rcases hri : LA.recoveryInst with _ | ri
          · iunfold riRep at Hri
            icases Hri with %Hnull
            wp_auto
            wp_if_destruct
            · ihave Hri := riRep_reply «$r0_ptr» g msl (if u = true then W64 1 else W64 0) false hcm
                $$ [«$r0»]
              · iframe # ∗
              rw [hm]
              ihave Hlb := lbRep_setRI ρ iv.lb' «$r0_ptr» gl LA _ Hglf $$ [Hgl Hprops Hcd Hri]
              · iframe
              have hpp : prPre LA m = { LA with recoveryInst := some (model.riOf m (if u = true then W64 1 else W64 0) false) } := by
                simp only [prPre, hri, hU]; rfl
              rw [hpp]
              iframe
            · exact absurd Hnull ‹_›
          · icases (riRep_some_open ..).1 $$ Hri with ⟨%gri, Hgri, #Hricmds, %Hrif⟩
            ihave %Hrinn := typedPointsto_not_null _ _ _ $$ Hgri
            wp_auto
            wp_if_destruct
            · exact absurd ‹_› Hrinn
            wp_if_destruct
            · -- kept
              rw [show prPre LA m = LA by simp [prPre, hri, hU]]
              ihave Hri : riRep gl.recoveryInst' (some ri) $$ [Hgri]
              · iapply (riRep_some_open ..).2; iexists gri; iframe Hgri Hricmds; ipureintro; exact Hrif
              ihave Hlb : lbRep ρ iv.lb' (some LA) $$ [Hgl Hprops Hcd Hri]
              · iapply (lbRep_some_open ..).2; iexists gl; rw [hri]; iframe; ipureintro; exact Hglf
              try wp_auto
              iframe
            · -- unchanged
              try wp_auto
              wp_if_destruct
              · -- counted
                have hgt : model.sgt ri.preAcceptCount 0 = true := by
                  rw [← Hrif.2.2.2.2.1]; simpa [model.sgt, model.slt] using ‹_›
                have hpp : prPre LA m = { LA with recoveryInst := some { ri with preAcceptCount := ri.preAcceptCount + 1 } } := by
                  unfold prPre; rw [hri]; simp only [hU, hgt, Bool.true_and, ↓reduceIte]
                rw [hpp]
                ihave Hri : riRep gl.recoveryInst' (some { ri with preAcceptCount := ri.preAcceptCount + 1 }) $$ [Hgri]
                · iapply (riRep_some_open ..).2; iexists _; iframe Hgri Hricmds; ipureintro
                  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := Hrif
                  exact ⟨f1, f2, f3, f4, by rw [f5]; rfl, f6, f7⟩
                ihave Hlb : lbRep ρ iv.lb' (some { LA with recoveryInst := some { ri with preAcceptCount := ri.preAcceptCount + 1 } }) $$ [Hgl Hprops Hcd Hri]
                · iapply (lbRep_some_open ..).2; iexists gl; iframe; ipureintro; exact Hglf
                iframe
              · -- replaces the candidate
                have hgt : model.sgt ri.preAcceptCount 0 = false := by
                  rw [← Hrif.2.2.2.2.1]
                  simp only [model.sgt, model.slt, decide_eq_false_iff_not]; exact Hif
                ihave Hri := riRep_reply «$r0_ptr» g msl (W64 1) gri.leaderResponded' hcm $$ [«$r0»]
                · iframe # ∗
                rw [hm]
                ihave Hlb := lbRep_setRI ρ iv.lb' «$r0_ptr» gl LA _ Hglf $$ [Hgl Hprops Hcd Hri]
                · iframe
                have hpp : prPre LA m = { LA with recoveryInst := some (model.riOf m (W64 1) gri.leaderResponded') } := by
                  unfold prPre; rw [hri]
                  simp only [hU, hgt, Bool.true_and, ↓reduceIte, Bool.false_eq_true]
                  rw [Hrif.2.2.2.2.2.1]; rfl
                rw [hpp]
                iframe
        wp_if_destruct
        · -- the instance's leader replied: return
          have hL : m.acceptorId = m.replica := by rw [hmac, hmq]; exact Hif
          obtain ⟨ri, hri⟩ := prPre_ri LA m
          icases (lbRep_some_open ..).1 $$ Hlb with ⟨%gl, Hgl, Hprops, Hcd, Hri, %Hglf⟩
          rw [hri]
          icases (riRep_some_open ..).1 $$ Hri with ⟨%gri, Hgri, #Hricmds, %Hrif⟩
          wp_auto
          have hpl : prLeader (prPre LA m) = { prPre LA m with recoveryInst := some { ri with leaderResponded := true } } := by
            unfold prLeader; rw [hri]
          ihave Hri : riRep gl.recoveryInst' (some { ri with leaderResponded := true }) $$ [Hgri]
          · iapply (riRep_some_open ..).2; iexists _; iframe Hgri Hricmds; ipureintro
            obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := Hrif
            exact ⟨f1, f2, f3, f4, f5, rfl, f7⟩
          ihave Hlb : lbRep ρ iv.lb' (some { prPre LA m with recoveryInst := some { ri with leaderResponded := true } }) $$ [Hgl Hprops Hcd Hri]
          · iapply (lbRep_some_open ..).2; iexists gl; iframe; ipureintro; exact Hglf
          iexists _
          iframe
          ipureintro
          left
          rw [if_pos hP, if_pos hL, hpl] at hmC
          simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hmC
          exact ⟨rfl, hmC.1.symm, hmC.2.symm⟩
        · iexists prPre LA m
          iframe
          ipureintro
          right
          refine ⟨by first | rfl | trivial, ?_⟩
          have hL : ¬m.acceptorId = m.replica := by rw [hmac, hmq]; exact Hif
          rw [if_pos hP, if_neg hL] at hmC; exact hmC
      · iexists LA
        iframe
        ipureintro
        right
        refine ⟨by first | rfl | trivial, ?_⟩
        rw [if_neg Hif] at hmC; exact hmC
    rcases HLB with ⟨rfl, rfl, rfl⟩ | ⟨rfl, hmQ⟩
    · -- returned (the leader's reply)
      wp_auto
      rw [hmq, hmi]
      h3_pr_keep
    -- the quorum test
    icases (lbRep_some_open ..).1 $$ Hlb with ⟨%gl, Hgl, Hprops, Hcd, Hri, %Hglf⟩
    wp_auto
    have hq : (sint.Z gl.prepareOKs' < sint.Z (BitVec.sdiv (W64 3) (W64 2))) ↔
        model.slt LB.prepareOKs model.NHALF = true := by
      rw [Hglf.2.1, show BitVec.sdiv (W64 3) (W64 2) = model.NHALF by decide]
      simp [model.slt]
    ihave Hlb : lbRep ρ iv.lb' (some LB) $$ [Hgl Hprops Hcd Hri]
    · iapply (lbRep_some_open ..).2; iexists gl; iframe; ipureintro; exact Hglf
    wp_if_destruct
    · -- below a majority: return
      have hlt := hq.1 Hif
      simp only [prQuorum, hlt, ↓reduceIte, Pure.pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at hmQ
      obtain ⟨rfl, rfl⟩ := hmQ
      rw [hmq, hmi]
      h3_pr_keep
    have hge : model.slt LB.prepareOKs model.NHALF = false := by
      cases h : model.slt LB.prepareOKs model.NHALF
      · rfl
      · exact absurd (hq.2 h) Hif
    simp only [prQuorum, hge, Bool.false_eq_true, ↓reduceIte] at hmQ
    -- the choice (`prChoose`)
    ihave #Hfix' := Hfix
    iunfold h2Fixed at Hfix'
    icases Hfix' with ⟨%pS, %alS, %addrs, %st, %cPA, %cA, %cC, %cCS, %cPAR, %cPAO, %cAR, %cEx,
      #HThr, #HExec, #HPO, #HPOS, #HPAL, #HPALS, %HPAl, #HSt, #HStOk, #Hrest⟩
    icases (lbRep_some_open ..).1 $$ Hlb with ⟨%gl, Hgl, Hprops, Hcd, Hri, %Hglf⟩
    wp_auto
    rcases hri : LB.recoveryInst with _ | ir
    · -- no candidate: the no-op
      iunfold riRep at Hri
      icases Hri with %Hnull
      wp_if_destruct
      rotate_left
      · exact absurd Hnull ‹_›
      have hqZ5 : 0 ≤ sint.Z (W64 (sint.Z g.Replica)) ∧ sint.Z (W64 (sint.Z g.Replica)) < 5 := by
        rw [hqZ]; omega
      rw [if_pos hqZ5]
      wp_apply wire.wp_store_arr32 noop_deps_ptr 5 _ _ _ $$ [noop_deps] as noop_deps
      · iframe; ipureintro; exact hqZ5
      wp_apply wp_slice_literal (V := src.state.Command) []
      isplitr
      · ipureintro; rfl
      iintro %slp ⟨Hsl, -⟩
      ihave Hsl := ownSlice_persist _ _ _ $$ Hsl
      imod Hsl
      icases Hsl with #Hsl
      wp_auto
      -- the model's no-op
      have hnoop := hmQ
      simp only [prChoose, hri] at hnoop
      split at hnoop
      rotate_left
      · cases hnoop
      rename_i outsN hbN
      simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hnoop
      obtain ⟨hs'eq, rfl⟩ := hnoop
      rw [hmq, hmi] at hbN hs'eq
      have hcoe : committedOrExecuted s (sint.Z g.Replica, sint.Z g.Instance) = false := by
        rw [coe_slot _ _ _ hbox', hc]; simp [hncs]
      obtain ⟨hnum, hlow, hnin⟩ := Hunc hcoe
      have hqN : (sint.Z g.Replica).toNat = g.Replica.toNat := by
        have := BitVec.toInt_eq_toNat_cond g.Replica
        simp only [sint.Z] at hq0 ⊢; split at this <;> omega
      have hdeps : depsOf (array.mk 5 ((List.replicate 5 (zero_val w32)).set (sint.Z g.Replica).toNat (g.Instance - W32 1))) = model.nildeps.setAt g.Replica.toNat (g.Instance - 1) := by
        rw [hqN]; rfl
      have hvt : vtOf ({ V' := W64 0, T' := { Ts' := W32 0, Cid' := W32 0, Rmwc' := W32 0 } } : src.gryffproto.ValTag) = model.vt0 := rfl
      -- `IS[q][i] = &Instance{...}`
      have hilt := (List.getElem?_eq_some_iff.1 hptr).1
      rw [hqZ, if_pos ⟨hq0, hqlen⟩]
      wp_apply wp_load_slice_index ispS _ isp _ sq hq0 $$ [Hisp] as -
      · iframe Hisp; ipureintro; exact hsq
      rw [hiZ, if_pos ⟨hi0, hilen⟩]
      wp_apply wp_store_slice_index sq _ ptrs «$r0_ptr» $$ [Hsq] as Hsq
      · iframe Hsq; ipureintro; omega
      irename «$r0» => HiI
      generalize «$r0_ptr» = pI
      ihave %HpInn := typedPointsto_not_null _ _ _ $$ HiI
      ihave Hri : riRep gl.recoveryInst' none $$ []
      · iunfold riRep; ipureintro; exact Hnull
      ihave Hlb := lbRep_unprep ρ iv.lb' gl LB none hri Hglf $$ [Hgl Hprops Hcd Hri]
      · iframe
      let c' : Copy := { cmds := [], ballot := c.ballot, status := model.St.ACCEPTED, seq := 0, deps := model.nildeps.setAt g.Replica.toNat (g.Instance - 1), base := model.vt0, lb := some { LB with preparing := false }, slot := g.Instance, leader := g.Replica, vbal := c.ballot }
      ihave Hc : copyRep ρ xs (sint.Z g.Replica, sint.Z g.Instance) pI c' $$ [HiI Hlb]
      · iapply (copyRep_open ..).2
        iexists _
        iframe HiI
        isplitr
        · iunfold cmdsRep; iexists []; iframe Hsl; ipureintro; exact ⟨rfl, rfl⟩
        isplitl [Hlb]
        · iexact Hlb
        ipureintro
        refine ⟨Hivf.1, rfl, rfl, hdeps, hvt, rfl, rfl, Hivf.1, rfl, rfl, ?_, ?_, ?_⟩
        · rw [hnum]; rfl
        · rw [hlow]; rfl
        · constructor
          · intro e; cases e
          · intro e; exact absurd e hnin
      icases Hclose with ⟨-, -, Hcl⟩
      ihave Hep := Hcl $$ %pI %c' [] Hsq Hc
      · ipureintro; exact ⟨rfl, hcoe, HpInn⟩
      imod Hep
      have hb : model.bcastAccept (s.setInst g.Replica g.Instance c') g.Replica g.Instance iv.ballot' (([] : List src.state.Command).map cmdOf) (W32 0) (depsOf (array.mk 5 ((List.replicate 5 (zero_val w32)).set (sint.Z g.Replica).toNat (g.Instance - W32 1)))) (vtOf ({ V' := W64 0, T' := { Ts' := W32 0, Cid' := W32 0, Rmwc' := W32 0 } } : src.gryffproto.ValTag)) = some outsN := by
        rw [hdeps, hvt, Hivf.1]; exact hbN
      ihave #Hnil : slice.nil ↦*□ ([] : List src.state.Command) $$ []
      · iapply ownSlice_nil
      wp_apply h2b.bcastAccept_wp' γ ρ k r gR h xs t (s.setInst g.Replica g.Instance c') g.Replica
        g.Instance iv.ballot' (W32 0) slice.nil [] _ _ outsN [] (by rw [setInst_id]; exact Hid) rfl hb
        $$ [Hep Hpend] as ⟨Hep, Hpend⟩
      · rw [List.append_nil]
        iframe # ∗
        unfold h2b.bcFixed
        iframe #
      have hs'' : s' = s.setInst g.Replica g.Instance c' := by
        rw [← hs'eq]; simp only [c', hri]
      subst hs''
      ihave Hco := coordOwn_congr ρ co _ k s (s.setInst g.Replica g.Instance c') rfl rfl rfl rfl $$ Hco
      iapply HΦ
      iframe Hpend
      iapply handler_close γ ρ k r gR h pa co xs
      iframe Henv
      iunfold parts
      simp only [setInst_tag, setInst_ongoing, setInst_val, setInst_proposeQ, setInst_id]
      iframe
      ipureintro; exact Hid
    · icases (riRep_some_open ..).1 $$ Hri with ⟨%gri, Hgri, #Hricmds, %Hrif⟩
      ihave %Hrinn := typedPointsto_not_null _ _ _ $$ Hgri
      wp_if_destruct
      · exact absurd ‹_› Hrinn
      -- the Accept test's value
      have hCA : (ir.status = model.St.ACCEPTED ∨ ((!ir.leaderResponded) = true ∧
          model.sge ir.preAcceptCount model.NHALF = true ∧ ir.status = model.St.PREACCEPTED_EQ)) ↔
          (gri.status' = W8 3 ∨ (gri.leaderResponded' = false ∧
            sint.Z (W64 1) ≤ sint.Z gri.preAcceptCount' ∧ gri.status' = W8 2)) := by
        obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := Hrif
        rw [f1, f5, f6]
        simp [model.sge, model.sle, model.NHALF, model.St.ACCEPTED, model.St.PREACCEPTED_EQ]
      wp_join (Q := fun v => iprop(⌜v = #(decide (gri.status' = W8 3 ∨ (gri.leaderResponded' = false ∧
            sint.Z (W64 1) ≤ sint.Z gri.preAcceptCount' ∧ gri.status' = W8 2)))⌝ ∗
          gl.recoveryInst' ↦ gri ∗ ir_ptr ↦ gl.recoveryInst' ∗ e_ptr ↦ h))
        at (if: _ then #true else _) with [Hgri ir e] as ⟨%Hv, Hgri, ir, e⟩
      · wp_if_destruct
        · iframe; ipureintro; congr 1; simp [Hif]
        have hn3 := Hif
        cases hlr : gri.leaderResponded'
        · simp only [Bool.not_false]
          wp_auto
          wp_if_destruct
          · have hc1 : sint.Z (W64 1) ≤ sint.Z gri.preAcceptCount' := by
              rw [show BitVec.sdiv (W64 3) (W64 2) = W64 1 by decide] at Hif; exact Hif
            try wp_auto
            iframe; ipureintro; congr 1
            exact decide_eq_decide.mpr ⟨fun h => Or.inr ⟨trivial, hc1, h⟩,
              fun h => h.elim (fun h3 => absurd h3 hn3) (fun h => h.2.2)⟩
          · iframe; ipureintro; congr 1
            rw [eq_comm, decide_eq_false_iff_not]
            rintro (h | ⟨-, h, -⟩)
            · exact hn3 h
            · apply Hif; rw [show BitVec.sdiv (W64 3) (W64 2) = W64 1 by decide]; exact h
        · simp only [Bool.not_true]
          try wp_auto
          iframe; ipureintro; congr 1
          first | (simp [hn3]; done) | (simp [hn3]; exact hn3)
      subst Hv
      have hch := hmQ
      simp only [prChoose, hri] at hch
      wp_if_destruct
      · -- Accept the candidate
        rw [if_pos (hCA.2 Hif)] at hch
        rw [hmq, hmi] at hch
        split at hch
        rotate_left
        · cases hch
        rename_i outsA hbA
        simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hch
        obtain ⟨hs'eq, rfl⟩ := hch
        have hcoe : committedOrExecuted s (sint.Z g.Replica, sint.Z g.Instance) = false := by
          rw [coe_slot _ _ _ hbox', hc]; simp [hncs]
        obtain ⟨hnum, hlow, hnin⟩ := Hunc hcoe
        let c' : Copy := { c with cmds := ir.cmds, seq := ir.seq, deps := ir.deps, base := ir.base, status := model.St.ACCEPTED, vbal := c.ballot, lb := some { LB with preparing := false, recoveryInst := some ir } }
        ihave Hri : riRep gl.recoveryInst' (some ir) $$ [Hgri]
        · iapply (riRep_some_open ..).2; iexists gri; iframe Hgri Hricmds; ipureintro; exact Hrif
        ihave Hlb := lbRep_unprep' ρ iv.lb' gl LB (some ir) Hglf $$ [Hgl Hprops Hcd Hri]
        · iframe
        ihave Hc : copyRep ρ xs (sint.Z g.Replica, sint.Z g.Instance) ptr c' $$ [Hiv Hlb]
        · iapply (copyRep_open ..).2
          iexists _
          iframe Hiv
          isplitr
          · iexact Hricmds
          isplitl [Hlb]
          · iexact Hlb
          ipureintro
          obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13⟩ := Hivf
          obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := Hrif
          refine ⟨b1, rfl, f2, f3, f4, b6, b7, b1, b9, b10, b11, b12, ?_⟩
          constructor
          · intro e; cases e
          · intro e; exact absurd e hnin
        icases Hclose with ⟨Ha, -⟩
        ihave Hep := Ha $$ %c' [] Hsq Hc
        · ipureintro; refine ⟨rfl, fun hh => ?_⟩; rw [hcoe] at hh; cases hh
        imod Hep
        icases (h2b.cmdsRep_open ..).1 $$ Hricmds with ⟨%gs, #Hgs, %Hgsf⟩
        have hb : model.bcastAccept (s.setInst g.Replica g.Instance c') g.Replica g.Instance iv.ballot' (gs.map cmdOf) gri.seq' (depsOf gri.deps') (vtOf gri.base') = some outsA := by
          rw [Hgsf.1, Hrif.2.1, Hrif.2.2.1, Hrif.2.2.2.1, Hivf.1]; exact hbA
        have hok : model.cmdsOk (gs.map cmdOf) = true := by rw [Hgsf.1]; exact Hgsf.2
        wp_apply h2b.bcastAccept_wp' γ ρ k r gR h xs t (s.setInst g.Replica g.Instance c') g.Replica
          g.Instance iv.ballot' gri.seq' gri.cmds' gs _ _ outsA [] (by rw [setInst_id]; exact Hid) hok hb
          $$ [Hep Hpend] as ⟨Hep, Hpend⟩
        · rw [List.append_nil]
          iframe # ∗
          unfold h2b.bcFixed
          iframe #
        have hs'' : s' = s.setInst g.Replica g.Instance c' := hs'eq.symm
        subst hs''
        ihave Hco := coordOwn_congr ρ co _ k s (s.setInst g.Replica g.Instance c') rfl rfl rfl rfl $$ Hco
        iapply HΦ
        iframe Hpend
        iapply handler_close γ ρ k r gR h pa co xs
        iframe Henv
        iunfold parts
        simp only [setInst_tag, setInst_ongoing, setInst_val, setInst_proposeQ, setInst_id]
        iframe
        ipureintro; exact Hid
      · rw [if_neg (fun h => Hif (hCA.1 h))] at hch
        -- the TryPreAccept test's value
        have hCB : ((!ir.leaderResponded) = true ∧ model.sge ir.preAcceptCount ((model.NHALF + 1) / 2) = true) ↔
            (gri.leaderResponded' = false ∧ sint.Z (W64 1) ≤ sint.Z gri.preAcceptCount') := by
          obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := Hrif
          rw [f5, f6]
          simp [model.sge, model.sle, model.NHALF]
        wp_join (Q := fun v => iprop(⌜v = #(decide (gri.leaderResponded' = false ∧
              sint.Z (W64 1) ≤ sint.Z gri.preAcceptCount'))⌝ ∗
            gl.recoveryInst' ↦ gri ∗ ir_ptr ↦ gl.recoveryInst' ∗ e_ptr ↦ h))
          at (if: _ then _ else #false) with [Hgri ir e] as ⟨%Hv, Hgri, ir, e⟩
        · cases hlr : gri.leaderResponded'
          · simp only [Bool.not_false]
            wp_auto
            have e1 : BitVec.sdiv (BitVec.sdiv (W64 3) (W64 2) + W64 1) (W64 2) = W64 1 := by decide
            wp_if_destruct
            · rw [e1] at Hif
              iframe; ipureintro; congr 1; simp only [_root_.true_and]; exact (decide_eq_true Hif).symm
            · rw [e1] at Hif
              iframe; ipureintro; congr 1; simp only [_root_.true_and]; exact (decide_eq_false Hif).symm
          · simp only [Bool.not_true]
            try wp_auto
            iframe; ipureintro; congr 1
        subst Hv
        wp_if_destruct
        · -- TryPreAccept: dead in the model
          exfalso; rw [if_pos (hCB.2 Hif)] at hch; cases hch
        rw [if_neg (fun h => Hif (hCB.1 h))] at hch
        -- restart phase 1 (`startPhase1`), the copy closed first (closing (a))
        rw [hmq, hmi] at hch
        have hcoe : committedOrExecuted s (sint.Z g.Replica, sint.Z g.Instance) = false := by
          rw [coe_slot _ _ _ hbox', hc]; simp [hncs]
        let c1 : Copy := { c with lb := some { LB with preparing := false, recoveryInst := some ir } }
        icases Hprops with #Hprops
        ihave Hri : riRep gl.recoveryInst' (some ir) $$ [Hgri]
        · iapply (riRep_some_open ..).2; iexists gri; iframe Hgri Hricmds; ipureintro; exact Hrif
        ihave Hlb := lbRep_unprep' ρ iv.lb' gl LB (some ir) Hglf $$ [Hgl Hcd Hri]
        · iframe # ∗
        ihave Hc : copyRep ρ xs (sint.Z g.Replica, sint.Z g.Instance) ptr c1 $$ [Hiv Hlb]
        · iapply (copyRep_open ..).2; iexists iv; iframe Hiv Hcmds Hlb; ipureintro; exact Hivf
        icases Hclose with ⟨Ha, -⟩
        ihave Hep := Ha $$ %c1 [] Hsq Hc
        · ipureintro; refine ⟨rfl, fun hh => ?_⟩; rw [hcoe] at hh; cases hh
        imod Hep
        have hslot : committedOrExecuted (s.setInst g.Replica g.Instance c1)
            (sint.Z g.Replica, sint.Z g.Instance) = false := by
          rw [coe_setInst _ _ _ _ hbox']; simpa [c1] using hncs
        icases (h2b.cmdsRep_open ..).1 $$ Hricmds with ⟨%gs, #Hgs, %Hgsf⟩
        ihave #HenvF : Perennial.gryff.replica2.epEnv γ ρ k r gR h pa co $$ []
        · unfold Perennial.gryff.replica2.epEnv; iframe #
        have hst : model.startPhase1 (s.setInst g.Replica g.Instance c1) g.Replica g.Instance iv.ballot'
            LB.clientProposals ir.cmds = .ok (s', outs) := by
          rw [Hivf.1]; exact hch
        wp_apply h2b.startPhase1_wp γ ρ k r gR h pa co xs t (s.setInst g.Replica g.Instance c1) s' outs []
          g.Replica g.Instance iv.ballot' gl.clientProposals' LB.clientProposals gri.cmds' ir.cmds
          gri.cmds'.len hst (by rw [setInst_id]; exact Hid) Hgsf.2 hslot
          $$ [Hep Hpa Hval Hpend] as ⟨Hep, Hpa, Hval, Hpend⟩
        · rw [List.append_nil]
          simp only [setInst_tag, setInst_ongoing, setInst_val]
          iframe # ∗
        obtain ⟨_, _, _, _, _, _, hs', _⟩ := h2b.startPhase1_cases _ _ _ _ _ _ _ _ hch
        have hsh : s'.maxN = s.maxN ∧ s'.rops = s.rops ∧ s'.wops = s.wops ∧
            s'.ongoingReqs = s.ongoingReqs ∧ s'.id = s.id ∧ s'.tag = s.tag ∧ s'.ongoing = s.ongoing ∧
            s'.val = s.val ∧ s'.proposeQ = s.proposeQ := by
          rw [hs']
          simp only [uc_maxN, uc_rops, uc_wops, uc_ongoingReqs, uc_id, uc_tag, uc_ongoing, uc_val,
            uc_proposeQ, setInst_maxN, setInst_rops, setInst_wops, setInst_ongoingReqs, setInst_id,
            setInst_tag, setInst_ongoing, setInst_val, setInst_proposeQ, _root_.and_self]
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hsh
        ihave Hco := coordOwn_congr ρ co _ k s s' h1 h2 h3 h4 $$ Hco
        iapply HΦ
        iframe Hpend
        iapply handler_close γ ρ k r gR h pa co xs s'
        iframe Henv
        iunfold parts
        rw [h6, h7, h8, h9]
        try simp only [setInst_tag, setInst_ongoing, setInst_val]
        iframe
        ipureintro; rw [h5]; exact Hid

variable [pD : GryffPartiDeps (GF := GF)] in
/-- The frozen `handlePrepareReply.wp`'s statement (`Replica2/Specs.lean`), from the primed one. -/
theorem handlePrepareReply_wp_frozen (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc)
    (m : model.PrepareReplyM) :
    epHandlerSpec γ ρ k r h go!"handlePrepareReply" (.prepareReply m) :=
  fun p t s s' outs hstep => handlePrepareReply_wp' γ ρ k r h p m t s s' outs hstep

end

end Perennial.gryff.replica2.h3
