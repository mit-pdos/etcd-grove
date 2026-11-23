/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2b/Phase1.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2b: `startPhase1`

`startPhase1(replica, instance, ballot, proposals, cmds, batchSize)` (a new proposal's batch from
`handlePropose`, or recovery's restart of phase 1 for an instance of any row: G9, G32): the
initial dependencies, `updateAttributes`, the base (the store's value and tag), the new instance
(with its leader's bookkeeping) written into the slot, `updateConflicts`, `maxSeq`,
`bcastPreAccept`, `cpcounter`; the checkpoint branch is dead (`DO_CHECKPOINTING` false).
-/
module

public import Dsverify.Proof.gryff.H2b.Bcast
public import Dsverify.Proof.gryff.H2b.Phase1Model
public import Dsverify.Proof.gryff.H2.InstOpen
public import Dsverify.Proof.gryff.H2.Attr
public import Dsverify.Proof.gryff.H2.Base
public import Dsverify.Proof.gryff.Wire.Proof.Lemmas
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2.h2b

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.replica2
open Perennial.gryff.model (RState Copy LB Proposal Msg Ev Out Cmd Deps)
open Perennial.gryff.replica (XS rowOwn nSlots)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF] -- H1-R6 / N-1
variable [sortA : Perennial.gryff.replica2.SortSliceHyp GF]
variable [strconvA : strconv.Assumptions] -- N-5


set_option goose.wp.extras true

/-- `epaxosOwn`'s `epaxosRest`, taken out (the other parts do not depend on it). -/
theorem epaxosOwn_rest (ρ : Repl2Names) (h r : Loc) (xs : XS) (s : RState) :
    epaxosOwn (GF := GF) ρ h r xs s ⊢ epaxosRest h ∗ (epaxosRest h -∗ epaxosOwn ρ h r xs s) := by
  iintro H
  icases (epaxosOwn_open ..).1 $$ H with ⟨%ispS, %crtS, %c1S, %isp, %msR, %pvtR, %cfs, %M, %cu,
    %pm, #HR, #HnoC, #HispS, #Hisp, #HcrtS, #Hc1S, #Hcfs, #HmsR, #HpvtR, Hcu, Hcrt, HM, HMe,
    Hrows, Hinsts, Hmono, Hconfs, Hms, Hpm, Hrest, %Hf⟩
  iframe Hrest
  iintro Hrest
  iapply (epaxosOwn_open ..).2
  iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm
  iframe # ∗
  ipureintro; exact Hf

/-- `epaxosRest`'s global `cpcounter`, taken out. -/
theorem epaxosRest_cpcounter (h : Loc) :
    epaxosRest (GF := GF) h ⊢ ∃ v : w64, globalAddr src.gryff.cpcounter ↦ v ∗
      (∀ v' : w64, globalAddr src.gryff.cpcounter ↦ v' -∗ epaxosRest h) := by
  unfold epaxosRest
  iintro ⟨%ms, %lcp, %lci, %cS, %cs, %mskR, %msk, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11,
    H12, H13, H14, H15, H16, ⟨%v, Hc⟩, Hr⟩
  iexists v
  iframe Hc
  iintro %v' Hc
  iexists ms, lcp, lci, cS, cs, mskR, msk
  iframe

/-- `deps` after `j` iterations of `for q := 0; q < N; q++ { deps[q] = -1 }`. -/
def depsInit (j : Nat) : List w32 := List.replicate j (W32 (-1)) ++ List.replicate (5 - j) (W32 0)

theorem depsInit_succ (j : Nat) (hj : j < 3) :
    (depsInit j).set j (W32 (-1)) = depsInit (j + 1) := by
  obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  all_goals rfl

/-- `startPhase1(replica, instance, ballot, proposals, cmds, batchSize)`: the step `model.startPhase1`
(the slot is free or holds an uncommitted copy, replaced; the commands are CAS on key 0). -/
theorem startPhase1_wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h pa co : Loc)
    (xs : XS) (t : List Ev) (s s' : RState) (outs rest : List Out) (replica islot ballot : w32)
    (psl : GoSlice) (prs : List Proposal) (csl : GoSlice) (cmds : List Cmd) (bs : w64)
    (hstep : model.startPhase1 s replica islot ballot prs cmds = .ok (s', outs))
    (hid : s.id = rid32 k) (hok : model.cmdsOk cmds = true)
    (hslot : committedOrExecuted s (sint.Z replica, sint.Z islot) = false) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ epEnv γ ρ k r gR h pa co ∗
        epaxosOwn ρ h r xs s ∗ partiOwn pa (replicaIface r) k s.tag s.ongoing ∗
        valOwn gR s.val ∗ proposalsRep ρ psl prs ∗ cmdsRep csl cmds ∗
        pendingOuts γ ρ k r t (outs ++ rest) }}
      (App (App (App (App (App (App (Val (h @!! go.GoType.PointerType
        src.gryff.EPaxosRMWHandler.ty @!! go!"startPhase1")) (Val #replica)) (Val #islot))
        (Val #ballot)) (Val #psl)) (Val #csl)) (Val #bs))
    {{ RET #(); epaxosOwn ρ h r xs s' ∗ partiOwn pa (replicaIface r) k s.tag s.ongoing ∗
        valOwn gR s.val ∗ pendingOuts γ ρ k r t rest }} := by
  obtain ⟨seq, deps, ch, hupd, hne, hbox, rfl, hbc⟩ :=
    startPhase1_cases s s' replica islot ballot prs cmds outs hstep
  clear hstep
  wp_start as ⟨#Henv, Hep, Hparti, Hval, Hprs, #Hcmds, Hpend⟩
  unfold epEnv
  icases Henv with ⟨#HgR, #Hpa, #Hco, #Hh, #HR, #HId, #HN, #HDur, #Hgen, #Hfix⟩
  wp_auto
  -- `deps[q] = -1` for each replica
  ihave HI : (∃ j : Nat, "%Hj" ∷ ⌜j ≤ 3⌝ ∗ "q" ∷ q_ptr ↦ W64 (j : Int) ∗
      "deps" ∷ deps_ptr ↦ (array.mk 5 (depsInit j) : GoArray w32 5) : IProp GF) $$ [q deps]
  · iexists 0
    iframe
    ipureintro; omega
  irename «instance» => Hinst
  wp_for HI
  wp_if_destruct
  · have hj3 : j < 3 := by word
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 (j : Int)) ∧ sint.Z (W64 (j : Int)) < 5 by word)]
    wp_apply wire.wp_store_arr32 $$ [deps] as deps
    · iframe deps; ipureintro; word
    wp_for_post
    iframe
    iexists (j + 1)
    rw [show (sint.Z (W64 (j : Int))).toNat = j by word, depsInit_succ j hj3]
    iframe deps
    isplitr
    · ipureintro; omega
    rw [show W64 ((j + 1 : Nat) : Int) = W64 (j : Int) + W64 1 by word]; iexact q
  obtain rfl : j = 3 := by word
  have hb' := of_decide_eq_true hbox
  obtain ⟨hq0, hq3, hi0, hiS⟩ := hb'
  have hqn : (sint.Z (W64 (sint.Z replica))).toNat = replica.toNat := by
    have h1 : uint.Z replica = sint.Z replica := by word
    have h2 : uint.Z replica = (replica.toNat : Int) := rfl
    have : sint.Z (W64 (sint.Z replica)) = sint.Z replica := by word
    omega
  wp_join iprop(deps_ptr ↦ (array.mk 5 (sp1Deps0 s replica islot) : GoArray w32 5) ∗
      instance_ptr ↦ islot ∗ replica_ptr ↦ replica ∗ e_ptr ↦ h)
    with [deps Hinst replica e] as ⟨deps, Hinst, replica, e⟩
  · have : sp1Deps0 s (rid32 k) islot = [-1, -1, -1, 0, 0] := by
      simp only [sp1Deps0, hid]; rw [if_neg (by simp)]
    rw [this]
    iframe
  · rw [ite_eq_left (show 0 ≤ sint.Z (W64 (sint.Z replica)) ∧ sint.Z (W64 (sint.Z replica)) < 5 by
      word)]
    wp_apply wire.wp_store_arr32 $$ [deps] as deps
    · iframe deps; ipureintro; word
    wp_join_done
    rw [hqn]
    have : sp1Deps0 s replica islot = model.Deps.setAt [-1, -1, -1, 0, 0] replica.toNat (islot - 1) := by
      simp only [sp1Deps0, hid]; rw [if_pos (by simpa using Hif)]
    rw [this]
    iframe
  -- `updateAttributes`
  icases (cmdsRep_open ..).1 $$ Hcmds with ⟨%gs, #Hgs, %Hgsc⟩
  obtain ⟨Hgsc, HgsOk⟩ := Hgsc
  subst Hgsc
  ihave #Hae : attrEnv k r gR h $$ []
  · unfold attrEnv; iframe #
  wp_apply (wp_updateAttributes ρ k r gR h xs s csl gs (W32 0)
    (array.mk 5 (sp1Deps0 s replica islot)) replica islot (seq, deps, ch) hok ⟨hq0, hq3⟩ hid hupd)
    $$ [$Hae $Hep $Hgs] as %seq' %deps' %ch' ⟨Hep, %Hres⟩
  simp only [Prod.mk.injEq] at Hres
  obtain ⟨rfl, hdeps, rfl⟩ := Hres
  -- the base: `{GetCurrentValue(cmds[0].K), *GetStoreMetadata(cmds[0].K).Tag}`
  obtain ⟨c0, hc0⟩ : ∃ c0, gs[0]? = some c0 := by
    cases hg : gs with
    | nil => exact absurd (by simp [hg]) hne
    | cons a _ => exact ⟨a, rfl⟩
  have hc0K : c0.K' = W64 0 := by
    have := hok
    simp only [model.cmdsOk, List.all_eq_true, List.mem_map] at this
    have h1 := this (cmdOf c0) ⟨c0, List.mem_of_getElem? hc0, rfl⟩
    simp [model.Cmd.ok, cmdOf] at h1
    exact h1.2
  ihave %Hsllen := ownSlice_len _ _ _ $$ Hgs
  have hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z csl.len := by
    have := Hsllen.1
    have : 0 < gs.length := by
      cases hg : gs with
      | nil => simp [hg] at hc0
      | cons _ _ => simp
    word
  rw [ite_eq_left hb0]
  icases ownSlice_elem_acc (sint.Z (W64 0)) c0 csl DFrac.discard gs (by decide) hc0 $$ Hgs
    with ⟨#Hc0, -⟩
  iStructNamed Hc0
  wp_apply (IntoValTyped.wp_load (t := src.state.Key.ty) _ _ _) $$ [$K] as -
  rw [hc0K]
  wp_apply (wp_Replica_GetCurrentValue r gR s.val) $$ [$HgR $Hval] as Hval
  rw [ite_eq_left hb0]
  wp_apply (IntoValTyped.wp_load (t := src.state.Key.ty) _ _ _) $$ [$K] as -
  try rw [hc0K]
  wp_apply (wp_Replica_GetStoreMetadata r pa k s.tag s.ongoing)
    $$ [$Hpa Hparti] as %md ⟨%tp, %gt, %Hgt, #Htp, Hmd, Hpclose⟩
  · iframe
  ihave Hparti := Hpclose $$ Hmd
  -- the new instance and its bookkeeping
  wp_apply wp_slice_literal (V := w32) [W32 (-1), W32 (-1), W32 (-1), W32 (-1), W32 (-1)]
  isplitr
  · ipureintro; rfl
  iintro %cdS ⟨HcdS, -⟩
  ihave #Hfix' := Hfix
  iunfold h2Fixed at Hfix'
  icases Hfix' with ⟨%pS, %alS, %addrs, %st, %cPA, %cA, %cC, %cCS, %cPAR, %cPAO, %cAR, %cEx,
    -, -, -, -, #HPAL, #HPALS, %HPAl, -⟩
  wp_auto
  ihave %HPALl := ownSlice_len _ _ _ $$ HPALS
  wp_apply (wp_slice_make2 (V := time.Time) alS.len) as %tS ⟨HtS, -⟩
  · ipureintro; exact HPALl.2
  -- `e.InstanceSpace[replica][instance] = &Instance{...}`
  icases epaxosOwn_inst_open' ρ h r xs s replica islot hbox $$ Hep with
    ⟨%ispS, %sq, %isp, %ptrs, %ptr, #HIS, #Hisp, %Hsl, Hsq, Hcase, %Hunc, Hclose⟩
  obtain ⟨hsq, hptr⟩ := Hsl
  ihave %HispL := ownSlice_len _ _ _ $$ Hisp
  ihave %HsqL := ownSlice_len _ _ _ $$ Hsq
  have hiZ : sint.Z (W64 (sint.Z islot)) = sint.Z islot := by unfold model.SLOTS at hiS; word
  have hqZ : sint.Z (W64 (sint.Z replica)) = sint.Z replica := by word
  have hqlen : sint.Z replica < sint.Z ispS.len := by
    have h0 := (List.getElem?_eq_some_iff.1 hsq).1
    have h1 := HispL.1; have h2 := HispL.2
    simp only [sint.nat, sint.Z] at h1 h2 hq0 h0 ⊢; omega
  have hilen : sint.Z islot < sint.Z sq.len := by
    have h0 := (List.getElem?_eq_some_iff.1 hptr).1
    have h1 := HsqL.1; have h2 := HsqL.2
    simp only [sint.nat, sint.Z] at h1 h2 hi0 h0 ⊢; omega
  wp_auto
  rw [hqZ, if_pos ⟨hq0, hqlen⟩]
  wp_apply wp_load_slice_index ispS _ isp _ sq hq0 $$ [Hisp] as -
  · iframe Hisp; ipureintro; exact hsq
  rw [hiZ, if_pos ⟨hi0, hilen⟩]
  have hilt := (List.getElem?_eq_some_iff.1 hptr).1
  wp_apply wp_store_slice_index sq _ ptrs «$r0_ptr» $$ [Hsq] as Hsq
  · iframe Hsq; ipureintro; omega
  irename «$r0» => HiI
  irename «$v6» => HlbI
  generalize «$r0_ptr» = pI
  generalize «$v6_ptr» = pL
  ihave %HpInn := typedPointsto_not_null _ _ _ $$ HiI
  -- the new copy's representation
  let n : Perennial.gryff.replica.Node := (sint.Z replica, sint.Z islot)
  obtain ⟨hnum, hlow, hnin⟩ := Hunc hslot
  let c' := sp1Copy replica islot ballot prs (gs.map cmdOf) seq deps s.storeVT
  ihave Hc : copyRep ρ xs n pI c' $$ [HiI HlbI HcdS Hprs]
  · iapply (copyRep_open ..).2
    iexists _
    iframe HiI
    isplitr
    · iapply (cmdsRep_open ..).2; iexists gs; iframe Hgs; ipureintro; exact ⟨rfl, HgsOk⟩
    isplitl [HlbI HcdS Hprs]
    · iunfold lbRep
      simp only [c', sp1Copy, sp1LB]
      iexists _
      isplitl [HlbI]
      · iexact HlbI
      dsimp only
      iframe Hprs
      isplitl [HcdS]
      · rw [show ([-1, -1, -1, -1, -1] : List w32) = [W32 (-1), W32 (-1), W32 (-1), W32 (-1), W32 (-1)]
          by decide]
        iexact HcdS
      isplitr
      · iunfold riRep; ipureintro; rfl
      ipureintro
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, hdeps.symm, rfl, rfl, rfl⟩
    ipureintro
    simp only [c', sp1Copy]
    refine ⟨trivial, rfl, trivial, hdeps.symm, ?_, trivial, trivial, trivial, rfl, rfl, ?_, ?_, ?_⟩
    · simp only [vtOf, Hgt, model.RState.storeVT]
    · rw [hnum]; rfl
    · rw [hlow]; rfl
    · constructor
      · intro e; cases e
      · intro e; exact absurd e hnin
  -- close the slot: (b) a nil slot, (c) an uncommitted copy's
  ihave Hep : |==> epaxosOwn ρ h r xs (s.setInst replica islot c') $$ [Hcase Hclose Hsq Hc]
  · rcases hc : s.inst replica islot with _ | c0'
    · icases Hclose with ⟨-, Hclose⟩
      icases Hclose with ⟨Hb, -⟩
      iapply Hb $$ %pI %c' [] Hsq Hc
      ipureintro; exact ⟨rfl, HpInn⟩
    · icases Hclose with ⟨-, Hclose⟩
      icases Hclose with ⟨-, Hcc⟩
      iapply Hcc $$ %pI %c' [] Hsq Hc
      ipureintro; exact ⟨rfl, hslot, HpInn⟩
  imod Hep
  -- `updateConflicts`
  wp_apply (wp_updateConflicts ρ k r gR h xs (s.setInst replica islot c') csl gs replica islot seq
    hok ⟨hq0, hq3⟩) $$ [$Hae $Hep $Hgs] as Hep
  -- `if seq >= e.maxSeq { e.maxSeq = seq + 1 }`
  icases epaxosOwn_rest ρ h r xs _ $$ Hep with ⟨Hrest, Hepc⟩
  icases epaxosRest_maxSeq h $$ Hrest with ⟨%ms, HmaxSeq, Hrestc⟩
  wp_auto
  wp_join iprop((∃ ms' : w32, h.[src.gryff.EPaxosRMWHandler, go!"maxSeq"] ↦ ms') ∗
      seq_ptr ↦ seq ∗ e_ptr ↦ h) with [HmaxSeq seq e] as ⟨⟨%ms', HmaxSeq⟩, seq, e⟩
  ihave Hrest := Hrestc $$ %ms' HmaxSeq
  ihave Hep := Hepc $$ Hrest
  -- `recordInstanceMetadata(e.InstanceSpace[replica][instance])`: the slot read again
  have hs'i : (model.updateConflicts (s.setInst replica islot c') (gs.map cmdOf) replica islot seq).inst
      replica islot = some c' := by
    rw [updateConflicts_inst, setInst_inst_self]
  icases epaxosOwn_inst_open' ρ h r xs _ replica islot hbox $$ Hep with
    ⟨%ispS2, %sq2, %isp2, %ptrs2, %ptr2, #HIS2, #Hisp2, %Hsl2, Hsq2, Hcase2, -, Hclose2⟩
  icombine HIS HIS2 gives %HispEq
  subst HispEq
  obtain ⟨hsq2, hptr2⟩ := Hsl2
  rw [hs'i]
  icases Hcase2 with ⟨%Hnn2, Hc2⟩
  ihave %HispL2 := ownSlice_len _ _ _ $$ Hisp2
  ihave %HsqL2 := ownSlice_len _ _ _ $$ Hsq2
  have hqlen2 : sint.Z replica < sint.Z ispS.len := by
    have h0 := (List.getElem?_eq_some_iff.1 hsq2).1
    have h1 := HispL2.1; have h2 := HispL2.2
    simp only [sint.nat, sint.Z] at h1 h2 hq0 h0 ⊢; omega
  have hilen2 : sint.Z islot < sint.Z sq2.len := by
    have h0 := (List.getElem?_eq_some_iff.1 hptr2).1
    have h1 := HsqL2.1; have h2 := HsqL2.2
    simp only [sint.nat, sint.Z] at h1 h2 hi0 h0 ⊢; omega
  rw [hqZ, if_pos ⟨hq0, hqlen2⟩]
  wp_apply wp_load_slice_index ispS _ isp2 _ sq2 hq0 $$ [Hisp2] as -
  · iframe Hisp2; ipureintro; exact hsq2
  rw [hiZ, if_pos ⟨hi0, hilen2⟩]
  wp_apply wp_load_slice_index sq2 _ ptrs2 _ ptr2 hi0 $$ [Hsq2] as Hsq2
  · iframe Hsq2; ipureintro; exact hptr2
  icases Hclose2 with ⟨Ha, -⟩
  ihave Hep := Ha $$ %c' [] Hsq2 Hc2
  · ipureintro
    refine ⟨by simp [hs'i], fun h => ?_⟩
    rwa [setInst_self _ _ _ _ hs'i]
  imod Hep
  rw [setInst_self _ _ _ _ hs'i]
  wp_apply (wp_recordInstanceMetadata h r gR ptr2) $$ [$HR $HgR $HDur]
  wp_apply (wp_recordCommands h r gR csl) $$ [$HR $HgR $HDur]
  wp_apply (wp_sync h r gR) $$ [$HR $HgR $HDur]
  -- `bcastPreAccept`
  have hid' : (model.updateConflicts (s.setInst replica islot c') (gs.map cmdOf) replica islot seq).id =
      rid32 k := by rw [updateConflicts_id, setInst_id, hid]
  have hbase : vtOf { V' := s.val, T' := gt } = s.storeVT := by
    simp only [vtOf, Hgt, model.RState.storeVT]
  have hb' : model.bcastPreAccept (model.updateConflicts (s.setInst replica islot c') (gs.map cmdOf)
      replica islot seq) replica islot ballot (gs.map cmdOf) seq (depsOf deps')
      (vtOf { V' := s.val, T' := gt }) = some outs := by
    rw [← hdeps, hbase]; exact hbc
  ihave #Hbc : bcFixed γ ρ k r gR h $$ []
  · unfold bcFixed
    iframe HR HgR HId HN
    isplitr
    · imodintro; iexact Hfix
    · imodintro; iexact Hgen
  icases epaxosOwn_rest ρ h r xs _ $$ Hep with ⟨Hrest, Hepc⟩
  ihave #Hcm : cmdsRep csl (gs.map cmdOf) $$ []
  · iapply (cmdsRep_open ..).2; iexists gs; iframe Hgs; ipureintro; exact ⟨rfl, HgsOk⟩
  wp_apply (bcastPreAccept_wp γ ρ k r gR h t _ replica islot ballot seq csl (gs.map cmdOf) deps'
    { V' := s.val, T' := gt } outs rest hid' hb') $$ [$Hbc $Hrest $Hcm $Hpend] as ⟨Hrest, Hpend⟩
  -- `cpcounter += batchSize`
  icases epaxosRest_cpcounter h $$ Hrest with ⟨%cpc, Hcpc, Hrestc⟩
  wp_auto
  ihave Hrest := Hrestc $$ %_ Hcpc
  ihave Hep := Hepc $$ Hrest
  -- the checkpoint branch: `DO_CHECKPOINTING` is false
  simp only [src.gryff.DO_CHECKPOINTING]
  wp_if_destruct <;> (try wp_auto) <;>
  · iapply HΦ
    iframe

/-- `bcastAccept` with `epaxosOwn` (H3's form: the global `ea` is in `epaxosRest`). -/
theorem bcastAccept_wp' (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc)
    (xs : XS) (t : List Ev) (s : RState) (q i b seq : w32) (sl : GoSlice)
    (gs : List src.state.Command) (deps : GoArray w32 5) (base : src.gryffproto.ValTag)
    (outs rest : List Out) (hid : s.id = rid32 k)
    (hok : model.cmdsOk (gs.map cmdOf) = true) -- H2c-R1
    (hb : model.bcastAccept s q i b (gs.map cmdOf) seq (depsOf deps) (vtOf base) = some outs) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ bcFixed γ ρ k r gR h ∗
        epaxosOwn ρ h r xs s ∗ sl ↦*□ gs ∗ pendingOuts γ ρ k r t (outs ++ rest) }}
      (App (App (App (App (App (App (App (Val (h @!! go.GoType.PointerType
        src.gryff.EPaxosRMWHandler.ty @!! go!"bcastAccept")) (Val #q)) (Val #i)) (Val #b))
        (Val #sl)) (Val #seq)) (Val #deps)) (Val #base))
    {{ RET #(); epaxosOwn ρ h r xs s ∗ pendingOuts γ ρ k r t rest }} := by
  iintro %Φ ⟨#Hpkg, #Hfix, Hep, #Hsl, Hpend⟩ HΦ
  icases epaxosOwn_rest ρ h r xs s $$ Hep with ⟨Hrest, Hepc⟩
  ihave #Hc : cmdsRep sl (gs.map cmdOf) $$ []
  · iapply (cmdsRep_open ..).2; iexists gs; iframe Hsl; ipureintro; exact ⟨rfl, hok⟩
  wp_apply bcastAccept_wp γ ρ k r gR h t s q i b seq sl (gs.map cmdOf) deps base outs rest hid hb
    $$ [$Hfix $Hrest $Hc $Hpend] as ⟨Hrest, Hpend⟩
  iapply HΦ; iframe Hpend; iapply Hepc $$ Hrest

/-- `bcastCommit` with `epaxosOwn` (H3's form: the globals `ec`, `ecs` are in `epaxosRest`). -/
theorem bcastCommit_wp' (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc)
    (xs : XS) (t : List Ev) (s : RState) (q i seq : w32) (sl : GoSlice)
    (gs : List src.state.Command) (deps : GoArray w32 5) (base : src.gryffproto.ValTag)
    (outs rest : List Out) (hid : s.id = rid32 k)
    (hok : model.cmdsOk (gs.map cmdOf) = true) -- H2c-R1
    (hb : model.bcastCommit s q i (gs.map cmdOf) seq (depsOf deps) (vtOf base) = some outs) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ bcFixed γ ρ k r gR h ∗
        epaxosOwn ρ h r xs s ∗ sl ↦*□ gs ∗ pendingOuts γ ρ k r t (outs ++ rest) }}
      (App (App (App (App (App (App (Val (h @!! go.GoType.PointerType
        src.gryff.EPaxosRMWHandler.ty @!! go!"bcastCommit")) (Val #q)) (Val #i))
        (Val #sl)) (Val #seq)) (Val #deps)) (Val #base))
    {{ RET #(); epaxosOwn ρ h r xs s ∗ pendingOuts γ ρ k r t rest }} := by
  iintro %Φ ⟨#Hpkg, #Hfix, Hep, #Hsl, Hpend⟩ HΦ
  icases epaxosOwn_rest ρ h r xs s $$ Hep with ⟨Hrest, Hepc⟩
  ihave #Hc : cmdsRep sl (gs.map cmdOf) $$ []
  · iapply (cmdsRep_open ..).2; iexists gs; iframe Hsl; ipureintro; exact ⟨rfl, hok⟩
  wp_apply bcastCommit_wp γ ρ k r gR h t s q i seq sl (gs.map cmdOf) deps base outs rest hid hb
    $$ [$Hfix $Hrest $Hc $Hpend] as ⟨Hrest, Hpend⟩
  iapply HΦ; iframe Hpend; iapply Hepc $$ Hrest

end

end Perennial.gryff.replica2.h2b
