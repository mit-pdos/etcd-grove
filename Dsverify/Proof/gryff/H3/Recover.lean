/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H3/Recover.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H3: `startRecoveryForInstance` (the recovery trigger).

In a section with one `HeapGS`; `startRecoveryForInstance_wp_frozen` is the frozen
`startRecoveryForInstance.wp`'s statement.
-/
module

public import Dsverify.Proof.gryff.H3.Env
public import Dsverify.Proof.gryff.H2.InstOpen -- C: `epaxosOwn_inst_open` moved to Replica2/Results.lean
public import Dsverify.Proof.gryff.H3.Bcast
public import Dsverify.Proof.gryff.H3.Ballot
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


/-- Setting an instance to its own copy changes nothing. -/
theorem setInst_self (s : RState) (q i : w32) (c : Copy) (h : s.inst q i = some c) :
    s.setInst q i c = s := by
  cases s
  simp only [RState.setInst, RState.mk.injEq, true_and, and_true]
  funext q' i'
  by_cases e : q' = q ∧ i' = i
  · obtain ⟨rfl, rfl⟩ := e; rw [if_pos ⟨rfl, rfl⟩]; exact h.symm
  · rw [if_neg e]

/-- The fresh copy of a nil slot. -/
theorem recBase_none (s : RState) (q i : w32) (h : s.inst q i = none) :
    recBase s q i =
      { cmds := [], ballot := 0, status := model.St.NONE, seq := 0, deps := model.nildeps,
        base := model.vt0, lb := none, slot := i, leader := q, vbal := -1 } := by
  simp [recBase, h]

set_option goose.wp.extras true

set_option hygiene false in
/-- The recovery stops at copy `c` (unchanged): put it back, close the replica. -/
local macro "h3_stop_close" : tactic => `(tactic| (
  ihave Hc : copyRep ρ xs (sint.Z q, sint.Z i) ptr c $$ [Hiv Hlb]
  · iapply (copyRep_open ..).2; iexists iv; iframe Hiv Hlb Hcmds; ipureintro; exact Hivf
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

theorem startRecoveryForInstance_wp' (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc)
    (q i : w32) (t : List Ev) (s s' : RState) (outs : List Out)
    (hstep : model.stepR k s (.recover q i) = .ok (s', outs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r ∗
        replicaOwn ρ k r s ∗ pendingOuts γ ρ k r t outs ∗ handlerOf r h }}
      (App (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!!
        go!"startRecoveryForInstance")) (Val #q)) (Val #i))
    {{ RET #(); replicaOwn ρ k r s' ∗ pendingOuts γ ρ k r t [] }} := by
  wp_start as ⟨#Hrep, Hown, Hpend, Hh⟩
  have hrec : model.stepRecover s q i = .ok (s', outs) := by
    simpa [model.stepR] using hstep
  obtain ⟨hbox, hres⟩ := stepRecover_ok s s' q i outs hrec
  ihave ⟨%gR, %pa, %co, %xs, #Henv, Hparts⟩ := handler_open γ ρ k r h s $$ [Hrep Hh Hown]
  · iframe # ∗
  iunfold parts at Hparts
  ihave #Henv' := Henv
  iunfold epEnv at Henv'
  icases Henv' with ⟨#HgR, #Hpa', #Hco', #Hh', #HR', #HId, #HN, #HDur, #Hok, #Hfix⟩
  icases Hparts with ⟨Hpa, Hval, Hco, Hep, Hxs, Hprop, Hscr, %Hid⟩
  have hbox' := hbox
  icases epaxosOwn_inst_open' ρ h r xs s q i hbox $$ Hep with
    ⟨%ispS, %sq, %isp, %ptrs, %ptr, #HIS, #Hisp, %Hsl, Hsq, Hcase, %Hunc, Hclose⟩
  simp only [model.inBox, decide_eq_true_eq] at hbox
  obtain ⟨hq0, hq3, hi0, hiS⟩ := hbox
  obtain ⟨hsq, hptr⟩ := Hsl
  ihave %HispL := ownSlice_len _ _ _ $$ Hisp
  ihave %HsqL := ownSlice_len _ _ _ $$ Hsq
  have hqZ : sint.Z (W64 (sint.Z q)) = sint.Z q := by word
  have hiZ : sint.Z (W64 (sint.Z i)) = sint.Z i := by word
  have hqlen : sint.Z q < sint.Z ispS.len := by
    have h0 := (List.getElem?_eq_some_iff.1 hsq).1
    have h1 := HispL.1; have h2 := HispL.2
    simp only [sint.nat, sint.Z] at h1 h2 hq0 h0 ⊢; omega
  have hilen : sint.Z i < sint.Z sq.len := by
    have h0 := (List.getElem?_eq_some_iff.1 hptr).1
    have h1 := HsqL.1; have h2 := HsqL.2
    simp only [sint.nat, sint.Z] at h1 h2 hi0 h0 ⊢; omega
  have hilt := (List.getElem?_eq_some_iff.1 hptr).1
  wp_auto
  rw [hqZ, if_pos ⟨hq0, hqlen⟩]
  wp_apply wp_load_slice_index ispS _ isp _ sq hq0 $$ [Hisp] as -
  · iframe Hisp; ipureintro; exact hsq
  rw [hiZ, if_pos ⟨hi0, hilen⟩]
  wp_apply wp_load_slice_index sq _ ptrs _ ptr hi0 $$ [Hsq] as Hsq
  · iframe Hsq; ipureintro; exact hptr
  rcases hres with ⟨⟨c, hc, hstop⟩, rfl, rfl⟩ | ⟨hns, rfl, hb⟩
  · -- the recovery stops: committed here, or no larger ballot
    rw [hc]
    icases Hcase with ⟨%Hnn, Hc⟩
    icases (copyRep_open ..).1 $$ Hc with ⟨%iv, Hiv, #Hcmds, Hlb, %Hivf⟩
    iapply wp_fupd
    wp_if_destruct
    · exact absurd rfl Hnn
    wp_if_destruct
    · h3_stop_close
    wp_if_destruct
    · h3_stop_close
    rw [hqZ, if_pos ⟨hq0, hqlen⟩]
    wp_apply wp_load_slice_index ispS _ isp _ sq hq0 $$ [Hisp] as -
    · iframe Hisp; ipureintro; exact hsq
    rw [hiZ, if_pos ⟨hi0, hilen⟩]
    wp_apply wp_load_slice_index sq _ ptrs _ ptr hi0 $$ [Hsq] as Hsq
    · iframe Hsq; ipureintro; exact hptr
    wp_if_destruct
    · exact absurd rfl Hnn
    wp_if_destruct
    · h3_stop_close
    · exfalso
      obtain ⟨hb, hs, -⟩ := Hivf
      rcases hstop with (h | h) | h
      · rw [← hs] at h; exact ‹¬iv.Status' = W8 4› h
      · rw [← hs] at h; exact ‹¬iv.Status' = W8 5› h
      · apply Hif
        have e1 : BitVec.sshiftRight' iv.ballot' (W64 4) = c.ballot.sshiftRight 4 := by
          rw [hb]; rfl
        have e2 : W32 134217727 = model.maxBallotHi := by decide
        rw [e1, e2]
        simpa [model.sge, model.sle] using h
  · -- the recovery starts: the slot's copy (a fresh one in a nil slot), then the common tail
    have hcoe : committedOrExecuted s (sint.Z q, sint.Z i) = false := by
      rw [coe_slot s q i hbox']
      rcases hc : s.inst q i with _ | c
      · rfl
      · have := hns c hc
        simp only [recStops, not_or] at this
        simp [this.1.1, this.1.2]
    obtain ⟨hnum, hlow, hnin⟩ := Hunc hcoe
    -- `if c := IS[q][i]; c != nil && committed { return }`: falls through
    wp_join at next with [Hcase c]
    · rcases hc : s.inst q i with _ | c
      · icases Hcase with %Hnull
        subst Hnull
        wp_auto
        wp_join_done
        iframe
        ipureintro; rfl
      · icases Hcase with ⟨%Hnn, Hc⟩
        icases (copyRep_open ..).1 $$ Hc with ⟨%iv, Hiv, #Hcmds, Hlb, %Hivf⟩
        have := hns c hc
        simp only [recStops, not_or] at this
        obtain ⟨⟨hn4, hn5⟩, hnb⟩ := this
        have hs := Hivf.2.1
        wp_if_destruct
        · exact absurd rfl Hnn
        wp_if_destruct
        · exact absurd (hs ▸ Hif) hn4
        wp_if_destruct
        · exact absurd (hs ▸ Hif) hn5
        wp_join_done
        iframe %Hnn
        isplitr [c]
        · iapply (copyRep_open ..).2; iexists iv; iframe Hiv Hlb Hcmds; ipureintro; exact Hivf
        iframe
    -- `if c := IS[q][i]; c != nil && no larger ballot { return }`: falls through
    wp_join at next with [Hcase Hsq e «instance» replica]
    · rw [hqZ, if_pos ⟨hq0, hqlen⟩]
      wp_apply wp_load_slice_index ispS _ isp _ sq hq0 $$ [Hisp] as -
      · iframe Hisp; ipureintro; exact hsq
      rw [hiZ, if_pos ⟨hi0, hilen⟩]
      wp_apply wp_load_slice_index sq _ ptrs _ ptr hi0 $$ [Hsq] as Hsq
      · iframe Hsq; ipureintro; exact hptr
      rcases hc : s.inst q i with _ | c
      · icases Hcase with %Hnull
        subst Hnull
        wp_auto
        wp_join_done
        iframe
        ipureintro; rfl
      · icases Hcase with ⟨%Hnn, Hc⟩
        icases (copyRep_open ..).1 $$ Hc with ⟨%iv, Hiv, #Hcmds, Hlb, %Hivf⟩
        have := hns c hc
        simp only [recStops, not_or] at this
        obtain ⟨⟨hn4, hn5⟩, hnb⟩ := this
        have hb := Hivf.1
        wp_if_destruct
        · exact absurd rfl Hnn
        wp_if_destruct
        · apply absurd _ hnb
          have e1 : BitVec.sshiftRight' iv.ballot' (W64 4) = c.ballot.sshiftRight 4 := by
            rw [hb]; rfl
          have e2 : W32 134217727 = model.maxBallotHi := by decide
          rw [e1, e2] at Hif
          simpa [model.sge, model.sle] using Hif
        wp_join_done
        iframe %Hnn
        isplitr [Hsq e «instance» replica]
        · iapply (copyRep_open ..).2; iexists iv; iframe Hiv Hlb Hcmds; ipureintro; exact Hivf
        iframe
    -- `if IS[q][i] == nil { IS[q][i] = &Instance{...} }`: the slot's copy, `recBase`
    wp_join iprop(∃ (ptr' : Loc) (ptrs' : List Loc), sq ↦* ptrs' ∗
        ⌜ptrs'[(sint.Z i).toNat]? = some ptr'⌝ ∗
        copyRep ρ xs (sint.Z q, sint.Z i) ptr' (recBase s q i) ∗
        (∀ c' : Copy, sq ↦* ptrs' -∗ copyRep ρ xs (sint.Z q, sint.Z i) ptr' c' -∗
          |==> epaxosOwn ρ h r xs (s.setInst q i c')) ∗
        e_ptr ↦ h ∗ instance_ptr ↦ i ∗ replica_ptr ↦ q ∗ nildeps_ptr ↦ zero_val (GoArray w32 5))
      at next with [Hcase Hsq Hclose e «instance» replica nildeps]
      as ⟨%ptr', %ptrs', Hsq, %hptr', Hc, Hcl, e, «instance», replica, nildeps⟩
    · rw [hqZ, if_pos ⟨hq0, hqlen⟩]
      wp_apply wp_load_slice_index ispS _ isp _ sq hq0 $$ [Hisp] as -
      · iframe Hisp; ipureintro; exact hsq
      rw [hiZ, if_pos ⟨hi0, hilen⟩]
      wp_apply wp_load_slice_index sq _ ptrs _ ptr hi0 $$ [Hsq] as Hsq
      · iframe Hsq; ipureintro; exact hptr
      rcases hc : s.inst q i with _ | c
      · icases Hcase with %Hnull
        subst Hnull
        wp_auto
        rw [hqZ, if_pos ⟨hq0, hqlen⟩]
        wp_apply wp_load_slice_index ispS _ isp _ sq hq0 $$ [Hisp] as -
        · iframe Hisp; ipureintro; exact hsq
        rw [hiZ, if_pos ⟨hi0, hilen⟩]
        wp_apply wp_store_slice_index sq _ ptrs «$r0_ptr» $$ [Hsq] as Hsq
        · iframe Hsq; ipureintro; omega
        irename «$r0» => HiI
        generalize «$r0_ptr» = pI
        ihave %HpInn := typedPointsto_not_null _ _ _ $$ HiI
        wp_join_done
        iexists pI, ptrs.set (sint.Z i).toNat pI
        iframe Hsq
        isplitr
        · ipureintro; simp [List.getElem?_set, hilt]
        isplitl [HiI]
        · rw [recBase_none s q i hc]
          iapply (copyRep_open ..).2
          iexists _
          iframe HiI
          isplitr
          · iunfold cmdsRep
            iexists []
            isplitl
            · iapply ownSlice_nil
            ipureintro; exact ⟨rfl, rfl⟩
          isplitr
          · iunfold lbRep; ipureintro; trivial
          ipureintro
          refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
          · show sint.Z q = sint.Z q; rfl
          · show sint.Z i = sint.Z i; rfl
          · rw [hnum]; rfl
          · rw [hlow]; rfl
          · constructor
            · intro e; cases e
            · intro e; exact absurd e hnin
        isplitl [Hclose]
        · icases Hclose with ⟨-, Hclose⟩
          icases Hclose with ⟨Hb, -⟩
          iintro %c' Hsq Hc
          iapply Hb $$ %pI %c' [] Hsq Hc
          ipureintro; exact ⟨rfl, HpInn⟩
        iframe
      · icases Hcase with ⟨%Hnn, Hc⟩
        wp_if_destruct
        · exact absurd rfl Hnn
        wp_join_done
        iexists ptr, ptrs
        iframe Hsq
        isplitr
        · ipureintro; exact hptr
        isplitl [Hc]
        · rw [show recBase s q i = c by simp [recBase, hc]]
          iexact Hc
        isplitl [Hclose]
        · icases Hclose with ⟨Ha, -⟩
          iintro %c' Hsq Hc
          iapply Ha $$ %c' [] Hsq Hc
          ipureintro
          refine ⟨rfl, fun hh => ?_⟩
          rw [hcoe] at hh; cases hh
        iframe
    -- the common tail, on the slot's copy `c0 = recBase s q i` at `ptr'`
    icases (copyRep_open ..).1 $$ Hc with ⟨%iv, Hiv, #Hcmds, Hlb, %Hivf⟩
    rw [hqZ, if_pos ⟨hq0, hqlen⟩]
    wp_apply wp_load_slice_index ispS _ isp _ sq hq0 $$ [Hisp] as -
    · iframe Hisp; ipureintro; exact hsq
    rw [hiZ, if_pos ⟨hi0, hilen⟩]
    have hilen' : (sint.Z i).toNat < ptrs'.length := (List.getElem?_eq_some_iff.1 hptr').1
    wp_apply wp_load_slice_index sq _ ptrs' _ ptr' hi0 $$ [Hsq] as Hsq
    · iframe Hsq; ipureintro; exact hptr'
    ihave #Hfix' := Hfix
    iunfold h2Fixed at Hfix'
    icases Hfix' with ⟨%pS, %alS, %addrs, %st, %cPA, %cA, %cC, %cCS, %cPAR, %cPAO, %cAR, %cEx,
      #HThr, #HExec, #HPO, #HPOS, #HPAL, #HPALS, %HPAl, #HSt, #HStOk, #Hrest⟩
    -- `inst.lb`: new bookkeeping, keeping the client proposals
    wp_join iprop(∃ lbp : Loc, ptr' ↦ { iv with lb' := lbp } ∗
        lbRep ρ lbp (some (recLB (recBase s q i))) ∗ inst_ptr ↦ ptr' ∗ e_ptr ↦ h ∗
        nildeps_ptr ↦ zero_val (GoArray w32 5))
      with [Hiv Hlb inst e nildeps] as ⟨%lbp, Hiv, Hlb, inst, e, nildeps⟩
    · -- no bookkeeping: a fresh one
      rcases hlb : (recBase s q i).lb with _ | b
      rotate_left
      · iunfold lbRep at Hlb
        icases Hlb with ⟨%g, Hg, -⟩
        ihave %Hgn := typedPointsto_not_null _ _ _ $$ Hg
        exact absurd Hif Hgn
      ihave %HalL := ownSlice_len _ _ _ $$ HPALS
      wp_apply (wp_slice_make2 (V := _root_.Perennial.time.Time) _) as %tsl ⟨-, -⟩
      · ipureintro; exact HalL.2
      wp_join_done
      iexists «$r0_ptr»
      iframe
      iunfold lbRep
      iexists _
      iframe «$r0»
      simp only [recLB, hlb]
      isplitr
      · iunfold proposalsRep
        iexists []
        isplitl
        · iapply ownSlice_nil
        simp only [List.length_nil, BigSepL.bigSepL_nil]
        isplitr
        · ipureintro; trivial
        isplitr
        · ipureintro; intro _; trivial
        iempintro
      isplitr
      · iapply ownSlice_nil
      isplitr
      · iunfold riRep; ipureintro; rfl
      ipureintro
      exact ⟨rfl, rfl, trivial, rfl, rfl, rfl, rfl, trivial, rfl, trivial⟩
    · -- existing bookkeeping: its client proposals move to the new one
      rcases hlb : (recBase s q i).lb with _ | b
      · iunfold lbRep at Hlb
        icases Hlb with %Hn
        exact absurd Hn Hif
      iunfold lbRep at Hlb
      icases Hlb with ⟨%gold, Hg, Hprops, -, -, -⟩
      wp_auto
      ihave %HalL := ownSlice_len _ _ _ $$ HPALS
      wp_apply (wp_slice_make2 (V := _root_.Perennial.time.Time) _) as %tsl ⟨-, -⟩
      · ipureintro; exact HalL.2
      wp_join_done
      iexists «$r0_ptr»
      iframe
      iunfold lbRep
      iexists _
      iframe «$r0»
      simp only [recLB, hlb]
      iframe Hprops
      isplitr
      · iapply ownSlice_nil
      isplitr
      · iunfold riRep; ipureintro; rfl
      ipureintro
      exact ⟨rfl, rfl, trivial, rfl, rfl, rfl, rfl, trivial, rfl, trivial⟩
    -- `inst.lb.recoveryInst`: the own candidate (`recRI`)
    iunfold lbRep at Hlb
    icases Hlb with ⟨%g, Hg, Hprops, Hcd, Hri, %Hgf⟩
    rw [show (recLB (recBase s q i)).recoveryInst = none from rfl]
    iunfold riRep at Hri
    icases Hri with %Hri0
    obtain ⟨hb0, hs0, hq0', hd0, hbase0, hslot0, hlead0, hvb0, hL, hS, hI, hLo, hEx⟩ := Hivf
    wp_join iprop(∃ rp : Loc, lbp ↦ { g with recoveryInst' := rp } ∗
        riRep rp (recRI s q (recBase s q i)) ∗
        ptr' ↦ { iv with lb' := lbp } ∗ inst_ptr ↦ ptr' ∗ e_ptr ↦ h ∗ replica_ptr ↦ q)
      with [Hg Hiv inst e replica] as ⟨%rp, Hg, Hri, Hiv, inst, e, replica⟩
    · -- ACCEPTED
      have hacc : (recBase s q i).status = model.St.ACCEPTED := hs0 ▸ Hif
      try wp_join_done
      iexists «$r0_ptr»
      iframe
      unfold recRI
      rw [if_pos hacc]
      iunfold riRep
      iexists _
      iframe «$r0» Hcmds
      ipureintro
      exact ⟨hs0, hq0', hd0, hbase0, rfl, rfl, hvb0⟩
    · have hna : ¬(recBase s q i).status = model.St.ACCEPTED := fun e => Hif (hs0.trans e)
      have hP1 : sint.Z model.St.PREACCEPTED = 1 := by rfl
      wp_if_destruct
      · -- (pre-)accepted below ACCEPTED: the candidate with its count
        have hpre : model.sge (recBase s q i).status model.St.PREACCEPTED = true := by
          rw [← hs0]; simpa [model.sge, model.sle, hP1] using Hif
        wp_join iprop(count_ptr ↦ (if iv.Status' = W8 2 ∧ iv.vbal' = W32 0 ∧ ¬rid32 k = q
            then W64 1 else W64 0) ∗
            ptr' ↦ { iv with lb' := lbp } ∗ inst_ptr ↦ ptr' ∗ e_ptr ↦ h ∗ replica_ptr ↦ q)
          with [count Hiv inst e replica] as ⟨count, Hiv, inst, e, replica⟩
        · repeat wp_if_destruct
          all_goals (try wp_join_done)
          all_goals (iframe Hiv inst e replica)
          all_goals first
            | (rw [if_pos ⟨‹_›, ‹_›, ‹_›⟩]; iframe)
            | (rw [if_neg (fun ⟨_, _, _⟩ => by contradiction)]; iframe)
        · repeat wp_if_destruct
          all_goals (try wp_join_done)
          all_goals (iframe Hiv inst e replica)
          all_goals first
            | (rw [if_pos ⟨‹_›, ‹_›, ‹_›⟩]; iframe)
            | (rw [if_neg (fun ⟨_, _, _⟩ => by contradiction)]; iframe)
        wp_join_done
        iexists «$r0_ptr»
        iframe
        unfold recRI
        rw [if_neg hna, if_pos hpre]
        iunfold riRep
        iexists _
        iframe «$r0» Hcmds
        ipureintro
        refine ⟨hs0, hq0', hd0, hbase0, ?_, ?_, hvb0⟩
        · simp only [hs0, hvb0, Hid]; rfl
        · simp only [Hid]; by_cases e : rid32 k = q <;> simp [e]
      · -- no candidate
        have hpre : ¬model.sge (recBase s q i).status model.St.PREACCEPTED = true := by
          rw [← hs0]; simpa [model.sge, model.sle, hP1] using Hif
        try wp_join_done
        iexists g.recoveryInst'
        iframe
        unfold recRI
        rw [if_neg hna, if_neg hpre]
        iunfold riRep
        ipureintro; exact Hri0
    -- `inst.ballot = makeBallotLargerThan(inst.ballot)`
    wp_apply makeBallotLargerThan.wp h k iv.ballot' $$ []
    · iexists r, gR; iframe #
    -- close the slot at the recovery's copy, then `bcastPrepare`
    let c' := recCopy s q i
    ihave Hc : copyRep ρ xs (sint.Z q, sint.Z i) ptr' c' $$ [Hiv Hg Hprops Hcd Hri]
    · iapply (copyRep_open ..).2
      iexists _
      iframe Hiv
      simp only [c', recCopy]
      isplitr
      · iexact Hcmds
      isplitl
      · iunfold lbRep
        iexists _
        iframe Hg
        iframe Hri
        simp only [recLB]
        iframe Hprops
        iframe Hcd
        ipureintro
        simp only [recLB] at Hgf
        exact Hgf
      ipureintro
      refine ⟨?_, hs0, hq0', hd0, hbase0, hslot0, hlead0, hvb0, hL, hS, hI, hLo, hEx⟩
      simp only [c', recCopy, Hid, hb0]
    ihave Hep := Hcl $$ %c' Hsq Hc
    imod Hep
    have hbal : model.makeBallotLargerThan (rid32 k) iv.ballot' = c'.ballot := by
      simp only [c', recCopy, Hid, hb0]
    rw [hbal]
    ihave #Hcodes := genericOk_prepCodes γ ρ k r gR h $$ Hok
    wp_apply bcastPrepare_wp γ ρ k r gR h t (s.setInst q i c') q i c'.ballot outs []
      (by rw [setInst_id]; exact Hid) hb $$ [Hpend] as Hpend
    · unfold recFixed
      iframe #
      rw [List.append_nil]
      iexact Hpend
    ihave Hco := coordOwn_congr ρ co _ k s (s.setInst q i c') rfl rfl rfl rfl $$ Hco
    iapply HΦ
    iframe Hpend
    iapply handler_close γ ρ k r gR h pa co xs
    iframe Henv
    iunfold parts
    simp only [setInst_tag, setInst_ongoing, setInst_val, setInst_proposeQ, setInst_id]
    iframe
    ipureintro; exact Hid

/-- The frozen `startRecoveryForInstance.wp`'s statement (`Replica2/Specs.lean`), proved. -/
theorem startRecoveryForInstance_wp_frozen (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3)
    (r h : Loc) (q i : w32) :
    stepSpec γ ρ k r (App (App (epM h go!"startRecoveryForInstance") (Val #q)) (Val #i))
      (handlerOf r h) (.recover q i) :=
  fun t s s' outs hstep => startRecoveryForInstance_wp' γ ρ k r h q i t s s' outs hstep

end

end Perennial.gryff.replica2.h3
