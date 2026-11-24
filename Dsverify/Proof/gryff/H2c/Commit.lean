/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2c/Commit.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2c: `handleCommit` (G23's executed guard, G44's re-proposal of a no-op's proposals)
-/
module

public import Dsverify.Proof.gryff.H2.Env
public import Dsverify.Proof.gryff.H2c.SlotOpen
public import Dsverify.Proof.gryff.H2c.CommitModel
public import Dsverify.Proof.gryff.H2c.Base
public import Dsverify.Proof.gryff.H2c.Propose
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
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

theorem msgAt_commit (p : Loc) (mm : model.ECommitM) :
    msgAt (GF := GF) p (.commit mm) ⊣⊢ ∃ (g : wire.gryffproto.ECommit.Msg) (sl : GoSlice),
      p ↦ wire.gryffproto.ECommit.goVal g sl ∗ sl ↦*□ g.Command ∗ ⌜commitOf g = mm⌝ := by
  unfold msgAt; exact .rfl

theorem cmS1_withCrt (s : RState) (m : model.ECommitM) :
    withCrt s (cmS1 s m).crtInstance = cmS1 s m := by
  unfold cmS1; split <;> rfl

@[simp] theorem cmS1_proposeQ (s : RState) (m : model.ECommitM) :
    (cmS1 s m).proposeQ = s.proposeQ := by
  unfold cmS1; split <;> rfl

@[simp] theorem cmS1_inst (s : RState) (m : model.ECommitM) : (cmS1 s m).inst = s.inst := by
  unfold cmS1; split <;> rfl

theorem cmS1_len (s : RState) (m : model.ECommitM) :
    (cmS1 s m).crtInstance.length = s.crtInstance.length := by
  unfold cmS1; split
  · simp [model.RState.setCrt]
  · rfl

set_option maxHeartbeats 4000000 in
theorem handleCommit_wp' (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h p : Loc)
    (m : model.ECommitM) (t : List Ev) (s s' : RState) (outs : List Out)
    (hstep : model.stepR k s (.msg (.commit m)) = .ok (s', outs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r ∗
        replicaOwn ρ k r s ∗ pendingOuts γ ρ k r t outs ∗ handlerOf r h ∗
        msgAt p (.commit m) }}
      (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!!
        go!"handleCommit")) (Val #p))
    {{ RET #(); replicaOwn ρ k r s' ∗ pendingOuts γ ρ k r t [] }} := by
  wp_start as ⟨Hrep, Hown, Hpend, Hh, Hmsg⟩
  icases handler_open γ ρ k r h s $$ [$Hrep $Hh $Hown] with ⟨%gR, %pa, %co, %xs, #Henv, Hparts⟩
  icases (msgAt_commit ..).1 $$ Hmsg with ⟨%g, %sl, Hp, #Hsl, %Hg⟩
  unfold parts
  icases Hparts with ⟨Hparti, Hval, Hcoord, Hep, Hxs, Hprop, Hscr, %Hid⟩
  simp only [model.stepR] at hstep
  obtain ⟨hcmdsOk, hbox, rfl, hcases⟩ := stepCommit_cases s s' outs m hstep
  clear hstep
  subst Hg
  have hbox' := hbox
  simp only [model.inBox, commitOf] at hbox'
  have hbox' := of_decide_eq_true hbox'
  obtain ⟨hq0, hq3, hi0, hiS⟩ := hbox'
  icases epaxosOwn_slot_open ρ h r xs s g.Replica g.Instance hbox $$ Hep with
    ⟨%ispS, %sq, %crtS, %isp, %ptrs, %ip, #HR, #HispS, #Hisp, %Hsl, Hrow, Hslot, %Hxsf, #HelS, #HcrtS,
      Hcrt, Hmono, Hrest, Hclose⟩
  unfold epEnv
  icases Henv with ⟨#HgR, #Hpa, #Hco, #Hh, #HR', #HId, #HN, #HDur, #Hgen, #Hfix⟩
  wp_auto
  h2c_printf
  -- `inst := e.InstanceSpace[Replica][Instance]`
  have hqw : sint.Z (W64 (sint.Z g.Replica)) = sint.Z g.Replica := by word
  have hiw : sint.Z (W64 (sint.Z g.Instance)) = sint.Z g.Instance := by
    unfold model.SLOTS at hiS; word
  ihave %HispSlen := ownSlice_len _ _ _ $$ Hisp
  obtain ⟨hsq, hip, hcrtlen⟩ := Hsl
  have hqlt := (List.getElem?_eq_some_iff.1 hsq).1
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 (sint.Z g.Replica)) ∧
      sint.Z (W64 (sint.Z g.Replica)) < sint.Z ispS.len by
    have h1 := HispSlen.1; have h2 := HispSlen.2; rw [hqw]; rw [h1] at hqlt; word)]
  wp_apply wp_load_slice_index (t := go.GoType.SliceType (go.GoType.PointerType src.gryff.Instance.ty))
    ispS _ isp _ sq (by rw [hqw]; omega) $$ [$Hisp] as -
  · ipureintro; rw [hqw]; exact hsq
  ihave %Hrowlen := ownSlice_len _ _ _ $$ Hrow
  have hilt := (List.getElem?_eq_some_iff.1 hip).1
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 (sint.Z g.Instance)) ∧
      sint.Z (W64 (sint.Z g.Instance)) < sint.Z sq.len by
    have h1 := Hrowlen.1; have h2 := Hrowlen.2; rw [hiw]; rw [h1] at hilt; word)]
  wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty)
    sq _ ptrs _ ip (by rw [hiw]; omega) $$ [$Hrow] as Hrow
  · ipureintro; rw [hiw]; exact hip
  -- `maxSeq`
  icases epaxosRest_maxSeq h $$ Hrest with ⟨%ms, HmaxSeq, Hrestc⟩
  wp_auto
  wp_join iprop((∃ ms' : w32, h.[src.gryff.EPaxosRMWHandler, go!"maxSeq"] ↦ ms') ∗
      p ↦ wire.gryffproto.ECommit.goVal g sl ∗ commit_ptr ↦ p ∗ e_ptr ↦ h)
    with [HmaxSeq Hp commit e] as ⟨⟨%ms', HmaxSeq⟩, Hp, commit, e⟩
  ihave Hrest := Hrestc $$ %ms' HmaxSeq
  -- `crtInstance[Replica] = Instance + 1` if needed
  obtain ⟨cq, hcq⟩ : ∃ cq, s.crtInstance[(sint.Z (W64 (sint.Z g.Replica))).toNat]? = some cq :=
    ⟨_, List.getElem?_eq_getElem (by rw [hqw, hcrtlen]; omega)⟩
  have hqn : (sint.Z (W64 (sint.Z g.Replica))).toNat = g.Replica.toNat := by
    rw [hqw]
    have h1 : uint.Z g.Replica = sint.Z g.Replica := by word
    have h2 : uint.Z g.Replica = (g.Replica.toNat : Int) := rfl
    omega
  have hcqs : cq = s.crt g.Replica := by
    rw [hqn] at hcq
    simp [model.RState.crt, List.getD_eq_getElem?_getD, hcq]
  ihave %Hcrtlen := ownSlice_len _ _ _ $$ Hcrt
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 (sint.Z g.Replica)) ∧
      sint.Z (W64 (sint.Z g.Replica)) < sint.Z crtS.len by
    rw [hqw]; have := Hcrtlen.1; rw [hcrtlen] at this; word)]
  wp_apply wp_load_slice_index (t := go.int32) crtS _ _ _ cq (by rw [hqw]; omega) $$ [$Hcrt] as Hcrt
  · ipureintro; exact hcq
  wp_join iprop(crtS ↦* (cmS1 s (commitOf g)).crtInstance ∗ crtMonos ρ (cmS1 s (commitOf g)) ∗
      e_ptr ↦ h ∗ commit_ptr ↦ p ∗ p ↦ wire.gryffproto.ECommit.goVal g sl)
    with [Hcrt Hmono e commit Hp] as ⟨Hcrt, Hmono, e, commit, Hp⟩
  · have hS1 : cmS1 s (commitOf g) = s.setCrt g.Replica (g.Instance + 1) := by
      simp only [cmS1, commitOf, model.sge, model.sle, ← hcqs, Hif, decide_true, ite_true]
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 (sint.Z g.Replica)) ∧
        sint.Z (W64 (sint.Z g.Replica)) < sint.Z crtS.len by
      rw [hqw]; have := Hcrtlen.1; rw [hcrtlen] at this; word)]
    ihave >Hmono := crt_monos_update ρ s g.Replica (g.Instance + 1) ?_ $$ Hmono
    · rw [← hcqs]
      have : sint.Z (g.Instance + 1) = sint.Z g.Instance + 1 := by unfold model.SLOTS at hiS; word
      omega
    wp_apply wp_store_slice_index (t := go.int32) crtS _ _ (g.Instance + W32 1) $$ [$Hcrt] as Hcrt
    · ipureintro; rw [hqw, hcrtlen]; omega
    wp_join_done
    rw [hS1, hqn, show W32 1 = (1 : w32) from rfl]
    iframe
  · have hS1 : cmS1 s (commitOf g) = s := by
      simp only [cmS1, commitOf, model.sge, model.sle, ← hcqs, Hif, decide_false]
      rfl
    rw [hS1]
    iframe
  ihave Hclose := Hclose $$ %(cmS1 s (commitOf g)).crtInstance %(by rw [cmS1_len]; exact hcrtlen)
    Hcrt [Hmono] Hrest
  · rw [cmS1_withCrt]; iexact Hmono
  rw [cmS1_withCrt]
  rcases hsi : s.inst g.Replica g.Instance with _ | c
  · -- no copy: a new committed instance
    icases Hslot with %hipn
    subst hipn
    have hsi' : s.inst (commitOf g).replica (commitOf g).inst = none := hsi
    obtain hs3 : model.updateCommitted (model.updateConflicts
        ((cmS1 s (commitOf g)).setInst (commitOf g).replica (commitOf g).inst (cmNew (commitOf g)))
        (commitOf g).cmds (commitOf g).replica (commitOf g).inst (commitOf g).seq)
        (commitOf g).replica = some s' := by
      rcases hcases with ⟨c, hc, -⟩ | ⟨c, hc, -⟩ | ⟨-, h3⟩
      · rw [hsi'] at hc; cases hc
      · rw [hsi'] at hc; cases hc
      · exact h3
    clear hcases
    wp_auto
    h2c_printf
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 (sint.Z g.Replica)) ∧
        sint.Z (W64 (sint.Z g.Replica)) < sint.Z ispS.len by
      have h1 := HispSlen.1; have h2 := HispSlen.2; rw [hqw]; rw [h1] at hqlt; word)]
    wp_apply wp_load_slice_index (t := go.GoType.SliceType (go.GoType.PointerType src.gryff.Instance.ty))
      ispS _ isp _ sq (by rw [hqw]; omega) $$ [$Hisp] as -
    · ipureintro; rw [hqw]; exact hsq
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 (sint.Z g.Instance)) ∧
        sint.Z (W64 (sint.Z g.Instance)) < sint.Z sq.len by
      have h1 := Hrowlen.1; have h2 := Hrowlen.2; rw [hiw]; rw [h1] at hilt; word)]
    wp_apply wp_store_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty)
      sq _ ptrs «$r0_ptr» $$ [$Hrow] as Hrow
    · ipureintro; rw [hiw]; omega
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ «$r0»
    icases Hclose with ⟨-, Hb, -⟩
    have hco : committedOrExecuted s (sint.Z g.Replica, sint.Z g.Instance) = false := by
      simp only [committedOrExecuted, model.committedCopy, BitVec.ofInt_toInt, hsi]
      split <;> rfl
    obtain ⟨hx1, hx2, hx3⟩ := Hxsf hco
    rw [hiw]
    ihave Hep := Hb $$ %«$r0_ptr» %(cmNew (commitOf g)) [] Hrow [«$r0»]
    · ipureintro; exact ⟨rfl, Hnn⟩
    · iapply (copyRep_open ..).2
      iexists _
      iframe «$r0»
      dsimp only [cmNew]
      isplitr
      · iapply (cmdsRep_open ..).2; iexists g.Command; iframe Hsl; ipureintro; exact ⟨rfl, hcmdsOk⟩
      isplitr
      · iapply (lbRep_none ..).2; ipureintro; rfl
      ipureintro
      simp only [commitOf, hx1, hx2]
      refine ⟨rfl, rfl, trivial, trivial, trivial, trivial, trivial, rfl, trivial, trivial, rfl, rfl, ?_⟩
      simp only [model.St.COMMITTED, model.St.EXECUTED]
      constructor
      · intro h; cases h
      · intro h; exact absurd h hx3
    imod Hep
    ihave #Hae : attrEnv k r gR h $$ []
    · unfold attrEnv; iframe #
    wp_apply (wp_updateConflicts ρ k r gR h xs _ sl g.Command g.Replica g.Instance g.Seq
      hcmdsOk ⟨hq0, hq3⟩) $$ [$Hae $Hep $Hsl] as Hep
    have hs3' : model.updateCommitted (model.updateConflicts ((cmS1 s (commitOf g)).setInst g.Replica
        g.Instance (cmNew (commitOf g))) (List.map cmdOf g.Command) g.Replica g.Instance g.Seq)
        g.Replica = some s' := hs3
    wp_apply (wp_updateCommitted ρ k r gR h xs _ s' g.Replica ⟨hq0, hq3⟩ hs3') $$ [$Hae $Hep]
      as Hep
    have hbox2 : model.inBox g.Replica g.Instance = true := hbox
    icases epaxosOwn_peek ρ h r xs s' g.Replica g.Instance hbox2 $$ Hep with
      ⟨%ispS2, %sq2, %isp2, %ptrs2, %p2, #HispS2, #Hisp2, %Hsl2, Hrow2, Hback⟩
    icombine HispS HispS2 gives %Hspe
    subst Hspe
    icombine Hisp Hisp2 gives %Hie
    subst Hie
    obtain ⟨hsq2, hp2⟩ := Hsl2
    rw [hsq] at hsq2
    cases hsq2
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 (sint.Z g.Replica)) ∧
        sint.Z (W64 (sint.Z g.Replica)) < sint.Z ispS.len by
      have h1 := HispSlen.1; have h2 := HispSlen.2; rw [hqw]; rw [h1] at hqlt; word)]
    wp_apply wp_load_slice_index (t := go.GoType.SliceType (go.GoType.PointerType src.gryff.Instance.ty))
      ispS _ isp _ sq (by rw [hqw]; omega) $$ [$Hisp] as -
    · ipureintro; rw [hqw]; exact hsq
    ihave %Hrowlen2 := ownSlice_len _ _ _ $$ Hrow2
    have hilt2 := (List.getElem?_eq_some_iff.1 hp2).1
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 (sint.Z g.Instance)) ∧
        sint.Z (W64 (sint.Z g.Instance)) < sint.Z sq.len by
      have h1 := Hrowlen2.1; have h2 := Hrowlen2.2; rw [hiw]; rw [h1] at hilt2; word)]
    wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty)
      sq _ ptrs2 _ p2 (by rw [hiw]; omega) $$ [$Hrow2] as Hrow2
    · ipureintro; rw [hiw]; exact hp2
    wp_apply (wp_recordInstanceMetadata h r gR) $$ [$HR' $HgR $HDur]
    wp_apply (wp_recordCommands h r gR) $$ [$HR' $HgR $HDur]
    ihave Hep := Hback $$ Hrow2
    have hso : sameOut s s' :=
      sameOut_trans (cmS1_sameOut s _) (sameOut_trans (sameOut_setInst _ _ _ _)
        (sameOut_trans (sameOut_updateConflicts _ _ _ _ _) (sameOut_updateCommitted hs3)))
    obtain ⟨ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho8, ho9, -⟩ := hso
    iapply HΦ
    iframe Hpend
    iapply handler_close γ ρ k r gR h pa co xs s'
    isplitr
    · unfold epEnv; iframe #
    unfold parts
    rw [ho2, ho3, ho4, ho9]
    iframe Hparti Hval Hxs Hprop Hscr Hep
    isplitl
    · iapply coordOwn_congr ρ co _ k s s' ho5 ho6 ho7 ho8 $$ Hcoord
    · ipureintro; rw [ho1]; exact Hid
  · -- an existing copy
    icases Hslot with ⟨%hipn, Hc⟩
    icases (copyRep_open ..).1 $$ Hc with ⟨%iv, Hiv, #Hcmds, Hlb, %Hivf⟩
    have hsi' : s.inst (commitOf g).replica (commitOf g).inst = some c := hsi
    simp only [hipn, decide_false, Bool.not_false]
    wp_auto
    wp_if_destruct
    · -- executed (G23): nothing changes
      have hcx : c.status = model.St.EXECUTED := by rw [← Hivf.2.1, Hif]; rfl
      obtain rfl : s' = cmS1 s (commitOf g) := by
        rcases hcases with ⟨c', hc', -, h3⟩ | ⟨c', hc', hx, -⟩ | ⟨hn, -⟩
        · exact h3
        · rw [hsi'] at hc'; cases hc'; exact absurd hcx hx
        · rw [hsi'] at hn; cases hn
      ihave Hc := (copyRep_open ρ xs _ ip c).2 $$ [Hiv Hlb]
      · iexists iv; iframe # ∗; ipureintro; exact Hivf
      icases Hclose with ⟨-, -, -, Ha⟩
      ihave Hep := Ha $$ %c [] Hrow Hc
      · ipureintro
        refine ⟨rfl, ?_⟩
        rw [setInst_self s _ _ c hsi]
      rw [setInst_self (cmS1 s (commitOf g)) _ _ c (by rw [cmS1_inst]; exact hsi)]
      obtain ⟨ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho8, ho9, -⟩ := cmS1_sameOut s (commitOf g)
      iapply HΦ
      iframe Hpend
      iapply handler_close γ ρ k r gR h pa co xs (cmS1 s (commitOf g))
      isplitr
      · unfold epEnv; iframe #
      unfold parts
      rw [ho2, ho3, ho4, ho9]
      iframe Hparti Hval Hxs Hprop Hscr Hep
      isplitl
      · iapply coordOwn_congr ρ co _ k s _ ho5 ho6 ho7 ho8 $$ Hcoord
      · ipureintro; rw [ho1]; exact Hid
    -- not executed
    have hcx : c.status ≠ model.St.EXECUTED := by
      intro h; apply Hif; rw [Hivf.2.1, h]; rfl
    obtain hs3 : model.updateCommitted ((cmS2 (cmS1 s (commitOf g)) c (commitOf g)).setInst
        (commitOf g).replica (commitOf g).inst (cmCopy c (commitOf g))) (commitOf g).replica =
        some s' := by
      rcases hcases with ⟨c', hc', hx, -⟩ | ⟨c', hc', -, h3⟩ | ⟨hn, -⟩
      · rw [hsi'] at hc'; cases hc'; exact absurd hx hcx
      · rw [hsi'] at hc'; cases hc'; exact h3
      · rw [hsi'] at hn; cases hn
    clear hcases
    simp only [hipn, decide_false, Bool.not_false]
    wp_auto
    wp_join iprop(∃ iv' : src.gryff.Instance, ip ↦ iv' ∗ ⌜iv' = { iv with lb' := iv'.lb' }⌝ ∗
        lbRep ρ iv'.lb' (if cmRe c (commitOf g) then none else c.lb) ∗
        proposeOwn ρ gR (cmS2 (cmS1 s (commitOf g)) c (commitOf g)).proposeQ ∗
        inst_ptr ↦ ip ∗ e_ptr ↦ h ∗ commit_ptr ↦ p ∗ p ↦ wire.gryffproto.ECommit.goVal g sl) at next
      with [Hiv Hlb Hprop inst e commit Hp] as ⟨%iv', Hiv, %Hiv', Hlb, Hprop, inst, e, commit, Hp⟩
    · rcases hlbc : c.lb with _ | b
      · -- no bookkeeping: nothing to re-propose
        have hre : ¬ cmRe c (commitOf g) := by rintro ⟨b, hb, -⟩; rw [hlbc] at hb; cases hb
        icases (lbRep_none ..).1 $$ Hlb with %Hlbn
        rw [Hlbn]
        wp_auto
        wp_join_done
        iexists iv
        simp only [cmS2, hre, ↓reduceIte, ite_self, cmS1_proposeQ]
        iframe
        iapply (lbRep_none ..).2; ipureintro; exact Hlbn
      · -- bookkeeping
        icases (lbRep_some ..).1 $$ Hlb with ⟨%gb, Hgb, Hprs, Hcd, Hri, %Hgbf⟩
        ihave %Hlbnn := typedPointsto_not_null _ _ _ $$ Hgb
        simp only [Hlbnn, decide_false, Bool.not_false]
        wp_auto
        unfold proposalsRep
        icases Hprs with ⟨%pps, #Hpps, %Hppl, %Hpnil, #Hels⟩
        ihave %Hppsl := ownSlice_len _ _ _ $$ Hpps
        ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
        by_cases hn : gb.clientProposals' = slice.nil
        · -- nil proposals: nothing to re-propose
          have hpps : pps = [] := by
            rw [hn] at Hppsl; exact List.length_eq_zero_iff.1 Hppsl.1
          have hre : ¬ cmRe c (commitOf g) := by
            rintro ⟨b', hb', hne, -⟩; rw [hlbc] at hb'; cases hb'
            subst hpps; exact hne (List.length_eq_zero_iff.1 Hppl.symm)
          rw [show decide (gb.clientProposals' = slice.nil) = true from decide_eq_true hn]
          simp only [Bool.not_true]
          wp_auto
          wp_join_done
          iexists iv
          simp only [cmS2, hre, ↓reduceIte, cmS1_proposeQ, hlbc]
          iframe
          iapply (lbRep_some ..).2
          iexists gb
          iframe
          unfold proposalsRep
          isplitl
          · iexists pps
            iframe # ∗
            ipureintro; exact ⟨Hppl, Hpnil⟩
          · ipureintro; exact Hgbf
        simp only [hn, decide_false, Bool.not_false]
        wp_auto
        by_cases hc0 : g.Command = []
        · -- a no-op committed
          have hsl0 : sl.len = W64 0 := by
            rw [hc0] at Hsll; simp at Hsll; word
          simp only [hsl0, _root_.decide_true]
          wp_auto
          by_cases hcp : b.clientProposals = []
          · exact absurd (Hpnil hcp) hn -- H2c-R2: a non-nil proposals slice is non-empty
          have hre : cmRe c (commitOf g) := ⟨b, hlbc, hcp, by simp [commitOf, hc0]⟩
          -- G44: the proposals re-proposed, in order
          icases proposeOwn_chan ρ gR _ $$ Hprop with ⟨Hprop, %ch, #Hch⟩
          ihave HL : (∃ (j : w64), "i" ∷ i_ptr ↦ j ∗ "p" ∷ (∃ v : Loc, p_ptr ↦ v) ∗
              "Hprop" ∷ proposeOwn ρ gR (s.proposeQ ++ b.clientProposals.take (sint.nat j)) ∗
              "Hpps" ∷ gb.clientProposals' ↦*□ pps ∗
              "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ pps.length⌝ : IProp GF) $$ [i p Hprop Hpps]
          · iexists W64 0
            simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.append_nil]
            iframe; iframe Hpps
            isplitl
            · iexists _; iexact p
            · ipureintro; simp
          wp_for HL
          obtain ⟨hj0, hjl⟩ := Hj
          have hlen : sint.nat gb.clientProposals'.len = pps.length := Hppsl.1.symm
          wp_if_destruct
          · -- an iteration
            have hjlt : sint.nat j < pps.length := by
              rw [← hlen]; word
            obtain ⟨pp, hpp⟩ : ∃ pp, pps[sint.nat j]? = some pp :=
              ⟨_, List.getElem?_eq_getElem hjlt⟩
            rw [ite_eq_left (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z gb.clientProposals'.len by omega)]
            wp_apply wp_load_slice_index (t := go.GoType.PointerType src.genericsmr.Propose.ty)
              gb.clientProposals' _ pps _ pp hj0 $$ [$Hpps] as Hpps
            · ipureintro; exact hpp
            ihave Hel := BigSepL.bigSepL_lookup hpp $$ Hels
            icases Hel with ⟨%pr, %Hpr, #Hppr⟩
            icases p with ⟨%v0, p⟩
            wp_auto
            wp_apply wp_propose_send $$ [$Hprop $Hch $Hppr] as Hprop
            wp_for_post
            iframe
            iexists j + W64 1
            iframe
            have hj1 : sint.Z (j + W64 1) = sint.Z j + 1 := by
              rw [← hlen] at hjlt; word
            have hcpl : sint.nat j < b.clientProposals.length := by rw [← Hppl]; exact hjlt
            have htake : b.clientProposals.take (sint.nat (j + W64 1)) =
                b.clientProposals.take (sint.nat j) ++ [pr] := by
              have : sint.nat (j + W64 1) = sint.nat j + 1 := by word
              rw [this, List.take_succ, Hpr]; rfl
            rw [htake, ← List.append_assoc]
            iframe
            isplitl
            · iexists _; iexact p
            · ipureintro
              refine ⟨by omega, ?_⟩
              word
          · -- done: all proposals sent, `lb = nil`
            have hjeq : sint.nat j = b.clientProposals.length := by
              rw [← Hppl, ← hlen]; rw [← hlen] at hjl; word
            rw [hjeq, List.take_length]
            wp_join_done
            iexists { iv with lb' := Loc.null }
            simp only [cmS2, hre, ↓reduceIte, cmS1_proposeQ, cmProps, hlbc]
            iframe
            iapply (lbRep_none ..).2; ipureintro; rfl
        · have hsl0 : sl.len ≠ W64 0 := by
            intro e; rw [e] at Hsll; apply hc0; have := Hsll.1; simpa [sint.nat] using this
          have hre : ¬ cmRe c (commitOf g) := by
            rintro ⟨-, -, -, h⟩; apply hc0; simpa [commitOf] using h
          simp only [hsl0, decide_false]
          wp_auto
          wp_join_done
          iexists iv
          simp only [cmS2, hre, ↓reduceIte, cmS1_proposeQ, hlbc]
          iframe
          iapply (lbRep_some ..).2
          iexists gb
          iframe
          unfold proposalsRep
          isplitl
          · iexists pps
            iframe # ∗
            ipureintro; exact ⟨Hppl, Hpnil⟩
          · ipureintro; exact Hgbf
    -- the slot back at the committed copy
    have hiv'lb := congrArg src.gryff.Instance.lb' Hiv'
    ihave Hc : copyRep ρ xs (sint.Z g.Replica, sint.Z g.Instance) ip (cmCopy c (commitOf g)) $$ [Hiv Hlb]
    · iapply (copyRep_open ..).2
      iexists _
      iframe Hiv
      dsimp only
      simp only [cmCopy_cmds, cmCopy_lb]
      iframe Hlb
      isplitr
      · iapply (cmdsRep_open ..).2; iexists g.Command; iframe Hsl; ipureintro; exact ⟨rfl, hcmdsOk⟩
      ipureintro
      have e1 : iv'.ballot' = iv.ballot' := by rw [Hiv']
      have e2 : iv'.Slot' = iv.Slot' := by rw [Hiv']
      have e3 : iv'.Leader' = iv.Leader' := by rw [Hiv']
      have e4 : iv'.vbal' = iv.vbal' := by rw [Hiv']
      have e5 : iv'.Index' = iv.Index' := by rw [Hiv']
      have e6 : iv'.Lowlink' = iv.Lowlink' := by rw [Hiv']
      obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13⟩ := Hivf
      simp only [cmCopy_ballot, cmCopy_status, cmCopy_seq, cmCopy_deps, cmCopy_base, cmCopy_slot,
        cmCopy_leader, cmCopy_vbal, e1, e2, e3, e4, e5, e6, commitOf]
      refine ⟨f1, rfl, trivial, trivial, trivial, f6, f7, f8, f9, f10, f11, f12, ?_⟩
      simp only [model.St.COMMITTED, model.St.EXECUTED]
      constructor
      · intro h; cases h
      · intro h; exact absurd (f13.2 h) hcx
    -- the slot closed at the committed copy
    icases Hclose with ⟨Ha, -⟩
    ihave Hep := Ha $$ %(cmCopy c (commitOf g)) [] Hrow Hc
    · ipureintro
      refine ⟨rfl, fun _ => ?_⟩
      have hbox2 : model.inBox g.Replica g.Instance = true := hbox
      rw [committedOrExecuted_setInst_self s _ _ _ hbox2]
      simp
    imod Hep with ⟨Hep, -⟩
    ihave Hep := epaxosOwn_proposeQ ρ h r xs _ (cmS2 (cmS1 s (commitOf g)) c (commitOf g)).proposeQ $$ Hep
    rw [← cmS2_setInst]
    ihave #Hae : attrEnv k r gR h $$ []
    · unfold attrEnv; iframe #
    have hs3' : model.updateCommitted ((cmS2 (cmS1 s (commitOf g)) c (commitOf g)).setInst
        g.Replica g.Instance (cmCopy c (commitOf g))) g.Replica = some s' := hs3
    wp_apply (wp_updateCommitted ρ k r gR h xs _ s' g.Replica ⟨hq0, hq3⟩ hs3') $$ [$Hae $Hep]
      as Hep
    have hbox2 : model.inBox g.Replica g.Instance = true := hbox
    icases epaxosOwn_peek ρ h r xs s' g.Replica g.Instance hbox2 $$ Hep with
      ⟨%ispS2, %sq2, %isp2, %ptrs2, %p2, #HispS2, #Hisp2, %Hsl2, Hrow2, Hback⟩
    icombine HispS HispS2 gives %Hspe
    subst Hspe
    icombine Hisp Hisp2 gives %Hie
    subst Hie
    obtain ⟨hsq2, hp2⟩ := Hsl2
    rw [hsq] at hsq2
    cases hsq2
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 (sint.Z g.Replica)) ∧
        sint.Z (W64 (sint.Z g.Replica)) < sint.Z ispS.len by
      have h1 := HispSlen.1; have h2 := HispSlen.2; rw [hqw]; rw [h1] at hqlt; word)]
    wp_apply wp_load_slice_index (t := go.GoType.SliceType (go.GoType.PointerType src.gryff.Instance.ty))
      ispS _ isp _ sq (by rw [hqw]; omega) $$ [$Hisp] as -
    · ipureintro; rw [hqw]; exact hsq
    ihave %Hrowlen2 := ownSlice_len _ _ _ $$ Hrow2
    have hilt2 := (List.getElem?_eq_some_iff.1 hp2).1
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 (sint.Z g.Instance)) ∧
        sint.Z (W64 (sint.Z g.Instance)) < sint.Z sq.len by
      have h1 := Hrowlen2.1; have h2 := Hrowlen2.2; rw [hiw]; rw [h1] at hilt2; word)]
    wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty)
      sq _ ptrs2 _ p2 (by rw [hiw]; omega) $$ [$Hrow2] as Hrow2
    · ipureintro; rw [hiw]; exact hp2
    wp_apply (wp_recordInstanceMetadata h r gR) $$ [$HR' $HgR $HDur]
    wp_apply (wp_recordCommands h r gR) $$ [$HR' $HgR $HDur]
    ihave Hep := Hback $$ Hrow2
    have hso : sameOut { (cmS1 s (commitOf g)).setInst g.Replica g.Instance (cmCopy c (commitOf g)) with
        proposeQ := (cmS2 (cmS1 s (commitOf g)) c (commitOf g)).proposeQ } s' := by
      rw [← cmS2_setInst]; exact sameOut_updateCommitted hs3
    obtain ⟨ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho8, ho9, -⟩ := hso
    obtain ⟨hp1, hp2', hp3, hp4, hp5, hp6, hp7, hp8, -⟩ := cmS1_sameOut s (commitOf g)
    iapply HΦ
    iframe Hpend
    iapply handler_close γ ρ k r gR h pa co xs s'
    isplitr
    · unfold epEnv; iframe #
    unfold parts
    rw [ho9]
    simp only [model.RState.setInst] at ho1 ho2 ho3 ho4 ho5 ho6 ho7 ho8
    rw [ho2, ho3, ho4, hp2', hp3, hp4]
    iframe Hparti Hval Hxs Hprop Hscr Hep
    isplitl
    · iapply coordOwn_congr ρ co _ k s s' (ho5.trans hp5) (ho6.trans hp6) (ho7.trans hp7)
        (ho8.trans hp8) $$ Hcoord
    · ipureintro; rw [ho1, hp1]; exact Hid

/-- **`handleCommit.wp`** (`Replica2/Specs.lean`), at its frozen statement. -/
theorem handleCommit_spec (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc)
    (m : model.ECommitM) : epHandlerSpec γ ρ k r h go!"handleCommit" (.commit m) := by
  intro p t s s' outs hstep
  iintro %Φ ⟨#Hpkg, #Hrep, Hown, Hpend, Hh, Hmsg⟩ HΦ
  iapply (handleCommit_wp' γ ρ k r h p m t s s' outs hstep) $$ [Hown Hpend Hh Hmsg] HΦ
  iframe # ∗

end

end Perennial.gryff.replica2
