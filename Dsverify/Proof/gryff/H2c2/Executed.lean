/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2c2/Executed.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2c2: `handleExecuted`, `incrementNumReplicasExecuted` (G43: the reply carries the
proposal's `OldValue`)
-/
module

public import Dsverify.Proof.gryff.H2.Env
public import Dsverify.Proof.gryff.H2c.SlotOpen
public import Dsverify.Proof.gryff.H2c2.Base
public import Dsverify.Proof.gryff.H2c2.ExecModel
public import Dsverify.Proof.gryff.H2b.Propose
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
variable [strconvA : strconv.Assumptions] -- N-5


set_option goose.wp.extras true

theorem msgAt_executed (p : Loc) (mm : model.ExecutedM) :
    msgAt (GF := GF) p (.executed mm) ⊣⊢ ∃ g : src.gryffproto.Executed, p ↦ g ∗ ⌜executedOf g = mm⌝ := by
  unfold msgAt; exact .rfl

set_option maxHeartbeats 4000000 in
/-- `handleExecuted(ex)` with the handler's resources open (`executeOverwrite` calls it on its
own `Executed`). -/
theorem handleExecuted_wp' (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h p : Loc)
    (m : model.ExecutedM) (t : List Ev) (s s' : RState) (outs : List Out)
    (hstep : model.handleExecuted s m = .ok (s', outs)) (g : src.gryffproto.Executed)
    (hg : executedOf g = m) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r ∗
        replicaOwn ρ k r s ∗ pendingOuts γ ρ k r t outs ∗ handlerOf r h ∗ p ↦ g }}
      (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!!
        go!"handleExecuted")) (Val #p))
    {{ RET #(); replicaOwn ρ k r s' ∗ pendingOuts γ ρ k r t [] }} := by
  wp_start as ⟨Hrep, Hown, Hpend, Hh, Hp⟩
  icases handler_open γ ρ k r h s $$ [$Hrep $Hh $Hown] with ⟨%gR, %pa, %co, %xs, #Henv, Hparts⟩
  unfold parts
  icases Hparts with ⟨Hparti, Hval, Hcoord, Hep, Hxs, Hprop, Hscr, %Hid⟩
  obtain ⟨hbox, hcases⟩ := handleExecuted_cases s s' outs m hstep
  clear hstep
  subst hg
  have hbox' := hbox
  simp only [model.inBox, executedOf] at hbox'
  have hbox' := of_decide_eq_true hbox'
  obtain ⟨hq0, hq3, hi0, hiS⟩ := hbox'
  have hbox2 : model.inBox g.Replica' g.Instance' = true := hbox
  ihave #Henv' := Henv
  unfold epEnv
  icases Henv' with ⟨#HgR, #Hpa, #Hco, #Hh, #HR', #HId, #HN, #HDur, #Hgen, #Hfix⟩
  have hqw : sint.Z (W64 (sint.Z g.Replica')) = sint.Z g.Replica' := by word
  have hiw : sint.Z (W64 (sint.Z g.Instance')) = sint.Z g.Instance' := by
    unfold model.SLOTS at hiS; word
  rcases hsi : s.inst g.Replica' g.Instance' with _ | c
  · -- no copy: nothing
    obtain ⟨hss, rfl⟩ : s' = s ∧ outs = [] := by
      rcases hcases with ⟨-, h1, h2⟩ | ⟨c, hc, -⟩
      · exact ⟨h1, h2⟩
      · have hc' : s.inst g.Replica' g.Instance' = some c := hc
        rw [hsi] at hc'; cases hc'
    rw [hss]
    icases epaxosOwn_peek' ρ h r xs s g.Replica' g.Instance' hbox2 $$ Hep with
      ⟨%ispS, %sq, %isp, %ptrs, %ip, #HispS, #Hisp, %Hsl, Hrow, Hback⟩
    obtain ⟨hsq, hip, hnull⟩ := Hsl
    have hipn := hnull hsi
    subst hipn
    ihave %HispSlen := ownSlice_len _ _ _ $$ Hisp
    have hqlt := (List.getElem?_eq_some_iff.1 hsq).1
    wp_auto
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 (sint.Z g.Replica')) ∧
        sint.Z (W64 (sint.Z g.Replica')) < sint.Z ispS.len by
      have h1 := HispSlen.1; have h2 := HispSlen.2; rw [hqw]; rw [h1] at hqlt; word)]
    wp_apply wp_load_slice_index (t := go.GoType.SliceType (go.GoType.PointerType src.gryff.Instance.ty))
      ispS _ isp _ sq (by rw [hqw]; omega) $$ [$Hisp] as -
    · ipureintro; rw [hqw]; exact hsq
    ihave %Hrowlen := ownSlice_len _ _ _ $$ Hrow
    have hilt := (List.getElem?_eq_some_iff.1 hip).1
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 (sint.Z g.Instance')) ∧
        sint.Z (W64 (sint.Z g.Instance')) < sint.Z sq.len by
      have h1 := Hrowlen.1; have h2 := Hrowlen.2; rw [hiw]; rw [h1] at hilt; word)]
    wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty)
      sq _ ptrs _ _ (by rw [hiw]; omega) $$ [$Hrow] as Hrow
    · ipureintro; rw [hiw]; exact hip
    wp_auto
    ihave Hep := Hback $$ Hrow
    iapply HΦ
    iframe Hpend
    iapply handler_close γ ρ k r gR h pa co xs s
    isplitr
    · unfold epEnv; iframe #
    unfold parts
    iframe Hparti Hval Hxs Hprop Hscr Hep Hcoord
    ipureintro; exact Hid
  icases epaxosOwn_slot_open ρ h r xs s g.Replica' g.Instance' hbox2 $$ Hep with
    ⟨%ispS, %sq, %crtS, %isp, %ptrs, %ip, #HR, #HispS, #Hisp, %Hsl, Hrow, Hslot, %Hxsf, #HelS, #HcrtS,
      Hcrt, Hmono, Hrest, Hclose⟩
  ihave Hclose := Hclose $$ %s.crtInstance %Hsl.2.2 Hcrt [Hmono] Hrest
  · rw [withCrt_self]; iexact Hmono
  rw [withCrt_self, hsi]
  icases Hslot with ⟨%hipn, Hc⟩
  icases (copyRep_open ..).1 $$ Hc with ⟨%iv, Hiv, #Hcmds, Hlb, %Hivf⟩
  ihave %HispSlen := ownSlice_len _ _ _ $$ Hisp
  obtain ⟨hsq, hip, hcrtlen⟩ := Hsl
  have hqlt := (List.getElem?_eq_some_iff.1 hsq).1
  wp_auto
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 (sint.Z g.Replica')) ∧
      sint.Z (W64 (sint.Z g.Replica')) < sint.Z ispS.len by
    have h1 := HispSlen.1; have h2 := HispSlen.2; rw [hqw]; rw [h1] at hqlt; word)]
  wp_apply wp_load_slice_index (t := go.GoType.SliceType (go.GoType.PointerType src.gryff.Instance.ty))
    ispS _ isp _ sq (by rw [hqw]; omega) $$ [$Hisp] as -
  · ipureintro; rw [hqw]; exact hsq
  ihave %Hrowlen := ownSlice_len _ _ _ $$ Hrow
  have hilt := (List.getElem?_eq_some_iff.1 hip).1
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 (sint.Z g.Instance')) ∧
      sint.Z (W64 (sint.Z g.Instance')) < sint.Z sq.len by
    have h1 := Hrowlen.1; have h2 := Hrowlen.2; rw [hiw]; rw [h1] at hilt; word)]
  wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty)
    sq _ ptrs _ ip (by rw [hiw]; omega) $$ [$Hrow] as Hrow
  · ipureintro; rw [hiw]; exact hip
  simp only [hipn, decide_false]
  wp_auto
  rcases hlbc : c.lb with _ | lb
  · -- no bookkeeping: nothing
    obtain ⟨hss, rfl⟩ : s' = s ∧ outs = [] := by
      rcases hcases with ⟨hn, -⟩ | ⟨c', hc', hc2⟩
      · rw [executedOf] at hn; simp only at hn; rw [hsi] at hn; cases hn
      have hc'' : s.inst g.Replica' g.Instance' = some c' := hc'
      rw [hsi] at hc''; cases hc''
      rcases hc2 with ⟨-, h1, h2⟩ | ⟨lb, hlb, -⟩
      · exact ⟨h1, h2⟩
      · rw [hlbc] at hlb; cases hlb
    rw [hss]
    icases (lbRep_none ..).1 $$ Hlb with %Hlbn
    rw [Hlbn]
    wp_auto
    ihave Hc := (copyRep_open ρ xs _ ip c).2 $$ [Hiv]
    · iexists iv; iframe # ∗; rw [hlbc]; isplitr
      · iapply (lbRep_none ..).2; ipureintro; exact Hlbn
      · ipureintro; exact Hivf
    icases Hclose with ⟨-, -, -, Ha⟩
    ihave Hep := Ha $$ %c [] Hrow Hc
    · ipureintro; refine ⟨rfl, ?_⟩; rw [setInst_self s _ _ c hsi]
    rw [setInst_self s _ _ c hsi]
    iapply HΦ
    iframe Hpend
    iapply handler_close γ ρ k r gR h pa co xs s
    isplitr
    · unfold epEnv; iframe #
    unfold parts
    iframe Hparti Hval Hxs Hprop Hscr Hep Hcoord
    ipureintro; exact Hid
  icases (lbRep_some ..).1 $$ Hlb with ⟨%gb, Hgb, Hprs, Hcd, Hri, %Hgbf⟩
  ihave %Hlbnn := typedPointsto_not_null _ _ _ $$ Hgb
  simp only [Hlbnn, decide_false]
  wp_auto
  wp_method_call
  wp_auto
  iStructNamed Hgb
  wp_apply (wp_AddInt32_own _ gb.numReplicasExecuted' (W32 1)) $$ [$numReplicasExecuted]
    as numReplicasExecuted
  have hcs : (exReply lb = true ∧ ∃ pr, lb.clientProposals.head? = some pr ∧
      s' = s.setInst g.Replica' g.Instance'
        { c with lb := some { exLB lb with repliedClient := true } } ∧
      outs = [.ext (.rmwReply pr.client pr.cmdId 1)]) ∨
      (exReply lb = false ∧ s' = s.setInst g.Replica' g.Instance' { c with lb := some (exLB lb) } ∧
        outs = []) := by
    rcases hcases with ⟨hn, -⟩ | ⟨c', hc', hc2⟩
    · have hn' : s.inst g.Replica' g.Instance' = none := hn
      rw [hsi] at hn'; cases hn'
    have hc'' : s.inst g.Replica' g.Instance' = some c' := hc'
    rw [hsi] at hc''; cases hc''
    rcases hc2 with ⟨hl, -⟩ | ⟨lb', hlb', h⟩
    · rw [hlbc] at hl; cases hl
    rw [hlbc] at hlb'; cases hlb'
    exact h
  clear hcases
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := Hgbf
  rcases hcs with ⟨hrep, pr, hpr, hss, rfl⟩ | ⟨hrep, hss, rfl⟩
  · -- a majority executed: the reply
    have hrep' := hrep
    simp only [exReply, Bool.and_eq_true, Bool.not_eq_true'] at hrep'
    rw [f10, hrep'.1]
    simp only [Bool.not_false]
    wp_auto
    have e2 : (W32 (sint.Z (BitVec.sdiv (W64 3) (W64 2) + W64 1)) : w32) = 2 := by decide
    rw [e2, f9]
    have hge : decide (sint.Z (2 : w32) ≤ sint.Z (lb.numReplicasExecuted + W32 1)) = true := by
      have := hrep'.2; simp only [model.sge, model.sle] at this; exact this
    rw [hge]
    wp_auto
    h2c_printf
    unfold proposalsRep
    icases Hprs with ⟨%pps, #Hpps, %Hppl, %Hpnil, #Hels⟩
    ihave %Hppsl := ownSlice_len _ _ _ $$ Hpps
    obtain ⟨pp, hpp⟩ : ∃ pp, pps[0]? = some pp := by
      have : 0 < pps.length := by
        rw [Hppl]; cases hc : lb.clientProposals with
        | nil => rw [hc] at hpr; cases hpr
        | cons _ _ => simp
      exact ⟨_, List.getElem?_eq_getElem this⟩
    ihave Hel := BigSepL.bigSepL_lookup hpp $$ Hels
    icases Hel with ⟨%pr', %Hpr', #Hppr⟩
    have hprr : pr' = pr := by
      rw [List.head?_eq_getElem?] at hpr; rw [hpr] at Hpr'; cases Hpr'; rfl
    subst hprr
    icases (h2b.proposalRep_open ..).1 $$ Hppr with ⟨%gp, %inner, #Hgp, #Hinner, #Hw, %Hinf⟩
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z gb.clientProposals'.len := by
      have : 0 < pps.length := (List.getElem?_eq_some_iff.1 hpp).1
      have := Hppsl.1; have := Hppsl.2; constructor <;> word
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index (t := go.GoType.PointerType src.genericsmr.Propose.ty)
      gb.clientProposals' _ pps _ pp h0.1 $$ [$Hpps] as -
    · ipureintro; exact hpp
    ihave #Hgp1 := Hgp
    iStructNamed Hgp1
    wp_apply (IntoValTyped.wp_load (t := go.GoType.PointerType src.genericsmrproto.Propose.ty) _ _ _)
      $$ [$Propose] as -
    ihave #Hin1 := Hinner
    iStructNamed Hin1
    wp_apply (IntoValTyped.wp_load (t := go.int32) _ _ _) $$ [$CommandId] as -
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index (t := go.GoType.PointerType src.genericsmr.Propose.ty)
      gb.clientProposals' _ pps _ pp h0.1 $$ [$Hpps] as -
    · ipureintro; exact hpp
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index (t := go.GoType.PointerType src.genericsmr.Propose.ty)
      gb.clientProposals' _ pps _ pp h0.1 $$ [$Hpps] as -
    · ipureintro; exact hpp
    iStructNamed Command
    wp_apply (IntoValTyped.wp_load (t := src.state.Value.ty) _ _ _) $$ [$OldValue] as -
    ihave Hpend : pendingOuts γ ρ k r t (.ext (.rmwReply pr'.client inner.CommandId' (W8 1)) :: [])
      $$ [Hpend]
    · rw [Hinf.1, show (W8 1 : w8) = 1 from rfl]; iexact Hpend
    wp_apply (completeRMWWriter.wp γ ρ k r gR h t pr'.client inner.CommandId' gp.Reply'
      inner.Command'.OldValue' []) $$ [$Hgen $HgR $Hw $Hpend] as Hpend
    let gb2 : src.gryff.LeaderBookkeeping := { gb with numReplicasExecuted' := gb.numReplicasExecuted' + W32 1, repliedClient' := true }
    ihave Hgb : iv.lb' ↦ gb2 $$ [clientProposals maxRecvBallot
        prepareOKs allEqual preAcceptOKs acceptOKs nacks originalDeps committedDeps recoveryInst
        preparing tryingToPreAccept possibleQuorum tpaOKs committedTime executedTime blockStartTime
        depReadTime numReplicasExecuted repliedClient]
    · iapply typedPointsto_combine _ _ _ Hlbnn
      simp only [typedPointstoDef, gb2, f9]
      iframe
    ihave Hlbn : lbRep ρ iv.lb' (some { exLB lb with repliedClient := true }) $$ [Hgb Hcd Hri]
    · iapply (lbRep_some ..).2
      iexists gb2
      iframe Hgb
      simp only [gb2, exLB]
      iframe Hcd Hri
      unfold proposalsRep
      isplitl
      · iexists pps; iframe #; ipureintro; exact ⟨Hppl, Hpnil⟩
      · ipureintro
        simp [f1, f2, f3, f4, f5, f6, f7, f8, f9]
    ihave Hc := (copyRep_open ρ xs _ ip { c with lb := some { exLB lb with repliedClient := true } }).2
      $$ [Hiv Hlbn]
    · iexists iv; iframe # ∗; ipureintro; exact Hivf
    icases Hclose with ⟨-, -, -, Ha⟩
    ihave Hep := Ha $$ %({ c with lb := some { exLB lb with repliedClient := true } }) [] Hrow Hc
    · ipureintro; exact ⟨rfl, committedOrExecuted_setInst_status' s _ _ c _ hbox2 hsi rfl⟩
    obtain ⟨ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho8, ho9, -⟩ :=
      sameOut_setInst s g.Replica' g.Instance' { c with lb := some { exLB lb with repliedClient := true } }
    rw [hss]
    iapply HΦ
    iframe Hpend
    iapply handler_close γ ρ k r gR h pa co xs _
    isplitr
    · unfold epEnv; iframe #
    unfold parts
    rw [ho2, ho3, ho4, ho9]
    iframe Hparti Hval Hxs Hprop Hscr Hep
    isplitl
    · iapply coordOwn_congr ρ co _ k s _ ho5 ho6 ho7 ho8 $$ Hcoord
    · ipureintro; rw [ho1]; exact Hid
  · -- no reply
    have e2 : (W32 (sint.Z (BitVec.sdiv (W64 3) (W64 2) + W64 1)) : w32) = 2 := by decide
    rw [f10]
    cases hrc : lb.repliedClient
    have hge : decide (sint.Z (2 : w32) ≤ sint.Z (lb.numReplicasExecuted + W32 1)) = false := by
      simp only [exReply, hrc, Bool.not_false, Bool.true_and, model.sge, model.sle] at hrep
      exact hrep
    simp only [Bool.not_false]
    wp_auto
    rw [e2, f9, hge]
    wp_auto
    rotate_left
    simp only [Bool.not_true]
    wp_auto
    all_goals
      let gb2 : src.gryff.LeaderBookkeeping := { gb with numReplicasExecuted' := gb.numReplicasExecuted' + W32 1 }
      ihave Hgb : iv.lb' ↦ gb2 $$ [clientProposals maxRecvBallot
          prepareOKs allEqual preAcceptOKs acceptOKs nacks originalDeps committedDeps recoveryInst
          preparing tryingToPreAccept possibleQuorum tpaOKs committedTime executedTime blockStartTime
          depReadTime numReplicasExecuted repliedClient]
      · iapply typedPointsto_combine _ _ _ Hlbnn
        simp only [typedPointstoDef, gb2, f9, f10, hrc]
        iframe
      ihave Hlbn : lbRep ρ iv.lb' (some (exLB lb)) $$ [Hgb Hprs Hcd Hri]
      · iapply (lbRep_some ..).2
        iexists gb2
        iframe Hgb
        simp only [gb2, exLB]
        iframe Hprs Hcd Hri
        ipureintro
        simp [f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
      ihave Hc := (copyRep_open ρ xs _ ip { c with lb := some (exLB lb) }).2 $$ [Hiv Hlbn]
      · iexists iv; iframe # ∗; ipureintro; exact Hivf
      icases Hclose with ⟨-, -, -, Ha⟩
      ihave Hep := Ha $$ %({ c with lb := some (exLB lb) }) [] Hrow Hc
      · ipureintro; exact ⟨rfl, committedOrExecuted_setInst_status' s _ _ c _ hbox2 hsi rfl⟩
      obtain ⟨ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho8, ho9, -⟩ :=
        sameOut_setInst s g.Replica' g.Instance' { c with lb := some (exLB lb) }
      rw [hss]
      iapply HΦ
      iframe Hpend
      iapply handler_close γ ρ k r gR h pa co xs _
      isplitr
      · unfold epEnv; iframe #
      unfold parts
      rw [ho2, ho3, ho4, ho9]
      iframe Hparti Hval Hxs Hprop Hscr Hep
      isplitl
      · iapply coordOwn_congr ρ co _ k s _ ho5 ho6 ho7 ho8 $$ Hcoord
      · ipureintro; rw [ho1]; exact Hid

/-- **`handleExecuted.wp`** (`Replica2/Specs.lean`), at its frozen statement. -/
theorem handleExecuted_spec (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc)
    (m : model.ExecutedM) : epHandlerSpec γ ρ k r h go!"handleExecuted" (.executed m) := by
  intro p t s s' outs hstep
  iintro %Φ ⟨#Hpkg, #Hrep, Hown, Hpend, Hh, Hmsg⟩ HΦ
  icases (msgAt_executed ..).1 $$ Hmsg with ⟨%g, Hp, %Hg⟩
  iapply (handleExecuted_wp' γ ρ k r h p m t s s' outs hstep g Hg) $$ [Hown Hpend Hh Hp] HΦ
  iframe # ∗

end

end Perennial.gryff.replica2
