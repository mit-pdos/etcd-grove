/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2c/AcceptReply.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2c: `handleAcceptReply` (G18: once accepted, a reply at the ballot counts once; the slow
path's commit)
-/
module

public import Dsverify.Proof.gryff.H2.Env
public import Dsverify.Proof.gryff.H2c.SlotOpen
public import Dsverify.Proof.gryff.H2c.LeaderModel
public import Dsverify.Proof.gryff.H2c.Base
public import Dsverify.Proof.gryff.H2c.Propose
public import Dsverify.Proof.gryff.H2c2.Base
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB Proposal Msg Ev Out Cmd Deps)
open Perennial.gryff.replica (XS rowOwn nSlots)

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- A copy replaced by one of the same status keeps its committedness. -/
theorem committedOrExecuted_setInst_status (s : RState) (q i : w32) (c c' : Copy)
    (hb : model.inBox q i = true) (h : s.inst q i = some c) (hst : c'.status = c.status) :
    committedOrExecuted (s.setInst q i c') (sint.Z q, sint.Z i) =
      committedOrExecuted s (sint.Z q, sint.Z i) := by
  have hb' := of_decide_eq_true hb
  unfold committedOrExecuted model.committedCopy
  simp only [BitVec.ofInt_toInt, model.RState.setInst, and_self, ↓reduceIte, h, hst]
  by_cases hc : c.status = model.St.COMMITTED ∨ c.status = model.St.EXECUTED <;> simp [hc, hb']

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF] -- H1-R6 / N-1
variable [strconvA : strconv.Assumptions] -- N-5


set_option goose.wp.extras true

theorem msgAt_acceptReply' (p : Loc) (mm : model.AcceptReplyM) :
    msgAt (GF := GF) p (.acceptReply mm) ⊣⊢ ∃ g : src.epaxosproto.AcceptReply, p ↦ g ∗ ⌜acceptReplyOf g = mm⌝ := by
  unfold msgAt; exact .rfl

set_option maxHeartbeats 4000000 in
theorem handleAcceptReply_wp' (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h p : Loc)
    (m : model.AcceptReplyM) (t : List Ev) (s s' : RState) (outs : List Out)
    (hstep : model.stepR k s (.msg (.acceptReply m)) = .ok (s', outs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r ∗
        replicaOwn ρ k r s ∗ pendingOuts γ ρ k r t outs ∗ handlerOf r h ∗
        msgAt p (.acceptReply m) }}
      (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!!
        go!"handleAcceptReply")) (Val #p))
    {{ RET #(); replicaOwn ρ k r s' ∗ pendingOuts γ ρ k r t [] }} := by
  wp_start as ⟨Hrep, Hown, Hpend, Hh, Hmsg⟩
  icases handler_open γ ρ k r h s $$ [$Hrep $Hh $Hown] with ⟨%gR, %pa, %co, %xs, #Henv, Hparts⟩
  icases (msgAt_acceptReply' ..).1 $$ Hmsg with ⟨%g, Hp, %Hg⟩
  unfold parts
  icases Hparts with ⟨Hparti, Hval, Hcoord, Hep, Hxs, Hprop, Hscr, %Hid⟩
  simp only [model.stepR] at hstep
  obtain ⟨hbox, c, hsi, hcases⟩ := stepAcceptReply_cases s s' outs m hstep
  clear hstep
  subst Hg
  have hbox' := hbox
  simp only [model.inBox, acceptReplyOf] at hbox'
  have hbox' := of_decide_eq_true hbox'
  obtain ⟨hq0, hq3, hi0, hiS⟩ := hbox'
  have hbox2 : model.inBox g.Replica' g.Instance' = true := hbox
  have hsi2 : s.inst g.Replica' g.Instance' = some c := hsi
  icases epaxosOwn_slot_open ρ h r xs s g.Replica' g.Instance' hbox2 $$ Hep with
    ⟨%ispS, %sq, %crtS, %isp, %ptrs, %ip, #HR, #HispS, #Hisp, %Hsl, Hrow, Hslot, %Hxsf, #HelS, #HcrtS,
      Hcrt, Hmono, Hrest, Hclose⟩
  ihave #Henv' := Henv
  unfold epEnv
  icases Henv' with ⟨#HgR, #Hpa, #Hco, #Hh, #HR', #HId, #HN, #HDur, #Hgen, #Hfix⟩
  ihave Hclose := Hclose $$ %s.crtInstance %Hsl.2.2 Hcrt [Hmono] Hrest
  · rw [withCrt_self]; iexact Hmono
  rw [withCrt_self]
  rw [hsi2]
  icases Hslot with ⟨%hipn, Hc⟩
  icases (copyRep_open ..).1 $$ Hc with ⟨%iv, Hiv, #Hcmds, Hlb, %Hivf⟩
  have hqw : sint.Z (W64 (sint.Z g.Replica')) = sint.Z g.Replica' := by word
  have hiw : sint.Z (W64 (sint.Z g.Instance')) = sint.Z g.Instance' := by
    unfold model.SLOTS at hiS; word
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
  simp only [src.epaxosproto.ACCEPTED, src.gryff.FALSE, src.gryff.TRUE, src.epaxosproto.COMMITTED]
  wp_if_destruct
  rotate_left
  · -- not accepted: a delayed reply
    obtain ⟨hss, rfl⟩ : s' = s ∧ outs = [] := by
      rcases hcases with ⟨-, h1, h2⟩ | ⟨hst, -⟩
      · exact ⟨h1, h2⟩
      · exact absurd (by rw [Hivf.2.1, hst]; rfl) Hif
    subst s'
    ihave Hc := (copyRep_open ρ xs _ ip c).2 $$ [Hiv Hlb]
    · iexists iv; iframe # ∗; ipureintro; exact Hivf
    icases Hclose with ⟨-, -, -, Ha⟩
    ihave Hep := Ha $$ %c [] Hrow Hc
    · ipureintro; refine ⟨rfl, ?_⟩; rw [setInst_self s _ _ c hsi2]
    rw [setInst_self s _ _ c hsi2]
    iapply HΦ
    iframe Hpend
    iapply handler_close γ ρ k r gR h pa co xs s
    isplitr
    · unfold epEnv; iframe #
    unfold parts
    iframe Hparti Hval Hxs Hprop Hscr Hep Hcoord
    ipureintro; exact Hid
  have hst3 := Hif
  wp_if_destruct
  rotate_left
  · -- another ballot
    obtain ⟨hss, rfl⟩ : s' = s ∧ outs = [] := by
      rcases hcases with ⟨-, h1, h2⟩ | ⟨-, hb, -⟩
      · exact ⟨h1, h2⟩
      · exact absurd (by rw [Hivf.1, hb]; rfl) Hif
    subst s'
    ihave Hc := (copyRep_open ρ xs _ ip c).2 $$ [Hiv Hlb]
    · iexists iv; iframe # ∗; ipureintro; exact Hivf
    icases Hclose with ⟨-, -, -, Ha⟩
    ihave Hep := Ha $$ %c [] Hrow Hc
    · ipureintro; refine ⟨rfl, ?_⟩; rw [setInst_self s _ _ c hsi2]
    rw [setInst_self s _ _ c hsi2]
    iapply HΦ
    iframe Hpend
    iapply handler_close γ ρ k r gR h pa co xs s
    isplitr
    · unfold epEnv; iframe #
    unfold parts
    iframe Hparti Hval Hxs Hprop Hscr Hep Hcoord
    ipureintro; exact Hid
  have hst : c.status = model.St.ACCEPTED := by rw [← Hivf.2.1, hst3]; rfl
  have hbl : c.ballot = g.Ballot' := by rw [← Hivf.1]; simpa using Hif
  rcases hcases with ⟨hn, -⟩ | ⟨-, -, lb, hlb, hcases⟩
  · exfalso; rcases hn with h1 | h1
    · exact h1 hst
    · exact h1 hbl
  rw [hlb]
  icases (lbRep_some ..).1 $$ Hlb with ⟨%gb, Hgb, Hprs, Hcd, Hri, %Hgbf⟩
  wp_if_destruct
  · -- a refusal: the bookkeeping counts it
    obtain ⟨hok, rfl, rfl⟩ : g.OK' = model.FALSE ∧ outs = [] ∧
        s' = s.setInst g.Replica' g.Instance' { c with lb := some (arNack lb g.Ballot') } := by
      rcases hcases with h1 | ⟨hn, -⟩ | ⟨hn, -⟩
      · exact h1
      · exact absurd Hif hn
      · exact absurd Hif hn
    repeat' (first | wp_if_destruct | wp_auto)
    all_goals
      ihave Hlbn : lbRep ρ iv.lb' (some (arNack lb g.Ballot')) $$ [Hgb Hprs Hcd Hri]
      · iapply (lbRep_some ..).2
        iexists _
        iframe Hgb
        dsimp only [arNack]
        iframe Hprs Hcd Hri
        ipureintro
        obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := Hgbf
        simp only [arNack, model.sgt, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
        refine ⟨?_, trivial, trivial, trivial, trivial, rfl, trivial, trivial, trivial, trivial⟩
        by_cases hlt : model.slt lb.maxRecvBallot g.Ballot' = true <;>
          simp only [hlt, ↓reduceIte, Bool.false_eq_true] <;> simp_all [model.slt] <;> omega
    all_goals
      ihave Hc := (copyRep_open ρ xs _ ip { c with lb := some (arNack lb g.Ballot') }).2 $$ [Hiv Hlbn]
      · iexists iv; iframe # ∗; ipureintro; exact Hivf
      icases Hclose with ⟨-, -, -, Ha⟩
      ihave Hep := Ha $$ %({ c with lb := some (arNack lb g.Ballot') }) [] Hrow Hc
      · ipureintro; exact ⟨rfl, committedOrExecuted_setInst_status s _ _ c _ hbox2 hsi2 rfl⟩
      obtain ⟨ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho8, ho9, -⟩ :=
        sameOut_setInst s g.Replica' g.Instance' { c with lb := some (arNack lb g.Ballot') }
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
  have hok : g.OK' ≠ model.FALSE := Hif
  wp_if_destruct
  · -- a majority: the commit (the slow path)
    obtain ⟨hc2, hlc⟩ : model.sgt (lb.acceptOKs + 1 + 1) model.NHALF = true ∧
        model.leaderCommit s g.Replica' g.Instance' c { lb with acceptOKs := lb.acceptOKs + 1 } =
          .ok (s', outs) := by
      rcases hcases with ⟨hn, -⟩ | ⟨-, hn, -⟩ | ⟨-, h1, h2⟩
      · exact absurd hn hok
      · exfalso
        simp only [model.sgt, model.slt, model.NHALF] at hn
        rw [← Hgbf.2.2.2.2.1] at hn
        have h3 : sint.Z (BitVec.sdiv (W64 3) (W64 2)) = sint.Z (1 : w64) := by decide
        have e1 : (W64 1 : w64) = 1 := rfl
        rw [h3, e1] at Hif
        exact of_decide_eq_false hn Hif
      · exact ⟨h1, h2⟩
    generalize hlb1 : ({ lb with acceptOKs := lb.acceptOKs + 1 } : LB) = lb1 at hlc
    obtain ⟨s2, hs2, hs', hbc⟩ := leaderCommit_cases s s' outs _ _ c lb1 hlc
    clear hlc hcases
    wp_apply time.wp_Now as %tn _
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 (sint.Z g.Replica')) ∧
        sint.Z (W64 (sint.Z g.Replica')) < sint.Z ispS.len by
      have h1 := HispSlen.1; have h2 := HispSlen.2; rw [hqw]; rw [h1] at hqlt; word)]
    wp_apply wp_load_slice_index (t := go.GoType.SliceType (go.GoType.PointerType src.gryff.Instance.ty))
      ispS _ isp _ sq (by rw [hqw]; omega) $$ [$Hisp] as -
    · ipureintro; rw [hqw]; exact hsq
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 (sint.Z g.Instance')) ∧
        sint.Z (W64 (sint.Z g.Instance')) < sint.Z sq.len by
      have h1 := Hrowlen.1; have h2 := Hrowlen.2; rw [hiw]; rw [h1] at hilt; word)]
    wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty)
      sq _ ptrs _ ip (by rw [hiw]; omega) $$ [$Hrow] as Hrow
    · ipureintro; rw [hiw]; exact hip
    dsimp only
    -- the copy committed: the slot closed (a)
    ihave Hlb1 : lbRep ρ iv.lb' (some lb1) $$ [Hgb Hprs Hcd Hri]
    · iapply (lbRep_some ..).2
      iexists _
      iframe Hgb
      subst hlb1
      dsimp only
      iframe Hprs Hcd Hri
      ipureintro
      obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := Hgbf
      simp only [f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
      exact ⟨trivial, trivial, trivial, trivial, rfl, trivial, trivial, trivial, trivial, trivial⟩
    ihave Hc1 : copyRep ρ xs (sint.Z g.Replica', sint.Z g.Instance') ip (lcC1 c lb1) $$ [Hiv Hlb1]
    · iapply (copyRep_open ..).2
      iexists _
      iframe Hiv
      dsimp only [lcC1]
      iframe Hcmds Hlb1
      ipureintro
      obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13⟩ := Hivf
      refine ⟨f1, rfl, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, ?_⟩
      rw [← f13, hst]
      simp only [model.St.COMMITTED, model.St.EXECUTED, model.St.ACCEPTED]
      decide
    icases Hclose with ⟨Ha, -⟩
    ihave Hep := Ha $$ %(lcC1 c lb1) [] Hrow Hc1
    · ipureintro
      refine ⟨rfl, fun _ => ?_⟩
      rw [committedOrExecuted_setInst_self s _ _ _ hbox2]
      simp [lcC1]
    imod Hep with ⟨Hep, #HelC⟩
    ihave #Hae : attrEnv k r gR h $$ []
    · unfold attrEnv; iframe #
    wp_apply (wp_updateCommitted ρ k r gR h xs _ s2 g.Replica' ⟨hq0, hq3⟩ hs2) $$ [$Hae $Hep]
      as Hep
    -- the slot reopened at `s2` (same pointer: `elemIf`)
    have hsi3 : s2.inst g.Replica' g.Instance' = some (lcC1 c lb1) := by
      rw [updateCommitted_inst hs2]; simp [model.RState.setInst]
    icases epaxosOwn_slot_open ρ h r xs s2 g.Replica' g.Instance' hbox2 $$ Hep with
      ⟨%ispS2, %sq2, %crtS2, %isp2, %ptrs2, %ip2, -, #HispS2, #Hisp2, %Hsl2, Hrow2, Hslot2, -,
        #HelS2, -, Hcrt2, Hmono2, Hrest2, Hclose2⟩
    icombine HispS HispS2 gives %Hspe
    subst Hspe
    icombine Hisp Hisp2 gives %Hie
    subst Hie
    obtain ⟨hsq2, hip2, hcrtlen2⟩ := Hsl2
    rw [hsq] at hsq2
    cases hsq2
    have hco1 : committedOrExecuted (s.setInst g.Replica' g.Instance' (lcC1 c lb1))
        (sint.Z g.Replica', sint.Z g.Instance') = true := by
      rw [committedOrExecuted_setInst_self s _ _ _ hbox2]; simp [lcC1]
    have hco2 : committedOrExecuted s2 (sint.Z g.Replica', sint.Z g.Instance') = true := by
      rw [← hco1]; unfold committedOrExecuted model.committedCopy; rw [updateCommitted_inst hs2]
    icases elemIf_agree ρ _ _ _ ip ip2 hco1 hco2 $$ [$HelC $HelS2] with %Hipe
    subst Hipe
    rw [hsi3]
    icases Hslot2 with ⟨-, Hc2⟩
    icases (copyRep_open ..).1 $$ Hc2 with ⟨%iv2, Hiv2, #Hcmds2, Hlb2, %Hivf2⟩
    dsimp only [lcC1] at Hivf2
    rw [show (lcC1 c lb1).lb = some lb1 from rfl, show (lcC1 c lb1).cmds = c.cmds from rfl]
    icases (lbRep_some ρ iv2.lb' lb1).1 $$ Hlb2 with ⟨%gb3, Hgb3, Hprs3, Hcd3, Hri3, %Hgbf3⟩
    unfold proposalsRep
    icases Hprs3 with ⟨%pps, #Hpps, %Hppl, %Hpnil, #Hels⟩
    ihave %Hppsl := ownSlice_len _ _ _ $$ Hpps
    icases (cmdsRep_open ..).1 $$ Hcmds2 with ⟨%gs, #Hgs, %Hgsf⟩
    ihave %Hgsl := ownSlice_len _ _ _ $$ Hgs
    wp_auto
    wp_join iprop(∃ iv' : src.gryff.Instance, ip ↦ iv' ∗ ⌜iv' = { iv2 with lb' := iv'.lb' }⌝ ∗
        lbRep ρ iv'.lb' (lcC3 c lb1).lb ∗ proposeOwn ρ gR (lcPQ s c lb1) ∗
        inst_ptr ↦ ip ∗ e_ptr ↦ h ∗ areply_ptr ↦ p ∗ writeKey0_ptr ↦ false ∗
        readKey0_ptr ↦ false) at next
      with [Hiv2 Hgb3 Hcd3 Hri3 Hprop inst e areply writeKey0 readKey0] as
        ⟨%iv', Hiv, %Hiv', Hlb, Hprop, inst, e, areply, writeKey0, readKey0⟩
    · -- G11's re-proposal, or the "all clear" loop
      by_cases hn : gb3.clientProposals' = slice.nil
      · -- nil proposals: neither
        have hprs0 : lb1.clientProposals = [] := by
          have : pps.length = 0 := by rw [Hppsl.1, hn]; rfl
          rw [← List.length_eq_zero_iff, ← Hppl, this]
        have hre : ¬ lcRe c lb1 := fun h => h.1 hprs0
        rw [show decide (gb3.clientProposals' = slice.nil) = true from decide_eq_true hn]
        simp only [Bool.not_true]
        wp_auto
        rw [show decide (gb3.clientProposals' = slice.nil) = true from decide_eq_true hn]
        simp only [Bool.not_true]
        wp_auto
        wp_join_done
        iexists iv2
        simp only [lcC3, lcPQ, hre, ↓reduceIte, lcC1]
        iframe
        iapply (lbRep_some ..).2
        iexists gb3
        iframe Hgb3 Hcd3 Hri3
        unfold proposalsRep
        isplitl
        · iexists pps; iframe # ∗; ipureintro; exact ⟨Hppl, Hpnil⟩
        · ipureintro; exact Hgbf3
      have hprs1 : lb1.clientProposals ≠ [] := fun h => hn (Hpnil h)
      simp only [hn, decide_false, Bool.not_false]
      wp_auto
      have hgsl : gs.length = c.cmds.length := by rw [← Hgsf.1, List.length_map]
      wp_if_destruct
      · -- G11: the committed value is not the clients': they are proposed again
        have hre : lcRe c lb1 := by
          refine ⟨hprs1, ?_⟩
          rw [← hgsl, ← Hppl, Hgsl.1, Hppsl.1]; word
        icases proposeOwn_chan ρ gR _ $$ Hprop with ⟨Hprop, %ch, #Hch⟩
        ihave HL : (∃ (j : w64), "i" ∷ i_ptr ↦ j ∗ "p" ∷ (∃ v : Loc, p_ptr ↦ v) ∗
            "Hprop" ∷ proposeOwn ρ gR (s.proposeQ ++ lb1.clientProposals.take (sint.nat j)) ∗
            "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ pps.length⌝ : IProp GF) $$ [i p Hprop]
        · iexists W64 0
          simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.append_nil]
          iframe
          isplitl
          · iexists _; iexact p
          · ipureintro; simp
        wp_for HL
        obtain ⟨hj0, hjl⟩ := Hj
        have hlen : sint.nat gb3.clientProposals'.len = pps.length := Hppsl.1.symm
        wp_if_destruct
        · -- an iteration
          have hjlt : sint.nat j < pps.length := by
            rw [← hlen]; word
          obtain ⟨pp, hpp⟩ : ∃ pp, pps[sint.nat j]? = some pp :=
            ⟨_, List.getElem?_eq_getElem hjlt⟩
          rw [ite_eq_left (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z gb3.clientProposals'.len by omega)]
          wp_apply wp_load_slice_index (t := go.GoType.PointerType src.genericsmr.Propose.ty)
            gb3.clientProposals' _ pps _ pp hj0 $$ [$Hpps] as -
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
          have hcpl : sint.nat j < lb1.clientProposals.length := by rw [← Hppl]; exact hjlt
          have htake : lb1.clientProposals.take (sint.nat (j + W64 1)) =
              lb1.clientProposals.take (sint.nat j) ++ [pr] := by
            have : sint.nat (j + W64 1) = sint.nat j + 1 := by word
            rw [this, List.take_add_one, Hpr]; rfl
          rw [htake, ← List.append_assoc]
          iframe
          isplitl
          · iexists _; iexact p
          · ipureintro
            refine ⟨by omega, ?_⟩
            word
        · -- done: all proposals sent, `lb = nil`
          have hjeq : sint.nat j = lb1.clientProposals.length := by
            rw [← Hppl, ← hlen]; rw [← hlen] at hjl; word
          rw [hjeq, List.take_length]
          wp_join_done
          iexists { iv2 with lb' := Loc.null }
          simp only [lcC3, lcPQ, hre, ↓reduceIte, lcC1]
          iframe
          iapply (lbRep_none ..).2; ipureintro; rfl
      · -- the "all clear" loop: every command is a CAS, no client is answered
        have hre : ¬ lcRe c lb1 := by
          rintro ⟨-, h2⟩
          apply Hif
          rw [← hgsl, ← Hppl, Hgsl.1, Hppsl.1] at h2; word
        have hle : pps.length ≤ gs.length := by
          rw [hgsl, Hppl]; exact Nat.le_of_not_lt fun h => hre ⟨hprs1, h⟩
        rw [show decide (gb3.clientProposals' = slice.nil) = false from decide_eq_false hn]
        simp only [Bool.not_false]
        wp_auto
        ihave HL : (∃ (j : w64), "i" ∷ i_ptr ↦ j ∗
            "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ pps.length⌝ : IProp GF) $$ [i]
        · iexists W64 0; iframe; ipureintro; simp
        wp_for HL
        obtain ⟨hj0, hjl⟩ := Hj
        have hlen : sint.nat gb3.clientProposals'.len = pps.length := Hppsl.1.symm
        wp_if_destruct
        · -- an iteration
          have hjlt : sint.nat j < pps.length := by
            rw [← hlen]; word
          obtain ⟨cm, hcm⟩ : ∃ cm, gs[(sint.Z j).toNat]? = some cm :=
            ⟨_, List.getElem?_eq_getElem (by have : (sint.Z j).toNat = sint.nat j := rfl; omega)⟩
          have hcok := cmdsOk_get gs _ cm (by rw [Hgsf.1]; exact Hgsf.2) hcm
          have hjb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z iv2.Cmds'.len := by
            refine ⟨hj0, ?_⟩
            have := Hgsl.1; word
          icases ownSlice_elem_acc (sint.Z j) cm iv2.Cmds' DFrac.discard gs hj0 hcm $$ Hgs with
            ⟨#Hc0, -⟩
          ihave #Hc1 := Hc0
          iStructNamed Hc1
          rw [ite_eq_left hjb]
          wp_apply (IntoValTyped.wp_load (t := src.state.Key.ty) _ _ _) $$ [$K] as -
          rw [hcok.1]
          simp only [decide_true, src.state.PUT, src.state.GET]
          wp_auto
          rw [ite_eq_left hjb]
          wp_apply (IntoValTyped.wp_load (t := src.state.Operation.ty) _ _ _) $$ [$Op] as -
          rw [hcok.2]
          wp_auto
          rw [ite_eq_left hjb]
          wp_apply (IntoValTyped.wp_load (t := src.state.Operation.ty) _ _ _) $$ [$Op] as -
          rw [ite_eq_left hjb]
          wp_auto
          ihave #HDr := h2Fixed_dreply k gR h $$ Hfix
          wp_apply (wp_NeedsWait r gR _ cm hcok.2) $$ [$HgR $HDr $Hc0]
          wp_for_post
          iframe
          iexists j + W64 1
          iframe
          ipureintro
          rw [← hlen] at hjlt
          constructor <;> word
        · -- done
          wp_join_done
          iexists iv2
          simp only [lcC3, lcPQ, hre, ↓reduceIte, lcC1]
          iframe
          iapply (lbRep_some ..).2
          iexists gb3
          iframe Hgb3 Hcd3 Hri3
          unfold proposalsRep
          isplitl
          · iexists pps; iframe # ∗; ipureintro; exact ⟨Hppl, Hpnil⟩
          · ipureintro; exact Hgbf3
    -- the tail: records, stats, the commit's broadcast
    wp_apply (wp_recordInstanceMetadata h r gR) $$ [$HR' $HgR $HDur]
    wp_apply (wp_sync h r gR) $$ [$HR' $HgR $HDur]
    icases h2Fixed_stats k gR h $$ Hfix with ⟨%st, #HSt, #Hstats⟩
    wp_auto
    wp_apply StatsMap.Increment.wp' $$ [Hstats] as %_ -
    · stats_key
    · iframe Hstats
    h2c_printf
    -- the slot closed (a0) at the final copy, `epaxosRest` out for the broadcast
    ihave Hclose2 := Hclose2 $$ %s2.crtInstance %hcrtlen2 Hcrt2 [Hmono2] Hrest2
    · rw [withCrt_self]; iexact Hmono2
    rw [withCrt_self]
    icases Hclose2 with ⟨-, -, -, Ha0⟩
    ihave Hc3 : copyRep ρ xs (sint.Z g.Replica', sint.Z g.Instance') ip (lcC3 c lb1) $$ [Hiv Hlb]
    · iapply (copyRep_open ..).2
      iexists _
      iframe Hiv Hlb
      rw [Hiv']
      dsimp only
      simp only [lcC3_cmds, lcC3_ballot, lcC3_status, lcC3_seq, lcC3_deps, lcC3_base, lcC3_slot,
        lcC3_leader, lcC3_vbal]
      isplitr
      · iapply (cmdsRep_open ..).2; iexists gs; iframe Hgs; ipureintro; exact Hgsf
      ipureintro
      exact Hivf2
    ihave Hep := Ha0 $$ %(lcC3 c lb1) [] Hrow2 Hc3
    · ipureintro
      refine ⟨rfl, ?_⟩
      rw [hco2, lcC3_committed s2 _ _ c lb1 hbox2]
    icases h2b.epaxosOwn_rest ρ h r xs _ $$ Hep with ⟨Hrest, Hback⟩
    have hS3 := lcS3_eq s s2 _ _ c lb1 hs2
    obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9⟩ := lcS3_sameOut s s2 _ _ c lb1 hs2
    rw [← hs'] at o1 o2 o3 o4 o5 o6 o7 o8 o9
    have hid' : s'.id = rid32 k := by rw [o1]; exact Hid
    have hbc' : model.bcastCommit s' g.Replica' g.Instance' (gs.map cmdOf) iv'.Seq'
        (depsOf iv'.Deps') (vtOf iv'.Base') = some outs := by
      rw [Hiv']; dsimp only
      obtain ⟨f1, f2, f3, f4, f5, -⟩ := Hivf2
      rw [Hgsf.1, f3, f4, f5]; exact hbc
    ihave #HE : epEnv γ ρ k r gR h pa co $$ []
    · unfold epEnv; iframe #
    ihave Hpend : pendingOuts γ ρ k r t (outs ++ []) $$ [Hpend]
    · rw [List.append_nil]; iexact Hpend
    have hcmd' : iv'.Cmds' = iv2.Cmds' := by rw [Hiv']
    rw [hcmd']
    wp_apply (wp_bcastCommit γ ρ k r gR h pa co t s' hid' _ _ iv2.Cmds' gs _ _ _ outs [] hbc'
      (by rw [Hgsf.1]; exact Hgsf.2)) $$ [$HE $Hrest $Hgs $Hpend] as ⟨Hrest, Hpend⟩
    ihave Hep := Hback $$ Hrest
    ihave Hep := epaxosOwn_proposeQ ρ h r xs _ (lcPQ s c lb1) $$ Hep
    rw [← hS3, ← hs']
    iapply HΦ
    iframe Hpend
    iapply handler_close γ ρ k r gR h pa co xs s'
    isplitr
    · iexact HE
    unfold parts
    rw [o2, o3, o4, o9]
    iframe Hparti Hval Hxs Hprop Hscr Hep
    isplitl
    · iapply coordOwn_congr ρ co _ k s s' o5 o6 o7 o8 $$ Hcoord
    · ipureintro; exact hid'
  · -- no majority yet
    obtain ⟨rfl, rfl⟩ : outs = [] ∧ s' = s.setInst g.Replica' g.Instance'
        { c with lb := some { lb with acceptOKs := lb.acceptOKs + 1 } } := by
      rcases hcases with ⟨hn, -⟩ | ⟨-, -, h1, h2⟩ | ⟨-, hn, -⟩
      · exact absurd hn hok
      · exact ⟨h1, h2⟩
      · exfalso
        simp only [model.sgt, model.slt, model.NHALF] at hn
        rw [← Hgbf.2.2.2.2.1] at hn
        have h3 : sint.Z (BitVec.sdiv (W64 3) (W64 2)) = sint.Z (1 : w64) := by decide
        have e1 : (W64 1 : w64) = 1 := rfl
        rw [h3, e1] at Hif
        exact Hif (of_decide_eq_true hn)
    ihave Hlbn : lbRep ρ iv.lb' (some { lb with acceptOKs := lb.acceptOKs + 1 }) $$ [Hgb Hprs Hcd Hri]
    · iapply (lbRep_some ..).2
      iexists _
      iframe Hgb
      dsimp only
      iframe Hprs Hcd Hri
      ipureintro
      obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := Hgbf
      simp only [f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
      exact ⟨trivial, trivial, trivial, trivial, rfl, trivial, trivial, trivial, trivial, trivial⟩
    ihave Hc := (copyRep_open ρ xs _ ip { c with lb := some { lb with acceptOKs := lb.acceptOKs + 1 } }).2 $$ [Hiv Hlbn]
    · iexists iv; iframe # ∗; ipureintro; exact Hivf
    icases Hclose with ⟨-, -, -, Ha⟩
    ihave Hep := Ha $$ %({ c with lb := some { lb with acceptOKs := lb.acceptOKs + 1 } }) [] Hrow Hc
    · ipureintro; exact ⟨rfl, committedOrExecuted_setInst_status s _ _ c _ hbox2 hsi2 rfl⟩
    obtain ⟨ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho8, ho9, -⟩ :=
      sameOut_setInst s g.Replica' g.Instance' { c with lb := some { lb with acceptOKs := lb.acceptOKs + 1 } }
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

/-- **`handleAcceptReply.wp`** (`Replica2/Specs.lean`), at its frozen statement. -/
theorem handleAcceptReply_spec (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc)
    (m : model.AcceptReplyM) : epHandlerSpec γ ρ k r h go!"handleAcceptReply" (.acceptReply m) := by
  intro p t s s' outs hstep
  iintro %Φ ⟨#Hpkg, #Hrep, Hown, Hpend, Hh, Hmsg⟩ HΦ
  iapply (handleAcceptReply_wp' γ ρ k r h p m t s s' outs hstep) $$ [Hown Hpend Hh Hmsg] HΦ
  iframe # ∗

end

end Perennial.gryff.replica2
