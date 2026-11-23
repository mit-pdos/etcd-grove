/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2c2/PreAcceptReply.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2c2: `handlePreAcceptReply` (G18: only while pre-accepted; attributes merged; the fast
path's commit, the slow path's start)
-/
module

public import Dsverify.Proof.gryff.H2.Env
public import Dsverify.Proof.gryff.H2c.SlotOpen
public import Dsverify.Proof.gryff.H2c.Propose
public import Dsverify.Proof.gryff.H2c2.Base
public import Dsverify.Proof.gryff.H2c2.PARModel
public import Dsverify.Proof.gryff.H2a.Merge
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

theorem msgAt_preAcceptReply (p : Loc) (mm : model.PreAcceptReplyM) :
    msgAt (GF := GF) p (.preAcceptReply mm) ⊣⊢ ∃ g : src.gryffproto.PreAcceptReply, p ↦ g ∗
      ⌜preAcceptReplyOf g = mm⌝ := by
  unfold msgAt; exact .rfl

variable [pD : GryffPartiDeps (GF := GF)] in
set_option maxHeartbeats 8000000 in
/-- `handlePreAcceptReply(pareply)` with the step's obligations. -/
theorem handlePreAcceptReply_wp' (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h p : Loc)
    (m : model.PreAcceptReplyM) (t : List Ev) (s s' : RState) (outs : List Out)
    (hstep : model.stepR k s (.msg (.preAcceptReply m)) = .ok (s', outs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r ∗
        replicaOwn ρ k r s ∗ pendingOuts γ ρ k r t outs ∗ handlerOf r h ∗
        msgAt p (.preAcceptReply m) }}
      (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!!
        go!"handlePreAcceptReply")) (Val #p))
    {{ RET #(); replicaOwn ρ k r s' ∗ pendingOuts γ ρ k r t [] }} := by
  wp_start as ⟨Hrep, Hown, Hpend, Hh, Hmsg⟩
  icases handler_open γ ρ k r h s $$ [$Hrep $Hh $Hown] with ⟨%gR, %pa, %co, %xs, #Henv, Hparts⟩
  icases (msgAt_preAcceptReply ..).1 $$ Hmsg with ⟨%g, Hp, %Hg⟩
  unfold parts
  icases Hparts with ⟨Hparti, Hval, Hcoord, Hep, Hxs, Hprop, Hscr, %Hid⟩
  simp only [model.stepR] at hstep
  obtain ⟨hbox, c, hsi, hcases⟩ := stepPreAcceptReply_cases s s' outs m hstep
  clear hstep
  subst Hg
  simp only [preAcceptReplyOf] at hbox hsi hcases
  have hbox' := hbox
  simp only [model.inBox] at hbox'
  have hbox' := of_decide_eq_true hbox'
  obtain ⟨hq0, hq3, hi0, hiS⟩ := hbox'
  icases epaxosOwn_slot_open ρ h r xs s g.Replica' g.Instance' hbox $$ Hep with
    ⟨%ispS, %sq, %crtS, %isp, %ptrs, %ip, #HR, #HispS, #Hisp, %Hsl, Hrow, Hslot, %Hxsf, #HelS, #HcrtS,
      Hcrt, Hmono, Hrest, Hclose⟩
  ihave #Henv' := Henv
  unfold epEnv
  icases Henv' with ⟨#HgR, #Hpa, #Hco, #Hh, #HR', #HId, #HN, #HDur, #Hgen, #Hfix⟩
  rw [hsi]
  icases Hslot with ⟨%hipn, Hc⟩
  icases (copyRep_open ..).1 $$ Hc with ⟨%iv, Hiv, #Hcmds, Hlb, %Hivf⟩
  have hqw : sint.Z (W64 (sint.Z g.Replica')) = sint.Z g.Replica' := by word
  have hiw : sint.Z (W64 (sint.Z g.Instance')) = sint.Z g.Instance' := by
    unfold model.SLOTS at hiS; word
  ihave %HispSlen := ownSlice_len _ _ _ $$ Hisp
  obtain ⟨hsq, hip, hcrtlen⟩ := Hsl
  have hqlt := (List.getElem?_eq_some_iff.1 hsq).1
  ihave %Hrowlen := ownSlice_len _ _ _ $$ Hrow
  have hilt := (List.getElem?_eq_some_iff.1 hip).1
  have hqb : 0 ≤ sint.Z (W64 (sint.Z g.Replica')) ∧ sint.Z (W64 (sint.Z g.Replica')) < sint.Z ispS.len := by
    have h1 := HispSlen.1; have h2 := HispSlen.2; rw [hqw]; rw [h1] at hqlt; word
  have hib : 0 ≤ sint.Z (W64 (sint.Z g.Instance')) ∧ sint.Z (W64 (sint.Z g.Instance')) < sint.Z sq.len := by
    have h1 := Hrowlen.1; have h2 := Hrowlen.2; rw [hiw]; rw [h1] at hilt; word
  wp_auto
  h2c_printf
  rw [ite_eq_left hqb]
  wp_apply wp_load_slice_index (t := go.GoType.SliceType (go.GoType.PointerType src.gryff.Instance.ty))
    ispS _ isp _ sq (by rw [hqw]; omega) $$ [$Hisp] as -
  · ipureintro; rw [hqw]; exact hsq
  rw [ite_eq_left hib]
  wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty)
    sq _ ptrs _ ip (by rw [hiw]; omega) $$ [$Hrow] as Hrow
  · ipureintro; rw [hiw]; exact hip
  wp_if_destruct
  rotate_left
  · -- not pre-accepted: a delayed reply
    obtain ⟨hss, rfl⟩ : s' = s ∧ outs = [] := by
      rcases hcases with ⟨-, h1, h2⟩ | ⟨hst, -⟩
      · exact ⟨h1, h2⟩
      · exact absurd (by rw [Hivf.2.1, hst]; rfl) Hif
    rw [hss]
    ihave Hclose := Hclose $$ %s.crtInstance %hcrtlen Hcrt [Hmono] Hrest
    · rw [withCrt_self]; iexact Hmono
    rw [withCrt_self]
    ihave Hc := (copyRep_open ρ xs _ ip c).2 $$ [Hiv Hlb]
    · iexists iv; iframe # ∗; ipureintro; exact Hivf
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
  have hst3 := Hif
  wp_if_destruct
  rotate_left
  · -- another ballot
    obtain ⟨hss, rfl⟩ : s' = s ∧ outs = [] := by
      rcases hcases with ⟨-, h1, h2⟩ | ⟨-, hb, -⟩
      · exact ⟨h1, h2⟩
      · exact absurd (by rw [Hivf.1, hb]) Hif
    rw [hss]
    ihave Hclose := Hclose $$ %s.crtInstance %hcrtlen Hcrt [Hmono] Hrest
    · rw [withCrt_self]; iexact Hmono
    rw [withCrt_self]
    ihave Hc := (copyRep_open ρ xs _ ip c).2 $$ [Hiv Hlb]
    · iexists iv; iframe # ∗; ipureintro; exact Hivf
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
  have hst : c.status = model.St.PREACCEPTED := by rw [← Hivf.2.1, hst3]; rfl
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
      rcases hcases with h1 | ⟨hn, -⟩
      · exact h1
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
      ihave Hclose := Hclose $$ %s.crtInstance %hcrtlen Hcrt [Hmono] Hrest
      · rw [withCrt_self]; iexact Hmono
      rw [withCrt_self]
      ihave Hc := (copyRep_open ρ xs _ ip { c with lb := some (arNack lb g.Ballot') }).2 $$ [Hiv Hlbn]
      · iexists iv; iframe # ∗; ipureintro; exact Hivf
      icases Hclose with ⟨-, -, -, Ha⟩
      ihave Hep := Ha $$ %({ c with lb := some (arNack lb g.Ballot') }) [] Hrow Hc
      · ipureintro; exact ⟨rfl, committedOrExecuted_setInst_status' s _ _ c _ hbox hsi rfl⟩
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
  rcases hcases with ⟨hn, -⟩ | ⟨-, seq, deps, eq0, hm, hcases⟩
  · exact absurd hn hok
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := Hgbf
  h2c_printf
  ihave #Hae : attrEnv k r gR h $$ []
  · unfold attrEnv; iframe #
  wp_apply (wp_mergeAttributes k r gR h s Hid iv.Seq' iv.Deps' g.Seq' g.Deps') $$ [$Hae]
    as %seq' %d' %eq' %Hmg
  rw [Hivf.2.2.1, Hivf.2.2.2.1, hm] at Hmg
  simp only [Prod.mk.injEq] at Hmg
  obtain ⟨rfl, hd', rfl⟩ := Hmg
  iStructNamed Hp
  ihave %HBnn := typedPointsto_not_null _ _ _ $$ Base
  iStructNamed Base
  wp_apply (wp_Tag_GreaterThan _ g.Base'.T' iv.Base'.T') $$ [$T] as T
  ihave Base : p.[src.gryffproto.PreAcceptReply, go!"Base"] ↦ g.Base' $$ [T V]
  · iapply typedPointsto_combine _ _ _ HBnn
    simp only [typedPointstoDef]
    iframe
  ihave #HThr : gR.[src.genericsmr.Replica, go!"Thrifty"] ↦□ false $$ []
  · iunfold h2Fixed at Hfix
    icases Hfix with ⟨%pS, %alS, %addrs, %st, %cPA, %cA, %cC, %cCS, %cPAR, %cPAO, %cAR, %cEx,
      #H, -⟩
    iexact H
  icases epaxosRest_ctrs h $$ Hrest with ⟨%v1, %v2, %v3, %v4, Hcf, Hhp, Hsl, Hwd, Hrestc⟩
  generalize hgt : (tagOf g.Base'.T').gt (tagOf iv.Base'.T') = bg
  wp_join iprop(∃ b : src.gryffproto.ValTag,
      ip ↦ ({ iv with Seq' := seq, Deps' := d', Base' := b } : src.gryff.Instance) ∗
      ⌜b = if bg then g.Base' else iv.Base'⌝ ∗ equal_ptr ↦ (if bg then false else eq0) ∗
      inst_ptr ↦ ip ∗ pareply_ptr ↦ p ∗ e_ptr ↦ h)
    with [Hiv equal inst pareply e Base] as ⟨%b, Hiv, %Hb, equal, inst, pareply, e⟩
  · iexists iv.Base'
    iframe
    ipureintro; rfl
  · iexists g.Base'
    iframe
    ipureintro; rfl
  h2c_printf
  dsimp only
  rw [f3]
  generalize hE1 : (if bg then false else eq0) = e1
  wp_apply (wp_if_and lb.allEqual e1 equal_ptr) $$ [$equal] as equal
  generalize hne : (!e1) = ne1
  wp_join iprop(∃ v : w64, globalAddr src.gryff.conflicted ↦ v) with [Hcf] as ⟨%v1', Hcf⟩
  -- the merged copy `c2` and bookkeeping `lb2`
  have hg2 : (vtOf g.Base').t.gt c.base.t = bg := by rw [← Hivf.2.2.2.2.1]; exact hgt
  simp only [prC, prEq, hg2] at hcases
  have hC : (if bg = true then { c with seq := seq, deps := deps, base := vtOf g.Base' }
      else { c with seq := seq, deps := deps }) = { c with seq := seq, deps := deps, base := vtOf b } := by
    rw [Hb]; cases bg
    · simp only [Bool.false_eq_true, ↓reduceIte]; rw [Hivf.2.2.2.2.1]
    · rfl
  rw [hC, hE1] at hcases
  have hlbiv : ({ iv with Seq' := seq, Deps' := d', Base' := b } : src.gryff.Instance).lb' = iv.lb' := rfl
  have hcmdiv : ({ iv with Seq' := seq, Deps' := d', Base' := b } : src.gryff.Instance).Cmds' = iv.Cmds' := rfl
  have Hivf2 : ({ iv with Seq' := seq, Deps' := d', Base' := b } : src.gryff.Instance).ballot' =
      ({ c with seq := seq, deps := deps, base := vtOf b } : Copy).ballot ∧
      ({ iv with Seq' := seq, Deps' := d', Base' := b } : src.gryff.Instance).Status' =
      ({ c with seq := seq, deps := deps, base := vtOf b } : Copy).status ∧
      ({ iv with Seq' := seq, Deps' := d', Base' := b } : src.gryff.Instance).Seq' =
      ({ c with seq := seq, deps := deps, base := vtOf b } : Copy).seq ∧
      depsOf ({ iv with Seq' := seq, Deps' := d', Base' := b } : src.gryff.Instance).Deps' =
      ({ c with seq := seq, deps := deps, base := vtOf b } : Copy).deps ∧
      vtOf ({ iv with Seq' := seq, Deps' := d', Base' := b } : src.gryff.Instance).Base' =
      ({ c with seq := seq, deps := deps, base := vtOf b } : Copy).base ∧
      ({ iv with Seq' := seq, Deps' := d', Base' := b } : src.gryff.Instance).Slot' =
      ({ c with seq := seq, deps := deps, base := vtOf b } : Copy).slot ∧
      ({ iv with Seq' := seq, Deps' := d', Base' := b } : src.gryff.Instance).Leader' =
      ({ c with seq := seq, deps := deps, base := vtOf b } : Copy).leader ∧
      ({ iv with Seq' := seq, Deps' := d', Base' := b } : src.gryff.Instance).vbal' =
      ({ c with seq := seq, deps := deps, base := vtOf b } : Copy).vbal ∧
      sint.Z ({ iv with Seq' := seq, Deps' := d', Base' := b } : src.gryff.Instance).Leader' =
        (sint.Z g.Replica', sint.Z g.Instance').1 ∧
      sint.Z ({ iv with Seq' := seq, Deps' := d', Base' := b } : src.gryff.Instance).Slot' =
        (sint.Z g.Replica', sint.Z g.Instance').2 ∧
      sint.Z ({ iv with Seq' := seq, Deps' := d', Base' := b } : src.gryff.Instance).Index' =
        xs.numF (sint.Z g.Replica', sint.Z g.Instance') ∧
      sint.Z ({ iv with Seq' := seq, Deps' := d', Base' := b } : src.gryff.Instance).Lowlink' =
        xs.lowF (sint.Z g.Replica', sint.Z g.Instance') ∧
      (({ c with seq := seq, deps := deps, base := vtOf b } : Copy).status = model.St.EXECUTED ↔
        (sint.Z g.Replica', sint.Z g.Instance') ∈ xs.1) := by
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13⟩ := Hivf
    exact ⟨e1, e2, rfl, hd'.symm, rfl, e6, e7, e8, e9, e10, e11, e12, e13⟩
  have hst2 : ({ c with seq := seq, deps := deps, base := vtOf b } : Copy).status =
      model.St.PREACCEPTED := hst
  have hcst : ({ c with seq := seq, deps := deps, base := vtOf b } : Copy).status = c.status := rfl
  have hccmd : ({ c with seq := seq, deps := deps, base := vtOf b } : Copy).cmds = c.cmds := rfl
  have hc2b : ({ c with seq := seq, deps := deps, base := vtOf b } : Copy).ballot = c.ballot := rfl
  rw [← hcmdiv] at *
  rw [← hlbiv]
  generalize ({ iv with Seq' := seq, Deps' := d', Base' := b } : src.gryff.Instance) = iv2 at *
  generalize ({ c with seq := seq, deps := deps, base := vtOf b } : Copy) = c2 at *
  rw [← hc2b, ← hccmd] at hcases
  rw [← hccmd]
  h2c_printf
  wp_apply (h2b.fastPathQuorum_wp r gR h) $$ [$HR' $HgR $HN $HThr]
  rw [f4]
  have hd1 : decide (sint.Z (model.FPQ - W64 1) ≤ sint.Z (lb.preAcceptOKs + W64 1)) =
      model.sge (prLB lb e1).preAcceptOKs (model.FPQ - 1) := rfl
  rw [hd1]
  have hfast : paFast c2 (prLB lb e1) = (model.sge (prLB lb e1).preAcceptOKs (model.FPQ - 1) &&
      (lb.allEqual && e1) && model.isInitialBallot c2.ballot) := rfl
  rw [hfast] at hcases
  generalize hA : model.sge (prLB lb e1).preAcceptOKs (model.FPQ - 1) = bA at hcases ⊢
  generalize hE : (lb.allEqual && e1) = bE at hcases ⊢
  generalize hI : model.isInitialBallot c2.ballot = bI at hcases
  cases bA <;> cases bE
  rotate_right
  wp_auto
  wp_apply wp_isInitialBallot
  rw [Hivf2.1, hI]
  cases bI
  rotate_left
  · -- the fast path's commit
    have hlc : model.leaderCommit s (g.Replica') g.Instance' c2 (prLB lb e1) = .ok (s', outs) := by
      rcases hcases with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · cases h
      · cases h
    clear hcases
    obtain ⟨s2, hs2, hs', hbc⟩ := leaderCommit_cases s s' outs _ _ c2 _ hlc
    clear hlc
    wp_auto
    h2c_printf
    wp_apply time.wp_Now as %tn _
    simp only [src.epaxosproto.COMMITTED]
    rw [ite_eq_left hqb]
    wp_apply wp_load_slice_index (t := go.GoType.SliceType (go.GoType.PointerType src.gryff.Instance.ty))
      ispS _ isp _ sq (by rw [hqw]; omega) $$ [$Hisp] as -
    · ipureintro; rw [hqw]; exact hsq
    rw [ite_eq_left hib]
    wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty)
      sq _ ptrs _ ip (by rw [hiw]; omega) $$ [$Hrow] as Hrow
    · ipureintro; rw [hiw]; exact hip
    ihave Hrest := Hrestc $$ Hcf Hhp Hsl Hwd
    ihave Hclose := Hclose $$ %s.crtInstance %hcrtlen Hcrt [Hmono] Hrest
    · rw [withCrt_self]; iexact Hmono
    rw [withCrt_self]
    ihave Hlb1 : lbRep ρ iv2.lb' (some (prLB lb e1)) $$ [Hgb Hprs Hcd Hri]
    · iapply (lbRep_some ..).2
      iexists _
      iframe Hgb
      dsimp only [prLB]
      iframe Hprs Hcd Hri
      ipureintro
      simp [prLB, f1, f2, f4, f5, f6, f7, f8, f9, f10, hE]
    generalize hlb1 : prLB lb e1 = lb1 at hs2 hs' hbc ⊢
    ihave Hc1 : copyRep ρ xs (sint.Z (g.Replica'), sint.Z g.Instance') ip (lcC1 c2 lb1) $$ [Hiv Hlb1]
    · iapply (copyRep_open ..).2
      iexists _
      iframe Hiv
      dsimp only [lcC1]
      iframe Hcmds Hlb1
      ipureintro
      obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13⟩ := Hivf2
      refine ⟨e1, rfl, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, ?_⟩
      rw [← e13, hst2]
      simp only [model.St.COMMITTED, model.St.EXECUTED, model.St.PREACCEPTED]
      decide
    icases Hclose with ⟨Ha, -⟩
    ihave Hep := Ha $$ %(lcC1 c2 lb1) [] Hrow Hc1
    · ipureintro
      refine ⟨rfl, fun _ => ?_⟩
      rw [committedOrExecuted_setInst_self s _ _ _ hbox]
      simp [lcC1]
    imod Hep with ⟨Hep, #HelC⟩
    ihave #Hae : attrEnv k r gR h $$ []
    · unfold attrEnv; iframe #
    wp_apply (wp_updateCommitted ρ k r gR h xs _ s2 (g.Replica') ⟨hq0, hq3⟩ hs2) $$ [$Hae $Hep]
      as Hep
    -- the slot reopened at `s2` (same pointer: `elemIf`)
    have hsi3 : s2.inst (g.Replica') g.Instance' = some (lcC1 c2 lb1) := by
      rw [updateCommitted_inst hs2]; simp [model.RState.setInst]
    icases epaxosOwn_slot_open ρ h r xs s2 (g.Replica') g.Instance' hbox $$ Hep with
      ⟨%ispS2, %sq2, %crtS2, %isp2, %ptrs2, %ip2, -, #HispS2, #Hisp2, %Hsl2, Hrow2, Hslot2, -,
        #HelS2, -, Hcrt2, Hmono2, Hrest2, Hclose2⟩
    icombine HispS HispS2 gives %Hspe
    subst Hspe
    icombine Hisp Hisp2 gives %Hie
    subst Hie
    obtain ⟨hsq2, hip2, hcrtlen2⟩ := Hsl2
    rw [hsq] at hsq2
    cases hsq2
    have hco1 : committedOrExecuted (s.setInst (g.Replica') g.Instance' (lcC1 c2 lb1))
        (sint.Z (g.Replica'), sint.Z g.Instance') = true := by
      rw [committedOrExecuted_setInst_self s _ _ _ hbox]; simp [lcC1]
    have hco2 : committedOrExecuted s2 (sint.Z (g.Replica'), sint.Z g.Instance') = true := by
      rw [← hco1]; unfold committedOrExecuted model.committedCopy; rw [updateCommitted_inst hs2]
    icases elemIf_agree ρ _ _ _ ip ip2 hco1 hco2 $$ [$HelC $HelS2] with %Hipe
    subst Hipe
    rw [hsi3]
    icases Hslot2 with ⟨-, Hc2⟩
    icases (copyRep_open ..).1 $$ Hc2 with ⟨%iv2, Hiv2, #Hcmds2, Hlb2, %Hivf2⟩
    dsimp only [lcC1] at Hivf2
    rw [show (lcC1 c2 lb1).lb = some lb1 from rfl, show (lcC1 c2 lb1).cmds = c2.cmds from rfl]
    icases (lbRep_some ρ iv2.lb' lb1).1 $$ Hlb2 with ⟨%gb3, Hgb3, Hprs3, Hcd3, Hri3, %Hgbf3⟩
    unfold proposalsRep
    icases Hprs3 with ⟨%pps, #Hpps, %Hppl, %Hpnil, #Hels⟩
    ihave %Hppsl := ownSlice_len _ _ _ $$ Hpps
    icases (cmdsRep_open ..).1 $$ Hcmds2 with ⟨%gs, #Hgs, %Hgsf⟩
    ihave %Hgsl := ownSlice_len _ _ _ $$ Hgs
    wp_auto
    wp_join iprop(∃ iv2' : src.gryff.Instance, ip ↦ iv2' ∗ ⌜iv2' = { iv2 with lb' := iv2'.lb' }⌝ ∗
        lbRep ρ iv2'.lb' (lcC3 c2 lb1).lb ∗ proposeOwn ρ gR (lcPQ s c2 lb1) ∗
        inst_ptr ↦ ip ∗ e_ptr ↦ h ∗ pareply_ptr ↦ p ∗ writeKey0_ptr ↦ false ∗
        readKey0_ptr ↦ false) at next
      with [Hiv2 Hgb3 Hcd3 Hri3 Hprop inst e pareply writeKey0 readKey0] as
        ⟨%iv2', Hiv, %Hiv', Hlb, Hprop, inst, e, pareply, writeKey0, readKey0⟩
    · -- G11's re-proposal, or the "all clear" loop
      by_cases hn : gb3.clientProposals' = slice.nil
      · -- nil proposals: neither
        have hprs0 : lb1.clientProposals = [] := by
          have : pps.length = 0 := by rw [Hppsl.1, hn]; rfl
          rw [← List.length_eq_zero_iff, ← Hppl, this]
        have hre : ¬ lcRe c2 lb1 := fun h => h.1 hprs0
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
        iexists _
        iframe Hgb3
        iframe Hcd3 Hri3
        unfold proposalsRep
        isplitl
        · iexists pps; iframe # ∗; ipureintro; exact ⟨Hppl, Hpnil⟩
        · ipureintro; exact Hgbf3
      have hprs1 : lb1.clientProposals ≠ [] := fun h => hn (Hpnil h)
      simp only [hn, decide_false, Bool.not_false]
      wp_auto
      have hgsl : gs.length = c2.cmds.length := by rw [← Hgsf.1, List.length_map]
      wp_if_destruct
      · -- G11: the committed value is not the clients': they are proposed again
        have hre : lcRe c2 lb1 := by
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
        have hre : ¬ lcRe c2 lb1 := by
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
          iexists _
          iframe Hgb3
          iframe Hcd3 Hri3
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
    h2c_printf
    -- the slot closed (a0) at the final copy, `epaxosRest` out for the broadcast
    ihave Hclose2 := Hclose2 $$ %s2.crtInstance %hcrtlen2 Hcrt2 [Hmono2] Hrest2
    · rw [withCrt_self]; iexact Hmono2
    rw [withCrt_self]
    icases Hclose2 with ⟨-, -, -, Ha0⟩
    ihave Hc3 : copyRep ρ xs (sint.Z (g.Replica'), sint.Z g.Instance') ip (lcC3 c2 lb1) $$ [Hiv Hlb]
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
    ihave Hep := Ha0 $$ %(lcC3 c2 lb1) [] Hrow2 Hc3
    · ipureintro
      refine ⟨rfl, ?_⟩
      rw [hco2, lcC3_committed s2 _ _ c2 lb1 hbox]
    icases h2b.epaxosOwn_rest ρ h r xs _ $$ Hep with ⟨Hrest, Hback⟩
    have hS3 := lcS3_eq s s2 _ _ c2 lb1 hs2
    obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9⟩ := lcS3_sameOut s s2 _ _ c2 lb1 hs2
    rw [← hs'] at o1 o2 o3 o4 o5 o6 o7 o8 o9
    have hid' : s'.id = rid32 k := by rw [o1]; exact Hid
    have hbc' : model.bcastCommit s' (g.Replica') g.Instance' (gs.map cmdOf) iv2'.Seq'
        (depsOf iv2'.Deps') (vtOf iv2'.Base') = some outs := by
      rw [Hiv']; dsimp only
      obtain ⟨f1, f2, f3, f4, f5, -⟩ := Hivf2
      rw [Hgsf.1, f3, f4, f5]; exact hbc
    ihave #HE : epEnv γ ρ k r gR h pa co $$ []
    · unfold epEnv; iframe #
    ihave Hpend : pendingOuts γ ρ k r t (outs ++ []) $$ [Hpend]
    · rw [List.append_nil]; iexact Hpend
    have hcmd' : iv2'.Cmds' = iv2.Cmds' := by rw [Hiv']
    rw [hcmd']
    wp_apply (wp_bcastCommit γ ρ k r gR h pa co t s' hid' _ _ iv2.Cmds' gs _ _ _ outs [] hbc'
      (by rw [Hgsf.1]; exact Hgsf.2)) $$ [$HE $Hrest $Hgs $Hpend] as ⟨Hrest, Hpend⟩
    ihave Hep := Hback $$ Hrest
    ihave Hep := epaxosOwn_proposeQ ρ h r xs _ (lcPQ s c2 lb1) $$ Hep
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

  all_goals
    simp only [Bool.false_and, Bool.and_false, Bool.true_and, Bool.false_eq_true, _root_.false_and, _root_.false_or,
      _root_.true_and] at hcases
    wp_auto
    have hd2 : decide (sint.Z (BitVec.sdiv (W64 3) (W64 2)) ≤ sint.Z (lb.preAcceptOKs + W64 1)) =
        model.sge (prLB lb e1).preAcceptOKs model.NHALF := by
      rw [show BitVec.sdiv (W64 3) (W64 2) = model.NHALF by decide]; rfl
    rw [hd2]
    generalize hN : model.sge (prLB lb e1).preAcceptOKs model.NHALF = bN at hcases ⊢
    cases bN
    · -- no majority yet
      simp only [Bool.false_eq_true, _root_.false_and, _root_.false_or, _root_.true_and] at hcases
      obtain ⟨rfl, rfl⟩ := hcases
      wp_auto
      ihave Hlbn : lbRep ρ iv2.lb' (some (prLB lb e1)) $$ [Hgb Hprs Hcd Hri]
      · iapply (lbRep_some ..).2
        iexists _
        iframe Hgb
        dsimp only [prLB]
        iframe Hprs Hcd Hri
        ipureintro
        simp [prLB, f1, f2, f4, f5, f6, f7, f8, f9, f10, hE]
      ihave Hrest := Hrestc $$ Hcf Hhp Hsl Hwd
      ihave Hclose := Hclose $$ %s.crtInstance %hcrtlen Hcrt [Hmono] Hrest
      · rw [withCrt_self]; iexact Hmono
      rw [withCrt_self]
      ihave Hc := (copyRep_open ρ xs _ ip { c2 with lb := some (prLB lb e1) }).2 $$ [Hiv Hlbn]
      · iexists iv2; iframe # ∗; ipureintro; exact Hivf2
      icases Hclose with ⟨-, -, -, Ha⟩
      ihave Hep := Ha $$ %({ c2 with lb := some (prLB lb e1) }) [] Hrow Hc
      · ipureintro; exact ⟨rfl, committedOrExecuted_setInst_status' s _ _ c _ hbox hsi hcst⟩
      obtain ⟨ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho8, ho9, -⟩ :=
        sameOut_setInst s (g.Replica') g.Instance' { c2 with lb := some (prLB lb e1) }
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
    · -- the slow path: accepted at the own ballot (G16), the Accept broadcast
      simp only [_root_.true_and, Bool.true_eq_false, _root_.false_and, _root_.or_false] at hcases
      obtain ⟨hss, hbc⟩ := hcases
      wp_auto
      wp_apply wp_isInitialBallot
      wp_apply (h2b.fastPathQuorum_wp r gR h) $$ [$HR' $HgR $HN $HThr]
      h2c_printf
      ihave Hrest := Hrestc $$ Hcf Hhp Hsl Hwd
      dsimp only
      ihave Hlbn : lbRep ρ iv2.lb' (some (prLB lb e1)) $$ [Hgb Hprs Hcd Hri]
      · iapply (lbRep_some ..).2
        iexists _
        iframe Hgb
        dsimp only [prLB]
        iframe Hprs Hcd Hri
        ipureintro
        simp [prLB, f1, f2, f4, f5, f6, f7, f8, f9, f10, hE]
      ihave Hclose := Hclose $$ %s.crtInstance %hcrtlen Hcrt [Hmono] Hrest
      · rw [withCrt_self]; iexact Hmono
      rw [withCrt_self]
      ihave Hc := (copyRep_open ρ xs _ ip (paAcc c2 (prLB lb e1))).2 $$ [Hiv Hlbn]
      · iexists _; iframe Hiv; dsimp only [paAcc]; iframe # ∗; ipureintro
        obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13⟩ := Hivf2
        refine ⟨e1, rfl, e3, e4, e5, e6, e7, e1, e9, e10, e11, e12, ?_⟩
        rw [← e13, hst2]
        simp only [model.St.ACCEPTED, model.St.EXECUTED, model.St.PREACCEPTED]
        decide
      have hco : committedOrExecuted (s.setInst (g.Replica') g.Instance' (paAcc c2 (prLB lb e1)))
          (sint.Z (g.Replica'), sint.Z g.Instance') = committedOrExecuted s (sint.Z (g.Replica'), sint.Z g.Instance') := by
        have ee1 : committedOrExecuted (s.setInst (g.Replica') g.Instance' (paAcc c2 (prLB lb e1)))
            (sint.Z (g.Replica'), sint.Z g.Instance') = false := by
          apply Bool.eq_false_iff.2; intro hh
          rw [committedOrExecuted_setInst_self s _ _ _ hbox] at hh
          simp [paAcc, model.St.ACCEPTED, model.St.COMMITTED, model.St.EXECUTED] at hh
        have e2 : committedOrExecuted s (sint.Z (g.Replica'), sint.Z g.Instance') = false := by
          apply Bool.eq_false_iff.2; intro hh
          rw [← setInst_self s _ _ c hsi, committedOrExecuted_setInst_self s _ _ _ hbox] at hh
          simp [hst, model.St.PREACCEPTED, model.St.COMMITTED, model.St.EXECUTED] at hh
        rw [ee1, e2]
      icases Hclose with ⟨-, -, -, Ha⟩
      ihave Hep := Ha $$ %(paAcc c2 (prLB lb e1)) [] Hrow Hc
      · ipureintro; exact ⟨rfl, hco⟩
      rw [← hss]
      icases h2b.epaxosOwn_rest ρ h r xs _ $$ Hep with ⟨Hrest, Hback⟩
      obtain ⟨ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho8, ho9, -⟩ :=
        sameOut_setInst s (g.Replica') g.Instance' (paAcc c2 (prLB lb e1))
      rw [← hss] at ho1 ho2 ho3 ho4 ho5 ho6 ho7 ho8 ho9
      have hid' : s'.id = rid32 k := by rw [ho1]; exact Hid
      icases (cmdsRep_open ..).1 $$ Hcmds with ⟨%gs, #Hgs, %Hgsf⟩
      have hbc' : model.bcastAccept s' (g.Replica') g.Instance' iv2.ballot' (gs.map cmdOf) iv2.Seq'
          (depsOf iv2.Deps') (vtOf iv2.Base') = some outs := by
        obtain ⟨e1, e2, e3, e4, e5, -⟩ := Hivf2
        rw [Hgsf.1, e1, e3, e4, e5]; exact hbc
      ihave #HE : epEnv γ ρ k r gR h pa co $$ []
      · unfold epEnv; iframe #
      ihave Hpend : pendingOuts γ ρ k r t (outs ++ []) $$ [Hpend]
      · rw [List.append_nil]; iexact Hpend
      wp_apply (wp_bcastAccept γ ρ k r gR h pa co t s' hid' _ _ _ iv2.Cmds' gs _ _ _ outs [] hbc'
        (by rw [Hgsf.1]; exact Hgsf.2)) $$ [$HE $Hrest $Hgs $Hpend] as ⟨Hrest, Hpend⟩
      ihave Hep := Hback $$ Hrest
      iapply HΦ
      iframe Hpend
      iapply handler_close γ ρ k r gR h pa co xs s'
      isplitr
      · iexact HE
      unfold parts
      rw [ho2, ho3, ho4, ho9]
      iframe Hparti Hval Hxs Hprop Hscr Hep
      isplitl
      · iapply coordOwn_congr ρ co _ k s s' ho5 ho6 ho7 ho8 $$ Hcoord
      · ipureintro; exact hid'

variable [pD : GryffPartiDeps (GF := GF)] in
/-- **`handlePreAcceptReply.wp`** (`Replica2/Specs.lean`), at its frozen statement. -/
theorem handlePreAcceptReply_spec (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc)
    (m : model.PreAcceptReplyM) :
    epHandlerSpec γ ρ k r h go!"handlePreAcceptReply" (.preAcceptReply m) := by
  intro p t s s' outs hstep
  iintro %Φ ⟨#Hpkg, #Hrep, Hown, Hpend, Hh, Hmsg⟩ HΦ
  iapply (handlePreAcceptReply_wp' γ ρ k r h p m t s s' outs hstep) $$ [Hown Hpend Hh Hmsg] HΦ
  iframe # ∗

end

end Perennial.gryff.replica2
