/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H3/Prepare.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H3: `handlePrepare` (an acceptor's answer to a Prepare).

In a section with one `HeapGS` (hub request H2-R0 / H3-R0): `handlePrepare_wp'` is the frozen
`handlePrepare.wp`'s statement.
-/
module

public import Dsverify.Proof.gryff.H3.Env
public import Dsverify.Proof.gryff.H2.InstOpen -- C: `epaxosOwn_inst_open` moved to Replica2/Results.lean
public import Dsverify.Proof.gryff.H3.Bcast
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

theorem handlePrepare_wp' (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h p : Loc)
    (m : model.PrepareM) (t : List Ev) (s s' : RState) (outs : List Out)
    (hstep : model.stepR k s (.msg (.prepare m)) = .ok (s', outs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r ∗
        replicaOwn ρ k r s ∗ pendingOuts γ ρ k r t outs ∗ (handlerOf r h ∗ msgAt p (.prepare m)) }}
      (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!!
        go!"handlePrepare")) (Val #p))
    {{ RET #(); replicaOwn ρ k r s' ∗ pendingOuts γ ρ k r t [] }} := by
  wp_start as ⟨#Hrep, Hown, Hpend, ⟨Hh, Hmsg⟩⟩
  obtain ⟨hbox, hres⟩ := stepPrepare_ok s s' m outs hstep
  ihave ⟨%gR, %pa, %co, %xs, #Henv, Hparts⟩ := handler_open γ ρ k r h s $$ [Hrep Hh Hown]
  · iframe # ∗
  iunfold parts at Hparts
  ihave #Henv' := Henv
  iunfold epEnv at Henv'
  icases Henv' with ⟨#HgR, #Hpa', #Hco', #Hh', #HR', #HId, #HN, #HDur, #Hok, #Hfix⟩
  icases Hparts with ⟨Hpa, Hval, Hco, Hep, Hxs, Hprop, Hscr, %Hid⟩
  iunfold msgAt at Hmsg
  icases Hmsg with ⟨%g, Hg, %Hg⟩
  subst Hg
  simp only [prepareOf] at hbox hres
  have hbox' := hbox
  icases epaxosOwn_inst_open' ρ h r xs s g.Replica' g.Instance' hbox $$ Hep with
    ⟨%ispS, %sq, %isp, %ptrs, %ptr, #HIS, #Hisp, %Hsl, Hsq, Hcase, %Hunc, Hclose⟩
  simp only [model.inBox, decide_eq_true_eq] at hbox
  obtain ⟨hq0, hq3, hi0, hiS⟩ := hbox
  obtain ⟨hsq, hptr⟩ := Hsl
  ihave %HispL := ownSlice_len _ _ _ $$ Hisp
  ihave %HsqL := ownSlice_len _ _ _ $$ Hsq
  have hqZ : sint.Z (W64 (sint.Z g.Replica')) = sint.Z g.Replica' := by word
  have hiZ : sint.Z (W64 (sint.Z g.Instance')) = sint.Z g.Instance' := by word
  have hqlen : sint.Z g.Replica' < sint.Z ispS.len := by
    have h0 := (List.getElem?_eq_some_iff.1 hsq).1
    have h1 := HispL.1; have h2 := HispL.2
    simp only [sint.nat, sint.Z] at h1 h2 hq0 h0 ⊢; omega
  have hilen : sint.Z g.Instance' < sint.Z sq.len := by
    have h0 := (List.getElem?_eq_some_iff.1 hptr).1
    have h1 := HsqL.1; have h2 := HsqL.2
    simp only [sint.nat, sint.Z] at h1 h2 hi0 h0 ⊢; omega
  wp_auto
  rw [hqZ, if_pos ⟨hq0, hqlen⟩]
  wp_apply wp_load_slice_index ispS _ isp _ sq hq0 $$ [Hisp] as -
  · iframe Hisp; ipureintro; exact hsq
  rw [hiZ, if_pos ⟨hi0, hilen⟩]
  wp_apply wp_load_slice_index sq _ ptrs _ ptr hi0 $$ [Hsq] as Hsq
  · iframe Hsq; ipureintro; exact hptr
  rcases hc : s.inst g.Replica' g.Instance' with _ | c
  · -- a new copy
    rw [hc] at hres
    try dsimp only
    icases Hcase with %Hnull
    subst Hnull
    obtain ⟨o, ho, rfl, rfl⟩ := hres
    obtain ⟨q, hq, hqk, rfl⟩ := sendPeer_some s k (by rw [Hid]; rfl) _ _ o ho
    wp_if_destruct
    rotate_left
    · exact absurd rfl Hif
    rw [hqZ, if_pos ⟨hq0, hqlen⟩]
    wp_apply wp_load_slice_index ispS _ isp _ sq hq0 $$ [Hisp] as -
    · iframe Hisp; ipureintro; exact hsq
    rw [hiZ, if_pos ⟨hi0, hilen⟩]
    have hilt := (List.getElem?_eq_some_iff.1 hptr).1
    wp_apply wp_store_slice_index sq _ ptrs «$r0_ptr» $$ [Hsq] as Hsq
    · iframe Hsq; ipureintro; omega
    irename «$r0» => Hrp
    generalize «$r0_ptr» = pR
    irename «$r0» => HiI
    rename_i pI
    ihave %HpInn := typedPointsto_not_null _ _ _ $$ HiI
    wp_pures
    -- the reply
    ihave Hrm : msgAt pR (.prepareReply (prepNewReply s (model.PrepareM.mk g.LeaderId'
        g.Replica' g.Instance' g.Ballot'))) $$ [Hrp]
    · iunfold msgAt
      iexists (wire.gryffproto.PrepareReply.Msg.mk (rid32 k) g.Replica' g.Instance' (W8 1) g.Ballot'
        (W32 (-1)) (W8 0) [] (W32 (-1)) (zero_val (GoArray w32 5))
        { V' := W64 0, T' := { Ts' := W32 0, Cid' := W32 0, Rmwc' := W32 0 } }), slice.nil
      simp only [wire.gryffproto.PrepareReply.goVal]
      iframe Hrp
      isplitr
      · iapply ownSlice_nil
      ipureintro
      simp only [prepareReplyOf, prepNewReply, prepareOf, Hid]
      rfl
    -- close: the new copy into the nil slot
    let n : replica.Node := (sint.Z g.Replica', sint.Z g.Instance')
    have hcoe : committedOrExecuted s n = false := by
      show committedOrExecuted s (sint.Z g.Replica', sint.Z g.Instance') = false
      rw [coe_slot s _ _ hbox', hc]
    obtain ⟨hnum, hlow, hnin⟩ := Hunc hcoe
    let c' := prepNewCopy (model.PrepareM.mk g.LeaderId' g.Replica' g.Instance' g.Ballot')
    ihave Hc : copyRep ρ xs n pI c' $$ [HiI]
    · iapply (copyRep_open ..).2
      iexists _
      iframe HiI
      isplitr
      · iunfold cmdsRep
        iexists []
        isplitl
        · iapply ownSlice_nil
        ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · iunfold lbRep; simp only [c', prepNewCopy]; ipureintro; trivial
      ipureintro
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · rw [hnum]; rfl
      · rw [hlow]; rfl
      · constructor
        · intro e; cases e
        · intro e; exact absurd e hnin
    icases Hclose with ⟨-, Hclose⟩
    icases Hclose with ⟨Hb, -⟩
    ihave Hep := Hb $$ %pI %c' [] Hsq Hc
    · ipureintro; exact ⟨trivial, HpInn⟩
    imod Hep
    have hLq : g.LeaderId' = rid32 q := by rw [hq]; rfl
    wp_apply replyPrepare_wp γ ρ k q r gR h t pR _ [] hqk _ hLq $$ [Hrm Hpend] as ⟨Hrm, Hpend⟩
    · iframe Hrm Hpend
      ihave #Hcodes := genericOk_prepCodes γ ρ k r gR h $$ Hok
      unfold recFixed
      iframe #
    ihave Hco := coordOwn_congr ρ co _ k s (s.setInst g.Replica' g.Instance' c') rfl rfl rfl rfl $$ Hco
    iapply HΦ
    iframe Hpend
    iapply handler_close γ ρ k r gR h pa co xs
    iframe Henv
    iunfold parts
    simp only [setInst_tag, setInst_ongoing, setInst_val, setInst_proposeQ, setInst_id]
    iframe
    ipureintro; exact Hid
  · -- an existing copy
    rw [hc] at hres
    try dsimp only
    icases Hcase with ⟨%Hnn, Hc⟩
    obtain ⟨o, ho, rfl, rfl⟩ := hres
    obtain ⟨q, hq, hqk, rfl⟩ := sendPeer_some s k (by rw [Hid]; rfl) _ _ o ho
    wp_if_destruct
    · exact absurd rfl Hnn
    icases (copyRep_open ..).1 $$ Hc with ⟨%iv, Hiv, #Hcmds, Hlb, %Hivf⟩
    simp only [src.gryff.TRUE, src.gryff.FALSE]
    wp_auto
    let m : model.PrepareM := ⟨g.LeaderId', g.Replica', g.Instance', g.Ballot'⟩
    wp_join iprop(ok_ptr ↦ (if model.slt g.Ballot' c.ballot then W8 0 else W8 1) ∗
        ptr ↦ { iv with ballot' := (prepCopy m c).ballot } ∗ prepare_ptr ↦ p ∗
        wire.epaxosproto.Prepare.own p (DFrac.own 1) g ∗ inst_ptr ↦ ptr)
      with [ok Hiv prepare Hg inst] as ⟨ok, Hiv, prepare, Hg, inst⟩
    · have hs : model.slt g.Ballot' c.ballot = true := by
        simp only [model.slt, decide_eq_true_eq]; rw [← Hivf.1]; exact Hif
      simp only [hs, ↓reduceIte, prepCopy, m]
      rw [← Hivf.1]
      iframe
    · have hs : model.slt g.Ballot' c.ballot = false := by
        simp only [model.slt, decide_eq_false_iff_not]; rw [← Hivf.1]; exact Hif
      simp only [hs, ↓reduceIte, prepCopy, m, Bool.false_eq_true]
      iframe
    irename «$r0» => Hrp
    generalize «$r0_ptr» = pR
    iunfold cmdsRep at Hcmds
    icases Hcmds with ⟨%gs, #Hgs, %Hgsc⟩
    obtain ⟨Hgsc, HgsOk⟩ := Hgsc
    have hrep : prepareReplyOf (wire.gryffproto.PrepareReply.Msg.mk (rid32 k) g.Replica'
      g.Instance' (if model.slt g.Ballot' c.ballot then W8 0 else W8 1) (prepCopy m c).ballot
      iv.vbal' iv.Status' gs iv.Seq' iv.Deps' iv.Base') = prepReply s m c := by
      obtain ⟨_, h2, h3, h4, h5, _, _, h8, _⟩ := Hivf
      simp only [prepareReplyOf, prepReply, Hid, h2, h3, h4, h5, h8, Hgsc]
      split <;> rfl
    ihave Hrm : msgAt pR (.prepareReply (prepReply s m c)) $$ [Hrp]
    · rw [← hrep]
      iapply prepareReply_msgAt pR _ iv.Cmds'
      iframe Hgs
      simp only [wire.gryffproto.PrepareReply.goVal]
      iframe Hrp
    -- close: the same pointer, the promised copy
    let c' := prepCopy m c
    have hst : c'.status = c.status := by simp only [c', prepCopy]; split <;> rfl
    ihave Hc : copyRep ρ xs (sint.Z g.Replica', sint.Z g.Instance') ptr c' $$ [Hiv Hlb]
    · iapply (copyRep_open ..).2
      iexists _
      iframe Hiv
      isplitr
      · have : c'.cmds = c.cmds := by simp only [c', prepCopy]; split <;> rfl
        iunfold cmdsRep; iexists gs; iframe Hgs; ipureintro; rw [this]; exact ⟨Hgsc, HgsOk⟩
      isplitl [Hlb]
      · have : c'.lb = c.lb := by simp only [c', prepCopy]; split <;> rfl
        rw [this]; iexact Hlb
      ipureintro
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := Hivf
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h9, h10, h11, h12, ?_⟩ <;>
        simp only [c', prepCopy] <;> split <;> simp_all
    icases Hclose with ⟨Ha, -⟩
    ihave Hep := Ha $$ %c' [] Hsq Hc
    · ipureintro
      refine ⟨rfl, fun hco => ?_⟩
      rw [coe_setInst s _ _ c' hbox', hst]
      rw [coe_slot s _ _ hbox', hc] at hco
      exact hco
    imod Hep
    have hLq : g.LeaderId' = rid32 q := by rw [hq]; rfl
    wp_apply replyPrepare_wp γ ρ k q r gR h t pR _ [] hqk _ hLq $$ [Hrm Hpend] as ⟨Hrm, Hpend⟩
    · iframe Hrm Hpend
      ihave #Hcodes := genericOk_prepCodes γ ρ k r gR h $$ Hok
      unfold recFixed
      iframe #
    ihave Hco := coordOwn_congr ρ co _ k s (s.setInst g.Replica' g.Instance' c') rfl rfl rfl rfl $$ Hco
    iapply HΦ
    iframe Hpend
    iapply handler_close γ ρ k r gR h pa co xs
    iframe Henv
    iunfold parts
    simp only [setInst_tag, setInst_ongoing, setInst_val, setInst_proposeQ, setInst_id]
    iframe
    ipureintro; exact Hid

/-- The frozen `handlePrepare.wp`'s statement (`Replica2/Specs.lean`), proved. -/
theorem handlePrepare_wp_frozen (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc)
    (m : model.PrepareM) : epHandlerSpec γ ρ k r h go!"handlePrepare" (.prepare m) :=
  fun p t s s' outs hstep => handlePrepare_wp' γ ρ k r h p m t s s' outs hstep

end

end Perennial.gryff.replica2.h3
