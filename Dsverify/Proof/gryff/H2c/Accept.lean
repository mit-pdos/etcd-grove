/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2c/Accept.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2c: `handleAccept` (G10: the instance's row, the reply to the sender; G15/G16/G19)
-/
module

public import Dsverify.Proof.gryff.H2.Env
public import Dsverify.Proof.gryff.H2c.SlotOpen
public import Dsverify.Proof.gryff.H2c.AcceptModel
public import Dsverify.Proof.gryff.H2c.Base
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB Proposal Msg Ev Out Cmd Deps)
open Perennial.gryff.replica (XS rowOwn nSlots)

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem acS1_withCrt (s : RState) (m : model.EAcceptM) :
    withCrt s (acS1 s m).crtInstance = acS1 s m := by
  unfold acS1; split <;> rfl

theorem acS1_len (s : RState) (m : model.EAcceptM) :
    (acS1 s m).crtInstance.length = s.crtInstance.length := by
  unfold acS1; split
  · simp [model.RState.setCrt]
  · rfl

@[simp] theorem acS1_inst (s : RState) (m : model.EAcceptM) : (acS1 s m).inst = s.inst := by
  unfold acS1; split <;> rfl

@[simp] theorem acS1_id (s : RState) (m : model.EAcceptM) : (acS1 s m).id = s.id := by
  unfold acS1; split <;> rfl

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF] -- H1-R6 / N-1
variable [sortA : Perennial.gryff.replica2.SortSliceHyp GF]
variable [strconvA : strconv.Assumptions] -- N-5


set_option goose.wp.extras true

theorem msgAt_accept (p : Loc) (mm : model.EAcceptM) :
    msgAt (GF := GF) p (.accept mm) ⊣⊢ ∃ (g : wire.gryffproto.EAccept.Msg) (sl : GoSlice),
      p ↦ wire.gryffproto.EAccept.goVal g sl ∗ sl ↦*□ g.Command ∗ ⌜acceptOf g = mm⌝ := by
  unfold msgAt; exact .rfl

theorem msgAt_acceptReply (p : Loc) (mm : model.AcceptReplyM) :
    msgAt (GF := GF) p (.acceptReply mm) ⊣⊢ ∃ g : src.epaxosproto.AcceptReply, p ↦ g ∗ ⌜acceptReplyOf g = mm⌝ := by
  unfold msgAt; exact .rfl

set_option maxHeartbeats 4000000 in
theorem handleAccept_wp' (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h p : Loc)
    (m : model.EAcceptM) (t : List Ev) (s s' : RState) (outs : List Out)
    (hstep : model.stepR k s (.msg (.accept m)) = .ok (s', outs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r ∗
        replicaOwn ρ k r s ∗ pendingOuts γ ρ k r t outs ∗ handlerOf r h ∗
        msgAt p (.accept m) }}
      (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!!
        go!"handleAccept")) (Val #p))
    {{ RET #(); replicaOwn ρ k r s' ∗ pendingOuts γ ρ k r t [] }} := by
  wp_start as ⟨Hrep, Hown, Hpend, Hh, Hmsg⟩
  icases handler_open γ ρ k r h s $$ [$Hrep $Hh $Hown] with ⟨%gR, %pa, %co, %xs, #Henv, Hparts⟩
  icases (msgAt_accept ..).1 $$ Hmsg with ⟨%g, %sl, Hp, #Hsl, %Hg⟩
  unfold parts
  icases Hparts with ⟨Hparti, Hval, Hcoord, Hep, Hxs, Hprop, Hscr, %Hid⟩
  simp only [model.stepR] at hstep
  obtain ⟨hcmdsOk, hbox, hcases⟩ := stepAccept_cases s s' outs m hstep
  clear hstep
  subst Hg
  have hbox' := hbox
  simp only [model.inBox, acceptOf] at hbox'
  have hbox' := of_decide_eq_true hbox'
  obtain ⟨hq0, hq3, hi0, hiS⟩ := hbox'
  icases epaxosOwn_slot_open ρ h r xs s g.Replica g.Instance hbox $$ Hep with
    ⟨%ispS, %sq, %crtS, %isp, %ptrs, %ip, #HR, #HispS, #Hisp, %Hsl, Hrow, Hslot, %Hxsf, #HelS, #HcrtS,
      Hcrt, Hmono, Hrest, Hclose⟩
  unfold epEnv
  icases Henv with ⟨#HgR, #Hpa, #Hco, #Hh, #HR', #HId, #HN, #HDur, #Hgen, #Hfix⟩
  wp_auto
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
      p ↦ wire.gryffproto.EAccept.goVal g sl ∗ accept_ptr ↦ p ∗ e_ptr ↦ h)
    with [HmaxSeq Hp accept e] as ⟨⟨%ms', HmaxSeq⟩, Hp, accept, e⟩
  ihave Hrest := Hrestc $$ %ms' HmaxSeq
  ihave #Henv : epEnv γ ρ k r gR h pa co $$ []
  · unfold epEnv; iframe #
  rcases hsi : s.inst g.Replica g.Instance with _ | c
  · -- no copy
    icases Hslot with %hipn
    subst hipn
    have hsi' : s.inst (acceptOf g).replica (acceptOf g).inst = none := hsi
    obtain ⟨o, hs', ho, rfl⟩ : ∃ o, s' = (acS1 s (acceptOf g)).setInst g.Replica g.Instance
          (acNew (acceptOf g)) ∧ model.sendPeer s' g.LeaderId
          (acReply (acceptOf g) model.TRUE g.Ballot) = some o ∧ outs = [o] := by
      rcases hcases with ⟨c', hc', -⟩ | ⟨c', o, hc', -⟩ | ⟨c', o, hc', -⟩ | ⟨o, -, h1, ho, h2⟩
      · rw [hsi'] at hc'; cases hc'
      · rw [hsi'] at hc'; cases hc'
      · rw [hsi'] at hc'; cases hc'
      · exact ⟨o, h1, ho, h2⟩
    subst hs'
    wp_auto
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
    wp_join iprop(crtS ↦* (acS1 s (acceptOf g)).crtInstance ∗ crtMonos ρ (acS1 s (acceptOf g)) ∗
        e_ptr ↦ h ∗ accept_ptr ↦ p ∗ p ↦ wire.gryffproto.EAccept.goVal g sl)
      with [Hcrt Hmono e accept Hp] as ⟨Hcrt, Hmono, e, accept, Hp⟩
    · have hS1 : acS1 s (acceptOf g) = s.setCrt g.Replica (g.Instance + 1) := by
        simp only [acS1, acceptOf, model.sge, model.sle, ← hcqs, Hif, decide_true, ite_true]
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
    · have hS1 : acS1 s (acceptOf g) = s := by
        simp only [acS1, acceptOf, model.sge, model.sle, ← hcqs, Hif, decide_false]
        rfl
      rw [hS1]
      iframe
    ihave Hclose := Hclose $$ %(acS1 s (acceptOf g)).crtInstance %(by rw [acS1_len]; exact hcrtlen)
      Hcrt [Hmono] Hrest
    · rw [acS1_withCrt]; iexact Hmono
    rw [acS1_withCrt]
    simp only [src.epaxosproto.ACCEPTED, src.gryff.TRUE]
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
    ihave Hep := Hb $$ %«$r0_ptr» %(acNew (acceptOf g)) [] Hrow [«$r0»]
    · ipureintro; simp [Hnn]
    · iapply (copyRep_open ..).2
      iexists _
      iframe «$r0»
      dsimp only [acNew]
      isplitr
      · iapply (cmdsRep_open ..).2; iexists g.Command; iframe Hsl; ipureintro; exact ⟨rfl, hcmdsOk⟩
      isplitr
      · iapply (lbRep_none ..).2; ipureintro; rfl
      ipureintro
      simp only [acceptOf, hx1, hx2]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals (try first | rfl | trivial)
      simp only [model.St.ACCEPTED, model.St.EXECUTED]
      constructor
      · intro h; cases h
      · intro h; exact absurd h hx3
    imod Hep
    obtain ⟨S, hS⟩ : ∃ S, S = (acS1 s (acceptOf g)).setInst g.Replica g.Instance (acNew (acceptOf g)) :=
      ⟨_, rfl⟩
    rw [← hS] at ho ⊢
    have hsoS : sameOut s S := by
      rw [hS]; exact sameOut_trans (acS1_sameOut s _) (sameOut_setInst _ _ _ _)
    -- the tail: `recordInstanceMetadata(ISP[q][i])`, `sync`, the reply, the optimization off
    have hbox2 : model.inBox g.Replica g.Instance = true := hbox
    icases epaxosOwn_peek ρ h r xs S g.Replica g.Instance hbox2 $$ Hep with
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
    wp_apply (wp_sync h r gR) $$ [$HR' $HgR $HDur]
    ihave Hep := Hback $$ Hrow2
    ihave Hm : msgAt «$a1_ptr» (.acceptReply ⟨g.Replica, g.Instance, model.TRUE, g.Ballot⟩) $$ [«$a1»]
    · iapply (msgAt_acceptReply ..).2
      iexists _
      iframe «$a1»
      ipureintro
      simp only [acceptReplyOf]; rfl
    have ho' : model.sendPeer S g.LeaderId
        (.acceptReply ⟨g.Replica, g.Instance, model.TRUE, g.Ballot⟩) = some o := ho
    have hidS : S.id = rid32 k := by rw [hsoS.1]; exact Hid
    wp_apply (wp_replyAccept γ ρ k r gR h pa co t S hidS
      g.LeaderId «$a1_ptr» _ o [] ho') $$ [$Henv $Hm $Hpend] as ⟨-, Hpend⟩
    ihave #HbO := h2Fixed_bcastOpt k gR h $$ Hfix
    wp_auto
    obtain ⟨ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho8, ho9, -⟩ := hsoS
    iapply HΦ
    iframe Hpend
    iapply handler_close γ ρ k r gR h pa co xs S
    iframe Henv
    unfold parts
    rw [ho2, ho3, ho4, ho9]
    iframe Hparti Hval Hxs Hprop Hscr Hep
    isplitl
    · iapply coordOwn_congr ρ co _ k s _ ho5 ho6 ho7 ho8 $$ Hcoord
    · ipureintro; rw [ho1]; exact Hid
  · icases Hslot with ⟨%hipn, Hc⟩
    icases (copyRep_open ..).1 $$ Hc with ⟨%iv, Hiv, #Hcmds, Hlb, %Hivf⟩
    have hsi' : s.inst (acceptOf g).replica (acceptOf g).inst = some c := hsi
    simp only [hipn, decide_false, Bool.not_false, src.epaxosproto.COMMITTED,
      src.epaxosproto.EXECUTED]
    by_cases hcm : c.status = model.St.COMMITTED ∨ c.status = model.St.EXECUTED
    · -- committed or executed: nothing changes
      obtain ⟨hss, rfl⟩ : s' = s ∧ outs = [] := by
        rcases hcases with ⟨c', hc', -, h1, h2⟩ | ⟨c', o, hc', hn, -⟩ | ⟨c', o, hc', hn, -⟩ | ⟨o, hn, -⟩
        · exact ⟨h1, h2⟩
        · rw [hsi'] at hc'; cases hc'; exact absurd hcm hn
        · rw [hsi'] at hc'; cases hc'; exact absurd hcm hn
        · rw [hsi'] at hn; cases hn
      subst s'
      wp_auto
      wp_if_destruct
      · ihave Hc := (copyRep_open ρ xs _ ip c).2 $$ [Hiv Hlb]
        · iexists iv; iframe # ∗; ipureintro; exact Hivf
        ihave Hclose := Hclose $$ %s.crtInstance %hcrtlen Hcrt [Hmono] Hrest
        · rw [withCrt_self]; iexact Hmono
        icases Hclose with ⟨-, -, -, Ha⟩
        ihave Hep := Ha $$ %c [] Hrow Hc
        · ipureintro; refine ⟨rfl, ?_⟩; rw [setInst_self s _ _ c hsi]
        rw [withCrt_self, setInst_self s _ _ c hsi]
        iapply HΦ
        iframe Hpend
        iapply handler_close γ ρ k r gR h pa co xs s
        iframe Henv
        unfold parts
        iframe Hparti Hval Hxs Hprop Hscr Hep Hcoord
        ipureintro; exact Hid
      have hne4 := Hif
      wp_if_destruct
      · ihave Hc := (copyRep_open ρ xs _ ip c).2 $$ [Hiv Hlb]
        · iexists iv; iframe # ∗; ipureintro; exact Hivf
        ihave Hclose := Hclose $$ %s.crtInstance %hcrtlen Hcrt [Hmono] Hrest
        · rw [withCrt_self]; iexact Hmono
        icases Hclose with ⟨-, -, -, Ha⟩
        ihave Hep := Ha $$ %c [] Hrow Hc
        · ipureintro; refine ⟨rfl, ?_⟩; rw [setInst_self s _ _ c hsi]
        rw [withCrt_self, setInst_self s _ _ c hsi]
        iapply HΦ
        iframe Hpend
        iapply handler_close γ ρ k r gR h pa co xs s
        iframe Henv
        unfold parts
        iframe Hparti Hval Hxs Hprop Hscr Hep Hcoord
        ipureintro; exact Hid
      · exfalso; rcases hcm with h1 | h1
        · exact hne4 (by rw [Hivf.2.1, h1]; rfl)
        · exact Hif (by rw [Hivf.2.1, h1]; rfl)
    -- not committed: the early check fails
    wp_auto
    wp_if_destruct
    · exfalso; apply hcm; left; rw [← Hivf.2.1, Hif]; rfl
    wp_if_destruct
    · exfalso; apply hcm; right; rw [← Hivf.2.1, Hif]; rfl
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
    wp_join iprop(crtS ↦* (acS1 s (acceptOf g)).crtInstance ∗ crtMonos ρ (acS1 s (acceptOf g)) ∗
        e_ptr ↦ h ∗ accept_ptr ↦ p ∗ p ↦ wire.gryffproto.EAccept.goVal g sl)
      with [Hcrt Hmono e accept Hp] as ⟨Hcrt, Hmono, e, accept, Hp⟩
    · have hS1 : acS1 s (acceptOf g) = s.setCrt g.Replica (g.Instance + 1) := by
        simp only [acS1, acceptOf, model.sge, model.sle, ← hcqs, Hif, _root_.decide_true, ite_true]
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
    · have hS1 : acS1 s (acceptOf g) = s := by
        simp only [acS1, acceptOf, model.sge, model.sle, ← hcqs, Hif, decide_false]
        rfl
      rw [hS1]
      iframe
    ihave Hclose := Hclose $$ %(acS1 s (acceptOf g)).crtInstance %(by rw [acS1_len]; exact hcrtlen)
      Hcrt [Hmono] Hrest
    · rw [acS1_withCrt]; iexact Hmono
    rw [acS1_withCrt]
    have hcm' : ¬ (c.status = model.St.COMMITTED ∨ c.status = model.St.EXECUTED) := hcm
    simp only [hipn, decide_false, Bool.not_false, src.gryff.FALSE, src.gryff.TRUE,
      src.epaxosproto.ACCEPTED]
    wp_auto
    wp_if_destruct
    · -- a smaller ballot: refuse
      obtain ⟨o, ho, rfl, rfl⟩ : ∃ o, model.sendPeer (acS1 s (acceptOf g)) g.LeaderId
          (acReply (acceptOf g) model.FALSE c.ballot) = some o ∧ s' = acS1 s (acceptOf g) ∧
          outs = [o] := by
        rcases hcases with ⟨c', hc', hn, -⟩ | ⟨c', o, hc', -, -, ho, h1, h2⟩ |
            ⟨c', o, hc', -, hb, -⟩ | ⟨o, hn, -⟩
        · rw [hsi'] at hc'; cases hc'; exact absurd hn hcm
        · rw [hsi'] at hc'; cases hc'; exact ⟨o, ho, h1, h2⟩
        · rw [hsi'] at hc'; cases hc'
          have : sint.Z g.Ballot < sint.Z c.ballot := by rw [← Hivf.1]; exact Hif
          simp [model.slt, acceptOf, this] at hb
        · rw [hsi'] at hn; cases hn
      ihave Hm : msgAt «$a1_ptr» (.acceptReply ⟨g.Replica, g.Instance, model.FALSE, c.ballot⟩) $$ [«$a1»]
      · iapply (msgAt_acceptReply ..).2
        iexists _
        iframe «$a1»
        ipureintro
        simp only [acceptReplyOf, Hivf.1]; rfl
      have ho' : model.sendPeer (acS1 s (acceptOf g)) g.LeaderId
          (.acceptReply ⟨g.Replica, g.Instance, model.FALSE, c.ballot⟩) = some o := ho
      wp_apply (wp_replyAccept γ ρ k r gR h pa co t (acS1 s (acceptOf g)) (by rw [acS1_id]; exact Hid)
        g.LeaderId «$a1_ptr» _ o [] ho') $$ [$Henv $Hm $Hpend] as ⟨-, Hpend⟩
      -- the copy unchanged
      ihave Hc := (copyRep_open ρ xs _ ip c).2 $$ [Hiv Hlb]
      · iexists iv; iframe # ∗; ipureintro; exact Hivf
      icases Hclose with ⟨-, -, -, Ha⟩
      ihave Hep := Ha $$ %c [] Hrow Hc
      · ipureintro; refine ⟨rfl, ?_⟩; rw [setInst_self s _ _ c hsi]
      rw [setInst_self (acS1 s (acceptOf g)) _ _ c (by rw [acS1_inst]; exact hsi)]
      obtain ⟨ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho8, ho9, -⟩ := acS1_sameOut s (acceptOf g)
      iapply HΦ
      iframe Hpend
      iapply handler_close γ ρ k r gR h pa co xs (acS1 s (acceptOf g))
      iframe Henv
      unfold parts
      rw [ho2, ho3, ho4, ho9]
      iframe Hparti Hval Hxs Hprop Hscr Hep
      isplitl
      · iapply coordOwn_congr ρ co _ k s _ ho5 ho6 ho7 ho8 $$ Hcoord
      · ipureintro; rw [ho1]; exact Hid
    -- accept: the copy updated
    obtain ⟨o, rfl, ho, rfl⟩ : ∃ o, s' = (acS1 s (acceptOf g)).setInst g.Replica g.Instance
          (acCopy c (acceptOf g)) ∧ model.sendPeer s' g.LeaderId
          (acReply (acceptOf g) model.TRUE g.Ballot) = some o ∧ outs = [o] := by
      rcases hcases with ⟨c', hc', hn, -⟩ | ⟨c', o, hc', -, hb, -⟩ |
          ⟨c', o, hc', -, -, h1, ho, h2⟩ | ⟨o, hn, -⟩
      · rw [hsi'] at hc'; cases hc'; exact absurd hn hcm
      · rw [hsi'] at hc'; cases hc'
        have : ¬ sint.Z g.Ballot < sint.Z c.ballot := by rw [← Hivf.1]; exact Hif
        simp [model.slt, acceptOf, this] at hb
      · rw [hsi'] at hc'; cases hc'; exact ⟨o, h1, h1 ▸ ho, h2⟩
      · rw [hsi'] at hn; cases hn
    ihave Hc : copyRep ρ xs (sint.Z g.Replica, sint.Z g.Instance) ip (acCopy c (acceptOf g)) $$ [Hiv Hlb]
    · iapply (copyRep_open ..).2
      iexists _
      iframe Hiv
      dsimp only
      simp only [acCopy_cmds, acCopy_lb]
      iframe Hlb
      isplitr
      · iapply (cmdsRep_open ..).2; iexists g.Command; iframe Hsl; ipureintro; exact ⟨rfl, hcmdsOk⟩
      ipureintro
      obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13⟩ := Hivf
      simp only [acCopy_ballot, acCopy_status, acCopy_seq, acCopy_deps, acCopy_base, acCopy_slot,
        acCopy_leader, acCopy_vbal, acceptOf]
      refine ⟨trivial, rfl, trivial, trivial, trivial, f6, f7, trivial, f9, f10, f11, f12, ?_⟩
      simp only [model.St.ACCEPTED, model.St.EXECUTED]
      constructor
      · intro h; cases h
      · intro h; exact absurd (f13.2 h) (fun e => hcm (.inr e))
    have hco : committedOrExecuted s (sint.Z g.Replica, sint.Z g.Instance) = false := by
      simp only [committedOrExecuted, model.committedCopy, BitVec.ofInt_toInt, hsi]
      split
      · simp only [hcm, ↓reduceIte, Option.isSome_none]
      · rfl
    have hbox2 : model.inBox g.Replica g.Instance = true := hbox
    icases Hclose with ⟨-, -, -, Ha⟩
    ihave Hep := Ha $$ %(acCopy c (acceptOf g)) [] Hrow Hc
    · ipureintro; refine ⟨rfl, ?_⟩
      have h2 := committedOrExecuted_setInst_self s g.Replica g.Instance (acCopy c (acceptOf g)) hbox2
      simp only [acCopy_status] at h2
      rw [hco]
      have h3 : ¬ (model.St.ACCEPTED = model.St.COMMITTED ∨ model.St.ACCEPTED = model.St.EXECUTED) := by
        decide
      rw [eq_false h3] at h2
      simpa using h2
    obtain ⟨S, hS⟩ : ∃ S, S = (acS1 s (acceptOf g)).setInst g.Replica g.Instance (acCopy c (acceptOf g)) :=
      ⟨_, rfl⟩
    rw [← hS] at ho ⊢
    have hsoS : sameOut s S := by
      rw [hS]; exact sameOut_trans (acS1_sameOut s _) (sameOut_setInst _ _ _ _)
    -- the tail: `recordInstanceMetadata(ISP[q][i])`, `sync`, the reply, the optimization off
    have hbox2 : model.inBox g.Replica g.Instance = true := hbox
    icases epaxosOwn_peek ρ h r xs S g.Replica g.Instance hbox2 $$ Hep with
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
    wp_apply (wp_sync h r gR) $$ [$HR' $HgR $HDur]
    ihave Hep := Hback $$ Hrow2
    ihave Hm : msgAt «$a1_ptr» (.acceptReply ⟨g.Replica, g.Instance, model.TRUE, g.Ballot⟩) $$ [«$a1»]
    · iapply (msgAt_acceptReply ..).2
      iexists _
      iframe «$a1»
      ipureintro
      simp only [acceptReplyOf]; rfl
    have ho' : model.sendPeer S g.LeaderId
        (.acceptReply ⟨g.Replica, g.Instance, model.TRUE, g.Ballot⟩) = some o := ho
    have hidS : S.id = rid32 k := by rw [hsoS.1]; exact Hid
    wp_apply (wp_replyAccept γ ρ k r gR h pa co t S hidS
      g.LeaderId «$a1_ptr» _ o [] ho') $$ [$Henv $Hm $Hpend] as ⟨-, Hpend⟩
    ihave #HbO := h2Fixed_bcastOpt k gR h $$ Hfix
    wp_auto
    obtain ⟨ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho8, ho9, -⟩ := hsoS
    iapply HΦ
    iframe Hpend
    iapply handler_close γ ρ k r gR h pa co xs S
    iframe Henv
    unfold parts
    rw [ho2, ho3, ho4, ho9]
    iframe Hparti Hval Hxs Hprop Hscr Hep
    isplitl
    · iapply coordOwn_congr ρ co _ k s _ ho5 ho6 ho7 ho8 $$ Hcoord
    · ipureintro; rw [ho1]; exact Hid

/-- **`handleAccept.wp`** (`Replica2/Specs.lean`), at its frozen statement. -/
theorem handleAccept_spec (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc)
    (m : model.EAcceptM) : epHandlerSpec γ ρ k r h go!"handleAccept" (.accept m) := by
  intro p t s s' outs hstep
  iintro %Φ ⟨#Hpkg, #Hrep, Hown, Hpend, Hh, Hmsg⟩ HΦ
  iapply (handleAccept_wp' γ ρ k r h p m t s s' outs hstep) $$ [Hown Hpend Hh Hmsg] HΦ
  iframe # ∗

end

end Perennial.gryff.replica2
