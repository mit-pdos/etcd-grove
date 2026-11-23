/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2c2/ExecOverwrite.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2c2: `executeOverwrite` (the executor's result: the store's overwrite, then the leader
learns the instance executed here)
-/
module

public import Dsverify.Proof.gryff.H2c2.Executed
public import Dsverify.Proof.gryff.H2a.Reply
public import Dsverify.Proof.gryff.H1.Iparti
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB Proposal Msg Ev Out Cmd Deps)
open Perennial.gryff.replica (XS rowOwn nSlots)

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem overwrite_eq (s : RState) (v : w64) (t : model.Tag) :
    s.overwrite v t = { s with val := (ovw s.storeVT v t).v, tag := (ovw s.storeVT v t).t } := by
  unfold model.RState.overwrite ovw model.RState.storeVT
  split <;> rfl

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF] -- H1-R6 / N-1
variable [sortA : Perennial.gryff.replica2.SortSliceHyp GF]
variable [strconvA : strconv.Assumptions] -- N-5


set_option goose.wp.extras true

theorem msgAt_executeOverwrite (p : Loc) (mm : model.ExecuteOverwriteM) :
    msgAt (GF := GF) p (.executeOverwrite mm) ⊣⊢ ∃ (eo : src.gryff.ExecuteOverwrite) (t : src.gryffproto.Tag),
      p ↦ eo ∗ eo.T' ↦□ t ∗ ⌜eo.K' = W64 0 ∧ mm = ⟨eo.V', tagOf t, eo.Leader', eo.Slot'⟩⌝ := by
  unfold msgAt; exact .rfl

theorem epaxosOwn_valTag (ρ : Repl2Names) (h r : Loc) (xs : XS) (s : RState) (v : w64)
    (t : model.Tag) :
    epaxosOwn (GF := GF) ρ h r xs s ⊢ epaxosOwn ρ h r xs { s with val := v, tag := t } := by
  unfold epaxosOwn; exact .rfl

set_option maxHeartbeats 4000000 in
theorem executeOverwrite_spec (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc)
    (m : model.ExecuteOverwriteM) :
    epHandlerSpec γ ρ k r h go!"executeOverwrite" (.executeOverwrite m) := by
  intro p t s s' outs hstep
  iintro %Φ ⟨#Hpkg, #Hrep, Hown, Hpend, Hh, Hmsg⟩ HΦ
  iunfold handlerOf at Hh
  icases Hh with #Hh
  icases (msgAt_executeOverwrite ..).1 $$ Hmsg with ⟨%eo, %gt, Hp, #Hgt, %Hm⟩
  obtain ⟨hK, rfl⟩ := Hm
  ihave HhO : handlerOf r h $$ []
  · unfold handlerOf; iexact Hh
  icases handler_open γ ρ k r h s $$ [$Hrep $HhO $Hown] with ⟨%gR, %pa, %co, %xs, #Henv, Hparts⟩
  unfold parts
  icases Hparts with ⟨Hparti, Hval, Hcoord, Hep, Hxs, Hprop, Hscr, %Hid⟩
  ihave #Henv' := Henv
  unfold epEnv
  icases Henv' with ⟨#HgR, #Hpa, #Hco, #Hh', #HR', #HId, #HN, #HDur, #Hgen, #Hfix⟩
  simp only [model.stepR, model.stepExecuteOverwrite] at hstep
  simp only [epM]
  wp_method_call
  wp_auto
  rw [hK]
  wp_method_call
  wp_auto
  -- integration (H1b-R2): `Replica_ipartiOk` moved to `Link`, takes `gryff`'s init and `h1Fixed`
  ihave #Hfix1 := genericOk_h1Fixed γ ρ k r gR h $$ Hgen
  ihave #Hip := Replica_ipartiOk_proof r gR $$ [$Hpkg $HgR $Hfix1]
  have hspec := GryffParticipant.HandleOverwrite.wp_proof pa (replicaIface r) k (valOwn (GF := GF) gR)
    s.storeVT s.ongoing eo.V' eo.T' gt
  simp only [partiM] at hspec
  rw [show s.tag = s.storeVT.t from rfl, show s.val = s.storeVT.v from rfl]
  wp_apply hspec $$ [$Hparti $Hip $Hval $Hgt] as ⟨Hparti, Hval⟩
  -- the handler's resources back, at the overwritten state
  generalize hs1 : s.overwrite eo.V' (tagOf gt) = s1 at hstep
  have hs1e := overwrite_eq s eo.V' (tagOf gt)
  rw [hs1] at hs1e
  have hid1 : s1.id = rid32 k := by rw [hs1e]; exact Hid
  ihave Hcoord := coordOwn_congr ρ co (replicaIface r) k s s1 (by rw [hs1e]) (by rw [hs1e])
    (by rw [hs1e]) (by rw [hs1e]) $$ Hcoord
  ihave Hep : epaxosOwn ρ h r xs s1 $$ [Hep]
  · rw [hs1e]; iapply epaxosOwn_valTag $$ Hep
  have ht1 : s1.tag = (ovw s.storeVT eo.V' (tagOf gt)).t := by rw [hs1e]
  have hv1 : s1.val = (ovw s.storeVT eo.V' (tagOf gt)).v := by rw [hs1e]
  have hp1 : s1.proposeQ = s.proposeQ := by rw [hs1e]
  have ho1 : s1.ongoing = s.ongoing := by rw [hs1e]
  ihave Hown : replicaOwn ρ k r s1 $$ [Hparti Hval Hcoord Hep Hxs Hprop Hscr]
  · iapply handler_close γ ρ k r gR h pa co xs s1
    isplitr
    · unfold epEnv; iframe #
    unfold parts
    rw [ht1, hv1, hp1, ho1]
    iframe Hparti Hval Hxs Hprop Hscr Hcoord Hep
    ipureintro; exact hid1
  wp_if_destruct
  · -- this replica leads the instance
    have hst : model.handleExecuted s1 ⟨eo.Leader', eo.Slot'⟩ = .ok (s', outs) := by
      simpa [hid1, Hif] using hstep
    h2c_printf
    ihave HhO : handlerOf r h $$ []
    · unfold handlerOf; iexact Hh
    wp_apply (handleExecuted_wp' γ ρ k r h _ _ t s1 s' outs hst ⟨eo.Leader', eo.Slot'⟩ rfl)
      $$ [$Hrep $Hown $Hpend $HhO $«$r0»] as Hfin
    iapply HΦ $$ Hfin
  · -- the leader is a peer: the notice
    simp only [hid1, Hif, ↓reduceIte] at hstep
    rcases hso : model.sendPeer s1 eo.Leader' (Msg.executed ⟨eo.Leader', eo.Slot'⟩) with _ | o
    · rw [hso] at hstep; cases hstep
    rw [hso] at hstep
    simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hstep
    obtain ⟨rfl, rfl⟩ := hstep
    obtain ⟨d, rfl, hld, hdk⟩ := sendPeer_some s1 k hid1 _ _ o hso
    ihave #Hbc : h2b.bcFixed γ ρ k r gR h $$ []
    · unfold h2b.bcFixed; iframe #
    ihave Hm : msgAt «$r0_ptr» (.executed ⟨eo.Leader', eo.Slot'⟩) $$ [«$r0»]
    · iapply (msgAt_executed ..).2; iexists _; iframe «$r0»; ipureintro; rfl
    wp_apply (h2b.replyExecuted_wp γ ρ k d r gR h t _ _ [] hdk _ hld) $$ [$Hbc $Hm $Hpend]
      as ⟨-, Hpend⟩
    iapply HΦ; iframe

end

end Perennial.gryff.replica2
