/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/Iparti.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1b: `*gryff.Replica` implements `IGryffParticipant` (`ipartiOk`).
-/
module

public import Dsverify.Proof.gryff.H1.CoordW2
public import Dsverify.GeneratedProof.gryff.examples.gryffnet
public import Dsverify.Proof.gryff.Lib.SortHyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB RecoveryInstance Proposal ReadOp WriteOp OngoingOp
  Msg Ev Ext Out Cmd Deps AMap StepRes)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF]
variable [sortA : SortSliceHyp GF]
variable [strconvA : strconv.Assumptions] -- N-5


set_option goose.wp.extras true

/-- `Replica_ipartiOk` with the premises its callbacks need (hub request H1b-R2): `gryff`'s
initialization (`Printf` reads `dlog.DLOG`) and the generic replica's `Stats` (`GetStats`). -/
theorem Replica_ipartiOk_proof (r gR : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
      r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ □ h1Fixed r gR ⊢
      ipartiOk (replicaIface r) (valOwn gR) := by
  iintro ⟨#Hpkg, #HgR, #Hfix⟩
  unfold ipartiOk specT
  isplitr
  · iintro %v !> %Φ HV HΦ
    unfold valOwn
    icases HV with ⟨%st, %smR, %sm, #Hex, #Hst, #Hsto, Hsm, %Hsm0⟩
    simp only [replicaIface]
    wp_auto
    wp_method_call
    wp_call
    wp_auto
    wp_apply wp_map_lookup1 $$ Hsm as Hsm
    iapply HΦ
    rw [show zero_val w64 = W64 0 from rfl, Hsm0.2]
    isplitl []
    · ipureintro; rfl
    iexists st, smR, sm
    iframe Hex Hst Hsto Hsm
    ipureintro; exact Hsm0
  isplitr
  · iintro %v %v' !> %Φ HV HΦ
    unfold valOwn
    icases HV with ⟨%st, %smR, %sm, #Hex, #Hst, #Hsto, Hsm, %Hsm0⟩
    simp only [replicaIface]
    wp_auto
    wp_method_call
    wp_call
    wp_auto
    wp_apply wp_mapInsert $$ Hsm as Hsm
    iapply HΦ
    isplitl []
    · ipureintro; rfl
    iexists st, smR, _
    iframe Hex Hst Hsto Hsm
    ipureintro
    refine ⟨fun kk hk => ?_, ?_⟩
    · change (<[W64 0 := v']> sm) !! kk = none
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)]; exact Hsm0.1 kk hk
    · change ((<[W64 0 := v']> sm) !! W64 0).getD (W64 0) = v'
      rw [GMap.lookup_insert]; rfl
  isplitr
  · iintro %f %a !> %Φ - HΦ
    simp only [replicaIface]
    wp_auto
    ihave #Hdl : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.dlog $$ []
    · iPkgInit
    ihave #Hdlog := replica.dlog_init_access $$ Hdl
    wp_apply wp_Replica_Printf $$ [$Hdlog]
    iapply HΦ
    isplitl []
    · ipureintro; rfl
    itrivial
  isplitr
  · iintro !> %Φ - HΦ
    simp only [replicaIface]
    wp_auto
    wp_method_call
    wp_call
    unfold h1Fixed
    icases Hfix with ⟨%st, %cR1, %cR2, %cW1, %cW2, %cR1R, %cR2R, %cW1R, %cW2R, #Hst, #Hsok, -⟩
    wp_auto
    iapply HΦ
    iexists st
    iframe Hsok
    ipureintro; rfl
  isplitr
  · iintro %c %w !> %Φ HF
    iexfalso; iexact HF
  · iintro %w !> %Φ HF
    iexfalso; iexact HF

end

end Perennial.gryff.replica2
