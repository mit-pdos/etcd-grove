/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/Icoord.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Units H1c, H1e: `*gryff.Replica` implements `IGryffCoordinator` (`icoordOk` over `coordCtx`).
-/
module

public import Dsverify.Proof.gryff.H1.Iparti
public import Dsverify.Proof.gryff.H1.Parti
public import Dsverify.Proof.gryff.N.Reply
public import Dsverify.Proof.gryff.H1.Send
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

/-- The frozen `Replica_icoordOk` with H1b-R2's premise (`isPkgInit gryff`). -/
theorem Replica_icoordOk_proof (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r pa : Loc)
    (t : List Ev) (ong : AMap 32 w32) :
    isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
      isReplica γ ρ k r ∗ r.[src.gryff.Replica, go!"parti"] ↦□ pa ⊢
      icoordOk ρ (replicaIface r) k (coordCtx γ ρ k r pa t ong) := by
  iintro ⟨#Hpkg, #Hrep, #Hpa⟩
  icases (isReplica_open ..).1 $$ Hrep with ⟨%gR0, %h, -, #HgR0, -, -, -, -, -, -, -, #Hgen⟩
  ihave #Hfix := genericOk_h1Fixed γ ρ k r gR0 h $$ Hgen
  unfold icoordOk specT
  isplitr
  · iintro %rop %ro %sl %rs %vt %outs %o %Hs !> %Φ ⟨HC, Hrop, Hsl⟩ HΦ
    simp only [replicaIface]
    wp_auto
    wp_apply wp_Replica_SendRead1 γ ρ k r pa t ong rop ro sl rs vt outs o Hs $$
      [$Hpkg $Hrep $Hpa $HC $Hrop $Hsl] as ⟨HC, Hrop, Hsl⟩
    iapply HΦ
    iframe HC Hrop Hsl
    ipureintro; rfl
  isplitr
  · iintro %rop %ro %rv %sl %rs %vt %outs %o %Hs !> %Φ ⟨HC, Hrop, Hsl⟩ HΦ
    simp only [replicaIface]
    wp_auto
    wp_apply wp_Replica_SendRead2 γ ρ k r pa t ong rop ro rv sl rs vt outs o Hs.1 Hs.2 $$
      [$Hpkg $Hrep $HC $Hrop $Hsl] as ⟨HC, Hrop, Hsl⟩
    iapply HΦ
    iframe HC Hrop Hsl
    ipureintro; rfl
  isplitr
  · iintro %co %wop %wo %mat %sl %rs %vt %outs %o %Hs !> %Φ ⟨HC, Hwop, Hco, #Hsl⟩ HΦ
    simp only [replicaIface]
    wp_auto
    wp_apply wp_Replica_SendWrite1 γ ρ k r pa t ong co wop wo mat sl rs vt outs o Hs $$
      [$Hpkg $Hrep $HC $Hwop $Hco $Hsl] as ⟨HC, Hwop, Hco⟩
    iapply HΦ
    iframe HC Hwop Hco
    ipureintro; rfl
  isplitr
  · iintro %co %wop %wo %wt %sl %rs %vt %outs %o %Hs !> %Φ ⟨HC, Hwop, #Hsl⟩ HΦ
    simp only [replicaIface]
    wp_auto
    wp_apply wp_Replica_SendWrite2 γ ρ k r pa t ong co wop wo wt sl rs vt outs o Hs.1 Hs.2 $$
      [$Hpkg $Hrep $HC $Hwop $Hsl] as ⟨HC, Hwop⟩
    iapply HΦ
    iframe HC Hwop
    ipureintro; rfl
  isplitr
  · iintro %rid %cid %v %vt %o %w !> %Φ ⟨HC, #Hw⟩ HΦ
    unfold coordCtx
    icases HC with ⟨%gR, #HgR, Hpo, HV, Hsc, Hpend⟩
    icombine HgR HgR0 gives %HeqR
    subst HeqR
    simp only [replicaIface]
    wp_auto
    rw [show (1 : w8) = W8 1 from rfl]
    wp_apply CompleteRead_wp γ ρ k r gR h t cid rid w v o $$ [$Hpkg $Hgen $HgR $Hw $Hpend] as Hpend
    iapply HΦ
    isplitl []
    · ipureintro; rfl
    iexists gR
    iframe HgR Hpo HV Hsc Hpend
  isplitr
  · iintro %rid %cid %vt %o %w !> %Φ ⟨HC, #Hw⟩ HΦ
    unfold coordCtx
    icases HC with ⟨%gR, #HgR, Hpo, HV, Hsc, Hpend⟩
    icombine HgR HgR0 gives %HeqR
    subst HeqR
    simp only [replicaIface]
    wp_auto
    rw [show (1 : w8) = W8 1 from rfl]
    wp_apply CompleteWrite_wp γ ρ k r gR h t cid rid w o $$ [$Hpkg $Hgen $HgR $Hw $Hpend] as Hpend
    iapply HΦ
    isplitl []
    · ipureintro; rfl
    iexists gR
    iframe HgR Hpo HV Hsc Hpend
  isplitr
  · iintro %v %tp %gt %vt %o !> %Φ ⟨HC, #Htp⟩ HΦ
    unfold coordCtx
    icases HC with ⟨%gR, #HgR, Hpo, HV, Hsc, Hpend⟩
    icombine HgR HgR0 gives %HeqR
    subst HeqR
    ihave #Hip := Replica_ipartiOk_proof r gR $$ [Hpkg HgR Hfix]
    · iframe Hpkg HgR Hfix
    ihave #Hpc : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon $$ []
    · iPkgInit
    simp only [replicaIface] at *
    wp_auto
    wp_method_call
    wp_call
    wp_auto
    wp_apply GryffParticipant.HandleOverwrite.wp_proof $$ [$Hpc $Hpo $Hip $HV $Htp] as ⟨Hpo, HV⟩
    iapply HΦ
    isplitl []
    · ipureintro; rfl
    iexists gR
    iframe HgR Hpo HV Hsc Hpend
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
  · iintro !> %Φ HF
    iexfalso; iexact HF
  isplitr
  · iintro %w !> %Φ HF
    iexfalso; iexact HF
  · iintro !> %Φ HF
    iexfalso; iexact HF

end

end Perennial.gryff.replica2
