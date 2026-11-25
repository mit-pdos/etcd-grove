/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/CoordForce.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1: the coordinator's `HandleForceWrite`.
-/
module

public import Dsverify.Proof.gryff.H1.Coord
public import Dsverify.GeneratedProof.gryff.examples.gryffnet
public import Dsverify.Proof.gryff.Replica2.Specs

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
variable [strconvA : strconv.Assumptions] -- N-5


theorem GryffCoordinator.HandleForceWrite.wp_proof (ρ : Repl2Names) (co : Loc) (ic : GoInterface)
    (k : Fin 3) (s : RState) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗ coordOwn ρ co ic k s }}
      (App (coordM co go!"HandleForceWrite") (Val #()))
    {{ RET #(); coordOwn ρ co ic k s }} := by
  simp only [coordM]
  wp_start as Hc
  icases (coordOwn_open ρ co ic k s).1 $$ Hc with
    ⟨%ropsR, %wopsR, %orR, %mtR, %fkR, %arS, #Hfix, Hmisc, %Hrk, Hr, Hw, Ho⟩
  unfold coordMisc
  icases Hmisc with ⟨%mst, %mat, %fkc, %mt, %fk, Hn, Hs, Ha, Hf, Hmt, Hfk, %Hmt0, Hmtm, Hfkc, %Hsrt⟩
  ihave %Hfl := ownSlice_len _ _ _ $$ Hfkc
  wp_auto
  wp_for
  wp_if_destruct
  · exfalso; simp at Hfl; word
  wp_apply wp_slice_make2 (V := w64) as %sl ⟨Hsl, -⟩
  · ipureintro; decide
  simp only [show sint.nat (W64 0) = 0 from rfl, List.replicate_zero]
  iapply HΦ
  iapply (coordOwn_open ρ co ic k s).2
  iexists ropsR, wopsR, orR, mtR, fkR, arS
  iframe Hfix Hr Hw Ho %Hrk
  unfold coordMisc
  iexists mst, mat, sl, mt, fk
  iframe Hn Hs Ha Hf Hmt Hfk Hmtm Hsl
  ipureintro; exact ⟨Hmt0, Hsrt⟩

end

end Perennial.gryff.replica2
