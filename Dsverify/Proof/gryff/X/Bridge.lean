/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/X/Bridge.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).
-/
module

public import Dsverify.Proof.gryff.X.Defs
public import Dsverify.Proof.gryff.Replica2.Specs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.X

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB RecoveryInstance Proposal Msg Ev Out Cmd Deps StepRes)
open Perennial.gryff.replica (XS rowOwn stackOwn euOwn nSlots)
open Perennial.gryff.replica2

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]

/-! The interface's sections declare `[G : GooseGlobalGS ..]` and `[hG : HeapGS ..]` apart: with
`hG.goose_globalGS = G` (request H-X-0, as stage 1's H-U2-7), `G` is `hG`'s, and every
abstraction predicate is its generic copy at `hG` (`rfl`). -/

theorem cmdsRep_eq (sl : GoSlice) (cs : List Cmd) :
    cmdsRep sl cs = cmdsRepG (hG := hG) sl cs := by
  unfold cmdsRep cmdsRepG; rfl

theorem writerIs_eq (ρ : Repl2Names) (cid : w32) (w : Loc) :
    writerIs ρ cid w = writerIsG (hG := hG) ρ cid w := by
  unfold writerIs writerIsG; rfl

theorem proposalRep_eq (ρ : Repl2Names) (pp : Loc) (pr : Proposal) :
    proposalRep ρ pp pr = proposalRepG (hG := hG) ρ pp pr := by
  unfold proposalRep proposalRepG; simp only [writerIs_eq]

theorem riRep_eq (l : Loc) (ri : Option RecoveryInstance) :
    riRep l ri = riRepG (hG := hG) l ri := by
  unfold riRep riRepG; cases ri <;> simp only [cmdsRep_eq]

theorem lbRep_eq (ρ : Repl2Names) (l : Loc) (lb : Option LB) :
    lbRep ρ l lb = lbRepG (hG := hG) ρ l lb := by
  unfold lbRep lbRepG proposalsRep proposalsRepG; cases lb <;> simp only [riRep_eq, proposalRep_eq]

theorem copyRep_eq (ρ : Repl2Names) (xs : XS) (n : replica.Node) (p : Loc) (c : Copy) :
    copyRep ρ xs n p c = copyRepG (hG := hG) ρ xs n p c := by
  unfold copyRep copyRepG; simp only [cmdsRep_eq, lbRep_eq]

theorem confRep_eq (mR : Loc) (o : Option w32) :
    confRep mR o = confRepG (hG := hG) mR o := by
  unfold confRep confRepG; rfl

theorem epaxosRest_eq (h : Loc) : epaxosRest h = epaxosRestG (hG := hG) h := by
  unfold epaxosRest epaxosRestG; rfl

theorem epaxosOwn_eq (ρ : Repl2Names) (h r : Loc) (xs : XS) (s : RState) :
    epaxosOwn ρ h r xs s = epaxosOwnG (hG := hG) ρ h r xs s := by
  unfold epaxosOwn epaxosOwnG instsG epFacts ptrElems; simp only [copyRep_eq, confRep_eq, epaxosRest_eq]

end
end Perennial.gryff.X
