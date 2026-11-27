/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2/Attr.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2: `updateAttributes`, `updateConflicts`, `updateCommitted` (and, re-exported, `mergeAttributes` (`H2a/Merge.lean`), `equal` (`H2a/Equal.lean`))
-/
module

public import Dsverify.Proof.gryff.H2a.AttrEnv
public import Dsverify.Proof.gryff.H2a.Conf
public import Dsverify.Proof.gryff.H2a.UpdAttr
public import Dsverify.Proof.gryff.H2a.Commit
public import Dsverify.Proof.gryff.H2a.Merge
public import Dsverify.Proof.gryff.H2a.Equal
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

/-- `updateAttributes(cmds, seq, deps, replica, instance)`. -/
theorem wp_updateAttributes (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc) (xs : XS) (s : RState)
    (sl : GoSlice) (gs : List src.state.Command) (seq : w32) (deps : GoArray w32 5)
    (replica inst : w32) (res : w32 × Deps × Bool)
    (hcs : model.cmdsOk (gs.map cmdOf) = true) (hrep : 0 ≤ sint.Z replica ∧ sint.Z replica < 3)
    (hid : s.id = rid32 k)
    (hres : model.updateAttributes s (gs.map cmdOf) seq (depsOf deps) replica = some res) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ attrEnv k r gR h ∗
        epaxosOwn ρ h r xs s ∗ sl ↦*□ gs }}
      (App (App (App (App (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!!
        go!"updateAttributes")) (Val #sl)) (Val #seq)) (Val #deps)) (Val #replica)) (Val #inst))
    {{ (seq' : w32) (deps' : GoArray w32 5) (ch : Bool), RET (PairV (PairV #seq' #deps') #ch);
        epaxosOwn ρ h r xs s ∗ ⌜res = (seq', depsOf deps', ch)⌝ }} := by
  exact wp_updateAttributes' ρ k r gR h xs s sl gs seq deps replica inst res hcs hrep hid hres

/-- `updateConflicts(cmds, replica, instance, seq)`. -/
theorem wp_updateConflicts (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc) (xs : XS) (s : RState)
    (sl : GoSlice) (gs : List src.state.Command) (replica inst seq : w32)
    (hcs : model.cmdsOk (gs.map cmdOf) = true) (hrep : 0 ≤ sint.Z replica ∧ sint.Z replica < 3) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ attrEnv k r gR h ∗
        epaxosOwn ρ h r xs s ∗ sl ↦*□ gs }}
      (App (App (App (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!!
        go!"updateConflicts")) (Val #sl)) (Val #replica)) (Val #inst)) (Val #seq))
    {{ RET #(); epaxosOwn ρ h r xs (model.updateConflicts s (gs.map cmdOf) replica inst seq) }} := by
  exact wp_updateConflicts' ρ k r gR h xs s sl gs replica inst seq hcs hrep

/-- `updateCommitted(replica)` (`replica` a valid row; the model's `updateCommitted` is not `dead`). -/
theorem wp_updateCommitted (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc) (xs : XS) (s s' : RState)
    (q : w32) (hq : 0 ≤ sint.Z q ∧ sint.Z q < 3) (hres : model.updateCommitted s q = some s') :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ attrEnv k r gR h ∗
        epaxosOwn ρ h r xs s }}
      (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!! go!"updateCommitted"))
        (Val #q))
    {{ RET #(); epaxosOwn ρ h r xs s' }} :=
  wp_updateCommitted' ρ k r gR h xs s s' q hq hres

end

end Perennial.gryff.replica2
