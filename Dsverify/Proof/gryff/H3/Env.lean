/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H3/Env.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H3: a handler's environment (a copy of unit H2's `H2/Env.lean`, in namespace `h3`, so
that H3 does not depend on H2's files while they follow the stage-2 hub changes; to be replaced by
H2's once merged)

`handler_open`: the replica's handle, its handler, its heap opened into the persistent fields
(`epEnv`) and the packages' parts; `handler_close` puts the heap back at a new state.
-/
module

public import Dsverify.Proof.gryff.Replica2.Specs
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2.h3

open Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB Proposal Msg Ev Out Cmd Deps)
open Perennial.gryff.replica (XS rowOwn nSlots)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics] [fa : src.fastrpc.Assumptions]
variable [gA : examples.gryffnet.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF]
variable [strconvA : strconv.Assumptions] -- N-5


/-- A command slice is persistent (unfolds `cmdsRep`). -/
instance h3_cmdsRep_persistent (sl : GoSlice) (cs : List Cmd) :
    Persistent (cmdsRep sl cs : IProp GF) := by
  unfold cmdsRep; infer_instance

/-- `copyRep`, unfolded (State's definition). -/
theorem copyRep_open (ρ : Repl2Names) (xs : XS) (n : replica.Node) (p : Loc) (c : Copy) :
    copyRep (GF := GF) ρ xs n p c ⊣⊢ ∃ iv : src.gryff.Instance, p ↦ iv ∗ cmdsRep iv.Cmds' c.cmds ∗
      lbRep ρ iv.lb' c.lb ∗
      ⌜iv.ballot' = c.ballot ∧ iv.Status' = c.status ∧ iv.Seq' = c.seq ∧
        depsOf iv.Deps' = c.deps ∧ vtOf iv.Base' = c.base ∧ iv.Slot' = c.slot ∧
        iv.Leader' = c.leader ∧ iv.vbal' = c.vbal ∧
        sint.Z iv.Leader' = n.1 ∧ sint.Z iv.Slot' = n.2 ∧
        sint.Z iv.Index' = xs.numF n ∧ sint.Z iv.Lowlink' = xs.lowF n ∧
        (c.status = model.St.EXECUTED ↔ n ∈ xs.1)⌝ := by
  unfold copyRep; exact .rfl

/-- Whether slot `(q, i)` (in the box) is committed or executed at `s`. -/
theorem coe_slot (s : RState) (q i : w32) (hb : model.inBox q i = true) :
    committedOrExecuted s (sint.Z q, sint.Z i) =
      match s.inst q i with
      | some c => decide (c.status = model.St.COMMITTED ∨ c.status = model.St.EXECUTED)
      | none => false := by
  simp only [model.inBox, decide_eq_true_eq] at hb
  have hq : BitVec.ofInt 32 (sint.Z q) = q := BitVec.ofInt_toInt
  have hi : BitVec.ofInt 32 (sint.Z i) = i := BitVec.ofInt_toInt
  simp only [committedOrExecuted, model.committedCopy, hq, hi, if_pos hb]
  rcases s.inst q i with _ | c
  · rfl
  · by_cases h : c.status = model.St.COMMITTED ∨ c.status = model.St.EXECUTED <;> simp [h]

theorem coe_setInst (s : RState) (q i : w32) (c : Copy) (hb : model.inBox q i = true) :
    committedOrExecuted (s.setInst q i c) (sint.Z q, sint.Z i) =
      decide (c.status = model.St.COMMITTED ∨ c.status = model.St.EXECUTED) := by
  rw [coe_slot _ q i hb]; simp [RState.setInst]

/-- The fixed fields a handler reads (persistent). -/
def epEnv (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h pa co : Loc) : IProp GF :=
  iprop(r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ r.[src.gryff.Replica, go!"parti"] ↦□ pa ∗
    r.[src.gryff.Replica, go!"coord"] ↦□ co ∗
    r.[src.gryff.Replica, go!"rmwHandler"] ↦□ handlerIface h ∗
    h.[src.gryff.EPaxosRMWHandler, go!"R"] ↦□ r ∗
    gR.[src.genericsmr.Replica, go!"Id"] ↦□ rid32 k ∗
    gR.[src.genericsmr.Replica, go!"N"] ↦□ W64 3 ∗
    gR.[src.genericsmr.Replica, go!"Durable"] ↦□ false ∗
    genericOk γ ρ k r gR h ∗ □ h2Fixed k gR h)

instance epEnv_persistent (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h pa co : Loc) :
    Persistent (epEnv γ ρ k r gR h pa co) := by
  unfold epEnv; infer_instance

theorem handlerOf_open (r h : Loc) :
    handlerOf (GF := GF) r h ⊣⊢ r.[src.gryff.Replica, go!"rmwHandler"] ↦□ handlerIface h := by
  unfold handlerOf; exact .rfl

/-- The replica's parts at state `s` (the heap with its packages' parts named). -/
def parts (ρ : Repl2Names) (k : Fin 3) (r gR h pa co : Loc) (xs : XS) (s : RState) : IProp GF :=
  iprop(partiOwn pa (replicaIface r) k s.tag s.ongoing ∗ valOwn gR s.val ∗
    coordOwn ρ co (replicaIface r) k s ∗ epaxosOwn ρ h r xs s ∗
    ghostVar ρ.xs (1 : Qp).half xs ∗ proposeOwn ρ gR s.proposeQ ∗ scratchOwn r ∗
    ⌜s.id = rid32 k⌝)

/-- **Open** a handler's resources. -/
theorem handler_open (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc) (s : RState) :
    isReplica γ ρ k r ∗ handlerOf r h ∗ replicaOwn ρ k r s ⊢
      ∃ (gR pa co : Loc) (xs : XS), epEnv γ ρ k r gR h pa co ∗ parts ρ k r gR h pa co xs s := by
  iintro ⟨Hrep, Hh, Hown⟩
  unfold replicaOwn
  icases Hown with ⟨%xs, Hown⟩
  icases (isReplica_open ..).1 $$ Hrep with
    ⟨%gR, %h1, Hex, #HgR, -, -, -, -, -, #HDur, -, Hgen⟩
  icases (isExec_open ..).1 $$ Hex with
    ⟨%gR1, %mtx, %ex, %pp, #HgR1, #Hh1, -, -, -, #HR, -, -, #HId, #HN, -, -, -, -, -, -⟩
  icombine HgR HgR1 gives %HgReq
  subst HgReq
  icases (handlerOf_open ..).1 $$ Hh with #Hh
  icombine Hh Hh1 gives %Hheq
  have hinj : ∀ a b : Loc, handlerIface a = handlerIface b → a = b := by
    intro a b H
    simp only [handlerIface, interface.mkOk, GoInterface.ok.injEq] at H
    injection H with _ hv
    exact go.intoVal_inj hv
  obtain rfl := (hinj _ _ Hheq).symm
  icases (replicaOwnX_split ..).1 $$ Hown with
    ⟨%gR2, %pa, %co, %h2, #HgR2, #Hpa, #Hco, #Hh2, Hpa, Hval, Hco, Hep, Hxs, Hprop, Hscr, %Hid⟩
  icombine HgR HgR2 gives %HgReq2
  subst HgReq2
  icombine Hh Hh2 gives %Hheq2
  obtain rfl := hinj _ _ Hheq2
  ihave #Hfix := genericOk_h2Fixed γ ρ k r gR h1 $$ Hgen
  iexists gR, pa, co, xs
  isplitl [Hgen]
  · unfold epEnv
    iframe # ∗
  · unfold parts
    iframe
    ipureintro; exact Hid

/-- **Close**: the parts at a new state are the replica's heap. -/
theorem handler_close (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h pa co : Loc)
    (xs : XS) (s : RState) :
    epEnv γ ρ k r gR h pa co ∗ parts ρ k r gR h pa co xs s ⊢ replicaOwn ρ k r s := by
  iintro ⟨#Henv, Hp⟩
  unfold epEnv parts
  icases Henv with ⟨#HgR, #Hpa, #Hco, #Hh, -⟩
  icases Hp with ⟨Hpa', Hval, Hco', Hep, Hxs, Hprop, Hscr, %Hid⟩
  unfold replicaOwn
  iexists xs
  iapply (replicaOwnX_split ..).2
  iexists gR, pa, co, h
  iframe # ∗
  ipureintro; exact Hid

end

end Perennial.gryff.replica2.h3
