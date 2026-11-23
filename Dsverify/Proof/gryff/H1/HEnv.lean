/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/HEnv.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1d: the gryff handlers' environment: the replica's heap opened into the coordinator's
part and the coordinator's callback context (`coordCtx`), and closed back after a coordinator
step (`epf`: the step keeps the participant's ongoing writes, the id, the EPaxos part).
-/
module

public import Dsverify.Proof.gryff.H1.PureFrame
public import Dsverify.Proof.gryff.H1.Iparti
public import Dsverify.Proof.gryff.H1.CoordW1
public import Dsverify.Proof.gryff.H1.CoordRead1
public import Dsverify.Proof.gryff.H1.CoordStart
public import Dsverify.Proof.gryff.H1.CoordWrite
public import Dsverify.Proof.gryff.H1.CoordRead
public import Dsverify.Proof.gryff.H1.CoordForce
public import Dsverify.Proof.gryff.H1.Parti
public import Dsverify.Proof.gryff.H2.Env
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB RecoveryInstance Proposal ReadOp WriteOp OngoingOp
  Msg Ev Ext Out Cmd Deps AMap StepRes)
open Perennial.gryff.replica (XS)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]


/-! ### The message kinds -/

theorem msgAt_read1 (p : Loc) (mm : model.Read1ProxiedM) :
    msgAt (GF := GF) p (.read1 mm) ⊣⊢ ∃ g : src.gryffproto.Read1Proxied, p ↦ g ∗ ⌜read1Of g = mm⌝ := by
  unfold msgAt; exact .rfl
theorem msgAt_read2 (p : Loc) (mm : model.Read2ProxiedM) :
    msgAt (GF := GF) p (.read2 mm) ⊣⊢ ∃ g : src.gryffproto.Read2Proxied, p ↦ g ∗ ⌜read2Of g = mm⌝ := by
  unfold msgAt; exact .rfl
theorem msgAt_write1 (p : Loc) (mm : model.Write1ProxiedM) :
    msgAt (GF := GF) p (.write1 mm) ⊣⊢ ∃ g : src.gryffproto.Write1Proxied, p ↦ g ∗ ⌜write1Of g = mm⌝ := by
  unfold msgAt; exact .rfl
theorem msgAt_write2 (p : Loc) (mm : model.Write2ProxiedM) :
    msgAt (GF := GF) p (.write2 mm) ⊣⊢ ∃ g : src.gryffproto.Write2Proxied, p ↦ g ∗ ⌜write2Of g = mm⌝ := by
  unfold msgAt; exact .rfl
theorem msgAt_read1Reply (p : Loc) (mm : model.Read1ReplyM) :
    msgAt (GF := GF) p (.read1Reply mm) ⊣⊢ ∃ g : src.gryffproto.Read1Reply, p ↦ g ∗ ⌜read1ReplyOf g = mm⌝ := by
  unfold msgAt; exact .rfl
theorem msgAt_read2Reply (p : Loc) (mm : model.Read2ReplyM) :
    msgAt (GF := GF) p (.read2Reply mm) ⊣⊢ ∃ g : src.gryffproto.Read2Reply, p ↦ g ∗ ⌜read2ReplyOf g = mm⌝ := by
  unfold msgAt; exact .rfl
theorem msgAt_write1Reply (p : Loc) (mm : model.Write1ReplyM) :
    msgAt (GF := GF) p (.write1Reply mm) ⊣⊢
      ∃ g : src.gryffproto.Write1Reply, p ↦ g ∗ ⌜write1ReplyOf g = mm⌝ := by
  unfold msgAt; exact .rfl
theorem msgAt_write2Reply (p : Loc) (mm : model.Write2ReplyM) :
    msgAt (GF := GF) p (.write2Reply mm) ⊣⊢
      ∃ g : src.gryffproto.Write2Reply, p ↦ g ∗ ⌜write2ReplyOf g = mm⌝ := by
  unfold msgAt; exact .rfl

/-! ### Open and close -/

/-- **Open** the replica's heap (a gryff handler's first step). -/
theorem g_open (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc) (s : RState) :
    isReplica γ ρ k r ∗ replicaOwn ρ k r s ⊢
      ∃ (gR pa co h : Loc) (xs : XS), epEnv γ ρ k r gR h pa co ∗ parts ρ k r gR h pa co xs s := by
  iintro ⟨#Hrep, Hown⟩
  icases (isReplica_open ..).1 $$ Hrep with ⟨%gR, %h, Hex, -⟩
  icases (isExec_open ..).1 $$ Hex with ⟨%gR1, %mtx, %ex, %pp, -, #Hh, -⟩
  ihave Hh' : handlerOf r h $$ [Hh]
  · unfold handlerOf; iexact Hh
  icases handler_open γ ρ k r h s $$ [$Hrep $Hh' $Hown] with ⟨%gR', %pa, %co, %xs, #Henv, Hp⟩
  iexists gR', pa, co, h, xs
  iframe # ∗

/-- The fixed fields the gryff handlers read. -/
theorem epEnv_fields (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h pa co : Loc) :
    epEnv γ ρ k r gR h pa co ⊢ r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗
      r.[src.gryff.Replica, go!"parti"] ↦□ pa ∗ r.[src.gryff.Replica, go!"coord"] ↦□ co ∗
      gR.[src.genericsmr.Replica, go!"Id"] ↦□ rid32 k ∗ genericOk γ ρ k r gR h := by
  iintro #H
  unfold epEnv
  icases H with ⟨#HgR, #Hpa, #Hco, -, -, #HId, -, -, #Hgen, -⟩
  iframe #

/-- The rest of the replica's parts while the coordinator runs. -/
def cRest (ρ : Repl2Names) (r gR h : Loc) (xs : XS) (s : RState) : IProp GF :=
  iprop(epaxosOwn ρ h r xs s ∗ ghostVar ρ.xs (1 : Qp).half xs ∗ proposeOwn ρ gR s.proposeQ)

/-- The parts as the coordinator's state and its callbacks' context. -/
theorem coord_split (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h pa co : Loc)
    (xs : XS) (s : RState) (t : List Ev) (outs : List Out) :
    epEnv γ ρ k r gR h pa co ∗ parts ρ k r gR h pa co xs s ∗ pendingOuts γ ρ k r t outs ⊢
      coordOwn ρ co (replicaIface r) k s ∗
      coordCtx γ ρ k r pa t s.ongoing s.storeVT (outs ++ []) ∗ cRest ρ r gR h xs s ∗
      ⌜s.id = rid32 k⌝ := by
  simp only [coordCtx, model.RState.storeVT, List.append_nil]
  iintro ⟨#Henv, Hp, Hpend⟩
  unfold parts cRest
  icases Hp with ⟨Hpa, Hval, Hco, Hep, Hxs, Hprop, Hscr, %Hid⟩
  icases epEnv_fields γ ρ k r gR h pa co $$ Henv with ⟨#HgR, -⟩
  iframe Hco Hep Hxs Hprop
  isplitl [Hpa Hval Hscr Hpend]
  · iexists gR
    iframe # ∗
  · ipureintro; exact Hid

/-- **Close** after a coordinator step that keeps the rest (`epf`). -/
theorem coord_close (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h pa co : Loc)
    (xs : XS) (s s' : RState) (t : List Ev) (hf : epf s' = epf s) (hid : s.id = rid32 k) :
    epEnv γ ρ k r gR h pa co ∗ cRest ρ r gR h xs s ∗ coordOwn ρ co (replicaIface r) k s' ∗
      coordCtx γ ρ k r pa t s.ongoing s'.storeVT [] ⊢
      replicaOwn ρ k r s' ∗ pendingOuts γ ρ k r t [] := by
  simp only [epf, Prod.mk.injEq] at hf
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hf
  simp only [coordCtx, model.RState.storeVT]
  iintro ⟨#Henv, Hrest, Hco, HC⟩
  unfold cRest
  icases Hrest with ⟨Hep, Hxs, Hprop⟩
  icases HC with ⟨%gR', #HgR', Hpa, Hval, Hscr, Hpend⟩
  icases epEnv_fields γ ρ k r gR h pa co $$ Henv with ⟨#HgR, -⟩
  icombine HgR HgR' gives %HgReq
  subst HgReq
  iframe Hpend
  iapply handler_close γ ρ k r gR h pa co xs s'
  iframe Henv
  unfold parts
  rw [h1, h9]
  ihave Hep := epaxosOwn_congr ρ h r xs s s' h3 h4 h5 h6 h7 h8 $$ Hep
  iframe Hpa Hval Hco Hep Hxs Hprop Hscr
  ipureintro; rw [h2]; exact hid

end

end Perennial.gryff.replica2
