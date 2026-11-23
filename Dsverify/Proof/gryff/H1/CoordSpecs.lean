/-
The coordinator's methods' triples (`gryffcommon/coordinator.go`), as specs (CLAUDE.md, "Import
tiers": a proof sees its callees through their specs only).

* `GryffSCDeps`: `ShortCircuit` (its triple over the opened coordinator, `ShortCircuit.specInt`),
  which `HandleWrite1Reply` and `HandleWrite2Reply` call (`CoordW1`, `CoordW2`).
* `GryffCoordDeps`: the methods the replica's handlers call (`GCoord`): `StartRead`, `StartWrite`,
  `HandleRead1Reply`, `HandleRead2Reply`, `HandleWrite1Reply`, `HandleWrite2Reply`,
  `HandleForceWrite`.

`Replica2/Results.lean` closes both with the `H1/Coord*.lean` proofs (`gryffSCDeps_holds`,
`gryffCoordDeps_holds`, local instances there). No `instance` of these classes exists.
-/
module

public import Dsverify.Proof.gryff.H1.CoordSCDefs
public import Dsverify.GeneratedProof.gryff.examples.gryffnet
public import Dsverify.Proof.gryff.Lib.SortHyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

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

attribute [-instance] go.InterfaceSemantics.method_interface_ok in
/-- The triple of `H1/CoordSC.lean`'s `GryffCoordinator.ShortCircuit.wp_int`. -/
def GryffCoordinator.ShortCircuit.specInt : Prop :=
  ∀ (ρ : Repl2Names) (co : Loc) (ic : GoInterface) (k : Fin 3)
     (C : model.ValTag → List Out → IProp GF) (s s' : RState) (outs o : List Out)
     (vt : model.ValTag) (n : w32) (vp : Loc) (gv : src.gryffproto.ValTag) (fo : Bool)
     (ropsR wopsR orR mtR fkR : Loc) (arS : GoSlice)
     (hsc : model.shortCircuit s n (vtOf gv) fo = some (s', outs)) (hrk : ropsKeyed s.rops),
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗
        coordFix co ic k ropsR wopsR orR mtR fkR arS ∗
        amapRep ropsR s.rops (fun p r => readOpRep ρ p r) ∗ amapRep orR s.ongoingReqs ongoingOpRep ∗
        icoordOk ρ ic k C ∗ C vt (outs ++ o) ∗ vp ↦□ gv }}
      (App (App (App (coordM co go!"ShortCircuit") (Val #n)) (Val #vp)) (Val #fo))
    {{ RET #(); scPost ρ ropsR orR s' ∗ C vt o }}

attribute [-instance] go.InterfaceSemantics.method_interface_ok in
/-- The triple of `H1/CoordStart.lean`'s `GryffCoordinator.StartRead.wp_proof`. -/
def GryffCoordinator.StartRead.spec : Prop :=
  ∀ (ρ : Repl2Names) (co : Loc) (ic : GoInterface) (k : Fin 3)
     (C : model.ValTag → List Out → IProp GF) (s s' : RState) (outs o : List Out) (rid cid : w32)
     (dp w : Loc) (gd : src.gryffproto.Dep) (hid : s.id = rid32 k)
     (hstep : model.stepR k s (.read rid cid 0 (depOf gd)) = .ok (s', outs)),
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗ coordOwn ρ co ic k s ∗
        icoordOk ρ ic k C ∗ C s.storeVT (outs ++ o) ∗ dp ↦□ gd ∗ writerIs ρ cid w }}
      (App (App (App (App (coordM co go!"StartRead") (Val #rid)) (Val #cid)) (Val #(W64 0)))
        (Val #dp))
    {{ RET #(); coordOwn ρ co ic k s' ∗ C s'.storeVT o }}

attribute [-instance] go.InterfaceSemantics.method_interface_ok in
/-- The triple of `H1/CoordWrite.lean`'s `GryffCoordinator.StartWrite.wp_proof`. -/
def GryffCoordinator.StartWrite.spec : Prop :=
  ∀ (ρ : Repl2Names) (co : Loc) (ic : GoInterface) (k : Fin 3)
     (C : model.ValTag → List Out → IProp GF) (s s' : RState) (outs o : List Out) (rid cid : w32)
     (v : w64) (dp w : Loc) (gd : src.gryffproto.Dep) (hid : s.id = rid32 k)
     (hstep : model.stepR k s (.write rid cid 0 v (depOf gd)) = .ok (s', outs)),
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗ coordOwn ρ co ic k s ∗
        icoordOk ρ ic k C ∗ C s.storeVT (outs ++ o) ∗ dp ↦□ gd ∗ writerIs ρ cid w }}
      (App (App (App (App (App (coordM co go!"StartWrite") (Val #rid)) (Val #cid))
        (Val #(W64 0))) (Val #v)) (Val #dp))
    {{ RET #(); coordOwn ρ co ic k s' ∗ C s'.storeVT o }}

attribute [-instance] go.InterfaceSemantics.method_interface_ok in
/-- The triple of `H1/CoordRead1.lean`'s `GryffCoordinator.HandleRead1Reply.wp_proof`. -/
def GryffCoordinator.HandleRead1Reply.spec : Prop :=
  ∀ (ρ : Repl2Names) (co : Loc) (ic : GoInterface) (k : Fin 3)
     (C : model.ValTag → List Out → IProp GF) (s s' : RState) (outs o : List Out)
     (m : model.Read1ReplyM) (vp : Loc) (gv : src.gryffproto.ValTag) (hv : vtOf gv = m.vt)
     (hid : s.id = rid32 k) (hstep : model.stepR k s (.msg (.read1Reply m)) = .ok (s', outs)),
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗ coordOwn ρ co ic k s ∗
        icoordOk ρ ic k C ∗ C s.storeVT (outs ++ o) ∗ vp ↦□ gv }}
      (App (App (App (coordM co go!"HandleRead1Reply")
        (Val #(model.shiftInts m.requestId m.clientId))) (Val #vp)) (Val #m.replicaId))
    {{ RET #(); coordOwn ρ co ic k s' ∗ C s'.storeVT o }}

attribute [-instance] go.InterfaceSemantics.method_interface_ok in
/-- The triple of `H1/CoordRead.lean`'s `GryffCoordinator.HandleRead2Reply.wp_proof`. -/
def GryffCoordinator.HandleRead2Reply.spec : Prop :=
  ∀ (ρ : Repl2Names) (co : Loc) (ic : GoInterface) (k : Fin 3)
     (C : model.ValTag → List Out → IProp GF) (s s' : RState) (outs o : List Out)
     (m : model.Read2ReplyM) (gt : src.gryffproto.Tag) (rep : w32)
     (hstep : model.stepR k s (.msg (.read2Reply m)) = .ok (s', outs)),
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗ coordOwn ρ co ic k s ∗
        icoordOk ρ ic k C ∗ C s.storeVT (outs ++ o) }}
      (App (App (App (coordM co go!"HandleRead2Reply")
        (Val #(model.shiftInts m.requestId m.clientId))) (Val #gt)) (Val #rep))
    {{ RET #(); coordOwn ρ co ic k s' ∗ C s'.storeVT o }}

attribute [-instance] go.InterfaceSemantics.method_interface_ok in
/-- The triple of `H1/CoordW1.lean`'s `GryffCoordinator.HandleWrite1Reply.wp_proof`. -/
def GryffCoordinator.HandleWrite1Reply.spec : Prop :=
  ∀ (ρ : Repl2Names) (co : Loc) (ic : GoInterface) (k : Fin 3)
     (C : model.ValTag → List Out → IProp GF) (s s' : RState) (outs o : List Out)
     (m : model.Write1ReplyM) (rep : w32) (vp : Loc) (gv : src.gryffproto.ValTag)
     (hv : vtOf gv = m.vt) (hid : s.id = rid32 k)
     (hstep : model.stepR k s (.msg (.write1Reply m)) = .ok (s', outs)),
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗ coordOwn ρ co ic k s ∗
        icoordOk ρ ic k C ∗ C s.storeVT (outs ++ o) ∗ vp ↦□ gv }}
      (App (App (App (App (coordM co go!"HandleWrite1Reply")
        (Val #(model.shiftInts m.requestId m.clientId))) (Val #m.clientId)) (Val #rep)) (Val #vp))
    {{ RET #(); coordOwn ρ co ic k s' ∗ C s'.storeVT o }}

attribute [-instance] go.InterfaceSemantics.method_interface_ok in
/-- The triple of `H1/CoordW2.lean`'s `GryffCoordinator.HandleWrite2Reply.wp_proof`. -/
def GryffCoordinator.HandleWrite2Reply.spec : Prop :=
  ∀ (ρ : Repl2Names) (co : Loc) (ic : GoInterface) (k : Fin 3)
     (C : model.ValTag → List Out → IProp GF) (s s' : RState) (outs o : List Out)
     (m : model.Write2ReplyM) (rep : w32) (tp : Loc)
     (hstep : model.stepR k s (.msg (.write2Reply m)) = .ok (s', outs)),
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗ coordOwn ρ co ic k s ∗
        icoordOk ρ ic k C ∗ C s.storeVT (outs ++ o) }}
      (App (App (App (App (App (coordM co go!"HandleWrite2Reply")
        (Val #(model.shiftInts m.requestId m.clientId))) (Val #rep)) (Val #tp))
        (Val #m.clientId)) (Val #m.applied))
    {{ RET #(); coordOwn ρ co ic k s' ∗ C s'.storeVT o }}

/-- The triple of `H1/CoordForce.lean`'s `GryffCoordinator.HandleForceWrite.wp_proof`. -/
def GryffCoordinator.HandleForceWrite.spec : Prop :=
  ∀ (ρ : Repl2Names) (co : Loc) (ic : GoInterface) (k : Fin 3) (s : RState),
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗ coordOwn ρ co ic k s }}
      (App (coordM co go!"HandleForceWrite") (Val #()))
    {{ RET #(); coordOwn ρ co ic k s }}

/-- `ShortCircuit`, which the write replies call (the file header). -/
class GryffSCDeps : Prop where
  shortCircuit : GryffCoordinator.ShortCircuit.specInt (GF := GF) (hG := hG)

/-- The coordinator's methods the replica's handlers call (the file header). -/
class GryffCoordDeps : Prop where
  startRead : GryffCoordinator.StartRead.spec (GF := GF) (hG := hG)
  startWrite : GryffCoordinator.StartWrite.spec (GF := GF) (hG := hG)
  handleRead1Reply : GryffCoordinator.HandleRead1Reply.spec (GF := GF) (hG := hG)
  handleRead2Reply : GryffCoordinator.HandleRead2Reply.spec (GF := GF) (hG := hG)
  handleWrite1Reply : GryffCoordinator.HandleWrite1Reply.spec (GF := GF) (hG := hG)
  handleWrite2Reply : GryffCoordinator.HandleWrite2Reply.spec (GF := GF) (hG := hG)
  handleForceWrite : GryffCoordinator.HandleForceWrite.spec (GF := GF) (hG := hG)

end

end Perennial.gryff.replica2
