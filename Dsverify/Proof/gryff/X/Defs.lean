/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/X/Defs.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit X: the executor's resources over a generic `GF`

Program proofs over the concrete `GF` do not finish in the kernel (stage 1's finding,
checked again: `dlog.Printf`'s three-line proof times out at `GF`). So the executor's proofs
are stated over a generic `GF`, with verbatim copies (`*G`) of the parts of
`Replica2/State.lean`'s abstraction they open (the EPaxos handler's heap, an instance, the
executor's own state, the channels), and the laws that are only stated at `GF`
(`critical_step`, `resolveExec`, the trace's lower bound, `pendingOuts_self`, `step_ok_exec`) as
hypotheses over abstract predicates (`ExecHyps`). `GryffProof/X/Bridge.lean` instantiates them
at `GF` (each copy is its original by `rfl`).
-/
module

public import Dsverify.Proof.gryff.Replica2.State

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.X

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB RecoveryInstance Proposal Msg Ev Out Cmd Deps StepRes)
open Perennial.gryff.replica (XS rowOwn stackOwn euOwn nSlots)
open Perennial.gryff.replica2 (Repl2Names tagOf vtOf depsOf cmdOf rid32 handlerIface)


section reps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [π : NetProtoGS] [sem : go.Semantics]

/-- `replica2.cmdsRep`. -/
def cmdsRepG (sl : GoSlice) (cs : List Cmd) : IProp GF :=
  iprop(∃ gs : List src.state.Command, sl ↦*□ gs ∗ ⌜gs.map cmdOf = cs ∧ model.cmdsOk cs⌝)

/-- `replica2.writerIs`. -/
def writerIsG (ρ : Repl2Names) (cid : w32) (w : Loc) : IProp GF :=
  ghostMapElem ρ.writers cid DFrac.discard w

/-- `replica2.proposalRep`. -/
def proposalRepG (ρ : Repl2Names) (pp : Loc) (pr : Proposal) : IProp GF :=
  iprop(∃ (gp : src.genericsmr.Propose) (inner : src.genericsmrproto.Propose), pp ↦□ gp ∗
    gp.Propose' ↦□ inner ∗ writerIsG ρ pr.client gp.Reply' ∗
    ⌜inner.CommandId' = pr.cmdId ∧ cmdOf inner.Command' = pr.cmd ∧ pr.cmd.ok = true⌝)

/-- `replica2.proposalsRep`. -/
def proposalsRepG (ρ : Repl2Names) (sl : GoSlice) (prs : List Proposal) : IProp GF :=
  iprop(∃ pps : List Loc, sl ↦*□ pps ∗ ⌜pps.length = prs.length⌝ ∗
    ⌜prs = [] → sl = slice.nil⌝ ∗
    [∗list] i ↦ pp ∈ pps, ∃ pr, ⌜prs[i]? = some pr⌝ ∗ proposalRepG ρ pp pr)

/-- `replica2.riRep`. -/
def riRepG (l : Loc) (ri : Option RecoveryInstance) : IProp GF :=
  match ri with
  | none => iprop(⌜l = Loc.null⌝)
  | some r => iprop(∃ g : src.gryff.RecoveryInstance, l ↦ g ∗ cmdsRepG g.cmds' r.cmds ∗
      ⌜g.status' = r.status ∧ g.seq' = r.seq ∧ depsOf g.deps' = r.deps ∧ vtOf g.base' = r.base ∧
        g.preAcceptCount' = r.preAcceptCount ∧ g.leaderResponded' = r.leaderResponded ∧
        g.vbal' = r.vbal⌝)

/-- `replica2.lbRep`. -/
def lbRepG (ρ : Repl2Names) (l : Loc) (lb : Option LB) : IProp GF :=
  match lb with
  | none => iprop(⌜l = Loc.null⌝)
  | some b => iprop(∃ g : src.gryff.LeaderBookkeeping, l ↦ g ∗
      proposalsRepG ρ g.clientProposals' b.clientProposals ∗
      g.committedDeps' ↦* b.committedDeps ∗ riRepG g.recoveryInst' b.recoveryInst ∗
      ⌜g.maxRecvBallot' = b.maxRecvBallot ∧ g.prepareOKs' = b.prepareOKs ∧
        g.allEqual' = b.allEqual ∧ g.preAcceptOKs' = b.preAcceptOKs ∧
        g.acceptOKs' = b.acceptOKs ∧ g.nacks' = b.nacks ∧ depsOf g.originalDeps' = b.originalDeps ∧
        g.preparing' = b.preparing ∧ g.numReplicasExecuted' = b.numReplicasExecuted ∧
        g.repliedClient' = b.repliedClient⌝)

/-- The pure part of `copyRep` (an instance's fields against its copy and the search state). -/
def copyFacts (xs : XS) (n : replica.Node) (iv : src.gryff.Instance) (c : Copy) : Prop :=
  iv.ballot' = c.ballot ∧ iv.Status' = c.status ∧ iv.Seq' = c.seq ∧ depsOf iv.Deps' = c.deps ∧
      vtOf iv.Base' = c.base ∧ iv.Slot' = c.slot ∧ iv.Leader' = c.leader ∧ iv.vbal' = c.vbal ∧
      sint.Z iv.Leader' = n.1 ∧ sint.Z iv.Slot' = n.2 ∧
      sint.Z iv.Index' = xs.numF n ∧ sint.Z iv.Lowlink' = xs.lowF n ∧
      (c.status = model.St.EXECUTED ↔ n ∈ xs.1)

/-- `replica2.copyRep`. -/
def copyRepG (ρ : Repl2Names) (xs : XS) (n : replica.Node) (p : Loc) (c : Copy) : IProp GF :=
  iprop(∃ iv : src.gryff.Instance, p ↦ iv ∗ cmdsRepG iv.Cmds' c.cmds ∗ lbRepG ρ iv.lb' c.lb ∗
    ⌜iv.ballot' = c.ballot ∧ iv.Status' = c.status ∧ iv.Seq' = c.seq ∧ depsOf iv.Deps' = c.deps ∧
      vtOf iv.Base' = c.base ∧ iv.Slot' = c.slot ∧ iv.Leader' = c.leader ∧ iv.vbal' = c.vbal ∧
      sint.Z iv.Leader' = n.1 ∧ sint.Z iv.Slot' = n.2 ∧
      sint.Z iv.Index' = xs.numF n ∧ sint.Z iv.Lowlink' = xs.lowF n ∧
      (c.status = model.St.EXECUTED ↔ n ∈ xs.1)⌝)

theorem copyRepG_open (ρ : Repl2Names) (xs : XS) (n : replica.Node) (p : Loc) (c : Copy) :
    copyRepG (GF := GF) ρ xs n p c ⊣⊢ ∃ iv : src.gryff.Instance, p ↦ iv ∗
      cmdsRepG iv.Cmds' c.cmds ∗ lbRepG ρ iv.lb' c.lb ∗ ⌜copyFacts xs n iv c⌝ := .rfl

/-- `replica2.confRep`. -/
def confRepG (mR : Loc) (o : Option w32) : IProp GF :=
  iprop(∃ m : GMap w64 Loc, mR ↦$ m ∗ ⌜∀ kk, kk ≠ W64 0 → m.lookup kk = none⌝ ∗
    match o with
    | none => iprop(⌜m.lookup (W64 0) = none⌝)
    | some v => iprop(∃ (ir : Loc) (im : GMap w8 w32), ⌜m.lookup (W64 0) = some ir⌝ ∗ ir ↦$ im ∗
        ⌜∀ op, im.lookup op = if op ∈ [W8 1, W8 2, W8 6] then some v else none⌝))

/-- `replica2.epaxosRest`. -/
def epaxosRestG (h : Loc) : IProp GF :=
  iprop(∃ (ms lcp lci : w32) (cS : GoSlice) (cs : List Loc) (mskR : Loc) (msk : GMap w64 w32),
    h.[src.gryff.EPaxosRMWHandler, go!"maxSeq"] ↦ ms ∗
    h.[src.gryff.EPaxosRMWHandler, go!"latestCPEPaxosRMWHandler"] ↦ lcp ∗
    h.[src.gryff.EPaxosRMWHandler, go!"latestCPInstance"] ↦ lci ∗
    h.[src.gryff.EPaxosRMWHandler, go!"conflicts"] ↦□ cS ∗ cS ↦*□ cs ∗
    ([∗list] c ∈ cs, ∃ m : GMap w64 w32, c ↦$ m) ∗
    h.[src.gryff.EPaxosRMWHandler, go!"maxSeqPerKey"] ↦□ mskR ∗ mskR ↦$ msk ∗
    (∃ v : src.gryffproto.PreAccept, globalAddr src.gryff.pa ↦ v) ∗
    (∃ v : src.gryffproto.EAccept, globalAddr src.gryff.ea ↦ v) ∗
    (∃ v : src.gryffproto.ECommit, globalAddr src.gryff.ec ↦ v) ∗
    (∃ v : src.epaxosproto.CommitShort, globalAddr src.gryff.ecs ↦ v) ∗
    (∃ v : w64, globalAddr src.gryff.conflicted ↦ v) ∗
    (∃ v : w64, globalAddr src.gryff.happy ↦ v) ∗
    (∃ v : w64, globalAddr src.gryff.slow ↦ v) ∗
    (∃ v : w64, globalAddr src.gryff.weird ↦ v) ∗
    (∃ v : w64, globalAddr src.gryff.cpcounter ↦ v) ∗
    (∃ v : GoSlice, globalAddr src.gryff.cpMarker ↦ v))

/-- The instances of `M` at model state `s`. -/
def instsG (ρ : Repl2Names) (xs : XS) (s : RState) (M : GMap replica.Node Loc) : IProp GF :=
  iprop([∗map] n ↦ p ∈ M, ∃ c, ⌜s.inst (BitVec.ofInt 32 n.1) (BitVec.ofInt 32 n.2) = some c⌝ ∗
      copyRepG ρ xs n p c)

/-- The pointer map's elements: persistent for the committed or executed instances. -/
def ptrElems (ρ : Repl2Names) (s : RState) (M : GMap replica.Node Loc) : IProp GF :=
  iprop([∗map] n ↦ p ∈ M, ghostMapElem ρ.ptrs n
      (if replica2.committedOrExecuted s n then DFrac.discard else DFrac.own 1) p)

/-- The pure facts of `epaxosOwn`. -/
def epFacts (xs : XS) (s : RState) (isp : List GoSlice) (cfs : List Loc)
    (M : GMap replica.Node Loc) (cu : GoArray w32 5) (pm : GMap w64 src.gryffproto.ValTag) : Prop :=
  isp.length = 3 ∧ cfs.length = 3 ∧ s.crtInstance.length = 3 ∧ depsOf cu = s.committedUpTo ∧
      (∀ kk, kk ≠ W64 0 → pm.lookup kk = none) ∧ (pm.lookup (W64 0)).map vtOf = s.prevValTag ∧
      (∀ q i : w32, model.inBox q i = true →
        (s.inst q i).isSome = (M.lookup (sint.Z q, sint.Z i)).isSome) ∧
      (∀ q i : w32, model.inBox q i = false → s.inst q i = none) ∧
      (∀ n, (n ∈ xs.1 ∨ xs.numF n ≠ 0 ∨ xs.lowF n ≠ 0) → (M.lookup n).isSome) ∧
      (∀ n, (n ∈ xs.1 ∨ xs.numF n ≠ 0 ∨ xs.lowF n ≠ 0) →
        replica2.committedOrExecuted s n = true) ∧
      s.conf.length = 3

/-- `replica2.epaxosOwn` (its instances `instsG`, its pure part `epFacts`). -/
def epaxosOwnG (ρ : Repl2Names) (h r : Loc) (xs : XS) (s : RState) : IProp GF :=
  iprop(∃ (ispS crtS c1S : GoSlice) (isp : List GoSlice) (msR pvtR : Loc) (cfs : List Loc)
      (M : GMap replica.Node Loc) (cu : GoArray w32 5) (pm : GMap w64 src.gryffproto.ValTag),
    h.[src.gryff.EPaxosRMWHandler, go!"R"] ↦□ r ∗
    h.[src.gryff.EPaxosRMWHandler, go!"noConflicts"] ↦□ false ∗
    h.[src.gryff.EPaxosRMWHandler, go!"InstanceSpace"] ↦□ ispS ∗ ispS ↦*□ isp ∗
    h.[src.gryff.EPaxosRMWHandler, go!"crtInstance"] ↦□ crtS ∗
    h.[src.gryff.EPaxosRMWHandler, go!"conflicts1"] ↦□ c1S ∗ c1S ↦*□ cfs ∗
    h.[src.gryff.EPaxosRMWHandler, go!"maxSeqPerKey1"] ↦□ msR ∗
    h.[src.gryff.EPaxosRMWHandler, go!"PrevValTag"] ↦□ pvtR ∗
    h.[src.gryff.EPaxosRMWHandler, go!"CommittedUpTo"] ↦ cu ∗
    crtS ↦* s.crtInstance ∗
    ghostMapAuth ρ.ptrs 1 M ∗ ptrElems ρ s M ∗
    ([∗list] q ↦ sq ∈ isp, rowOwn M q sq) ∗ instsG ρ xs s M ∗
    ([∗list] q ∈ List.finRange 3, monoNatAuthOwn (ρ.crt q) 1 (sint.Z (s.crt (rid32 q))).toNat) ∗
    ([∗list] q ↦ cr ∈ cfs, confRepG cr (s.confAt q)) ∗ confRepG msR s.maxSeqK0 ∗
    pvtR ↦$ pm ∗ epaxosRestG h ∗ ⌜epFacts xs s isp cfs M cu pm⌝)

/-- `replica2.bagAt`. -/
def bagAtG {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.GoType}
    [IntoValTyped (GF := GF) V t] (ρ : Repl2Names) (T : Type) (l : Loc) (f : GoString)
    (nm : String) (P : V → IProp GF) : IProp GF :=
  iprop(∃ ch : Loc, l.[T, f] ↦□ ch ∗ isChanBag (ρ.chans nm) ch P)

/-- `replica2.recoverChanP`. -/
def recoverChanPG (ρ : Repl2Names) (p : Loc) : IProp GF :=
  iprop(∃ q i : w32, p ↦ (src.gryff.instanceId.mk q i) ∗ ⌜model.rowOk q = true ∧ 0 ≤ sint.Z i⌝ ∗
    ∃ hq : sint.Z q < 3, monoNatLbOwn (ρ.crt ⟨(sint.Z q).toNat, by omega⟩) ((sint.Z i).toNat + 1))

/-- `replica2.eoChanP`, with the receive token abstract (`Tok`). -/
def eoChanPG (Tok : Msg → IProp GF) (p : Loc) : IProp GF :=
  iprop(∃ m, (∃ (eo : src.gryff.ExecuteOverwrite) (t : src.gryffproto.Tag), p ↦ eo ∗ eo.T' ↦□ t ∗
      ⌜eo.K' = W64 0 ∧ m = ⟨eo.V', tagOf t, eo.Leader', eo.Slot'⟩⌝) ∗ Tok (.executeOverwrite m))

/-- `replica2.execPriv2`. -/
def execPrivG (ρ : Repl2Names) (h : Loc) (xs : XS) (S : List replica.Node) : IProp GF :=
  iprop(ghostVar ρ.xs (1 : Qp).half xs ∗ stackOwn ρ.toR1 S ∗
    ∃ euS : GoSlice, h.[src.gryff.EPaxosRMWHandler, go!"ExecedUpTo"] ↦□ euS ∗ euOwn euS xs.1)

end reps

end Perennial.gryff.X
