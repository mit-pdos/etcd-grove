/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Replica2/State.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Stage 2: a replica's heap and its model state (interface, draft)

The abstraction relating a Gryff replica's heap (`*gryff.Replica` with its generic replica, its
participant, its coordinator, its EPaxos handler) to the pure model's `RState`
(`GryffProof/Model/Types.lean`), the replica's lock invariant (G2's mutex) and its persistent
handle. The handler specs stated over these are in `Replica2/Specs.lean`;
`notes/stage2-interface-code.md` explains the choices.

**Layers.**
* Pure projections of Go values to the model's (`tagOf`, `vtOf`, `depOf`, `cmdOf`, `depsOf`, one
  `*Of` per message kind) and of a message pointer to a model message (`msgAt`: the kind's
  struct, `Wire/Enc.lean`'s ownership, projected by `*Of`), of a client request (`reqAt`).
* Per Go object (sealed): `cmdsRep` (a command slice, persistent: shared between instances and
  messages), `proposalRep` (a `*genericsmr.Propose`, persistent), `riRep`, `lbRep`, `copyRep`
  (an `*Instance`), `readOpRep`, `writeOpRep`, `ongoingOpRep`.
* Per package (sealed, each with the laws its callers need): `partiOwn` (the participant: the
  store's tag, `OngoingWrites`), `valOwn` (the store's value, `r.State.Store`, written through the
  `IGryffParticipant` callbacks), `coordOwn` (the coordinator), `epaxosOwn` (the EPaxos handler:
  instance space, `crtInstance`, `CommittedUpTo`, the conflict tables, `PrevValTag`), `proposeOwn`
  (`ProposeChan`'s contents: owned by the lock, read only by `handlePropose`), and `replicaOwn`
  (all of them at one `s : RState`).
* The network side of the lock (`pendingOuts`): the peer writers with the stream prefixes on the
  wire, the self-stream cursor, the client writers; indexed by the
  outputs still owed, so that `pendingOuts γ ρ k t []` is what the lock holds between steps.
* `replicaLockInv` and the handle `isReplica`.

**Aliasing** (the Go code shares pointers between maps, structs and messages): every `Tag` cell
the participant's store points to (`storeTag[0].Tag`, set by `HandleOverwrite` to a pointer into
a message, a read op, an `ExecuteOverwrite` or a local) is persistent (`↦□`): the caller of
`HandleOverwrite` gives up the pointee for good. Command slices are persistent (`cmdsRep`):
an instance's `Cmds` is the `Command` slice of the message that created it (or of the proposals),
and the same slice goes out in later messages. Proposals are persistent (`proposalRep`): a
leader's bookkeeping, `ProposeChan` and re-proposals share them. A read op's `maxValTag` /
`ReadValTag` point into the `Read1Reply` that set them (persistent).
-/
module

public import Dsverify.Proof.gryff.Proto2.Replica
public import Dsverify.Proof.gryff.N.NetDefs
public import Dsverify.Proof.gryff.Replica.ExecDefs
public import Dsverify.Proof.gryff.Replica.ExecModel
public import Dsverify.Proof.gryff.Wire.Enc
public import Dsverify.Proof.gryff.Wire.Proof.Lemmas
public import Perennial.Ghost.MonoNat
public import Dsverify.Proof.gryff.PureLc.FrameC
public import Dsverify.Proof.gryff.S.Mono

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB RecoveryInstance Proposal ReadOp WriteOp OngoingOp
  Msg Ev Ext Out Cmd Deps AMap StepRes)
open Perennial.gryff.replica (XS rowOwn stackOwn euOwn nSlots)
open github_com.goose_lang.primitive (ProphId)

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## Pure projections of Go values -/

section proj
variable [GooseExts] [GoGlobalContext]

/-- A Go tag as the model's. -/
def tagOf (t : src.gryffproto.Tag) : model.Tag := ⟨t.Ts', t.Cid', t.Rmwc'⟩
/-- A Go value-tag as the model's. -/
def vtOf (v : src.gryffproto.ValTag) : model.ValTag := ⟨v.V', tagOf v.T'⟩
/-- A Go dependency as the model's. -/
def depOf (d : src.gryffproto.Dep) : model.Dep := ⟨d.Key', vtOf d.Vt'⟩
/-- A Go command as the model's. -/
def cmdOf (c : src.state.Command) : Cmd := ⟨c.Op', c.K', c.V', c.OldValue'⟩
/-- A Go `[5]int32` as the model's `Deps`. -/
def depsOf (a : GoArray w32 5) : Deps := a.arr

open wire.gryffproto in
/-- The model's view of each message kind (the fields `Model/Msg.lean` keeps, in its order; the
same projection the trace prophecy's words resolve: `proph.go`, `Model/Codec.lean`). -/
def read1Of (g : Read1Proxied.Msg) : model.Read1ProxiedM :=
  ⟨g.RequestId', g.ClientId', g.K', depOf g.D', g.ReplicaId', vtOf g.Vt'⟩
open wire.gryffproto in
def read2Of (g : Read2Proxied.Msg) : model.Read2ProxiedM :=
  ⟨g.RequestId', g.ClientId', g.K', vtOf g.Vt', g.ReplicaId'⟩
open wire.gryffproto in
def read1ReplyOf (g : Read1Reply.Msg) : model.Read1ReplyM :=
  ⟨g.RequestId', g.ClientId', g.ReplicaId', vtOf g.Vt'⟩
open wire.gryffproto in
def read2ReplyOf (g : Read2Reply.Msg) : model.Read2ReplyM := ⟨g.RequestId', g.ClientId'⟩
open wire.gryffproto in
def write1Of (g : Write1Proxied.Msg) : model.Write1ProxiedM :=
  ⟨g.RequestId', g.ClientId', g.ForceWrite', g.K', depOf g.D', g.ReplicaId'⟩
open wire.gryffproto in
def write1ReplyOf (g : Write1Reply.Msg) : model.Write1ReplyM :=
  ⟨g.RequestId', g.ClientId', vtOf g.Vt'⟩
open wire.gryffproto in
def write2Of (g : Write2Proxied.Msg) : model.Write2ProxiedM :=
  ⟨g.RequestId', g.ClientId', g.K', vtOf g.Vt', g.ReplicaId'⟩
open wire.gryffproto in
def write2ReplyOf (g : Write2Reply.Msg) : model.Write2ReplyM :=
  ⟨g.RequestId', g.ClientId', g.Applied'⟩
open wire.gryffproto in
def preAcceptOf (g : PreAccept.Msg) : model.PreAcceptM :=
  ⟨g.LeaderId, g.Replica, g.Instance, g.Ballot, g.Command.map cmdOf, g.Seq, depsOf g.Deps,
    vtOf g.Base⟩
open wire.gryffproto in
def preAcceptReplyOf (g : PreAcceptReply.Msg) : model.PreAcceptReplyM :=
  ⟨g.Replica', g.Instance', g.OK', g.Ballot', g.Seq', depsOf g.Deps', vtOf g.Base'⟩
open wire.epaxosproto in
def preAcceptOKOf (g : PreAcceptOK.Msg) : model.PreAcceptOKM := ⟨g.Instance'⟩
open wire.gryffproto in
def acceptOf (g : EAccept.Msg) : model.EAcceptM :=
  ⟨g.LeaderId, g.Replica, g.Instance, g.Ballot, g.Seq, depsOf g.Deps, g.Command.map cmdOf,
    vtOf g.Base⟩
open wire.epaxosproto in
def acceptReplyOf (g : AcceptReply.Msg) : model.AcceptReplyM :=
  ⟨g.Replica', g.Instance', g.OK', g.Ballot'⟩
open wire.gryffproto in
def commitOf (g : ECommit.Msg) : model.ECommitM :=
  ⟨g.Replica, g.Instance, g.Command.map cmdOf, g.Seq, depsOf g.Deps, vtOf g.Base⟩
open wire.epaxosproto in
def prepareOf (g : Prepare.Msg) : model.PrepareM :=
  ⟨g.LeaderId', g.Replica', g.Instance', g.Ballot'⟩
open wire.gryffproto in
def prepareReplyOf (g : PrepareReply.Msg) : model.PrepareReplyM :=
  ⟨g.AcceptorId, g.Replica, g.Instance, g.OK, g.Ballot, g.VBallot, g.Status,
    g.Command.map cmdOf, g.Seq, depsOf g.Deps, vtOf g.Base⟩
open wire.gryffproto in
def executedOf (g : Executed.Msg) : model.ExecutedM := ⟨g.Replica', g.Instance'⟩

/-- The Go type of the pointer a message of each kind travels as (the channels' interface
values, `fastrpc.Serializable`; `ExecuteOverwrite` travels as a bare pointer). -/
def msgTy : Msg → go.GoType
  | .read1 _ => go.GoType.PointerType src.gryffproto.Read1Proxied.ty
  | .read2 _ => go.GoType.PointerType src.gryffproto.Read2Proxied.ty
  | .read1Reply _ => go.GoType.PointerType src.gryffproto.Read1Reply.ty
  | .read2Reply _ => go.GoType.PointerType src.gryffproto.Read2Reply.ty
  | .write1 _ => go.GoType.PointerType src.gryffproto.Write1Proxied.ty
  | .write2 _ => go.GoType.PointerType src.gryffproto.Write2Proxied.ty
  | .write1Reply _ => go.GoType.PointerType src.gryffproto.Write1Reply.ty
  | .write2Reply _ => go.GoType.PointerType src.gryffproto.Write2Reply.ty
  | .preAccept _ => go.GoType.PointerType src.gryffproto.PreAccept.ty
  | .preAcceptReply _ => go.GoType.PointerType src.gryffproto.PreAcceptReply.ty
  | .preAcceptOK _ => go.GoType.PointerType src.epaxosproto.PreAcceptOK.ty
  | .accept _ => go.GoType.PointerType src.gryffproto.EAccept.ty
  | .acceptReply _ => go.GoType.PointerType src.epaxosproto.AcceptReply.ty
  | .commit _ => go.GoType.PointerType src.gryffproto.ECommit.ty
  | .prepare _ => go.GoType.PointerType src.epaxosproto.Prepare.ty
  | .prepareReply _ => go.GoType.PointerType src.gryffproto.PrepareReply.ty
  | .executed _ => go.GoType.PointerType src.gryffproto.Executed.ty
  | .executeOverwrite _ => go.GoType.PointerType src.gryff.ExecuteOverwrite.ty

/-- The model event of a client request's Go struct (the run loop's `readS.Obj.(*Read)`, ...). -/
def readEvOf (g : src.gryffproto.Read) : Ev := .read g.RequestId' g.ClientId' g.K' (depOf g.D')
def writeEvOf (g : src.gryffproto.Write) : Ev :=
  .write g.RequestId' g.ClientId' g.K' g.V' (depOf g.D')
def rmwEvOf (g : src.gryffproto.RMW) : Ev :=
  .rmw g.RequestId' g.ClientId' g.K' (depOf g.D') g.OldValue' g.NewValue'

/-- A replica id (`Fin 3`) as Go's `int32`. -/
def rid32 (k : Fin 3) : w32 := W32 k.val

end proj

/-! ## Ghost names of one replica -/

/-- A replica's own ghost names (allocated by `NewReplica`). -/
structure Repl2Names where
  /-- the executor's search state (`XS`): half in the lock, half the executor's (stage 1's) -/
  xs : GName
  /-- each instance's pointer (persistent elements for committed or executed instances, whose
  slot keeps its pointer; owned, by the lock, for the others: H3-R1) -/
  ptrs : GName
  /-- per row `q`, a lower bound on `crtInstance[q]` (mono nat; the recovery trigger's guard) -/
  crt : Fin 3 → GName
  /-- client id ↦ its connection's writer (persistent elements; `GetClientWriter`) -/
  writers : GName
  /-- the lock's boot state (a ghost variable, half in the lock, half the run goroutine's:
  `true` until the run loop's first `Lock` completes the lock invariant) -/
  boot : GName
  /-- the channels' names (one bag per channel the run loop selects on) -/
  chans : String → ChanNames


/-! ## Per-object representations -/

section reps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]


/-- Message `m` at `p` (full ownership of its kind's struct, `Wire/Enc.lean`'s `own`, projected
by its `*Of`; for `ExecuteOverwrite`, the struct and its persistent tag cell). For the kinds
carrying a `Command` slice (`PreAccept`, `EAccept`, `ECommit`, `PrepareReply`): the struct owned,
the slice persistent (H2-R1, H3-R3: a sender's slice is an instance's `Cmds`, `cmdsRep`, shared;
`SendMsg` only reads it; a listener persists its fresh slice before the channel send). -/
@[irreducible] def msgAt (p : Loc) (m : Msg) : IProp GF :=
  match m with
  | .read1 mm => iprop(∃ g, wire.gryffproto.Read1Proxied.own p (DFrac.own 1) g ∗ ⌜read1Of g = mm⌝)
  | .read2 mm => iprop(∃ g, wire.gryffproto.Read2Proxied.own p (DFrac.own 1) g ∗ ⌜read2Of g = mm⌝)
  | .read1Reply mm =>
    iprop(∃ g, wire.gryffproto.Read1Reply.own p (DFrac.own 1) g ∗ ⌜read1ReplyOf g = mm⌝)
  | .read2Reply mm =>
    iprop(∃ g, wire.gryffproto.Read2Reply.own p (DFrac.own 1) g ∗ ⌜read2ReplyOf g = mm⌝)
  | .write1 mm =>
    iprop(∃ g, wire.gryffproto.Write1Proxied.own p (DFrac.own 1) g ∗ ⌜write1Of g = mm⌝)
  | .write2 mm =>
    iprop(∃ g, wire.gryffproto.Write2Proxied.own p (DFrac.own 1) g ∗ ⌜write2Of g = mm⌝)
  | .write1Reply mm =>
    iprop(∃ g, wire.gryffproto.Write1Reply.own p (DFrac.own 1) g ∗ ⌜write1ReplyOf g = mm⌝)
  | .write2Reply mm =>
    iprop(∃ g, wire.gryffproto.Write2Reply.own p (DFrac.own 1) g ∗ ⌜write2ReplyOf g = mm⌝)
  | .preAccept mm =>
    iprop(∃ (g : wire.gryffproto.PreAccept.Msg) (sl : GoSlice),
      p ↦ wire.gryffproto.PreAccept.goVal g sl ∗ sl ↦*□ g.Command ∗ ⌜preAcceptOf g = mm⌝)
  | .preAcceptReply mm =>
    iprop(∃ g, wire.gryffproto.PreAcceptReply.own p (DFrac.own 1) g ∗ ⌜preAcceptReplyOf g = mm⌝)
  | .preAcceptOK mm =>
    iprop(∃ g, wire.epaxosproto.PreAcceptOK.own p (DFrac.own 1) g ∗ ⌜preAcceptOKOf g = mm⌝)
  | .accept mm =>
    iprop(∃ (g : wire.gryffproto.EAccept.Msg) (sl : GoSlice),
      p ↦ wire.gryffproto.EAccept.goVal g sl ∗ sl ↦*□ g.Command ∗ ⌜acceptOf g = mm⌝)
  | .acceptReply mm =>
    iprop(∃ g, wire.epaxosproto.AcceptReply.own p (DFrac.own 1) g ∗ ⌜acceptReplyOf g = mm⌝)
  | .commit mm =>
    iprop(∃ (g : wire.gryffproto.ECommit.Msg) (sl : GoSlice),
      p ↦ wire.gryffproto.ECommit.goVal g sl ∗ sl ↦*□ g.Command ∗ ⌜commitOf g = mm⌝)
  | .prepare mm =>
    iprop(∃ g, wire.epaxosproto.Prepare.own p (DFrac.own 1) g ∗ ⌜prepareOf g = mm⌝)
  | .prepareReply mm =>
    iprop(∃ (g : wire.gryffproto.PrepareReply.Msg) (sl : GoSlice),
      p ↦ wire.gryffproto.PrepareReply.goVal g sl ∗ sl ↦*□ g.Command ∗ ⌜prepareReplyOf g = mm⌝)
  | .executed mm =>
    iprop(∃ g, wire.gryffproto.Executed.own p (DFrac.own 1) g ∗ ⌜executedOf g = mm⌝)
  | .executeOverwrite mm =>
    iprop(∃ (eo : src.gryff.ExecuteOverwrite) (t : src.gryffproto.Tag), p ↦ eo ∗ eo.T' ↦□ t ∗
      ⌜eo.K' = W64 0 ∧ mm = ⟨eo.V', tagOf t, eo.Leader', eo.Slot'⟩⌝)

/-- A client request's Go struct at `p` (the `Obj` of a `*genericsmr.ClientRPC` on `readChan`,
`writeChan`, `rmwChan`) is event `e`; the struct's type is the channel kind `kd`'s (`"read"`,
`"write"`, else an `RMW`; B-R2). -/
@[irreducible] def reqAt (kd : String) (p : Loc) (e : Ev) : IProp GF :=
  if kd = "read" then iprop(∃ g : src.gryffproto.Read, p ↦ g ∗ ⌜readEvOf g = e⌝)
  else if kd = "write" then iprop(∃ g : src.gryffproto.Write, p ↦ g ∗ ⌜writeEvOf g = e⌝)
  else iprop(∃ g : src.gryffproto.RMW, p ↦ g ∗ ⌜rmwEvOf g = e⌝)

/-- A command slice (persistent: an instance's commands are its creating message's or its
proposals', and go out again in later messages; never written after creation). Its commands are
CAS on key 0 (H2c-R1: `model.cmdsOk`, as every writer's source: the messages' `never` guard,
`proposalRep`'s `pr.cmd.ok`). -/
@[irreducible] def cmdsRep (sl : GoSlice) (cs : List Cmd) : IProp GF :=
  iprop(∃ gs : List src.state.Command, sl ↦*□ gs ∗ ⌜gs.map cmdOf = cs ∧ model.cmdsOk cs⌝)

/-- Client id `cid`'s connection writer is `w` (persistent: a client id is bound to one
connection, `serveClient` stores its writer once). -/
@[irreducible] def writerIs (ρ : Repl2Names) (cid : w32) (w : Loc) : IProp GF :=
  ghostMapElem ρ.writers cid DFrac.discard w

/-- A client proposal (persistent): `*genericsmr.Propose{&genericsmrproto.Propose{CommandId,
Command, 0}, writer}` whose writer is its client id's (`HandleRMW`'s `GetClientWriter`); its
command is a CAS on key 0 (`Cmd.ok`, H2-R6: `updateAttributes` / `updateConflicts` index the
conflict tables by the command's key and operation). -/
@[irreducible] def proposalRep (ρ : Repl2Names) (pp : Loc) (pr : Proposal) : IProp GF :=
  iprop(∃ (gp : src.genericsmr.Propose) (inner : src.genericsmrproto.Propose), pp ↦□ gp ∗
    gp.Propose' ↦□ inner ∗ writerIs ρ pr.client gp.Reply' ∗
    ⌜inner.CommandId' = pr.cmdId ∧ cmdOf inner.Command' = pr.cmd ∧ pr.cmd.ok = true⌝)

/-- A slice of proposals (persistent, H2b-R1: a proposals slice is never written after
`handlePropose` fills it; `startPhase1`'s restart and recovery's new `lb` share it); a non-nil one
is non-empty (H2c-R2). -/
def proposalsRep (ρ : Repl2Names) (sl : GoSlice) (prs : List Proposal) : IProp GF :=
  iprop(∃ pps : List Loc, sl ↦*□ pps ∗ ⌜pps.length = prs.length⌝ ∗
    ⌜prs = [] → sl = slice.nil⌝ ∗ -- H2c-R2: a non-nil proposals slice is a batch (≥ 1)
    [∗list] i ↦ pp ∈ pps, ∃ pr, ⌜prs[i]? = some pr⌝ ∗ proposalRep ρ pp pr)

instance proposalsRep_persistent (ρ : Repl2Names) (sl : GoSlice) (prs : List Proposal) :
    Persistent (proposalsRep (GF := GF) ρ sl prs) := by
  unfold proposalsRep proposalRep writerIs; infer_instance

/-- A recovery instance (`lb.recoveryInst`; `none`: nil). -/
@[irreducible] def riRep (l : Loc) (ri : Option RecoveryInstance) : IProp GF :=
  match ri with
  | none => iprop(⌜l = Loc.null⌝)
  | some r => iprop(∃ g : src.gryff.RecoveryInstance, l ↦ g ∗ cmdsRep g.cmds' r.cmds ∗
      ⌜g.status' = r.status ∧ g.seq' = r.seq ∧ depsOf g.deps' = r.deps ∧ vtOf g.base' = r.base ∧
        g.preAcceptCount' = r.preAcceptCount ∧ g.leaderResponded' = r.leaderResponded ∧
        g.vbal' = r.vbal⌝)

/-- A leader's bookkeeping (`inst.lb`; `none`: nil). The dropped fields (TryPreAccept's, the
times) hold any value. -/
@[irreducible] def lbRep (ρ : Repl2Names) (l : Loc) (lb : Option LB) : IProp GF :=
  match lb with
  | none => iprop(⌜l = Loc.null⌝)
  | some b => iprop(∃ g : src.gryff.LeaderBookkeeping, l ↦ g ∗
      proposalsRep ρ g.clientProposals' b.clientProposals ∗
      g.committedDeps' ↦* b.committedDeps ∗ riRep g.recoveryInst' b.recoveryInst ∗
      ⌜g.maxRecvBallot' = b.maxRecvBallot ∧ g.prepareOKs' = b.prepareOKs ∧
        g.allEqual' = b.allEqual ∧ g.preAcceptOKs' = b.preAcceptOKs ∧
        g.acceptOKs' = b.acceptOKs ∧ g.nacks' = b.nacks ∧ depsOf g.originalDeps' = b.originalDeps ∧
        g.preparing' = b.preparing ∧ g.numReplicasExecuted' = b.numReplicasExecuted ∧
        g.repliedClient' = b.repliedClient⌝)

/-- Instance `n`'s struct at `p` is the copy `c`; its `Index` / `Lowlink` are the executor's
search state `xs` at `n` (stage 1's `instOwn`), its status is EXECUTED iff `n` is in `xs`'s
executed list. -/
@[irreducible] def copyRep (ρ : Repl2Names) (xs : XS) (n : replica.Node) (p : Loc) (c : Copy) :
    IProp GF :=
  iprop(∃ iv : src.gryff.Instance, p ↦ iv ∗ cmdsRep iv.Cmds' c.cmds ∗ lbRep ρ iv.lb' c.lb ∗
    ⌜iv.ballot' = c.ballot ∧ iv.Status' = c.status ∧ iv.Seq' = c.seq ∧ depsOf iv.Deps' = c.deps ∧
      vtOf iv.Base' = c.base ∧ iv.Slot' = c.slot ∧ iv.Leader' = c.leader ∧ iv.vbal' = c.vbal ∧
      sint.Z iv.Leader' = n.1 ∧ sint.Z iv.Slot' = n.2 ∧
      sint.Z iv.Index' = xs.numF n ∧ sint.Z iv.Lowlink' = xs.lowF n ∧
      (c.status = model.St.EXECUTED ↔ n ∈ xs.1)⌝)

/-- A Go `*ValTag` cell (persistent: see the module header) holding `v`; `none`: nil. -/
def optVtRep (l : Loc) (v : Option model.ValTag) : IProp GF :=
  match v with
  | none => iprop(⌜l = Loc.null⌝)
  | some x => iprop(∃ g : src.gryffproto.ValTag, l ↦□ g ∗ ⌜vtOf g = x⌝)

/-- A coordinator's read op (`*gryffcommon.ReadOp`, with its `*Op`). Dropped fields: any value
(`read1Replies`, `maxUpdateId`, `ReadUpdateId`; the op's `Key` is 0; its `Dep` points into the
client's request, persistent). The client
id's writer is known (`writerIs`: the request came on its connection). -/
@[irreducible] def readOpRep (ρ : Repl2Names) (p : Loc) (r : ReadOp) : IProp GF :=
  iprop(∃ (g : src.gryffcommon.ReadOp) (o : src.gryffcommon.Op) (rws : List w32) (w : Loc)
      (gd : src.gryffproto.Dep),
    writerIs ρ r.clientId w ∗ p ↦ g ∗ o.Dep' ↦□ gd ∗
    g.Op' ↦ o ∗ optVtRep g.maxValTag' r.maxValTag ∗ optVtRep g.ReadValTag' r.readValTag ∗
    g.replicasWithMaxTag' ↦* rws ∗
    ownSliceCap w32 g.replicasWithMaxTag' (DFrac.own 1) ∗ -- H1-R11 (`append(.., id)`)
    ⌜o.RequestId' = r.requestId ∧ o.ClientId' = r.clientId ∧ o.Key' = W64 0 ∧ g.N' = r.n ∧
      g.numRead1Replies' = r.numRead1Replies ∧ g.numRead2Replies' = r.numRead2Replies ∧
      g.readsWithMaxTag' = r.readsWithMaxTag ∧ g.sentRead2Round' = r.sentRead2Round ∧
      g.determinedReadVal' = r.determinedReadVal ∧ rws = r.replicasWithMaxTag⌝)

/-- A coordinator's write op (`*gryffcommon.WriteOp`). Its `Op.Dep` points into the client's
request (persistent), projecting to the model's `dep` (`SendWrite1` forwards it). `maxValTag`
points to a persistent cell
(the initial `{-1, tag0}`, or a `Write1Reply`'s `Vt`), `WriteTag` likewise; `MaxAppliedTag` is
the coordinator `co`'s field `maxAppliedTag` (`&c.maxAppliedTag` through `MaxTags`) or a
persistent cell (a slow write's `WriteTag`); `ForceWrite` is 1, `startedShortcircuitTimeout` false;
the dropped fields any value. The client id's writer is known (`writerIs`: the request came on
its connection). -/
@[irreducible] def writeOpRep (ρ : Repl2Names) (co : Loc) (p : Loc) (w : WriteOp) : IProp GF :=
  iprop(∃ (g : src.gryffcommon.WriteOp) (o : src.gryffcommon.Op) (wr : Loc)
      (gd : src.gryffproto.Dep),
    writerIs ρ w.clientId wr ∗ p ↦ g ∗ g.Op' ↦ o ∗ o.Dep' ↦□ gd ∗
    (⌜g.MaxAppliedTag' = co.[src.gryffcommon.GryffCoordinator, go!"maxAppliedTag"]⌝ ∨
      ∃ gt : src.gryffproto.Tag, g.MaxAppliedTag' ↦□ gt) ∗
    optVtRep g.maxValTag' (some w.maxValTag) ∗
    (match w.writeTag with
     | none => iprop(⌜g.WriteTag' = Loc.null⌝)
     | some t => iprop(∃ gt : src.gryffproto.Tag, g.WriteTag' ↦□ gt ∗ ⌜tagOf gt = t⌝)) ∗
    ⌜o.RequestId' = w.requestId ∧ o.ClientId' = w.clientId ∧ o.Key' = W64 0 ∧ g.N' = w.n ∧
      depOf gd = w.dep ∧ g.WriteValue' = w.writeValue ∧ g.ForceWrite' = W32 1 ∧
      g.numWrite1Applies' = w.numWrite1Applies ∧ g.numWrite1Replies' = w.numWrite1Replies ∧
      g.numWrite2Applies' = w.numWrite2Applies ∧ g.numWrite2Replies' = w.numWrite2Replies ∧
      g.sentWrite2Round' = w.sentWrite2Round ∧ g.startedShortcircuitTimeout' = false⌝)

/-- An `OngoingReqs` entry (`*gryffcommon.OngoingOp`): `ShortWrites` empty (only appended to when
a write is not forced). -/
@[irreducible] def ongoingOpRep (p : Loc) (o : OngoingOp) : IProp GF :=
  iprop(∃ (g : src.gryffcommon.OngoingOp) (sw : List w32), p ↦ g ∗ g.ShortReads' ↦* o.shortReads ∗
    ownSliceCap w32 g.ShortReads' (DFrac.own 1) ∗ -- H1-R11 (`StartRead`'s `append`)
    g.ShortWrites' ↦* sw ∗
    ⌜g.RequestId' = o.requestId ∧ g.ClientId' = o.clientId ∧ g.OpType' = o.isRead ∧
      g.Key' = W64 0 ∧ sw = []⌝)

end reps

/-! ## Per-package ownership -/

section owns
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]


/-- The participant (`*gryffcommon.GryffParticipant` at `pa`, its `iparti` the interface value
`ip`): the store's tag `tag` (`storeTag[0].Tag`, a persistent cell; no entry: `tag0`), the
ongoing writes `ong` (client id ↦ request id; each entry's `SentWrite1Reply` is true and
`FastOverwite` false: every Write1 is forced). Key 0 only. -/
@[irreducible] def partiOwn (pa : Loc) (ip : GoInterface) (k : Fin 3) (tag : model.Tag)
    (ong : AMap 32 w32) : IProp GF :=
  iprop(∃ (smR owR : Loc) (sm : GMap w64 Loc) (ow : GMap w32 Loc),
    pa.[src.gryffcommon.GryffParticipant, go!"id"] ↦□ rid32 k ∗
    pa.[src.gryffcommon.GryffParticipant, go!"iparti"] ↦□ ip ∗
    pa.[src.gryffcommon.GryffParticipant, go!"noConflicts"] ↦□ false ∗
    pa.[src.gryffcommon.GryffParticipant, go!"storeTag"] ↦□ smR ∗
    pa.[src.gryffcommon.GryffParticipant, go!"OngoingWrites"] ↦□ owR ∗
    smR ↦$ sm ∗ owR ↦$ ow ∗
    ⌜∀ kk, kk ≠ W64 0 → sm.lookup kk = none⌝ ∗
    (match sm.lookup (W64 0) with
     | none => iprop(⌜tag = model.tag0⌝)
     | some md => iprop(∃ (tp : Loc) (gt : src.gryffproto.Tag),
        md ↦ (src.gryffcommon.StoreMetadata.mk tp) ∗ tp ↦□ gt ∗ ⌜tagOf gt = tag⌝)) ∗
    ⌜∀ c, (ow.lookup c).isSome = (ong.get? c).isSome⌝ ∗
    [∗map] c ↦ op ∈ ow, ∃ (r : w32) (g : src.gryffcommon.OngoingWriteOp)
        (wm : src.gryffproto.Write1Proxied), ⌜ong.get? c = some r⌝ ∗ op ↦ g ∗
      g.Write1Proxied' ↦ wm ∗
      ⌜g.SentWrite1Reply' = true ∧ g.FastOverwite' = false ∧ wm.RequestId' = r ∧
        wm.ClientId' = c ∧ wm.K' = W64 0⌝)

/-- The store's value (`r.State.Store[0]`, absent: 0; `Exec` is true), which the participant
reads and writes through `IGryffParticipant.GetCurrentValue` / `SetCurrentValue`. -/
@[irreducible] def valOwn (gR : Loc) (v : w64) : IProp GF :=
  iprop(∃ (st smR : Loc) (sm : GMap w64 w64),
    gR.[src.genericsmr.Replica, go!"Exec"] ↦□ true ∗
    gR.[src.genericsmr.Replica, go!"State"] ↦□ st ∗
    st.[src.state.State, go!"Store"] ↦□ smR ∗ smR ↦$ sm ∗
    ⌜(∀ kk, kk ≠ W64 0 → sm.lookup kk = none) ∧ (sm.lookup (W64 0)).getD (W64 0) = v⌝)

/-- A map from Go keys to objects, one object per entry of the model's association list, each
represented by `R`. -/
def amapRep {n : Nat} {V : Type} (mR : Loc) (am : AMap n V) (R : Loc → V → IProp GF) :
    IProp GF :=
  iprop(∃ m : GMap (BitVec n) Loc, mR ↦$ m ∗
    ⌜∀ key, (m.lookup key).isSome = (am.get? key).isSome⌝ ∗
    [∗map] key ↦ p ∈ m, ∃ v, ⌜am.get? key = some v⌝ ∗ R p v)

/-- The coordinator (`*gryffcommon.GryffCoordinator` at `co`, its `icoord` the interface value
`ic`): `maxN`, `rops`, `wops`, `OngoingReqs` are `s`'s; the fixed fields are the kit's
configuration (not regular, 3 replicas, proxy, not thrifty, not EPaxos mode); the dropped fields
(`maxSeenTag`, `maxAppliedTag`, `ForcedKeys`) hold any value (`maxAppliedTag` is aliased by write
ops' `MaxAppliedTag`: `writeOpRep`). `MaxTags` (H1-R2: `HandleWrite2Reply` dereferences
`MaxTags[0]`) has key 0 only, absent while no write op exists (`StartWrite` sets it to
`&c.maxAppliedTag`), else `&c.maxAppliedTag` or a write's persistent `WriteTag`.
`ForcedKeysChanged` (H1-R8: `HandleForceWrite` ranges over it) is an owned empty slice
(`HandleForceWrite` stores a fresh `make([]Key, 0)`; nothing else writes it). -/
@[irreducible] def coordOwn (ρ : Repl2Names) (co : Loc) (ic : GoInterface) (k : Fin 3)
    (s : RState) : IProp GF :=
  iprop(∃ (ropsR wopsR orR mtR fkR : Loc) (arS : GoSlice) (mst mat : src.gryffproto.Tag)
      (fkc : GoSlice) (mt : GMap w64 Loc) (fk : GMap w64 w32),
    co.[src.gryffcommon.GryffCoordinator, go!"id"] ↦□ rid32 k ∗
    co.[src.gryffcommon.GryffCoordinator, go!"icoord"] ↦□ ic ∗
    co.[src.gryffcommon.GryffCoordinator, go!"regular"] ↦□ false ∗
    co.[src.gryffcommon.GryffCoordinator, go!"numReplicas"] ↦□ W64 3 ∗
    co.[src.gryffcommon.GryffCoordinator, go!"proxy"] ↦□ true ∗
    co.[src.gryffcommon.GryffCoordinator, go!"thrifty"] ↦□ false ∗
    co.[src.gryffcommon.GryffCoordinator, go!"epaxosMode"] ↦□ false ∗
    co.[src.gryffcommon.GryffCoordinator, go!"allReplicas"] ↦□ arS ∗ arS ↦*□ [W32 0, W32 1, W32 2] ∗
    co.[src.gryffcommon.GryffCoordinator, go!"rops"] ↦□ ropsR ∗
    co.[src.gryffcommon.GryffCoordinator, go!"wops"] ↦□ wopsR ∗
    co.[src.gryffcommon.GryffCoordinator, go!"OngoingReqs"] ↦□ orR ∗
    co.[src.gryffcommon.GryffCoordinator, go!"MaxTags"] ↦□ mtR ∗
    co.[src.gryffcommon.GryffCoordinator, go!"ForcedKeys"] ↦□ fkR ∗
    co.[src.gryffcommon.GryffCoordinator, go!"maxN"] ↦ s.maxN ∗
    co.[src.gryffcommon.GryffCoordinator, go!"maxSeenTag"] ↦ mst ∗
    co.[src.gryffcommon.GryffCoordinator, go!"maxAppliedTag"] ↦ mat ∗
    co.[src.gryffcommon.GryffCoordinator, go!"ForcedKeysChanged"] ↦ fkc ∗
    mtR ↦$ mt ∗ fkR ↦$ fk ∗
    ⌜∀ kk, kk ≠ W64 0 → mt.lookup kk = none⌝ ∗
    (match mt.lookup (W64 0) with
     | none => iprop(⌜s.wops = []⌝)
     | some p => iprop(⌜p = co.[src.gryffcommon.GryffCoordinator, go!"maxAppliedTag"]⌝ ∨
        ∃ gt : src.gryffproto.Tag, p ↦□ gt)) ∗
    fkc ↦* ([] : List w64) ∗
    ⌜(s.wops.map (fun e => e.1.toNat)).Pairwise (· < ·)⌝ ∗ -- H1-R10: `wops`'s keys sorted
    -- H1b-R1: a read op sits at the key of its ids (`StartRead` puts it at `ShiftInts(rid, cid)`)
    ⌜∀ id r, s.rops.get? id = some r → id = model.shiftInts r.requestId r.clientId⌝ ∗
    amapRep ropsR s.rops (fun p r => readOpRep ρ p r) ∗
    amapRep wopsR s.wops (fun p w => writeOpRep ρ co p w) ∗
    amapRep orR s.ongoingReqs ongoingOpRep)

/-- One row's conflict entry (`conflicts1[q]`, or `maxSeqPerKey1`): a `map[Key]map[Operation]int32`
with key 0 only; `none`: no entry, `some v`: the `PUT`, `GET` and `CAS` entries (`1`, `2`, `6`) are
present and `v`, no other (H2a-R1: `updateConflicts` sets the three together). -/
@[irreducible] def confRep (mR : Loc) (o : Option w32) : IProp GF :=
  iprop(∃ m : GMap w64 Loc, mR ↦$ m ∗ ⌜∀ kk, kk ≠ W64 0 → m.lookup kk = none⌝ ∗
    match o with
    | none => iprop(⌜m.lookup (W64 0) = none⌝)
    | some v => iprop(∃ (ir : Loc) (im : GMap w8 w32), ⌜m.lookup (W64 0) = some ir⌝ ∗ ir ↦$ im ∗
        ⌜∀ op, im.lookup op = if op ∈ [W8 1, W8 2, W8 6] then some v else none⌝)) -- H2a-R1

/-- The EPaxos handler's fields the model drops but the reachable code writes (`maxSeq`, the old
conflict tables `conflicts` / `maxSeqPerKey`, `latestCP*`): any values. Also (H2-R2) the `gryff`
package's globals the handlers write under the lock: the scratch messages `pa`, `ea`, `ec`, `ecs`
(`bcast*` fill them and send `&pa`, ...: any value, their `Command` slice any slice; `msgAt` asks
for it persistent at the send), the counters `conflicted`, `happy`, `slow`, `weird`
(`handlePreAcceptReply` / `handlePreAcceptOK`), `cpcounter`, `cpMarker` (`startPhase1`): any
values. (`tpa`, `paokr`, `aokr` are written only by `bcastTryPreAccept`,
`bcastPreAcceptOKReply`, `bcastAcceptOKReply`: unreachable in this configuration.) -/
@[irreducible] def epaxosRest (h : Loc) : IProp GF :=
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

/-- Instance `n` is committed or executed in `s` (`model.committedCopy`; in the box). -/
def committedOrExecuted (s : RState) (n : replica.Node) : Bool := (model.committedCopy s n).isSome

/-- The EPaxos handler (`*EPaxosRMWHandler` at `h`) at model state `s`, with the executor's
search state `xs` (the instances' `Index` / `Lowlink`, stage 1's): the instance space (rows of
pointers, `rowOwn`; the instances, `copyRep`; the pointer map `ρ.ptrs`, stage 1's, whose elements
are persistent for the committed or executed copies and owned for the others: H3-R1, an
uncommitted instance's pointer may be replaced by a fresh struct, a committed one's never; a copy
becoming committed persists its element), `crtInstance` (and its lower bounds' authority,
`ρ.crt`), `CommittedUpTo`, the conflict tables (`confRep`), `PrevValTag` (written by the
executor, under the lock). The executor's search state is non-trivial only at committed or
executed instances (it visits only those; H2-R5, H3-R1): a fresh struct's `Index = Lowlink = 0`
matches `xs` at any other node. -/
@[irreducible] def epaxosOwn (ρ : Repl2Names) (h r : Loc) (xs : XS) (s : RState) : IProp GF :=
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
    ghostMapAuth ρ.ptrs 1 M ∗
    ([∗map] n ↦ p ∈ M, ghostMapElem ρ.ptrs n
      (if committedOrExecuted s n then DFrac.discard else DFrac.own 1) p) ∗
    ([∗list] q ↦ sq ∈ isp, rowOwn M q sq) ∗
    ([∗map] n ↦ p ∈ M, ∃ c, ⌜s.inst (BitVec.ofInt 32 n.1) (BitVec.ofInt 32 n.2) = some c⌝ ∗
      copyRep ρ xs n p c) ∗
    ([∗list] q ∈ List.finRange 3, monoNatAuthOwn (ρ.crt q) 1 (sint.Z (s.crt (rid32 q))).toNat) ∗
    ([∗list] q ↦ cr ∈ cfs, confRep cr (s.confAt q)) ∗ confRep msR s.maxSeqK0 ∗
    pvtR ↦$ pm ∗ epaxosRest h ∗
    ⌜isp.length = 3 ∧ cfs.length = 3 ∧ s.crtInstance.length = 3 ∧ depsOf cu = s.committedUpTo ∧
      (∀ kk, kk ≠ W64 0 → pm.lookup kk = none) ∧ (pm.lookup (W64 0)).map vtOf = s.prevValTag ∧
      (∀ q i : w32, model.inBox q i = true →
        (s.inst q i).isSome = (M.lookup (sint.Z q, sint.Z i)).isSome) ∧
      (∀ q i : w32, model.inBox q i = false → s.inst q i = none) ∧
      (∀ n, (n ∈ xs.1 ∨ xs.numF n ≠ 0 ∨ xs.lowF n ≠ 0) → (M.lookup n).isSome) ∧
      (∀ n, (n ∈ xs.1 ∨ xs.numF n ≠ 0 ∨ xs.lowF n ≠ 0) → committedOrExecuted s n = true) ∧
      s.conf.length = 3⌝) -- H2a-R2

/-- `ProposeChan`'s contents, oldest first (only the lock's holder sends to it, re-proposals,
and receives from it, `handlePropose`; the kit's clients never send `GEN_PROPOSE`, which the
client stream protocol excludes, so `serveClient` never does). -/
@[irreducible] def proposeOwn (ρ : Repl2Names) (gR : Loc) (ps : List Proposal) : IProp GF :=
  iprop(∃ (ch : Loc) (pps : List Loc),
    gR.[src.genericsmr.Replica, go!"ProposeChan"] ↦□ ch ∗
    isChan ch (ρ.chans "propose") Loc ∗ ownChan (ρ.chans "propose") Loc (.Buffered pps) ∗
    ⌜pps.length = ps.length⌝ ∗
    [∗list] i ↦ pp ∈ pps, ∃ pr, ⌜ps[i]? = some pr⌝ ∗ proposalRep ρ pp pr)

/-- The replica's scratch messages (`r.read1`, `r.read2`, `r.write1`, `r.write2`: fully set
before each send; any value between steps; `r.read1`'s `D` is never written, so it stays the
zero `dep0` (H1e-1)). -/
@[irreducible] def scratchOwn (r : Loc) : IProp GF :=
  iprop(∃ (p1 p2 p3 p4 : Loc) (v1 : src.gryffproto.Read1Proxied)
      (v2 : src.gryffproto.Read2Proxied) (v3 : src.gryffproto.Write1Proxied)
      (v4 : src.gryffproto.Write2Proxied),
    r.[src.gryff.Replica, go!"read1"] ↦□ p1 ∗ p1 ↦ v1 ∗
    r.[src.gryff.Replica, go!"read2"] ↦□ p2 ∗ p2 ↦ v2 ∗
    r.[src.gryff.Replica, go!"write1"] ↦□ p3 ∗ p3 ↦ v3 ∗
    r.[src.gryff.Replica, go!"write2"] ↦□ p4 ∗ p4 ↦ v4 ∗
    ⌜depOf v1.D' = model.dep0⌝) -- H1e-1: `r.read1.D` is never written (zero at allocation)

/-- The interface value of `*gryff.Replica` `r` (its participant's `iparti`, its coordinator's
`icoord`). -/
def replicaIface (r : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType src.gryff.Replica.ty) #r
/-- The interface value of the EPaxos handler `h` (`r.rmwHandler`). -/
def handlerIface (h : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty) #h

/-- **The replica's heap at model state `s`** (replica id `k`, `*gryff.Replica` at `r`), with the
executor's search state `xs` (the lock's half of `ρ.xs`). -/
@[irreducible] def replicaOwnX (ρ : Repl2Names) (k : Fin 3) (r : Loc) (xs : XS) (s : RState) :
    IProp GF :=
  iprop(∃ (gR pa co h : Loc),
    r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗
    r.[src.gryff.Replica, go!"parti"] ↦□ pa ∗
    r.[src.gryff.Replica, go!"coord"] ↦□ co ∗
    r.[src.gryff.Replica, go!"rmwHandler"] ↦□ handlerIface h ∗
    partiOwn pa (replicaIface r) k s.tag s.ongoing ∗ valOwn gR s.val ∗
    coordOwn ρ co (replicaIface r) k s ∗ epaxosOwn ρ h r xs s ∗ ghostVar ρ.xs (1 : Qp).half xs ∗
    proposeOwn ρ gR s.proposeQ ∗ scratchOwn r ∗ ⌜s.id = rid32 k⌝)

/-- The replica's heap at model state `s` (the executor's search state hidden). -/
def replicaOwn (ρ : Repl2Names) (k : Fin 3) (r : Loc) (s : RState) : IProp GF :=
  iprop(∃ xs, replicaOwnX ρ k r xs s)

end owns

/-! ## The network side: obligations, channels -/

section bag
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]

/-- A channel field `f` of the struct at `l` (struct type `T`) holding a bag channel named
`ρ.chans nm` with element predicate `P`. -/
def bagAt {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.GoType}
    [IntoValTyped (GF := GF) V t] (ρ : Repl2Names) (T : Type) (l : Loc) (f : GoString)
    (nm : String) (P : V → IProp GF) : IProp GF :=
  iprop(∃ ch : Loc, l.[T, f] ↦□ ch ∗ isChanBag (ρ.chans nm) ch P)

end bag


section net
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics] [fa : src.fastrpc.Assumptions]


/-- The ghost name of the client writers' escrow (unit N's; a name of `ρ.chans` no channel
uses, allocated with the others by `NewReplica`): the client ids whose writers the run loop has
taken (`clientsOwn`). -/
def escrowName (ρ : Repl2Names) : GName := (ρ.chans "clientEscrow").stateName

/-- Replica id `k`'s peers. -/
def peers (k : Fin 3) : List (Fin 3) := (List.finRange 3).filter (· ≠ k)

/-- **Unit N's slot.** Replica id `k`'s writer `w` of its connection with peer `q` has been handed
the first messages `ms` of `k`'s stream to `q` (on the wire if the writer has no error: the
connection's protocol, `peerStreamOk`, holds of what it sent; a failed writer accepts nothing
more, `Wire/Specs.lean`'s `wp_Marshal`), with nothing buffered. Its body (the `bufio.Writer`'s
`ownWriter` with the dial / accept protocol of the connection, `Proto/Wire.lean`) is unit N's. -/
@[irreducible] def peerWriterAt (_γ : GryffNames GF) (_k _q : Fin 3) (_w : Loc)
    (_ms : List Msg) : IProp GF := netN.peerWriterB _γ _k _q _w _ms

/-- **Unit N's slot.** The client writers replica `k` has taken from `clientWriters` (the lock's
part of the client-writer hand-off: `serveClient` registers a connection's writer under
`clientIdMapsLock`; the run loop, under the replica's lock, writes the replies), each writer's
bytes being whole replies with their `clientReplyOk` (`Proto/Wire.lean`'s `acceptStream`). -/
@[irreducible] def clientsOwn (_γ : GryffNames GF) (_ρ : Repl2Names) (_k : Fin 3) (_gR : Loc) :
    IProp GF :=
  iprop((∃ C : GMap w32 Loc, ghostMapAuth (escrowName _ρ) (1 : Qp) C ∗
      [∗map] hs ↦ w ∈ C, writerIs _ρ hs w ∗ netN.clientWriterB _γ hs w) ∗
    ∃ (dS : GoSlice) (dms : List Loc), _gR.[src.genericsmr.Replica, go!"delayRPC"] ↦□ dS ∗
      dS ↦*□ dms ∗ ⌜dms.length = 3⌝ ∗
      [∗list] mp ∈ dms, ∃ M : GMap w8 Bool, mp ↦$ M ∗ ⌜∀ c b, M !! c = some b → b = false⌝)

/-- The self stream's receiving side, held by the lock: the cursor (`rxCurTok γ k k n`), with
`owed` the self-messages still to be given tokens, the stream's suffix after the cursor
(`n + |owed| = |st|` and `st.drop n = owed`, S-1; `st` the stream `streamOf k k t`). Every self-send happens under the lock after its step's resolution (the run
loop's handlers; the executor's `ExecuteOverwrite` since fork 9b1b858), so each self-message's
token is minted (`recv_msg` at `k = q`) before its channel send and travels in the channel
element (`msgChanP`, `eoChanP`): no escrow. -/
def selfOwn (γ : GryffNames GF) (k : Fin 3) (st owed : List Msg) : IProp GF :=
  iprop(∃ n : Nat, rxCurTok γ.proto k k n ∗ ⌜n + owed.length = st.length ∧ st.drop n = owed⌝)

/-- The generic replica's `Alive` slice after `ConnectToPeers` (N1-3): the peers' entries true,
the own entry `k` false (the code never sets it; the broadcast loops range over the peers). -/
def aliveList (k : Fin 3) : List Bool :=
  [decide ((0 : Fin 3) ≠ k), decide ((1 : Fin 3) ≠ k), decide ((2 : Fin 3) ≠ k)]

theorem aliveList_get (k q : Fin 3) : (aliveList k)[q.val]? = some (decide (q ≠ k)) := by
  obtain ⟨q, hq⟩ := q
  rcases q with _ | _ | _ | q
  · rfl
  · rfl
  · rfl
  · omega

/-- The `Alive` field of the generic replica `gR` of replica `k` (persistent; set by
`ConnectToPeers` / `waitForPeerConnections` without the lock, before the run loop; N1-3). -/
def aliveAt (k : Fin 3) (gR : Loc) : IProp GF :=
  iprop(∃ aS : GoSlice, gR.[src.genericsmr.Replica, go!"Alive"] ↦□ aS ∗ aS ↦*□ aliveList k)

instance aliveAt_persistent (k : Fin 3) (gR : Loc) : Persistent (aliveAt (GF := GF) k gR) := by
  unfold aliveAt; infer_instance

/-- The network side of replica `k`'s lock at trace `t`, with `owed q` the messages to `q` still to
send (a suffix of `streamOf k q t`): the peer writers, the self stream, the client writers, the
trace's lower bound, the `Alive` slice (N1-3). -/
def netAt (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc) (t : List Ev)
    (owed : Fin 3 → List Msg) : IProp GF :=
  iprop(∃ (gR : Loc) (pwS : GoSlice) (pws : List Loc),
    r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗
    gR.[src.genericsmr.Replica, go!"PeerWriters"] ↦□ pwS ∗ pwS ↦*□ pws ∗
    ([∗list] q ∈ peers k, ∃ (w : Loc) (ms : List Msg),
      ⌜pws[q.val]? = some w ∧ ms ++ owed q = streamOf k q t⌝ ∗ peerWriterAt γ k q w ms) ∗
    selfOwn γ k (streamOf k k t) (owed k) ∗ clientsOwn γ ρ k gR ∗ traceLb γ.proto k t ∗
    aliveAt k gR) -- N1-3

/-- **The obligations of a step** (replica `k` at trace `t`, after `replica_step`): the outputs
`outs` still to be sent, in order per destination (a message to a peer by `SendMsg`, to itself on
its channel with its receive token, a client reply with its `opDone`). `pendingOuts γ ρ k r t []` is
what the lock holds between steps. It depends on `outs` only through each destination's
messages and the replies (`pendingOuts_congr`): the code may interleave destinations. -/
@[irreducible] def pendingOuts (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc)
    (t : List Ev) (outs : List Out) : IProp GF :=
  iprop(netAt γ ρ k r t (fun q => sentToR q outs) ∗
    [∗list] x ∈ pure.extsIn outs, opDone γ.proto x.keyZ x.out)

/-- The kind of a message (the run loop's channel for it, and its `fastrpc` registration). -/
def msgKind : Msg → String
  | .read1 _ => "read1" | .read2 _ => "read2" | .read1Reply _ => "read1Reply"
  | .read2Reply _ => "read2Reply" | .write1 _ => "write1" | .write2 _ => "write2"
  | .write1Reply _ => "write1Reply" | .write2Reply _ => "write2Reply"
  | .preAccept _ => "preAccept" | .preAcceptReply _ => "preAcceptReply"
  | .preAcceptOK _ => "preAcceptOK" | .accept _ => "accept" | .acceptReply _ => "acceptReply"
  | .commit _ => "commit" | .prepare _ => "prepare" | .prepareReply _ => "prepareReply"
  | .executed _ => "executed" | .executeOverwrite _ => "executeOverwrite"

/-- An element of the channel of kind `kd` (the `fastrpc.Serializable` channels the listeners
and the replica's self-sends fill): a message of that kind with its receive token (`recv_msg`'s:
from a peer's listener, `k' ≠ k`, or from the replica's own send under its lock, `k' = k`,
`pendingOuts_self`). -/
def msgChanP (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (kd : String) (v : GoInterface) :
    IProp GF :=
  iprop(∃ (p : Loc) (m : Msg), ⌜msgKind m = kd ∧ v = interface.mkOk (msgTy m) #p⌝ ∗ msgAt p m ∗
    ∃ (k' : Fin 3) (n : Nat), rxTok γ.proto k' k n m)

/-- An element of `executeOverwriteChan` (a bare `*ExecuteOverwrite`; self-messages only, sent by
the executor under the lock after `resolveExec` and the step: `pendingOuts_self`'s token). -/
def eoChanP (γ : GryffNames GF) (k : Fin 3) (p : Loc) : IProp GF :=
  iprop(∃ m, msgAt p (.executeOverwrite m) ∗ ∃ n, rxTok γ.proto k k n (.executeOverwrite m))

/-- An element of a client request channel (`readChan`, `writeChan`, `rmwChan`, kind `kd`): a
`*ClientRPC{obj, writer}` from `serveClient`, the request event `e` with its token (`req_mint`),
the writer its client id's, and the request's shape (`Ev.Producible`: key 0, `D.Key < 0`, client
id ≥ 0), which `serveClient` reads off the parsed bytes (`Proto/WireDefs.reqBytesD`: `K' = 0`,
`D'.Key' = -1`, `ClientId' = hs`; the handshake's `hs < peerMark`), for `step_ok_req`. -/
def reqChanP (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (kd : String) (c : Loc) :
    IProp GF :=
  iprop(∃ (p w : Loc) (e : Ev) (cid rid : w32) (i : dsverify_lab.harness.RegInput w64),
    c ↦ (src.genericsmr.ClientRPC.mk (interface.mkOk (go.GoType.PointerType
      (if kd = "read" then src.gryffproto.Read.ty else if kd = "write" then src.gryffproto.Write.ty
       else src.gryffproto.RMW.ty)) #p) w) ∗
    reqAt kd p e ∗ writerIs ρ cid w ∗ evTok γ.proto k e ∗
    ⌜e.clientReq = some (cid, rid, i) ∧ e.Producible⌝)

/-- An element of `instancesToRecover` (`*instanceId{q, i}` from the executor, which saw
`i < crtInstance[q]`): the recovery trigger's guard, by `crtInstance`'s monotonicity. -/
def recoverChanP (ρ : Repl2Names) (p : Loc) : IProp GF :=
  iprop(∃ q i : w32, p ↦ (src.gryff.instanceId.mk q i) ∗ ⌜model.rowOk q = true ∧ 0 ≤ sint.Z i⌝ ∗
    ∃ hq : sint.Z q < 3, monoNatLbOwn (ρ.crt ⟨(sint.Z q).toNat, by omega⟩) ((sint.Z i).toNat + 1))

/-! ## The lock invariant and the handle -/

/-- The lock's contents at trace `t` and search state `xs` (what a holder of the lock opens,
after the boot). -/
def lockedAt (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc) (p : ProphId)
    (t : List Ev) (xs : XS) : IProp GF :=
  iprop(traceHalf γ.proto k t ∗ replicaProph γ.proto k p t [] ∗
    replicaOwnX ρ k r xs (pure.stOf k t) ∗ pendingOuts γ ρ k r t [] ∗
    ghostVar ρ.boot (1 : Qp).half false)

/-- The lock's contents before the run loop's first `Lock` (the boot state): the EPaxos handler at
the initial state only. `NewEPaxosRMWHandler` starts the executor (`go e.executeCommands()`)
before `NewReplica` has built the participant, the coordinator and the rpc tables, and before
`ConnectToPeers` has set the peer writers (without the lock): the run goroutine holds the rest
(`loopTok`) and completes the lock invariant at its first iteration; meanwhile the executor finds
no instance (`crtInstance` is all 0) and only reads the instance space's bookkeeping. -/
def lockBoot (ρ : Repl2Names) (k : Fin 3) (r : Loc) : IProp GF :=
  iprop(∃ (h : Loc) (xs : XS), r.[src.gryff.Replica, go!"rmwHandler"] ↦□ handlerIface h ∗
    epaxosOwn ρ h r xs (model.RState.init k.val) ∗ ghostVar ρ.xs (1 : Qp).half xs ∗
    ghostVar ρ.boot (1 : Qp).half true)

/-- **Replica `k`'s lock invariant** (G2's mutex; `p` its trace prophecy): after the boot, the
trace's half, the prophecy at that trace with nothing resolved ahead, the heap at the trace's
model state, the network side with nothing owed (`lockedAt`); before, `lockBoot`. -/
def replicaLockInv (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc) (p : ProphId) :
    IProp GF :=
  iprop((∃ (t : List Ev) (xs : XS), lockedAt γ ρ k r p t xs) ∨ lockBoot ρ k r)

/-- The run goroutine's boot resources beyond the network side (unit N's, `loopTok`'s body): the
prophecy at the empty trace, the trace's half, and the replica's heap at the initial state but
the EPaxos part (which the lock's boot state holds, `lockBoot`). -/
def bootRest (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc) : IProp GF :=
  iprop(∃ (p : ProphId) (gR pa co h : Loc), r.[src.gryff.Replica, go!"proph"] ↦□ p ∗
    traceHalf γ.proto k [] ∗ replicaProph γ.proto k p [] [] ∗
    r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ r.[src.gryff.Replica, go!"parti"] ↦□ pa ∗
    r.[src.gryff.Replica, go!"coord"] ↦□ co ∗
    r.[src.gryff.Replica, go!"rmwHandler"] ↦□ handlerIface h ∗
    partiOwn pa (replicaIface r) k (pure.stOf k []).tag (pure.stOf k []).ongoing ∗
    valOwn gR (pure.stOf k []).val ∗ coordOwn ρ co (replicaIface r) k (pure.stOf k []) ∗
    proposeOwn ρ gR (pure.stOf k []).proposeQ ∗ scratchOwn r ∗ ⌜(pure.stOf k []).id = rid32 k⌝)

/-- **Unit H/N's slot.** The run goroutine's own resources across `Loop` iterations: before the
first, the boot half `ghostVar ρ.boot ½ true` with the rest of the replica's heap at the initial
state (`replicaOwn` without the EPaxos part), the trace's half at `[]`, the prophecy, and the
network side with the peer writers `ConnectToPeers` set (to deposit into the lock: `lockBoot` ⟶
`lockedAt`); after, the half `ghostVar ρ.boot ½ false`. -/
@[irreducible] def loopTok (_γ : GryffNames GF) (_ρ : Repl2Names) (_k : Fin 3) (_r : Loc) :
    IProp GF :=
  iprop(ghostVar _ρ.boot (1 : Qp).half false ∨
    (ghostVar _ρ.boot (1 : Qp).half true ∗ bootRest _γ _ρ _k _r ∗ pendingOuts _γ _ρ _k _r [] []))


/-- The run loop's channels (`Loop`'s `select`), each a bag: the message channels of the
`gryff.Replica` (`*ChanProxied`, `*ReplyChan`) and of the EPaxos handler (`prepareChan`, ...),
the client request channels, `forceWriteChan`
(no content), and the channels nothing sends to in this configuration (element `False`:
`write1TimeoutChan`, `write2ConcurrentTimeoutChan`, `commitShortChan`, `tryPreAcceptChan`,
`tryPreAcceptReplyChan`, `preAcceptOKReplyChan`, `acceptOKReplyChan`, `BeaconChan`,
`DoneAdaptingChan`, `OnClientConnect`; the listeners never get those kinds: the peer stream
protocol carries model messages only). `executeOverwriteChan` and `instancesToRecover` are the
executor's handle's (`isExec`). -/
@[irreducible] def replicaChans (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc) :
    IProp GF :=
  iprop(
    bagAt (t := src.fastrpc.Serializable.ty) ρ src.gryff.Replica r go!"read1ChanProxied" "read1" (msgChanP γ ρ k "read1") ∗
    bagAt (t := src.fastrpc.Serializable.ty) ρ src.gryff.Replica r go!"read2ChanProxied" "read2" (msgChanP γ ρ k "read2") ∗
    bagAt (t := src.fastrpc.Serializable.ty) ρ src.gryff.Replica r go!"write1ChanProxied" "write1" (msgChanP γ ρ k "write1") ∗
    bagAt (t := src.fastrpc.Serializable.ty) ρ src.gryff.Replica r go!"write2ChanProxied" "write2" (msgChanP γ ρ k "write2") ∗
    bagAt (t := src.fastrpc.Serializable.ty) ρ src.gryff.Replica r go!"read1ReplyChan" "read1Reply" (msgChanP γ ρ k "read1Reply") ∗
    bagAt (t := src.fastrpc.Serializable.ty) ρ src.gryff.Replica r go!"read2ReplyChan" "read2Reply" (msgChanP γ ρ k "read2Reply") ∗
    bagAt (t := src.fastrpc.Serializable.ty) ρ src.gryff.Replica r go!"write1ReplyChan" "write1Reply"
      (msgChanP γ ρ k "write1Reply") ∗
    bagAt (t := src.fastrpc.Serializable.ty) ρ src.gryff.Replica r go!"write2ReplyChan" "write2Reply"
      (msgChanP γ ρ k "write2Reply") ∗
    bagAt (t := src.fastrpc.Serializable.ty) ρ src.gryff.EPaxosRMWHandler h go!"prepareChan" "prepare" (msgChanP γ ρ k "prepare") ∗
    bagAt (t := src.fastrpc.Serializable.ty) ρ src.gryff.EPaxosRMWHandler h go!"preAcceptChan" "preAccept"
      (msgChanP γ ρ k "preAccept") ∗
    bagAt (t := src.fastrpc.Serializable.ty) ρ src.gryff.EPaxosRMWHandler h go!"acceptChan" "accept" (msgChanP γ ρ k "accept") ∗
    bagAt (t := src.fastrpc.Serializable.ty) ρ src.gryff.EPaxosRMWHandler h go!"commitChan" "commit" (msgChanP γ ρ k "commit") ∗
    bagAt (t := src.fastrpc.Serializable.ty) ρ src.gryff.EPaxosRMWHandler h go!"prepareReplyChan" "prepareReply"
      (msgChanP γ ρ k "prepareReply") ∗
    bagAt (t := src.fastrpc.Serializable.ty) ρ src.gryff.EPaxosRMWHandler h go!"preAcceptReplyChan" "preAcceptReply"
      (msgChanP γ ρ k "preAcceptReply") ∗
    bagAt (t := src.fastrpc.Serializable.ty) ρ src.gryff.EPaxosRMWHandler h go!"preAcceptOKChan" "preAcceptOK"
      (msgChanP γ ρ k "preAcceptOK") ∗
    bagAt (t := src.fastrpc.Serializable.ty) ρ src.gryff.EPaxosRMWHandler h go!"acceptReplyChan" "acceptReply"
      (msgChanP γ ρ k "acceptReply") ∗
    bagAt (t := src.fastrpc.Serializable.ty) ρ src.gryff.EPaxosRMWHandler h go!"executedChan" "executed"
      (msgChanP γ ρ k "executed") ∗
    bagAt (t := go.GoType.PointerType src.genericsmr.ClientRPC.ty) ρ src.gryff.Replica r go!"readChan" "read" (reqChanP γ ρ k "read") ∗
    bagAt (t := go.GoType.PointerType src.genericsmr.ClientRPC.ty) ρ src.gryff.Replica r go!"writeChan" "write" (reqChanP γ ρ k "write") ∗
    bagAt (t := go.GoType.PointerType src.genericsmr.ClientRPC.ty) ρ src.gryff.Replica r go!"rmwChan" "rmw" (reqChanP γ ρ k "rmw") ∗
    bagAt (t := go.bool) ρ src.gryff.Replica r go!"forceWriteChan" "forceWrite" (fun (_ : Bool) => iprop(True)) ∗
    bagAt (t := src.fastrpc.Serializable.ty) ρ src.gryff.Replica r go!"write1TimeoutChan" "w1timeout"
      (fun (_ : GoInterface) => iprop(False)) ∗
    bagAt (t := src.fastrpc.Serializable.ty) ρ src.gryff.Replica r go!"write2ConcurrentTimeoutChan" "w2timeout"
      (fun (_ : GoInterface) => iprop(False)) ∗
    bagAt (t := src.fastrpc.Serializable.ty) ρ src.gryff.EPaxosRMWHandler h go!"commitShortChan" "commitShort"
      (fun (_ : GoInterface) => iprop(False)) ∗
    bagAt (t := src.fastrpc.Serializable.ty) ρ src.gryff.EPaxosRMWHandler h go!"tryPreAcceptChan" "tryPreAccept"
      (fun (_ : GoInterface) => iprop(False)) ∗
    bagAt (t := src.fastrpc.Serializable.ty) ρ src.gryff.EPaxosRMWHandler h go!"tryPreAcceptReplyChan" "tryPreAcceptReply"
      (fun (_ : GoInterface) => iprop(False)) ∗
    bagAt (t := src.fastrpc.Serializable.ty) ρ src.gryff.EPaxosRMWHandler h go!"preAcceptOKReplyChan" "preAcceptOKReply"
      (fun (_ : GoInterface) => iprop(False)) ∗
    bagAt (t := src.fastrpc.Serializable.ty) ρ src.gryff.EPaxosRMWHandler h go!"acceptOKReplyChan" "acceptOKReply"
      (fun (_ : GoInterface) => iprop(False)) ∗
    bagAt (t := go.GoType.PointerType src.genericsmr.Beacon.ty) ρ src.genericsmr.Replica gR
      go!"BeaconChan" "beacon" (fun (_ : Loc) => iprop(False)) ∗
    bagAt (t := go.bool) ρ src.genericsmr.Replica gR go!"DoneAdaptingChan" "doneAdapting"
      (fun (_ : Bool) => iprop(False)) ∗
    bagAt (t := go.bool) ρ src.genericsmr.Replica gR go!"OnClientConnect" "onClientConnect"
      (fun (_ : Bool) => iprop(False)))

/-- The message kinds on the peer connections (`fastrpc` registrations of the run loop's
channels). -/
def netKinds : List String :=
  ["prepare", "prepareReply", "preAccept", "preAcceptReply", "preAcceptOK", "accept",
    "acceptReply", "commit", "executed", "read1", "read2", "write1", "write2", "read1Reply",
    "read2Reply", "write1Reply", "write2Reply"]

/-- The Go type of the registered object of a kind (`msgTy` of its messages). -/
def kindTy (kd : String) : go.GoType :=
  if kd = "prepare" then go.GoType.PointerType src.epaxosproto.Prepare.ty
  else if kd = "prepareReply" then go.GoType.PointerType src.gryffproto.PrepareReply.ty
  else if kd = "preAccept" then go.GoType.PointerType src.gryffproto.PreAccept.ty
  else if kd = "preAcceptReply" then go.GoType.PointerType src.gryffproto.PreAcceptReply.ty
  else if kd = "preAcceptOK" then go.GoType.PointerType src.epaxosproto.PreAcceptOK.ty
  else if kd = "accept" then go.GoType.PointerType src.gryffproto.EAccept.ty
  else if kd = "acceptReply" then go.GoType.PointerType src.epaxosproto.AcceptReply.ty
  else if kd = "commit" then go.GoType.PointerType src.gryffproto.ECommit.ty
  else if kd = "executed" then go.GoType.PointerType src.gryffproto.Executed.ty
  else if kd = "read1" then go.GoType.PointerType src.gryffproto.Read1Proxied.ty
  else if kd = "read2" then go.GoType.PointerType src.gryffproto.Read2Proxied.ty
  else if kd = "write1" then go.GoType.PointerType src.gryffproto.Write1Proxied.ty
  else if kd = "write2" then go.GoType.PointerType src.gryffproto.Write2Proxied.ty
  else if kd = "read1Reply" then go.GoType.PointerType src.gryffproto.Read1Reply.ty
  else if kd = "read2Reply" then go.GoType.PointerType src.gryffproto.Read2Reply.ty
  else if kd = "write1Reply" then go.GoType.PointerType src.gryffproto.Write1Reply.ty
  else go.GoType.PointerType src.gryffproto.Write2Reply.ty

/-- The client request kinds (`RegisterClientRPC`'s, beyond `GEN_PING`). -/
def reqKinds : List String := ["read", "write", "rmw"]

/-- The opcode of a client request kind (`clientproto.Gryff_READ`, ...). -/
def reqCode (kd : String) : w8 :=
  if kd = "read" then gryffRead else if kd = "write" then gryffWrite else gryffRMW

/-- The Go type of a client request kind's object. -/
def reqTy (kd : String) : go.GoType :=
  if kd = "read" then go.GoType.PointerType src.gryffproto.Read.ty
  else if kd = "write" then go.GoType.PointerType src.gryffproto.Write.ty
  else go.GoType.PointerType src.gryffproto.RMW.ty

/-- The fixed fields of the generic replica, of the EPaxos handler `h` and of `*gryff.Replica` `r`
that the handlers read (unit N's, in `genericOk`; `Replica2/Specs.lean`'s `h2Fixed` and
`prepCodes` are its laws): `Thrifty` false, `Exec` true, `PreferredPeerOrder` (`Alive` is not here:
`ConnectToPeers` writes it; it is in the lock's `netAt`, `aliveAt`, N1-3),
`PeerAddrList` (3 addresses), `Stats` (`statsOk`'s body), the broadcast optimization off, and the
rpc codes each kind was registered with, in the handler's and the replica's `*RPC` fields,
`Dreply` true (H2c-R3), `r.maxSeenTag` (never written after `NewReplica`: `TagSeen` is never
called). -/
def genericFixed (k : Fin 3) (r gR h : Loc) : IProp GF :=
  iprop(∃ (pS alS : GoSlice) (addrs : List GoString) (st : Loc)
      (cPA cA cC cCS cPAR cPAO cAR cEx cP cPR cR1 cR2 cW1 cW2 cR1R cR2R cW1R cW2R : w8),
    gR.[src.genericsmr.Replica, go!"Thrifty"] ↦□ false ∗
    gR.[src.genericsmr.Replica, go!"Exec"] ↦□ true ∗ -- `Alive`: N1-3 (in `netAt`)
    gR.[src.genericsmr.Replica, go!"PreferredPeerOrder"] ↦□ pS ∗
      pS ↦*□ [W32 (((k.val : Int) + 1) % 3), W32 (((k.val : Int) + 2) % 3), rid32 k] ∗ -- N-9
    gR.[src.genericsmr.Replica, go!"PeerAddrList"] ↦□ alS ∗ alS ↦*□ addrs ∗
      ⌜addrs.length = 3⌝ ∗
    gR.[src.genericsmr.Replica, go!"Stats"] ↦□ st ∗ netN.statsOkB st ∗
    h.[src.gryff.EPaxosRMWHandler, go!"broadcastOptimizationEnabled"] ↦□ false ∗
    h.[src.gryff.EPaxosRMWHandler, go!"preAcceptRPC"] ↦□ cPA ∗ ⌜netN.kindCode "preAccept" = some cPA⌝ ∗
    h.[src.gryff.EPaxosRMWHandler, go!"acceptRPC"] ↦□ cA ∗ ⌜netN.kindCode "accept" = some cA⌝ ∗
    h.[src.gryff.EPaxosRMWHandler, go!"commitRPC"] ↦□ cC ∗ ⌜netN.kindCode "commit" = some cC⌝ ∗
    h.[src.gryff.EPaxosRMWHandler, go!"commitShortRPC"] ↦□ cCS ∗
    h.[src.gryff.EPaxosRMWHandler, go!"preAcceptReplyRPC"] ↦□ cPAR ∗
      ⌜netN.kindCode "preAcceptReply" = some cPAR⌝ ∗
    h.[src.gryff.EPaxosRMWHandler, go!"preAcceptOKRPC"] ↦□ cPAO ∗
      ⌜netN.kindCode "preAcceptOK" = some cPAO⌝ ∗
    h.[src.gryff.EPaxosRMWHandler, go!"acceptReplyRPC"] ↦□ cAR ∗
      ⌜netN.kindCode "acceptReply" = some cAR⌝ ∗
    h.[src.gryff.EPaxosRMWHandler, go!"executedRPC"] ↦□ cEx ∗ ⌜netN.kindCode "executed" = some cEx⌝ ∗
    h.[src.gryff.EPaxosRMWHandler, go!"prepareRPC"] ↦□ cP ∗ ⌜netN.kindCode "prepare" = some cP⌝ ∗
    h.[src.gryff.EPaxosRMWHandler, go!"prepareReplyRPC"] ↦□ cPR ∗
      ⌜netN.kindCode "prepareReply" = some cPR⌝ ∗
    r.[src.gryff.Replica, go!"read1RPC"] ↦□ cR1 ∗ ⌜netN.kindCode "read1" = some cR1⌝ ∗
    r.[src.gryff.Replica, go!"read2RPC"] ↦□ cR2 ∗ ⌜netN.kindCode "read2" = some cR2⌝ ∗
    r.[src.gryff.Replica, go!"write1RPC"] ↦□ cW1 ∗ ⌜netN.kindCode "write1" = some cW1⌝ ∗
    r.[src.gryff.Replica, go!"write2RPC"] ↦□ cW2 ∗ ⌜netN.kindCode "write2" = some cW2⌝ ∗
    r.[src.gryff.Replica, go!"read1ReplyRPC"] ↦□ cR1R ∗ ⌜netN.kindCode "read1Reply" = some cR1R⌝ ∗
    r.[src.gryff.Replica, go!"read2ReplyRPC"] ↦□ cR2R ∗ ⌜netN.kindCode "read2Reply" = some cR2R⌝ ∗
    r.[src.gryff.Replica, go!"write1ReplyRPC"] ↦□ cW1R ∗
      ⌜netN.kindCode "write1Reply" = some cW1R⌝ ∗
    r.[src.gryff.Replica, go!"write2ReplyRPC"] ↦□ cW2R ∗
      ⌜netN.kindCode "write2Reply" = some cW2R⌝ ∗
    gR.[src.genericsmr.Replica, go!"Dreply"] ↦□ true ∗ -- H2c-R3 (integrator 3)
    ∃ tg : src.gryffproto.Tag, r.[src.gryff.Replica, go!"maxSeenTag"] ↦□ tg)

/-- **Unit N's slot.** The rpc code of a message kind (`RegisterRPC`'s registration order;
persistent): the code `SendMsg` writes before a message of kind `kd`, and `msgWire`'s
(`Proto2/Wire.lean`). -/
@[irreducible] def rpcCodeIs (_kd : String) (_code : w8) : IProp GF :=
  iprop(⌜netN.kindCode _kd = some _code⌝)

/-- **Unit N's slot.** The generic replica's fixed parts (persistent): the rpc codes the replica
registered (in `r.*RPC` / `e.*RPC`) and the `rpcTable` / `clientRpcTable` mapping them to the
channels of `replicaChans` (the listeners' dispatch); `delayRPC` empty (no delayed sends); the
`clientIdMapsLock` with its invariant (the client readers and writers, `writerIs`); `Stats`
(`statsOk`); `PeerAddrList` (the replicas' addresses, `nodes`). -/
@[irreducible] def genericOk (_γ : GryffNames GF) (_ρ : Repl2Names) (_k : Fin 3)
    (_r _gR _h : Loc) : IProp GF :=
  iprop(□ ∃ (rt ct st mu cwm crm : Loc) (M CM : GMap w8 Loc),
    _gR.[src.genericsmr.Replica, go!"rpcTable"] ↦□ rt ∗ rt ↦${DFrac.discard} M ∗
    ([∗list] kd ∈ netKinds, ∃ (c : w8) (pp obj ch : Loc),
      ⌜netN.kindCode kd = some c ∧ M !! c = some pp⌝ ∗
      pp ↦□ src.genericsmr.RPCPair.mk (interface.mkOk (kindTy kd) #obj) ch ∗
      isChanBag (_ρ.chans kd) ch (msgChanP _γ _ρ _k kd)) ∗
    _gR.[src.genericsmr.Replica, go!"clientRpcTable"] ↦□ ct ∗ ct ↦${DFrac.discard} CM ∗
    ([∗list] kd ∈ reqKinds, ∃ (c : w8) (pp obj ch : Loc),
      ⌜reqCode kd = c ∧ CM !! c = some pp⌝ ∗
      pp ↦□ src.genericsmr.ClientRPCPair.mk (interface.mkOk (reqTy kd) #obj) ch ∗
      isChanBag (_ρ.chans kd) ch (reqChanP _γ _ρ _k kd)) ∗
    _gR.[src.genericsmr.Replica, go!"Stats"] ↦□ st ∗ netN.statsOkB st ∗
    _gR.[src.genericsmr.Replica, go!"clientIdMapsLock"] ↦□ mu ∗
    _gR.[src.genericsmr.Replica, go!"clientWriters"] ↦□ cwm ∗
    _gR.[src.genericsmr.Replica, go!"clientReaders"] ↦□ crm ∗
    sync.isMutex mu iprop(∃ (RM WM : GMap w32 Loc), crm ↦$ RM ∗ cwm ↦$ WM ∗
      ghostMapAuth _ρ.writers (1 : Qp).half WM ∗
      [∗map] hs ↦ _w ∈ WM, ∃ c : Nat, clientConnAt _γ hs c ∗ placedConn _γ c) ∗
    inv netN.escrowN iprop(∃ WM : GMap w32 Loc, ghostMapAuth _ρ.writers (1 : Qp).half WM ∗
      [∗map] hs ↦ w ∈ WM, netN.clientWriterB _γ hs w ∨
        ghostMapElem (escrowName _ρ) hs (DFrac.own 1) w) ∗
    _gR.[src.genericsmr.Replica, go!"Id"] ↦□ rid32 _k ∗
    _gR.[src.genericsmr.Replica, go!"Shutdown"] ↦□ false ∗
    _gR.[src.genericsmr.Replica, go!"clientConnect"] ↦□ false ∗
    isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
    isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
    genericFixed _k _r _gR _h)

/-- `rpcCodeIs` is persistent (H2-R3; its body is unit N's sealed slot). -/
instance rpcCodeIs_persistent (kd : String) (c : w8) : Persistent (rpcCodeIs (GF := GF) kd c : IProp GF) := by
  unfold rpcCodeIs; infer_instance

/-- `genericOk` is persistent (H2-R3; its body is unit N's sealed slot). -/
instance genericOk_persistent (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc) :
    Persistent (genericOk γ ρ k r gR h) := by
  unfold genericOk; infer_instance

/-- **The executor's handle** (persistent; what `go e.executeCommands()` starts with, inside
`NewEPaxosRMWHandler`, before the replica is complete): the fixed fields it reads, the mutex with
the lock invariant, the two channels it sends to, the invariants. -/
@[irreducible] def isExec (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc) :
    IProp GF :=
  iprop(∃ (gR mtx ex : Loc) (p : ProphId),
    r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗
    r.[src.gryff.Replica, go!"rmwHandler"] ↦□ handlerIface h ∗
    r.[src.gryff.Replica, go!"mtx"] ↦□ mtx ∗
    r.[src.gryff.Replica, go!"proph"] ↦□ p ∗
    r.[src.gryff.Replica, go!"Shutdown"] ↦□ false ∗ -- H-X-4 (`executeCommands`' loop test)
    h.[src.gryff.EPaxosRMWHandler, go!"R"] ↦□ r ∗
    h.[src.gryff.EPaxosRMWHandler, go!"exec"] ↦□ ex ∗ ex.[src.gryff.Exec, go!"r"] ↦□ h ∗
    gR.[src.genericsmr.Replica, go!"Id"] ↦□ rid32 k ∗
    gR.[src.genericsmr.Replica, go!"N"] ↦□ W64 3 ∗
    gR.[src.genericsmr.Replica, go!"Shutdown"] ↦□ false ∗
    sync.isMutex mtx (replicaLockInv γ ρ k r p) ∗
    bagAt (t := go.GoType.PointerType src.gryff.ExecuteOverwrite.ty) ρ src.gryff.EPaxosRMWHandler h
      go!"executeOverwriteChan" "executeOverwrite" (eoChanP γ k) ∗
    bagAt (t := go.GoType.PointerType src.gryff.instanceId.ty) ρ src.gryff.EPaxosRMWHandler h
      go!"instancesToRecover" "recover" (recoverChanP ρ) ∗
    gryffInv2 γ.proto ∗ predsSet γ.proto)

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 400000 in
instance isExec_persistent (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc) :
    Persistent (isExec γ ρ k r h) := by
  unfold isExec bagAt; infer_instance

/-- **Replica `k`'s handle** (persistent; `*gryff.Replica` at `r`): the executor's handle, the
configuration's flags (`Shutdown` false for good, proxy mode, `shortcircuitTime` 100 (B-R3: `run`
reads it), no beacons, replies after
execution, not durable), the run loop's channels, the generic replica's fixed parts. -/
@[irreducible] def isReplica (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc) :
    IProp GF :=
  iprop(∃ (gR h : Loc), isExec γ ρ k r h ∗
    r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗
    r.[src.gryff.Replica, go!"Shutdown"] ↦□ false ∗
    r.[src.gryff.Replica, go!"proxy"] ↦□ true ∗
    r.[src.gryff.Replica, go!"shortcircuitTime"] ↦□ W64 100 ∗
    gR.[src.genericsmr.Replica, go!"Beacon"] ↦□ false ∗
    gR.[src.genericsmr.Replica, go!"Dreply"] ↦□ true ∗
    gR.[src.genericsmr.Replica, go!"Durable"] ↦□ false ∗
    replicaChans γ ρ k r gR h ∗ genericOk γ ρ k r gR h)

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 400000 in
instance isReplica_persistent (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc) :
    Persistent (isReplica γ ρ k r) := by
  unfold isReplica replicaChans bagAt; infer_instance

end net

/-! ## The executor's own state (stage 1's, over `Repl2Names`) -/

section exec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]


/-- Stage 1's names from stage 2's (the stack's elements use `ptrs` only). -/
def Repl2Names.toR1 (ρ : Repl2Names) : replica.ReplNames :=
  ⟨ρ.xs, ρ.ptrs, ρ.ptrs, ρ.chans "executeOverwrite"⟩ -- `cm`, `ch`: unused by `stackOwn`

/-- The executor's own state (stage 1's `execPriv` without stage 1's chain share; `PrevValTag` is
the model's now, under the lock): its half of the search state, the package's `stack`,
`ExecedUpTo` (every instance up to it is executed). -/
@[irreducible] def execPriv2 (ρ : Repl2Names) (h : Loc) (xs : XS) (S : List replica.Node) :
    IProp GF :=
  iprop(ghostVar ρ.xs (1 : Qp).half xs ∗ stackOwn ρ.toR1 S ∗
    ∃ euS : GoSlice, h.[src.gryff.EPaxosRMWHandler, go!"ExecedUpTo"] ↦□ euS ∗ euOwn euS xs.1)

/-- What `strongconnect(v)` needs of the search's state beyond Tarjan's invariant (stage 1's
`scFacts` over the model state `s`): the stack's and the executed instances are committed or
executed in `s`, the executed ones are `s`'s, the index counter fits; and (H-X-2 (a)) the executed
set is closed under `s`'s dependencies (stage 1's `chainOk` gave it). -/
def scFacts2 (s : RState) (xs : XS) (S : List replica.Node) (idx : Nat) : Prop :=
  ((∀ u, u ∈ S ∨ u ∈ xs.1 → (model.committedCopy s u).isSome) ∧
    (∀ n, n ∈ xs.1 ↔ model.executedB s n = true) ∧
    ∃ vis : List replica.Node, vis.Nodup ∧ vis.length + 1 = idx ∧
      (∀ n ∈ vis, xs.numF n ≠ 0 ∧ replica.inBox n) ∧ ∀ u ∈ S, u ∈ vis) ∧
  replica.XClosed (model.depR s) xs.1 -- H-X-2 (a)

end exec

/-! ## Laws (statements; proofs in Prove)

Each with the callers that need it (`notes/stage2-interface-code.md`, §2). -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics] [fa : src.fastrpc.Assumptions]


/-! ### The model facts the abstraction needs (unit M's) -/

/-- `crtInstance` never decreases (the recovery trigger's guard survives the lock's release:
`recoverChanP`'s lower bound; every handler updating `crtInstance` updates `ρ.crt`). -/
theorem stepR_crt_mono (k : Fin 3) (s s' : RState) (e : Ev) (o : List Out)
    (h : model.stepR k s e = .ok (s', o)) (q : w32) : sint.Z (s.crt q) ≤ sint.Z (s'.crt q) :=
  (pure.step_pc h).2.1 q

/-- A step keeps the replica id. -/
theorem stepR_id (k : Fin 3) (s s' : RState) (e : Ev) (o : List Out)
    (h : model.stepR k s e = .ok (s', o)) : s'.id = s.id :=
  (pure.step_pc h).1

/-! ### The heap's projection -/

/-- The heap does not hold the model's ghost fields (`nReqs`, `used`): a client request's step
changes them for free. -/
theorem replicaOwnX_ghost (ρ : Repl2Names) (k : Fin 3) (r : Loc) (xs : XS) (s : RState)
    (n : Nat) (u : List (w32 × w32)) :
    replicaOwnX (GF := GF) ρ k r xs s ⊢ replicaOwnX ρ k r xs { s with nReqs := n, used := u } := by
  unfold replicaOwnX coordOwn epaxosOwn; exact .rfl

/-- The replica id. -/
theorem replicaOwn_id (ρ : Repl2Names) (k : Fin 3) (r : Loc) (s : RState) :
    replicaOwn (GF := GF) ρ k r s ⊢ replicaOwn ρ k r s ∗ ⌜s.id = rid32 k⌝ := by
  unfold replicaOwn replicaOwnX
  iintro ⟨%xs, %gR, %pa, %co, %h, H1, H2, H3, H4, Hp, Hv, Hc, He, Hx, Hpr, Hs, %Hid⟩
  isplitl
  · iexists xs, gR, pa, co, h
    iframe
    ipureintro; exact Hid
  · ipureintro; exact Hid

/-- **Split** (every handler's first step): the replica's heap is its packages' parts. -/
theorem replicaOwnX_split (ρ : Repl2Names) (k : Fin 3) (r : Loc) (xs : XS) (s : RState) :
    replicaOwnX ρ k r xs s ⊣⊢ ∃ (gR pa co h : Loc),
      r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ r.[src.gryff.Replica, go!"parti"] ↦□ pa ∗
      r.[src.gryff.Replica, go!"coord"] ↦□ co ∗
      r.[src.gryff.Replica, go!"rmwHandler"] ↦□ handlerIface h ∗
      partiOwn pa (replicaIface r) k s.tag s.ongoing ∗ valOwn gR s.val ∗
      coordOwn ρ co (replicaIface r) k s ∗ epaxosOwn ρ h r xs s ∗
      ghostVar ρ.xs (1 : Qp).half xs ∗ proposeOwn ρ gR s.proposeQ ∗ scratchOwn r ∗
      ⌜s.id = rid32 k⌝ := by
  unfold replicaOwnX; exact .rfl

/-- The coordinator's part depends on `maxN`, `rops`, `wops`, `ongoingReqs` only (the
coordinator's specs move the rest of the state with the participant's callbacks). -/
theorem coordOwn_congr (ρ : Repl2Names) (co : Loc) (ic : GoInterface) (k : Fin 3)
    (s s' : RState) (h1 : s'.maxN = s.maxN) (h2 : s'.rops = s.rops) (h3 : s'.wops = s.wops)
    (h4 : s'.ongoingReqs = s.ongoingReqs) :
    coordOwn (GF := GF) ρ co ic k s ⊢ coordOwn ρ co ic k s' := by
  unfold coordOwn; rw [h1, h2, h3, h4]

/-- The EPaxos part depends on the instances, `crtInstance`, `CommittedUpTo`, the conflict
tables and `PrevValTag` only. -/
theorem epaxosOwn_congr (ρ : Repl2Names) (h r : Loc) (xs : XS) (s s' : RState)
    (h1 : s'.inst = s.inst) (h2 : s'.crtInstance = s.crtInstance)
    (h3 : s'.committedUpTo = s.committedUpTo) (h4 : s'.conf = s.conf)
    (h5 : s'.maxSeqK0 = s.maxSeqK0) (h6 : s'.prevValTag = s.prevValTag) :
    epaxosOwn (GF := GF) ρ h r xs s ⊢ epaxosOwn ρ h r xs s' := by
  have hc : s'.crt = s.crt := by funext q; unfold RState.crt; rw [h2]
  have hcf : s'.confAt = s.confAt := by funext q; unfold RState.confAt; rw [h4]
  have hce : committedOrExecuted s' = committedOrExecuted s := by
    funext n; unfold committedOrExecuted model.committedCopy; rw [h1]
  unfold epaxosOwn; rw [hc, hcf, hce, h1, h2, h3, h4, h5, h6]

/-- A lower bound of `crtInstance[q]` (the executor's, before it sends a recovery trigger). -/
theorem epaxosOwn_crtLb (ρ : Repl2Names) (h r : Loc) (xs : XS) (s : RState) (q : Fin 3) :
    epaxosOwn (GF := GF) ρ h r xs s ⊢
      epaxosOwn ρ h r xs s ∗ monoNatLbOwn (ρ.crt q) (sint.Z (s.crt (rid32 q))).toNat := by
  unfold epaxosOwn
  iintro ⟨%ispS, %crtS, %c1S, %isp, %msR, %pvtR, %cfs, %M, %cu, %pm, H1, H2, H3, H4, H5, H6, H7,
    H8, H9, H10, H11, H12, H13, H14, H15, Hm, Hrest⟩
  icases unitS.monos_lb ρ.crt (fun q' => (sint.Z (s.crt (rid32 q'))).toNat) q $$ Hm with ⟨Hm, Hlb⟩
  iframe Hlb
  iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm
  iframe

/-- A lower bound is below `crtInstance[q]` (the run loop's recovery case: the trigger's guard). -/
theorem epaxosOwn_crtLb_le (ρ : Repl2Names) (h r : Loc) (xs : XS) (s : RState) (q : Fin 3)
    (n : Nat) :
    epaxosOwn ρ h r xs s ∗ monoNatLbOwn (ρ.crt q) n ⊢
      epaxosOwn ρ h r xs s ∗ ⌜n ≤ (sint.Z (s.crt (rid32 q))).toNat⌝ := by
  unfold epaxosOwn
  iintro ⟨⟨%ispS, %crtS, %c1S, %isp, %msR, %pvtR, %cfs, %M, %cu, %pm, H1, H2, H3, H4, H5, H6, H7,
    H8, H9, H10, H11, H12, H13, H14, H15, Hm, Hrest⟩, Hlb⟩
  icases unitS.monos_le ρ.crt (fun q' => (sint.Z (s.crt (rid32 q'))).toNat) q n $$ [Hm Hlb] with
    ⟨Hm, %hle⟩
  · iframe
  isplitl
  · iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm
    iframe
  · ipureintro; exact hle

/-! ### The obligations -/

/-- Only each destination's messages and the replies count (the code may interleave
destinations, and the participant's `OngoingWrites` loop may answer in any order). -/
theorem pendingOuts_congr (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc)
    (t : List Ev) (outs outs' : List Out) (h1 : ∀ q, sentToR q outs = sentToR q outs')
    (h2 : (pure.extsIn outs).Perm (pure.extsIn outs')) :
    pendingOuts γ ρ k r t outs ⊢ pendingOuts γ ρ k r t outs' := by
  have hf : (fun q => sentToR q outs) = (fun q => sentToR q outs') := funext h1
  unfold pendingOuts
  rw [hf]
  iintro ⟨Hn, Hd⟩
  iframe Hn
  iapply (BigSepL.bigSepL_perm h2).1 $$ Hd

/-- **After the step** (`Loop`'s cases, after `replica_step`): the lock's network side at `t`
with nothing owed, and `replica_step`'s results at `t ++ [e]`, are the obligations to send `outs`. -/
theorem pendingOuts_step (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc)
    (t : List Ev) (e : Ev) (outs : List Out)
    (hs : ∀ q : Fin 3, streamOf k q (t ++ [e]) = streamOf k q t ++ sentToR q outs) :
    pendingOuts γ ρ k r t [] ∗ traceLb γ.proto k (t ++ [e]) ∗
        ([∗list] x ∈ pure.extsIn outs, opDone γ.proto x.keyZ x.out) ⊢
      pendingOuts γ ρ k r (t ++ [e]) outs := by
  have sentToR_nil : ∀ q : Fin 3, sentToR q [] = [] := fun _ => rfl
  unfold pendingOuts netAt selfOwn
  iintro ⟨⟨⟨%gR, %pwS, %pws, #H1, #H2, #H3, Hpeers, ⟨%n, Hcur, %hn⟩, Hcl, -, #Hal⟩, -⟩, #Htlb, Hdone⟩
  iframe Hdone
  iexists gR, pwS, pws
  iframe H1 H2 H3 Hcl Htlb Hal
  isplitl [Hpeers]
  · iapply BigSepL.bigSepL_mono (fun {i x} _ => ?_) $$ Hpeers
    iintro ⟨%w, %ms, %hw, Hw⟩
    iexists w, ms
    iframe Hw
    ipureintro
    refine ⟨hw.1, ?_⟩
    have h2 := hw.2
    simp only [sentToR_nil, List.append_nil] at h2
    rw [hs x, h2]
  · iexists n
    iframe Hcur
    ipureintro
    simp only [sentToR_nil, List.length_nil, Nat.add_zero] at hn
    obtain ⟨h1, h2⟩ := hn
    refine ⟨?_, ?_⟩
    · show n + (sentToR k outs).length = (streamOf k k (t ++ [e])).length
      rw [hs k, List.length_append, h1]
    · show (streamOf k k (t ++ [e])).drop n = sentToR k outs
      rw [hs k, List.drop_append_of_le_length (by omega), h2, List.nil_append]

/-- **A send to itself** (`send*To(r.Id)`, `reply*Replica(r.Id)` in the run loop's handlers; the
executor's `executeOverwriteChan <- ...`; all under the lock, after the step): the next owed
message to itself gets its receive token (`recv_msg` at `k = q`, from the lock's self cursor and
the trace's lower bound), which goes in the channel element (`msgChanP`, `eoChanP`). -/
theorem pendingOuts_self (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc)
    (t : List Ev) (m : Msg) (outs : List Out) (E : CoPset) (hE : ↑gryffN ⊆ E) :
    gryffInv2 γ.proto ∗ pendingOuts γ ρ k r t (.send k m :: outs) ⊢
      |={E}=> ∃ j, pendingOuts γ ρ k r t outs ∗ rxTok γ.proto k k j m := by
  have hk : sentToR k (.send k m :: outs) = m :: sentToR k outs := by
    unfold sentToR; rw [pure.sentTo_eq, pure.sentTo_eq, pure.sentR_cons]; simp
  have hq : ∀ q, q ≠ k → sentToR q (.send k m :: outs) = sentToR q outs := by
    intro q hqk
    unfold sentToR; rw [pure.sentTo_eq, pure.sentTo_eq, pure.sentR_cons]; simp [Ne.symm hqk]
  have hx : pure.extsIn (.send k m :: outs) = pure.extsIn outs := rfl
  unfold pendingOuts netAt selfOwn
  rw [hx]
  iintro ⟨#Hinv, ⟨⟨%gR, %pwS, %pws, #H1, #H2, #H3, Hpeers, ⟨%n, Hcur, %hn⟩, Hcl, #Htlb, #Hal⟩, Hd⟩⟩
  simp only [] at hn
  rw [hk] at hn
  obtain ⟨hlen, hdrop⟩ := hn
  have hpre : (streamOf k k t).take n ++ [m] <+: streamOf k k t := by
    refine ⟨sentToR k outs, ?_⟩
    rw [List.append_assoc, List.singleton_append, ← hdrop, List.take_append_drop]
  have hl : ((streamOf k k t).take n).length = n := by
    rw [List.length_take]; simp only [List.length_cons] at hlen; omega
  ihave #Hs := streamLb_intro γ.proto k k t $$ Htlb
  ihave #Hs' := streamLb_prefix γ.proto k k _ _ hpre $$ Hs
  imod recv_msg γ.proto k k n _ m E hE hl $$ [Hcur] with ⟨Hcur, Htok⟩
  · iframe Hcur; iframe #
  imodintro
  iexists n
  iframe Htok
  iframe Hd
  iexists gR, pwS, pws
  iframe H1 H2 H3 Hcl Htlb Hal
  isplitl [Hpeers]
  · iapply BigSepL.bigSepL_mono (fun {i x} hx => ?_) $$ Hpeers
    have hxk : x ≠ k := by
      have := List.mem_of_getElem? hx
      unfold peers at this
      simpa using this
    iintro ⟨%w, %ms, %hw, Hw⟩
    iexists w, ms
    iframe Hw
    ipureintro
    refine ⟨hw.1, ?_⟩
    show ms ++ sentToR x outs = streamOf k x t
    rw [← hq x hxk]; exact hw.2
  · iexists n + 1
    iframe Hcur
    ipureintro
    simp only [List.length_cons] at hlen
    show n + 1 + (sentToR k outs).length = (streamOf k k t).length ∧
      (streamOf k k t).drop (n + 1) = sentToR k outs
    refine ⟨by omega, ?_⟩
    simpa using congrArg List.tail hdrop

/-- A step without outputs: the lock's network side moves to the new trace. -/
theorem pendingOuts_nil_step (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc)
    (t : List Ev) (e : Ev) (hs : ∀ q : Fin 3, streamOf k q (t ++ [e]) = streamOf k q t) :
    pendingOuts γ ρ k r t [] ∗ traceLb γ.proto k (t ++ [e]) ⊢ pendingOuts γ ρ k r (t ++ [e]) [] := by
  iintro ⟨Hp, Hlb⟩
  iapply pendingOuts_step γ ρ k r t e [] (fun q => by rw [hs q]; exact (List.append_nil _).symm)
  iframe Hp Hlb
  simp only [pure.extsIn, List.filterMap_nil]
  iapply BigSepL.bigSepL_nil.2
  itrivial

/-- **The `Alive` slice** (N1-3): the lock's network side holds it (`netAt`'s `aliveAt`), for
the handlers' broadcasts (`bcast*`, recovery) that skip the peers not alive. -/
theorem pendingOuts_alive (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR : Loc)
    (t : List Ev) (outs : List Out) :
    r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ pendingOuts γ ρ k r t outs ⊢
      pendingOuts γ ρ k r t outs ∗ aliveAt k gR := by
  unfold pendingOuts netAt
  iintro ⟨#HgR, ⟨%gR', %pwS, %pws, #HgR', #Hpw, #HpwS, Hpeers, Hself, Hcl, #Htlb, #Hal⟩, Hdone⟩
  icombine HgR HgR' gives %Heq
  subst Heq
  isplitl
  · iframe Hdone
    iexists gR, pwS, pws
    iframe
    iframe #
  · iexact Hal

/-! ### The handle -/

/-- The handle's contents (the run loop's first step). -/
theorem isReplica_open (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc) :
    isReplica γ ρ k r ⊣⊢ ∃ (gR h : Loc), isExec γ ρ k r h ∗
      r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗
      r.[src.gryff.Replica, go!"Shutdown"] ↦□ false ∗ r.[src.gryff.Replica, go!"proxy"] ↦□ true ∗
      r.[src.gryff.Replica, go!"shortcircuitTime"] ↦□ W64 100 ∗
      gR.[src.genericsmr.Replica, go!"Beacon"] ↦□ false ∗
      gR.[src.genericsmr.Replica, go!"Dreply"] ↦□ true ∗
      gR.[src.genericsmr.Replica, go!"Durable"] ↦□ false ∗
      replicaChans γ ρ k r gR h ∗ genericOk γ ρ k r gR h := by
  unfold isReplica; exact .rfl

/-- The executor's handle's contents (the executor's and the run loop's first step). -/
theorem isExec_open (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc) :
    isExec γ ρ k r h ⊣⊢ ∃ (gR mtx ex : Loc) (p : ProphId),
      r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗
      r.[src.gryff.Replica, go!"rmwHandler"] ↦□ handlerIface h ∗
      r.[src.gryff.Replica, go!"mtx"] ↦□ mtx ∗ r.[src.gryff.Replica, go!"proph"] ↦□ p ∗
      r.[src.gryff.Replica, go!"Shutdown"] ↦□ false ∗ -- H-X-4
      h.[src.gryff.EPaxosRMWHandler, go!"R"] ↦□ r ∗
      h.[src.gryff.EPaxosRMWHandler, go!"exec"] ↦□ ex ∗ ex.[src.gryff.Exec, go!"r"] ↦□ h ∗
      gR.[src.genericsmr.Replica, go!"Id"] ↦□ rid32 k ∗
      gR.[src.genericsmr.Replica, go!"N"] ↦□ W64 3 ∗
      gR.[src.genericsmr.Replica, go!"Shutdown"] ↦□ false ∗
      sync.isMutex mtx (replicaLockInv γ ρ k r p) ∗
      bagAt (t := go.GoType.PointerType src.gryff.ExecuteOverwrite.ty) ρ src.gryff.EPaxosRMWHandler h
        go!"executeOverwriteChan" "executeOverwrite" (eoChanP γ k) ∗
      bagAt (t := go.GoType.PointerType src.gryff.instanceId.ty) ρ src.gryff.EPaxosRMWHandler h
        go!"instancesToRecover" "recover" (recoverChanP ρ) ∗
      gryffInv2 γ.proto ∗ predsSet γ.proto := by
  unfold isExec; exact .rfl

end laws

end Perennial.gryff.replica2
