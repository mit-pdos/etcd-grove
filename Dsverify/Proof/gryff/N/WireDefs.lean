/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/N/WireDefs.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit N: the peer wire's per-message encoding (the body of `msgWire`)

A model message `m` is on the wire as the rpc code its kind was registered with (`rpcCodeOf`:
`RegisterRPC`'s order, `NewEPaxosRMWHandler` then `gryff.NewReplica`'s proxy registrations,
from `GEN_GENERIC_SMR_BEACON_REPLY + 1 = 8`), then its Go struct's encoding (`Wire/Enc.lean`)
whose model projection (the same projections as `Replica2/State.lean`'s `*Of`, restated here
because `Proto2/Wire.lean` comes before `State.lean`) is `m`. The struct is well formed: its
`[5]int32` arrays have five elements and its command slice fits an `int64` (true of every Go
value in memory; what makes the encoding injective). `ExecuteOverwrite` never goes on the wire.
-/
module

public import Dsverify.Proof.gryff.Wire.Enc
public import Dsverify.Proof.gryff.Model.Msg

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.gryff.netN

open model wire

variable [GooseExts]

/-! ## Projections (`Replica2/State.lean`'s, restated) -/

def tagOf (t : src.gryffproto.Tag) : model.Tag := ⟨t.Ts', t.Cid', t.Rmwc'⟩
def vtOf (v : src.gryffproto.ValTag) : model.ValTag := ⟨v.V', tagOf v.T'⟩
def depOf (d : src.gryffproto.Dep) : model.Dep := ⟨d.Key', vtOf d.Vt'⟩
def cmdOf (c : src.state.Command) : Cmd := ⟨c.Op', c.K', c.V', c.OldValue'⟩
def depsOf (a : GoArray w32 5) : Deps := a.arr

open wire.gryffproto wire.epaxosproto

def read1Of (g : Read1Proxied.Msg) : model.Read1ProxiedM :=
  ⟨g.RequestId', g.ClientId', g.K', depOf g.D', g.ReplicaId', vtOf g.Vt'⟩
def read2Of (g : Read2Proxied.Msg) : model.Read2ProxiedM :=
  ⟨g.RequestId', g.ClientId', g.K', vtOf g.Vt', g.ReplicaId'⟩
def read1ReplyOf (g : Read1Reply.Msg) : model.Read1ReplyM :=
  ⟨g.RequestId', g.ClientId', g.ReplicaId', vtOf g.Vt'⟩
def read2ReplyOf (g : Read2Reply.Msg) : model.Read2ReplyM := ⟨g.RequestId', g.ClientId'⟩
def write1Of (g : Write1Proxied.Msg) : model.Write1ProxiedM :=
  ⟨g.RequestId', g.ClientId', g.ForceWrite', g.K', depOf g.D', g.ReplicaId'⟩
def write1ReplyOf (g : Write1Reply.Msg) : model.Write1ReplyM :=
  ⟨g.RequestId', g.ClientId', vtOf g.Vt'⟩
def write2Of (g : Write2Proxied.Msg) : model.Write2ProxiedM :=
  ⟨g.RequestId', g.ClientId', g.K', vtOf g.Vt', g.ReplicaId'⟩
def write2ReplyOf (g : Write2Reply.Msg) : model.Write2ReplyM :=
  ⟨g.RequestId', g.ClientId', g.Applied'⟩
def preAcceptOf (g : PreAccept.Msg) : model.PreAcceptM :=
  ⟨g.LeaderId, g.Replica, g.Instance, g.Ballot, g.Command.map cmdOf, g.Seq, depsOf g.Deps,
    vtOf g.Base⟩
def preAcceptReplyOf (g : PreAcceptReply.Msg) : model.PreAcceptReplyM :=
  ⟨g.Replica', g.Instance', g.OK', g.Ballot', g.Seq', depsOf g.Deps', vtOf g.Base'⟩
def preAcceptOKOf (g : PreAcceptOK.Msg) : model.PreAcceptOKM := ⟨g.Instance'⟩
def acceptOf (g : EAccept.Msg) : model.EAcceptM :=
  ⟨g.LeaderId, g.Replica, g.Instance, g.Ballot, g.Seq, depsOf g.Deps, g.Command.map cmdOf,
    vtOf g.Base⟩
def acceptReplyOf (g : AcceptReply.Msg) : model.AcceptReplyM :=
  ⟨g.Replica', g.Instance', g.OK', g.Ballot'⟩
def commitOf (g : ECommit.Msg) : model.ECommitM :=
  ⟨g.Replica, g.Instance, g.Command.map cmdOf, g.Seq, depsOf g.Deps, vtOf g.Base⟩
def prepareOf (g : Prepare.Msg) : model.PrepareM :=
  ⟨g.LeaderId', g.Replica', g.Instance', g.Ballot'⟩
def prepareReplyOf (g : PrepareReply.Msg) : model.PrepareReplyM :=
  ⟨g.AcceptorId, g.Replica, g.Instance, g.OK, g.Ballot, g.VBallot, g.Status,
    g.Command.map cmdOf, g.Seq, depsOf g.Deps, vtOf g.Base⟩
def executedOf (g : Executed.Msg) : model.ExecutedM := ⟨g.Replica', g.Instance'⟩

/-! ## The rpc codes -/

/-- The rpc code of each kind on the wire (`RegisterRPC`'s registration order). -/
def msgCode : Msg → Option w8
  | .prepare _ => some (W8 8) | .prepareReply _ => some (W8 9)
  | .preAccept _ => some (W8 10) | .preAcceptReply _ => some (W8 11)
  | .preAcceptOK _ => some (W8 12) | .accept _ => some (W8 13)
  | .acceptReply _ => some (W8 14) | .commit _ => some (W8 15)
  | .executed _ => some (W8 19)
  | .read1 _ => some (W8 22) | .read2 _ => some (W8 23)
  | .write1 _ => some (W8 24) | .write2 _ => some (W8 25)
  | .read1Reply _ => some (W8 26) | .read2Reply _ => some (W8 27)
  | .write1Reply _ => some (W8 28) | .write2Reply _ => some (W8 29)
  | .executeOverwrite _ => none

/-- The rpc code of a kind name (`Replica2/State.lean`'s `msgKind`). -/
def kindCode (kd : String) : Option w8 :=
  if kd = "prepare" then some (W8 8) else if kd = "prepareReply" then some (W8 9)
  else if kd = "preAccept" then some (W8 10) else if kd = "preAcceptReply" then some (W8 11)
  else if kd = "preAcceptOK" then some (W8 12) else if kd = "accept" then some (W8 13)
  else if kd = "acceptReply" then some (W8 14) else if kd = "commit" then some (W8 15)
  else if kd = "executed" then some (W8 19)
  else if kd = "read1" then some (W8 22) else if kd = "read2" then some (W8 23)
  else if kd = "write1" then some (W8 24) else if kd = "write2" then some (W8 25)
  else if kd = "read1Reply" then some (W8 26) else if kd = "read2Reply" then some (W8 27)
  else if kd = "write1Reply" then some (W8 28) else if kd = "write2Reply" then some (W8 29)
  else none

/-! ## The per-message bytes -/

/-- Model message `m` is the bytes `b`: its code, then a well-formed Go struct's encoding whose
projection is `m`. -/
def msgWireB : Msg → List w8 → Prop
  | .read1 mm, b => ∃ g : Read1Proxied.Msg, b = W8 22 :: Read1Proxied.enc g ∧ read1Of g = mm
  | .read2 mm, b => ∃ g : Read2Proxied.Msg, b = W8 23 :: Read2Proxied.enc g ∧ read2Of g = mm
  | .read1Reply mm, b =>
    ∃ g : Read1Reply.Msg, b = W8 26 :: Read1Reply.enc g ∧ read1ReplyOf g = mm
  | .read2Reply mm, b =>
    ∃ g : Read2Reply.Msg, b = W8 27 :: Read2Reply.enc g ∧ read2ReplyOf g = mm
  | .write1 mm, b => ∃ g : Write1Proxied.Msg, b = W8 24 :: Write1Proxied.enc g ∧ write1Of g = mm
  | .write2 mm, b => ∃ g : Write2Proxied.Msg, b = W8 25 :: Write2Proxied.enc g ∧ write2Of g = mm
  | .write1Reply mm, b =>
    ∃ g : Write1Reply.Msg, b = W8 28 :: Write1Reply.enc g ∧ write1ReplyOf g = mm
  | .write2Reply mm, b =>
    ∃ g : Write2Reply.Msg, b = W8 29 :: Write2Reply.enc g ∧ write2ReplyOf g = mm
  | .preAccept mm, b => ∃ g : PreAccept.Msg, b = W8 10 :: PreAccept.enc g ∧
    PreAccept.wf g ∧ g.Deps.arr.length = 5 ∧ preAcceptOf g = mm
  | .preAcceptReply mm, b => ∃ g : PreAcceptReply.Msg, b = W8 11 :: PreAcceptReply.enc g ∧
    g.Deps'.arr.length = 5 ∧ g.CommittedDeps'.arr.length = 5 ∧ preAcceptReplyOf g = mm
  | .preAcceptOK mm, b =>
    ∃ g : PreAcceptOK.Msg, b = W8 12 :: PreAcceptOK.enc g ∧ preAcceptOKOf g = mm
  | .accept mm, b => ∃ g : EAccept.Msg, b = W8 13 :: EAccept.enc g ∧
    EAccept.wf g ∧ g.Deps.arr.length = 5 ∧ acceptOf g = mm
  | .acceptReply mm, b =>
    ∃ g : AcceptReply.Msg, b = W8 14 :: AcceptReply.enc g ∧ acceptReplyOf g = mm
  | .commit mm, b => ∃ g : ECommit.Msg, b = W8 15 :: ECommit.enc g ∧
    ECommit.wf g ∧ g.Deps.arr.length = 5 ∧ commitOf g = mm
  | .prepare mm, b => ∃ g : Prepare.Msg, b = W8 8 :: Prepare.enc g ∧ prepareOf g = mm
  | .prepareReply mm, b => ∃ g : PrepareReply.Msg, b = W8 9 :: PrepareReply.enc g ∧
    PrepareReply.wf g ∧ g.Deps.arr.length = 5 ∧ prepareReplyOf g = mm
  | .executed mm, b => ∃ g : Executed.Msg, b = W8 19 :: Executed.enc g ∧ executedOf g = mm
  | .executeOverwrite _, _ => False

end Perennial.gryff.netN
