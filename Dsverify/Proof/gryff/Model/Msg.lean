/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Model/Msg.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

The model's messages (`Msg`), events (`Ev`) and external outputs (`Ext`).

`Msg` has one constructor per message kind ever sent in this configuration, each holding the
projection of the Go struct: the fields some reachable branch of its handler reads (a dropped
field is named in the structure's doc comment, with why). Kinds never sent: TryPreAccept(Reply)
(TryPreAccept is unreachable, see `stepPrepareReply`), CommitShort (Exec = true), PreAcceptOKReply,
AcceptOKReply (broadcast optimization off), beacons (off), Write1 timeouts (every Write1 is
forced), Write2 concurrent timeouts (only commented-out code starts them).

Self-messages (sent to the replica's own channels) are messages to self (`kahn.Out.send self`):
the coordinator's Write1/Write2 to itself, the participant's replies to its own coordinator, the
executor's `ExecuteOverwrite`.
-/
module

public import Dsverify.Proof.gryff.Model.Types

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.model

/-! ## Gryff (participant/coordinator) messages (`gryffproto/tupaqproto.go`) -/

/-- `Read1Proxied`: all fields. `D` is the zero `Dep` (key 0) as sent (`SendRead1` never sets it);
the handler overwrites with it when `D.Key >= 0`. -/
structure Read1ProxiedM where
  requestId : w32
  clientId : w32
  k : w64
  d : Dep
  replicaId : w32
  vt : ValTag
deriving DecidableEq, Repr

/-- `Read2Proxied`. Dropped: `UpdateId` (`HandleRead2` ignores it). -/
structure Read2ProxiedM where
  requestId : w32
  clientId : w32
  k : w64
  vt : ValTag
  replicaId : w32
deriving DecidableEq, Repr

/-- `Read1Reply`: all fields. -/
structure Read1ReplyM where
  requestId : w32
  clientId : w32
  replicaId : w32
  vt : ValTag
deriving DecidableEq, Repr

/-- `Read2Reply`. Dropped: `ReplicaId` (statistics only), `T` (`HandleRead2Reply` ignores it). -/
structure Read2ReplyM where
  requestId : w32
  clientId : w32
deriving DecidableEq, Repr

/-- `Write1Proxied`. Dropped: `N`, `V`, `MaxAppliedTag` (stored in the participant's ongoing-write
entry, whose fields other than `RequestId` are never read: see `RState.ongoing`). -/
structure Write1ProxiedM where
  requestId : w32
  clientId : w32
  forceWrite : w32
  k : w64
  d : Dep
  replicaId : w32
deriving DecidableEq, Repr

/-- `Write1Reply`. Dropped: `ReplicaId` (statistics and logging only). -/
structure Write1ReplyM where
  requestId : w32
  clientId : w32
  vt : ValTag
deriving DecidableEq, Repr

/-- `Write2Proxied`. Dropped: `N` (read only by `HandleWrite2ConcurrentTimeout`'s caller). -/
structure Write2ProxiedM where
  requestId : w32
  clientId : w32
  k : w64
  vt : ValTag
  replicaId : w32
deriving DecidableEq, Repr

/-- `Write2Reply`. Dropped: `ReplicaId` (statistics only), `T` (logging only). -/
structure Write2ReplyM where
  requestId : w32
  clientId : w32
  applied : w32
deriving DecidableEq, Repr

/-! ## EPaxos messages (`gryffproto` EPaxos part, `epaxosproto`) -/

/-- `gryffproto.PreAccept`: all fields. -/
structure PreAcceptM where
  leaderId : w32
  replica : w32
  inst : w32
  ballot : w32
  cmds : List Cmd
  seq : w32
  deps : Deps
  base : ValTag
deriving DecidableEq, Repr

/-- `gryffproto.PreAcceptReply`. Dropped: `CommittedDeps` (read only for N > 3). -/
structure PreAcceptReplyM where
  replica : w32
  inst : w32
  ok : w8
  ballot : w32
  seq : w32
  deps : Deps
  base : ValTag
deriving DecidableEq, Repr

/-- `epaxosproto.PreAcceptOK`: all fields. -/
structure PreAcceptOKM where
  inst : w32
deriving DecidableEq, Repr

/-- `gryffproto.EAccept`. Dropped: `Count` (read only when `DO_CHECKPOINTING`). -/
structure EAcceptM where
  leaderId : w32
  replica : w32
  inst : w32
  ballot : w32
  seq : w32
  deps : Deps
  cmds : List Cmd
  base : ValTag
deriving DecidableEq, Repr

/-- `epaxosproto.AcceptReply`: all fields. -/
structure AcceptReplyM where
  replica : w32
  inst : w32
  ok : w8
  ballot : w32
deriving DecidableEq, Repr

/-- `gryffproto.ECommit`. Dropped: `LeaderId` (`handleCommit` never reads it). -/
structure ECommitM where
  replica : w32
  inst : w32
  cmds : List Cmd
  seq : w32
  deps : Deps
  base : ValTag
deriving DecidableEq, Repr

/-- `epaxosproto.Prepare`: all fields. -/
structure PrepareM where
  leaderId : w32
  replica : w32
  inst : w32
  ballot : w32
deriving DecidableEq, Repr

/-- `gryffproto.PrepareReply`: all fields. -/
structure PrepareReplyM where
  acceptorId : w32
  replica : w32
  inst : w32
  ok : w8
  ballot : w32
  vbal : w32
  status : w8
  cmds : List Cmd
  seq : w32
  deps : Deps
  base : ValTag
deriving DecidableEq, Repr

/-- `gryffproto.Executed`: all fields. -/
structure ExecutedM where
  replica : w32
  inst : w32
deriving DecidableEq, Repr

/-- `ExecuteOverwrite` (the executor to its run loop). Dropped: `K` (the executed command's key,
always 0). `T` is a pointer in Go (to the executor's local `vt.T`, never mutated after). -/
structure ExecuteOverwriteM where
  v : w64
  t : Tag
  leader : w32
  slot : w32
deriving DecidableEq, Repr

/-- A message (its content). -/
inductive Msg where
  | read1 (m : Read1ProxiedM)
  | read2 (m : Read2ProxiedM)
  | read1Reply (m : Read1ReplyM)
  | read2Reply (m : Read2ReplyM)
  | write1 (m : Write1ProxiedM)
  | write2 (m : Write2ProxiedM)
  | write1Reply (m : Write1ReplyM)
  | write2Reply (m : Write2ReplyM)
  | preAccept (m : PreAcceptM)
  | preAcceptReply (m : PreAcceptReplyM)
  | preAcceptOK (m : PreAcceptOKM)
  | accept (m : EAcceptM)
  | acceptReply (m : AcceptReplyM)
  | commit (m : ECommitM)
  | prepare (m : PrepareM)
  | prepareReply (m : PrepareReplyM)
  | executed (m : ExecutedM)
  | executeOverwrite (m : ExecuteOverwriteM)
deriving DecidableEq, Repr

/-- An external output: a reply to a client (by Gryff client id; the replica writes it to the
client id's connection, `GetClientWriter`). `ok` is always 1 (`CompleteRead`/`CompleteWrite` are
always called with `success = true`; `completeRMWWriter` sends 1). Dropped: `ReadReply.MaxSeenTag`,
`WriteReply.MaxSeenTag` (`r.maxSeenTag`, never updated: `TagSeen` is never called; the client
ignores it), `RMWReply.ReplicaId`, `RMWReply.OldValue` (the client ignores them, `kit.go`). The
client matches replies by request id (and client id for reads and writes). -/
inductive Ext where
  | readReply (clientId requestId : w32) (v : w64) (ok : w8)
  | writeReply (clientId requestId : w32) (ok : w8)
  | rmwReply (clientId requestId : w32) (ok : w8)
deriving DecidableEq, Repr

/-- An event of a replica: a message handled (from a peer or itself), a client request (with the
fields of `gryffproto.Read`/`Write`/`RMW`, `D` as received: the system's clients send a
dependency with `Key < 0`, none, whose other fields the code carries but never reads), the
forced-write ticker, a recovery trigger for
instance `(q, i)` (the executor's `instancesToRecover`), the execution of instance `(q, i)`. -/
inductive Ev where
  | msg (m : Msg)
  | read (requestId clientId : w32) (k : w64) (d : Dep)
  | write (requestId clientId : w32) (k : w64) (v : w64) (d : Dep)
  | rmw (requestId clientId : w32) (k : w64) (d : Dep) (oldV newV : w64)
  | forceWrite
  | recover (q i : w32)
  | exec (q i : w32)
deriving DecidableEq, Repr

/-- The message an event consumes. -/
def Ev.recv : Ev → Option Msg
  | .msg m => some m
  | _ => none

end Perennial.gryff.model
