/-
The EPaxos protocol messages as pure records (the pure model's vocabulary, shared by the wire
layer and the protocol model). Field for field as `epaxos/defs.go` declares them at the fork's
`net` (after fixes R-VB: `PrepareReply.VBallot` is sent; R-ACC: `Accept` carries the commands).
Commands are `WCmd` (`Epaxos/Interface/Wire.lean`: op byte, key, value bytes). Integers are the
Go types' words (`w32` for `int32`, `w8` for `int8` statuses).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Wire

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

deriving instance DecidableEq for WCmd
deriving instance Inhabited for WCmd

/-- `epaxos.Prepare` -/
structure Prepare where
  leaderId : w32
  replica : w32
  inst : w32
  ballot : w32
deriving DecidableEq, Inhabited

/-- `epaxos.PrepareReply` -/
structure PrepareReply where
  acceptorId : w32
  replica : w32
  inst : w32
  ballot : w32
  vballot : w32
  status : w8
  command : List WCmd
  seq : w32
  deps : List w32
deriving DecidableEq, Inhabited

/-- `epaxos.PreAccept` -/
structure PreAccept where
  leaderId : w32
  replica : w32
  inst : w32
  ballot : w32
  command : List WCmd
  seq : w32
  deps : List w32
deriving DecidableEq, Inhabited

/-- `epaxos.PreAcceptReply` -/
structure PreAcceptReply where
  replica : w32
  inst : w32
  ballot : w32
  vballot : w32
  seq : w32
  deps : List w32
  committedDeps : List w32
  status : w8
deriving DecidableEq, Inhabited

/-- `epaxos.Accept` (with the commands, fix R-ACC) -/
structure Accept where
  leaderId : w32
  replica : w32
  inst : w32
  ballot : w32
  command : List WCmd
  seq : w32
  deps : List w32
deriving DecidableEq, Inhabited

/-- `epaxos.AcceptReply` -/
structure AcceptReply where
  replica : w32
  inst : w32
  ballot : w32
deriving DecidableEq, Inhabited

/-- `epaxos.Commit` -/
structure Commit where
  leaderId : w32
  replica : w32
  inst : w32
  ballot : w32
  command : List WCmd
  seq : w32
  deps : List w32
deriving DecidableEq, Inhabited

/-- `epaxos.TryPreAccept` (never sent: TryPreAccept is dead code, see decisions.md D2) -/
structure TryPreAccept where
  leaderId : w32
  replica : w32
  inst : w32
  ballot : w32
  command : List WCmd
  seq : w32
  deps : List w32
deriving DecidableEq, Inhabited

/-- `epaxos.TryPreAcceptReply` (never sent) -/
structure TryPreAcceptReply where
  acceptorId : w32
  replica : w32
  inst : w32
  ballot : w32
  vballot : w32
  conflictReplica : w32
  conflictInstance : w32
  conflictStatus : w8
deriving DecidableEq, Inhabited

/-- A message on a peer stream: the protocol messages (each preceded on the wire by its rpc code,
`epaxos.New`'s registrations in order from `defs.RPC_TABLE` = 9: Prepare 9, PrepareReply 10,
PreAccept 11, PreAcceptReply 12, Accept 13, AcceptReply 14, Commit 15, TryPreAccept 16,
TryPreAcceptReply 17) and the replica framework's beacons (`GENERIC_SMR_BEACON` 6,
`GENERIC_SMR_BEACON_REPLY` 7, an int64 timestamp each). -/
inductive Msg where
  | prepare (m : Prepare)
  | prepareReply (m : PrepareReply)
  | preAccept (m : PreAccept)
  | preAcceptReply (m : PreAcceptReply)
  | accept (m : Accept)
  | acceptReply (m : AcceptReply)
  | commit (m : Commit)
  | tryPreAccept (m : TryPreAccept)
  | tryPreAcceptReply (m : TryPreAcceptReply)
  | beacon (ts : w64)
  | beaconReply (ts : w64)
deriving DecidableEq, Inhabited

/-- The message's code byte on the wire. -/
def Msg.code : Msg → w8
  | .prepare _ => W8 9
  | .prepareReply _ => W8 10
  | .preAccept _ => W8 11
  | .preAcceptReply _ => W8 12
  | .accept _ => W8 13
  | .acceptReply _ => W8 14
  | .commit _ => W8 15
  | .tryPreAccept _ => W8 16
  | .tryPreAcceptReply _ => W8 17
  | .beacon _ => W8 6
  | .beaconReply _ => W8 7

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
