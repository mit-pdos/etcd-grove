/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Model/Types.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

The pure model of one Gryff replica (stage 2, unit M): its data types and its state `RState`.

Configuration (fixed): N = 3, not thrifty, Exec = true, Dreply = true, beacons off, not durable,
proxy mode, regular = false, epaxosMode = false, noConflicts = false, broadcast optimization off,
DO_CHECKPOINTING = false (a constant of `epaxosrmwhandler.go`). Every client command is a CAS on
key 0 (`HandleRMW` builds `state.Command{CAS, K, NewValue, OldValue}`, the kit uses key 0).

Every Go integer is a Go word (`w8`/`w32`/`w64`, Perennial.Std.Word); comparisons are signed
(`slt`, `sle`: `sint.Z`) where Go's are (all compared Go integers here are signed). Go `int` is
`w64`. Each field of `RState` is a plain projection of heap fields (named in its doc comment); the
refinement relation (unit I) is the lock invariant's statement that the heap projects to it.

Go maps are association lists sorted by key (`AMap`, canonical: the sorted list of the map's
entries); the instance space (a Go array of arrays) is a function `(row, slot) ↦ Option Copy`,
meaningful only inside the box (rows 0..2, slots 0..2^21-1; outside it the function is `none` and
never read: every access checks `inBox` first, an access outside it being a Go index panic).
-/
module

public import Perennial.Std.Word

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.model

/-! ## Go word helpers -/

/-- Go's signed `a < b` (`int8`, `int32`, `int64`). -/
def slt {n : Nat} (a b : BitVec n) : Bool := decide (sint.Z a < sint.Z b)
/-- Go's signed `a <= b`. -/
def sle {n : Nat} (a b : BitVec n) : Bool := decide (sint.Z a ≤ sint.Z b)
/-- Go's signed `a > b`. -/
def sgt {n : Nat} (a b : BitVec n) : Bool := slt b a
/-- Go's signed `a >= b`. -/
def sge {n : Nat} (a b : BitVec n) : Bool := sle b a

/-- Go's `FALSE` (`uint8(0)`), `TRUE` (`uint8(1)`) of `tupaq.go`. -/
def FALSE : w8 := 0
def TRUE : w8 := 1

/-- The number of replicas (`r.N`). -/
def N : Nat := 3

/-- `MAX_BATCH` (`tupaq.go`). -/
def MAX_BATCH : w64 := 5000

/-- The instance space's slots per row (`make([]*Instance, 2*1024*1024)`). -/
def SLOTS : Int := 2 * 1024 * 1024

/-! ## Tags, values, dependencies, commands (`gryffproto`, `state`) -/

/-- `gryffproto.Tag` (a carstamp). -/
structure Tag where
  ts : w32
  cid : w32
  rmwc : w32
deriving DecidableEq, Repr, Inhabited

def tag0 : Tag := ⟨0, 0, 0⟩

/-- `gryffproto.Tag.Compare`, literally: `-1`, `0` or `1` (lexicographic, signed). -/
def Tag.cmp (a b : Tag) : Int :=
  if slt a.ts b.ts || (a.ts == b.ts && slt a.cid b.cid) ||
      (a.ts == b.ts && a.cid == b.cid && slt a.rmwc b.rmwc) then -1
  else if a.ts == b.ts && a.cid == b.cid && a.rmwc == b.rmwc then 0
  else 1

/-- `Tag.GreaterThan`. -/
def Tag.gt (a b : Tag) : Bool := decide (a.cmp b > 0)
/-- `Tag.LessThan`. -/
def Tag.lt (a b : Tag) : Bool := decide (a.cmp b < 0)
/-- `Tag.Equals`. -/
def Tag.eqT (a b : Tag) : Bool := decide (a.cmp b = 0)

/-- `gryffproto.ValTag`. -/
structure ValTag where
  v : w64
  t : Tag
deriving DecidableEq, Repr, Inhabited

/-- `gryffproto.ValTag{0, gryffproto.Tag{0, 0, 0}}`. -/
def vt0 : ValTag := ⟨0, tag0⟩

/-- `gryffproto.Dep`: a dependency (`Key < 0`: none). -/
structure Dep where
  key : w64
  vt : ValTag
deriving DecidableEq, Repr, Inhabited

/-- The zero `Dep` (`Key` 0: what `SendRead1` sends, as it never sets `r.read1.D`). -/
def dep0 : Dep := ⟨0, vt0⟩

/-- The kit's dependency (`examples/gryffnet/kit.go`, `noDep`: key -1). The model's client steps
accept any dependency with `Key < 0` (Go's own test, `participant.go`: `if dep.Key >= 0`), not
only this one. -/
def noDep : Dep := ⟨-1, vt0⟩

/-- `state.Operation` codes. -/
def opPUT : w8 := 1
def opCAS : w8 := 6

/-- `state.Command`: `Op`, `K`, `V` (the new value), `OldValue`. -/
structure Cmd where
  op : w8
  k : w64
  v : w64
  oldV : w64
deriving DecidableEq, Repr, Inhabited

/-- A command of the system's shape: a CAS on key 0 (every command is a client RMW's). -/
def Cmd.ok (c : Cmd) : Bool := c.op == opCAS && c.k == 0

/-- All commands of a batch have the system's shape. -/
def cmdsOk (cs : List Cmd) : Bool := cs.all Cmd.ok

/-! ## EPaxos instances (`epaxosrmwhandler.go`, `epaxosproto`) -/

/-! `epaxosproto` status codes (`int8`). -/
namespace St
def NONE : w8 := 0
def PREACCEPTED : w8 := 1
def PREACCEPTED_EQ : w8 := 2
def ACCEPTED : w8 := 3
def COMMITTED : w8 := 4
def EXECUTED : w8 := 5
end St

/-- A `[DS]int32` array (`DS = 5`): a list of 5 words (only entries 0..2 are ever read). -/
abbrev Deps := List w32

/-- `deps[q]` (`q` a valid index). -/
def Deps.at (d : Deps) (q : Nat) : w32 := d.getD q 0
/-- `deps[q] = x`. -/
def Deps.setAt (d : Deps) (q : Nat) (x : w32) : Deps := d.set q x

/-- `var nildeps [DS]int32`. -/
def nildeps : Deps := [0, 0, 0, 0, 0]

/-- A client proposal (`genericsmr.Propose`): `CommandId` (the RMW's request id), the command,
and the client id whose writer `Reply` is (`HandleRMW`: `e.R.GetClientWriter(rmw.ClientId)`).
`Timestamp` (always 0) is dropped: only `ReplyProposeTS` reads it, never called (Dreply, CAS). -/
structure Proposal where
  cmdId : w32
  client : w32
  cmd : Cmd
deriving DecidableEq, Repr, Inhabited

/-- `RecoveryInstance` (all fields). -/
structure RecoveryInstance where
  cmds : List Cmd
  status : w8
  seq : w32
  deps : Deps
  base : ValTag
  /-- `preAcceptCount int` -/
  preAcceptCount : w64
  leaderResponded : Bool
  vbal : w32
deriving DecidableEq, Repr, Inhabited

/-- `LeaderBookkeeping`. Dropped: `tryingToPreAccept`, `possibleQuorum`, `tpaOKs` (read only by
TryPreAccept code, unreachable: see `stepPrepareReply`), the times (`committedTime`, `executedTime`,
`blockStartTime`, `depReadTime`: statistics/logging). `clientProposals` is `[]` for Go's `nil`
(a non-nil empty slice never occurs: `handlePropose`'s batch has at least one proposal);
`committedDeps` is `[]` for `nil` (read only for N > 3). -/
structure LB where
  clientProposals : List Proposal
  maxRecvBallot : w32
  prepareOKs : w64
  allEqual : Bool
  preAcceptOKs : w64
  acceptOKs : w64
  nacks : w64
  originalDeps : Deps
  committedDeps : List w32
  recoveryInst : Option RecoveryInstance
  preparing : Bool
  numReplicasExecuted : w32
  repliedClient : Bool
deriving DecidableEq, Repr, Inhabited

/-- `Instance` (a replica's copy of an instance). Dropped: `Index`, `Lowlink` (the executor's
search state, abstracted by the execution event's guard), `bfilter` (always nil, never read).
`cmds` is `[]` for Go's `nil`: only copies of status NONE have `nil` commands (wire-decoded
command lists are never nil: `make([]state.Command, alen)`), and the executor's waits on `nil`
commands concern only uncommitted copies, which its guard excludes. -/
structure Copy where
  cmds : List Cmd
  ballot : w32
  status : w8
  seq : w32
  deps : Deps
  base : ValTag
  lb : Option LB
  slot : w32
  leader : w32
  vbal : w32
deriving DecidableEq, Repr, Inhabited

/-! ## Ballots (`makeUniqueBallot`, ...: Go's `>>` on `int32` is arithmetic) -/

def makeUniqueBallot (id ballot : w32) : w32 := (ballot <<< 4) ||| id
def makeBallotLargerThan (id ballot : w32) : w32 := makeUniqueBallot id (ballot.sshiftRight 4 + 1)
def isInitialBallot (ballot : w32) : Bool := ballot.sshiftRight 4 == 0
/-- `math.MaxInt32 >> 4`. -/
def maxBallotHi : w32 := (0x7FFFFFFF : w32).sshiftRight 4

/-! ## Gryff coordinator's records (`gryffcommon/coordinator.go`) -/

/-- `ReadOp`. Dropped: `Op.Key` (always 0: checked when the read starts), `Op.Dep` (never read),
`read1Replies`, `maxUpdateId` (never read), `ReadUpdateId` (always 0, sent only as `Read2Proxied`'s
`UpdateId`, which no handler reads). `maxValTag`/`ReadValTag` are `none` for `nil`. -/
structure ReadOp where
  requestId : w32
  clientId : w32
  n : w32
  maxValTag : Option ValTag
  readValTag : Option ValTag
  numRead1Replies : w64
  numRead2Replies : w64
  readsWithMaxTag : w64
  sentRead2Round : Bool
  determinedReadVal : Bool
  replicasWithMaxTag : List w32
deriving DecidableEq, Repr, Inhabited

/-- `WriteOp`. `dep` is `Op.Dep` (the client request's `D`, which `SendWrite1` forwards as
`Write1Proxied.D`; the system's clients send `Key < 0`, no dependency). Dropped: `Op.Key` (always
0), `MaxAppliedTag` (sent only as `Write1Proxied`'s
`MaxAppliedTag`, read only for non-forced writes), `ForceWrite` (always 1: `StartWrite` sets
`forceWrite = 1` unconditionally), `maxGreenTag`, `repliesWithMaxGreenTag`, `replicasWithTag`
(never read), `startedShortcircuitTimeout` (always false: only commented-out code sets it).
`writeTag` is `none` for `nil`. -/
structure WriteOp where
  requestId : w32
  clientId : w32
  n : w32
  writeValue : w64
  dep : Dep
  maxValTag : ValTag
  numWrite1Applies : w64
  numWrite1Replies : w64
  numWrite2Applies : w64
  numWrite2Replies : w64
  sentWrite2Round : Bool
  writeTag : Option Tag
deriving DecidableEq, Repr, Inhabited

/-- `OngoingOp`. Dropped: `Key` (always 0), `Value` (always nil, never read), `SentWrite1` (never
read), `ShortWrites` (always empty: appended only when `forceWrite == 0`, never), `Replicas` (read
only by `HandleWrite2ConcurrentTimeout`, never triggered). `isRead` is `OpType`. -/
structure OngoingOp where
  requestId : w32
  clientId : w32
  isRead : Bool
  shortReads : List w32
deriving DecidableEq, Repr, Inhabited

/-- `gryffcommon.ShiftInts`: `(int64(a) << 32) | int64(b)` (`b` sign-extended, as Go does). -/
def shiftInts (a b : w32) : w64 := (a.signExtend 64 <<< 32) ||| b.signExtend 64

/-! ## Finite maps (Go maps): association lists sorted by key -/

/-- A Go map with word keys: its entries, sorted by the key's unsigned value, keys distinct. -/
abbrev AMap (n : Nat) (V : Type) := List (BitVec n × V)

namespace AMap
variable {n : Nat} {V : Type}

def get? (m : AMap n V) (k : BitVec n) : Option V := m.lookup k

/-- `m[k] = v`. -/
def put (m : AMap n V) (k : BitVec n) (v : V) : AMap n V :=
  match m with
  | [] => [(k, v)]
  | (k', v') :: t =>
    if k = k' then (k, v) :: t
    else if k.toNat < k'.toNat then (k, v) :: (k', v') :: t
    else (k', v') :: put t k v

/-- `delete(m, k)`. -/
def del (m : AMap n V) (k : BitVec n) : AMap n V := m.filter (fun e => e.1 != k)
end AMap

/-! ## The replica's state -/

/-- One replica's state: the projection of the heap that the replica's lock protects (G2). -/
structure RState where
  /-- `r.Id` (`genericsmr.Replica.Id`). -/
  id : w32
  -- participant (`gryffcommon/participant.go`) and the store
  /-- `r.State.Store[0]` (absent: 0). Only key 0 is ever written. -/
  val : w64
  /-- `*r.parti.storeTag[0].Tag` (absent: `tag0`, `GetStoreMetadata`). -/
  tag : Tag
  /-- `r.parti.OngoingWrites`: client id ↦ its entry's `RequestId`. The entries' other fields are
  never read in this configuration: every entry has `SentWrite1Reply = true` (every Write1 is
  forced) and `FastOverwite = false`, `K = 0`; `HandleWrite2`'s loop reads them only in branches
  requiring `!SentWrite1Reply` (an invariant of the refinement relation). -/
  ongoing : AMap 32 w32
  -- coordinator (`gryffcommon/coordinator.go`)
  /-- `r.coord.maxN`. -/
  maxN : w32
  /-- `r.coord.rops` (keyed by `ShiftInts(RequestId, ClientId)`). -/
  rops : AMap 64 ReadOp
  /-- `r.coord.wops`. -/
  wops : AMap 64 WriteOp
  /-- `r.coord.OngoingReqs` (keyed by the op's `N`). -/
  ongoingReqs : AMap 32 OngoingOp
  -- EPaxos (`epaxosrmwhandler.go`)
  /-- `e.InstanceSpace[q][i]` (`nil`: `none`) for `inBox q i`; `none` outside the box. -/
  inst : w32 → w32 → Option Copy
  /-- `e.crtInstance` (3 entries). -/
  crtInstance : List w32
  /-- `e.CommittedUpTo` (5 entries). -/
  committedUpTo : Deps
  /-- `e.conflicts1[q][0]` for each row `q` (3 entries): `none` if key 0 has no entry, else the
  common value of its `PUT`, `GET`, `CAS` entries (always set together: every command is a CAS,
  which conflicts with every operation, `state.OpTypesConflict`). -/
  conf : List (Option w32)
  /-- `e.maxSeqPerKey1[0]`, as `conf` (`none`: absent). -/
  maxSeqK0 : Option w32
  /-- `e.PrevValTag[0]` (`none`: absent). -/
  prevValTag : Option ValTag
  /-- The contents of `e.R.ProposeChan`, oldest first (only re-proposals are ever sent to it: the
  kit's clients never send `GEN_PROPOSE`). -/
  proposeQ : List Proposal
  /-- The number of client requests handled (a ghost counter for the per-replica budget). -/
  nReqs : Nat
  /-- The (client id, request id) of the client requests handled (ghost: a client request whose
  key was already used here is not enabled; the kit's clients never repeat a key). -/
  used : List (w32 × w32)
deriving Inhabited

/-! ## Accessors -/

/-- `(q, i)` is inside the instance space (else Go's index panics). -/
def inBox (q i : w32) : Bool :=
  decide (0 ≤ sint.Z q ∧ sint.Z q < 3 ∧ 0 ≤ sint.Z i ∧ sint.Z i < SLOTS)

/-- A valid row (replica id). -/
def rowOk (q : w32) : Bool := decide (0 ≤ sint.Z q ∧ sint.Z q < 3)

namespace RState
variable (s : RState)

/-- `e.InstanceSpace[q][i] = c`. -/
def setInst (q i : w32) (c : Copy) : RState :=
  { s with inst := fun q' i' => if q' = q ∧ i' = i then some c else s.inst q' i' }

/-- `e.crtInstance[q]`. -/
def crt (q : w32) : w32 := s.crtInstance.getD q.toNat 0
def setCrt (q x : w32) : RState := { s with crtInstance := s.crtInstance.set q.toNat x }

/-- `e.CommittedUpTo[q]`. -/
def cut (q : w32) : w32 := s.committedUpTo.at q.toNat

/-- `e.conflicts1[q][0][op]` (any op). -/
def confAt (q : Nat) : Option w32 := s.conf.getD q none

/-- `GetStoreMetadata(0).Tag`, `GetCurrentValue(0)` as a `ValTag`. -/
def storeVT : ValTag := ⟨s.val, s.tag⟩
end RState

/-- The initial state of replica `k` (`NewReplica`, `NewEPaxosRMWHandler`,
`NewGryffParticipant`, `NewGryffCoordinator`). -/
def RState.init (k : Nat) : RState where
  id := BitVec.ofNat 32 k
  val := 0
  tag := tag0
  ongoing := []
  maxN := 0
  rops := []
  wops := []
  ongoingReqs := []
  inst := fun _ _ => none
  crtInstance := [0, 0, 0]
  committedUpTo := [-1, -1, -1, -1, -1]
  conf := [none, none, none]
  maxSeqK0 := none
  prevValTag := none
  proposeQ := []
  nReqs := 0
  used := []

end Perennial.gryff.model
