/-
The pure image of one epaxos replica's protocol state (`RState`), field for field as the Go code
has it at the fork's `net` (`epaxos/epaxos.go`, `epaxos/exec.go`, after fixes E1-E3 and R-*), and
the replica's handlers as pure functions over it (`hPreAccept`, `hAccept`, `hCommit`, `hPrepare`
written in full, mirroring the Go code statement by statement; the others declared, to be defined
by the epaxos prover in the same style).

**Conventions.**
* Go `int32` fields (ballots, seq, deps entries, instance numbers held in fields) are `w32`, and
  every comparison is the signed one the code makes (`BitVec.slt`/`sle`); `int8` statuses are
  `w8`; Go `int` counters are `w64`. Row and instance *indices* (`InstanceSpace[q][i]`) are `Nat`
  (`toN` of the `int32`: the code only indexes with values in range, which the invariant's `wf`
  conjunct says).
* A Go slice of commands is `Option (List WCmd)`: `nil` (`none`) and the empty slice (`some []`)
  are told apart because the code tests `Cmds == nil` (`executeCommands`, `strongconnect`,
  `startRecoveryForInstance`, `handlePreAccept`'s ACCEPTED branch). A `deps` slice is a
  `List w32`: the code never tests `Deps == nil`, so `nil` is `[]` (only `newInstanceDefault`
  makes a `nil` deps).
* A Go map is a function to `Option` (`conflicts`, `maxSeqPerKey`, the store); `InstanceSpace` is
  a function from `InstId` to `Option InstRec` (`nil` pointer = `none`; each row has
  `MAX_INSTANCE` entries).
* **Aliasing.** The only in-place write into a slice is `mergeAttributes`'s write into `lb.deps`
  (`handlePreAcceptReply`), and it never reaches another holder's array: `startPhase1` leaves
  `lb.ballot = -1`, so the first counted `PreAcceptReply` (its `VBallot` is its ballot, `≥ 0`, for a
  pre-accepted reply) runs `lb.deps = pareply.Deps` before the first `mergeAttributes`, and every
  later write goes into that decoded array, which no other field holds until the fast/slow path's
  `inst.Deps = lb.deps` (after which `lb.status` is ACCEPTED/COMMITTED and no reply is merged in
  this bookkeeping again). So `lb.deps` is written only while `lbDepsOwned lb` (pre-accepted with
  a counted reply); everywhere else every deps array (`inst.Deps`, `lb.deps`, a `PrepareReply`'s
  `Deps` in `lb.prepareReplies`) is shared read-only, and the model treats the arrays as values
  (no write-through). Other shared arrays (`lb.cmds`/`inst.Cmds`, `lb.originalDeps`, the
  `Command` of a `PrepareReply`, a PUT's value bytes in the store) are never written in place.
* Excluded: `Index`/`Lowlink` (0 outside an executor pass for non-executed instances), `bfilter`,
  `proposeTime`, statistics, the channels, `latestCP*`, `clientMutex`, `batchWait`, `transconf`
  (false), the executor goroutine's locals (`problemInstance`, `timeout`: they only decide when
  the executor asks for a recovery, and the model lets any in-range instance be recovered at any
  time, `Step.recover`), the executor's Tarjan stack (`Exec.stack`), the package globals (`cpcounter`, ...:
  `Epaxos/Top/PkgState.lean`),
  and the `LeaderBookkeeping` fields the code never reads with N = 5 or only past
  `tryingToPreAccept` (never true: TryPreAccept is dead, decisions.md D2): `originalDeps`,
  `committedDeps` (read only when `N > 7`), `possibleQuorum`, `tpaReps`, `tpaAccepted`.

**Outputs.** A handler returns the new state and a list of `Out`: the messages it sends
directly (`SendMsg(to, code, m)`, in order: the replies), at most one **pending broadcast**
(`Out.bcast`, last: every `bcast*` is its handler's last protocol action), the client replies
(`ReplyProposeTS`, only the executor's with `Dreply`), the re-proposals (`handleCommit`'s
`r.ProposeChan <- p`), and **ghost events** (`Out.ev`), which the code does not perform: they
mark, at the statement where it happens, a vote, a proposal, a commit, an attribute computation
with its conflicts-map record, and are what the invariant (`Epaxos/Model/Inv.lean`) speaks of.

**Broadcasts (fix B4).** A `bcast*` builds its message from `lb` and then, peer by peer, reads
`r.alive(q)` (`r.Alive[q]` under `r.M`, written by the framework at any time) and sends when it is
true, up to `need` sends. The handler's step only records the broadcast (`Bcast`: the message,
the peers still to read, how many sends are still wanted); each read is a step of its own
(`Sys.bcastStep`, taken right after `r.alive(q)` returned, with the value it returned), which
appends the message to the outbox when the value is true and, for `bcastPreAccept`, updates
`lb.preAcceptsSent`. The instance lock is held throughout, so the replica takes no other step
until the broadcast is over (`Sys.idle`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Msg

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

/-! ## Constants -/

/-- `r.N`: the number of replicas. -/
def nR : Nat := 5
/-- `r.F`: the number of tolerated failures (`epaxos.New(..., failures = 2, ...)`). -/
def fR : Nat := 2
/-- `MAX_INSTANCE`: the capacity of a row of `InstanceSpace`. -/
def MAX_INSTANCE : Nat := 10 * 1024 * 1024
/-- `COMMIT_GRACE_PERIOD` (ns), `SLEEP_TIME_NS`. -/
def COMMIT_GRACE_PERIOD : Nat := 10 * 1000000000
def SLEEP_TIME_NS : Nat := 1000000

/-- The instance statuses (`NONE` ... `EXECUTED`, `int8`). -/
def stNONE : w8 := W8 0
def stPREACCEPTED : w8 := W8 1
def stPREACCEPTED_EQ : w8 := W8 2
def stACCEPTED : w8 := W8 3
def stCOMMITTED : w8 := W8 4
def stEXECUTED : w8 := W8 5

/-- `a >= b` on statuses (`int8`, signed). -/
def stGe (a b : w8) : Bool := b.sle a

/-- An `int32` used as an index (negative values map to 0; the code indexes only with values in
range). -/
def toN (x : w32) : Nat := (sint.Z x).toNat

/-- Function update. -/
def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun a' => if a' = a then b else f a'

/-! ## Identities -/

/-- An instance `replica.instance` (`instanceId`; `q` the row, i.e. the instance's command
leader). -/
structure InstId where
  q : Nat
  i : Nat
deriving DecidableEq, Inhabited

/-- A client proposal's identity: the id `cid` of the connection its `PROPOSE` came on (the
`*defs.GPropose`'s `Reply` writer is that connection's; `CommandId` and `Timestamp` are 0 for the
kit's client) and its command. -/
structure Proposal where
  cid : w64
  cmd : WCmd
deriving DecidableEq, Inhabited

/-- `state.NOOP()`: one `NONE` command, key 0, empty value. -/
def noop : List WCmd := [⟨opNONE, 0, []⟩]

/-! ## The records -/

/-- `InstPair`: the last instance of a row touching a key, and the last one writing it. -/
structure InstPair where
  last : w32
  lastWrite : w32
deriving DecidableEq, Inhabited

/-- An entry of `lb.prepareReplies`: the reply, and whether its `Command` is `nil` (only the
recovering replica's own reply, built from `inst.Cmds`, can be: decoded lists are never
`nil`). -/
structure PReply where
  m : PrepareReply
  cmdsNil : Bool
deriving DecidableEq, Inhabited

/-- `LeaderBookkeeping`, the fields the code reads (see the file's docstring for the excluded
ones). `clientProposals` is `nil` (`none`) or the batch's proposals, in batch order. -/
structure LbRec where
  clientProposals : Option (List Proposal)
  ballot : w32
  allEqual : Bool
  preAcceptOKs : w64
  acceptOKs : w64
  nacks : w64
  prepareReplies : List PReply
  preparing : Bool
  tryingToPreAccept : Bool
  lastTriedBallot : w32
  cmds : Option (List WCmd)
  status : w8
  seq : w32
  deps : List w32
  leaderResponded : Bool
  preAcceptsSent : w64
deriving DecidableEq, Inhabited

/-- `Instance`: commands, ballot (`bal`, the promise), vote ballot (`vbal`), status, seq, deps,
the bookkeeping (`lb`, `nil` = `none`) and `id` (its `instanceId`, set at creation). -/
structure InstRec where
  cmds : Option (List WCmd)
  bal : w32
  vbal : w32
  status : w8
  seq : w32
  deps : List w32
  lb : Option LbRec
  id : InstId
deriving DecidableEq, Inhabited

/-- One replica's protocol state. `peerOrder` is the framework's `PreferredPeerOrder` (read by
the `bcast*`; set by `ComputeClosestPeers` before the run loop handles anything); `isLeader`,
`maxRecvBallot` and the per-row arrays are the `epaxos.Replica` fields; `store` is `r.State`'s map
(`state.State.Store`). -/
structure RState where
  id : Nat
  peerOrder : List Nat
  isLeader : Bool
  inst : InstId → Option InstRec
  crtInstance : Nat → w32
  committedUpTo : Nat → w32
  execedUpTo : Nat → w32
  conflicts : Nat → w64 → Option InstPair
  /-- per row, the last instance holding a SCAN / a PUT (fix S1) -/
  lastScan : Nat → w32
  lastPut : Nat → w32
  maxSeqPerKey : w64 → Option w32
  maxSeq : w32
  maxRecvBallot : w32
  store : w64 → Option (List w8)

/-- Replica `i` as `epaxos.New` leaves it (and `executeCommands` starts): no instance, every row
at -1, empty maps, `maxSeq` 0, `maxRecvBallot` -1, the framework's initial peer order
`(i + 1 + j) mod N`. -/
def RState.init (i : Nat) : RState where
  id := i
  peerOrder := (List.range nR).map (fun j => (i + 1 + j) % nR)
  isLeader := false
  inst := fun _ => none
  crtInstance := fun _ => W32 (-1)
  committedUpTo := fun _ => W32 (-1)
  execedUpTo := fun _ => W32 (-1)
  conflicts := fun _ _ => none
  lastScan := fun _ => W32 (-1)
  lastPut := fun _ => W32 (-1)
  maxSeqPerKey := fun _ => none
  maxSeq := W32 0
  maxRecvBallot := W32 (-1)
  store := fun _ => none

instance : Inhabited RState := ⟨RState.init 0⟩

/-! ## Outputs -/

/-- A value of an instance: commands and attributes. -/
structure Val where
  cmds : List WCmd
  seq : w32
  deps : List w32
deriving DecidableEq, Inhabited

/-- Ghost events (no code effect; see the file's docstring). Emitted by the handlers at the
statement they describe, except `sent`, which the system step logs for every `Out.send`. -/
inductive Event where
  /-- `makeBallot` chose ballot `b` for `x` (`lb.lastTriedBallot = b`), or `handlePropose` started
  `x` at its initial ballot. -/
  | makeBallot (x : InstId) (b : w32)
  /-- the replica's instance `x` now holds a vote at ballot `b` with status `st` (PREACCEPTED,
  PREACCEPTED_EQ or ACCEPTED) and value `v`. -/
  | vote (x : InstId) (b : w32) (st : w8) (v : Val)
  /-- `startPhase1` at ballot `b`: commands `v.cmds`, the proposer's attributes. -/
  | phase1 (x : InstId) (b : w32) (v : Val)
  /-- `bcastAccept` at ballot `b` with value `v` (emitted even if no peer is alive). -/
  | accept (x : InstId) (b : w32) (v : Val)
  /-- the replica's instance `x` became COMMITTED with value `v` (`b`: the ballot it records). -/
  | commit (x : InstId) (b : w32) (v : Val)
  /-- the fast path committed `v` (`handlePreAcceptReply`'s fast branch, at the instance's
  initial ballot, by its leader `x.q`), emitted with that `commit` (T2-5). -/
  | fastCommit (x : InstId) (v : Val)
  /-- `updateConflicts(cmds, x.q, x.i, _)` alone (no attribute computation in the same handler:
  `handlePreAccept`'s ACCEPTED branch, `handleCommit`): `x` recorded in the conflicts map for
  `cmds`' keys. -/
  | record (x : InstId) (cmds : List WCmd)
  /-- `updateAttributes(cmds, _, _, x.q, x.i, _)` returned deps `deps`, and the same handler, with
  nothing in between that touches the conflicts map, recorded `x` for `cmds` (`updateConflicts`):
  `handlePreAccept`'s pre-accept branch and `startPhase1` (one event: fix B13). -/
  | attrsRec (x : InstId) (cmds : List WCmd) (deps : List w32)
  /-- `startRecoveryForInstance` put its own `PrepareReply` `m` into `lb.prepareReplies` (it is
  sent to nobody: the recovering replica's own report, a promise at `m.ballot`). -/
  | selfReply (m : PrepareReply)
  /-- (logged by the system step) the replica sent `m` to `to`. -/
  | sent (to : Nat) (m : Msg)
deriving DecidableEq, Inhabited

/-- A pending broadcast (fix B4): instance `x`'s message `m`, the peers whose `r.alive(q)` is still
to be read (in the order the code reads them), the sends still wanted (`need`: the loop stops when
`sent ≥ need`), the sends made so far, and whether each send sets `lb.preAcceptsSent = sent`
(`bcastPreAccept`). -/
structure Bcast where
  x : InstId
  m : Msg
  peers : List Nat
  need : Nat
  sent : Nat
  trackPA : Bool
deriving DecidableEq, Inhabited

/-- A broadcast that is over (no peer left, or enough sends) is no longer pending. -/
def Bcast.norm (b : Bcast) : Option Bcast :=
  if b.peers = [] ∨ b.need ≤ b.sent then none else some b

/-- The broadcast after reading `alive` = `a` for its next peer. -/
def Bcast.next (b : Bcast) (a : Bool) : Option Bcast :=
  match b.peers with
  | [] => none
  | _ :: ps => if a then { b with peers := ps, sent := b.sent + 1 }.norm
               else { b with peers := ps }.norm

/-- A handler's output. -/
inductive Out where
  | send (to : Nat) (m : Msg)
  | bcast (b : Bcast)
  | reply (p : Proposal) (v : List w8)
  | repropose (p : Proposal)
  | ev (e : Event)
deriving DecidableEq, Inhabited

/-- The broadcast a handler's outputs leave pending (the last `Out.bcast`, normalized). -/
def pendOf (outs : List Out) : Option Bcast :=
  outs.foldl (fun acc o => match o with | .bcast b => b.norm | _ => acc) none

/-! ## Helpers (as the Go code has them) -/

namespace RState

def setInst (σ : RState) (x : InstId) (r : InstRec) : RState :=
  { σ with inst := upd σ.inst x (some r) }

/-- The deps a replica reports (`r.CommittedUpTo` as a slice). -/
def committedList (σ : RState) : List w32 := (List.range nR).map σ.committedUpTo

end RState

/-- `newInstanceDefault(replica, instance)`: no commands, ballots -1, NONE, seq -1, `nil`
deps. -/
def newInstanceDefault (x : InstId) : InstRec :=
  { cmds := none, bal := W32 (-1), vbal := W32 (-1), status := stNONE, seq := W32 (-1),
    deps := [], lb := none, id := x }

/-- The instance `x`, created by `newInstanceDefault` if `nil` (the pattern `if inst == nil {
inst = r.newInstanceDefault(...); r.InstanceSpace[...] = inst }`). -/
def getOrDefault (σ : RState) (x : InstId) : RState × InstRec :=
  match σ.inst x with
  | some r => (σ, r)
  | none => (σ.setInst x (newInstanceDefault x), newInstanceDefault x)

/-- `updateConflicts(cmds, replica, instance, seq)` (fix S1: a SCAN raises `lastScan[replica]`,
a PUT `lastPut[replica]`, to the instance). -/
def updateConflicts (σ : RState) (cmds : List WCmd) (q : Nat) (n seq : w32) : RState :=
  cmds.foldl (fun σ c =>
    let p' : InstPair :=
      match σ.conflicts q c.key with
      | some p =>
        ⟨if p.last.slt n then n else p.last,
         if p.lastWrite.slt n ∧ c.op ≠ opGET then n else p.lastWrite⟩
      | none => ⟨n, if c.op ≠ opGET then n else W32 (-1)⟩
    let s' : w32 :=
      match σ.maxSeqPerKey c.key with
      | some s => if s.slt seq then seq else s
      | none => seq
    { σ with conflicts := upd σ.conflicts q (upd (σ.conflicts q) c.key (some p')),
             lastScan := if c.op = opSCAN ∧ (σ.lastScan q).slt n then upd σ.lastScan q n
               else σ.lastScan,
             lastPut := if c.op = opPUT ∧ (σ.lastPut q).slt n then upd σ.lastPut q n
               else σ.lastPut,
             maxSeqPerKey := upd σ.maxSeqPerKey c.key (some s') }) σ

/-- `updateAttributes(cmds, seq, deps, replica, instance, leader)`: raises `seq` and `deps` over
the instances interfering with `cmds` that the replica knows, in every row (fix B3: the R-ROW skip
of row `replica` is removed; `replica` and `leader` are no longer read; fix S1: per row and
command, after the key's entry, a SCAN's row's last PUT and a PUT's row's last SCAN, `-1`
otherwise, with the same update). Returns `(seq, deps, changed)`. (`InstanceSpace[q][d]` is non-nil for `d` read from the conflicts map or `lastScan`/`lastPut`:
the invariant's `wf` and `classWf`; the model reads seq 0 otherwise.) -/
def updateAttributes (σ : RState) (cmds : List WCmd) (seq : w32) (deps : List w32) :
    w32 × List w32 × Bool :=
  let r1 := (List.range nR).foldl (fun (acc : w32 × List w32 × Bool) q =>
    cmds.foldl (fun (acc : w32 × List w32 × Bool) c =>
      let step (acc : w32 × List w32 × Bool) (d : w32) : w32 × List w32 × Bool :=
        if (acc.2.1.getD q (W32 0)).slt d then
          let dseq := ((σ.inst ⟨q, toN d⟩).map (·.seq)).getD (W32 0)
          (if acc.1.sle dseq then dseq + 1 else acc.1, acc.2.1.set q d, true)
        else acc
      let acc := match σ.conflicts q c.key with
        | none => acc
        | some p => step acc (if c.op ≠ opGET then p.last else p.lastWrite)
      step acc (if c.op = opSCAN then σ.lastPut q
        else if c.op = opPUT then σ.lastScan q else W32 (-1))) acc) (seq, deps, false)
  cmds.foldl (fun (acc : w32 × List w32 × Bool) c =>
    match σ.maxSeqPerKey c.key with
    | some s => if acc.1.sle s then (s + 1, acc.2.1, true) else acc
    | none => acc) r1

/-- `CommittedUpTo[q]` advanced over the committed/executed instances that follow it (at most
`fuel` steps; `MAX_INSTANCE` suffices: the last slot of a row stays `nil`, fix R-CAP). -/
def advanceCommitted (σ : RState) (q : Nat) : Nat → w32 → w32
  | 0, c => c
  | fuel + 1, c =>
    match σ.inst ⟨q, toN (c + 1)⟩ with
    | some x =>
      if x.status = stCOMMITTED ∨ x.status = stEXECUTED then advanceCommitted σ q fuel (c + 1)
      else c
    | none => c

/-- `updateCommitted(replica)`. -/
def updateCommitted (σ : RState) (q : Nat) : RState :=
  let c := advanceCommitted σ q MAX_INSTANCE (σ.committedUpTo q)
  { σ with committedUpTo := upd σ.committedUpTo q c }

/-- The `maxRecvBallot` update every handler starts with. -/
def bumpRecvBallot (σ : RState) (b : w32) : RState :=
  if σ.maxRecvBallot.slt b then { σ with maxRecvBallot := b } else σ

/-- The `crtInstance` update (`if m.Instance > r.crtInstance[m.Replica]`). -/
def bumpCrt (σ : RState) (q : Nat) (n : w32) : RState :=
  if (σ.crtInstance q).slt n then { σ with crtInstance := upd σ.crtInstance q n } else σ

/-- `lb.preAcceptsSent = n` in instance `x`'s bookkeeping (`bcastPreAccept`'s loop). -/
def setPreAcceptsSent (σ : RState) (x : InstId) (n : Nat) : RState :=
  match σ.inst x with
  | some w =>
    match w.lb with
    | some lb => σ.setInst x { w with lb := some { lb with preAcceptsSent := W64 n } }
    | none => σ
  | none => σ

/-- `lb.deps` is written in place (by `mergeAttributes`) only in this state: pre-accepted with a
counted reply, `lb.deps` being then the first counted reply's decoded array (see the file's
docstring). The heap image owns `lb.deps` exclusively exactly then (`ownLb`). -/
def lbDepsOwned (lb : LbRec) : Bool :=
  decide ((lb.status = stPREACCEPTED ∨ lb.status = stPREACCEPTED_EQ) ∧ lb.preAcceptOKs ≠ W64 0)

/-! ## The broadcasts (each `bcast*`'s message, peers and number of sends) -/

/-- The peers `bcastPrepare` reads, in order: `r.Id + 1, ..., r.Id + N - 1` (mod `N`). -/
def cyclePeers (σ : RState) : List Nat := (List.range (nR - 1)).map (fun j => (σ.id + 1 + j) % nR)

/-- `bcastPrepare(replica, instance)` at ballot `b` (`lb.lastTriedBallot`): every alive peer. -/
def bcastPrepareOf (σ : RState) (x : InstId) (b : w32) : Bcast :=
  { x := x, m := .prepare { leaderId := W32 σ.id, replica := W32 x.q, inst := W32 x.i, ballot := b },
    peers := cyclePeers σ, need := nR - 1, sent := 0, trackPA := false }

/-- `bcastPreAccept` (thrifty): the first `2F - 1` alive peers of `PreferredPeerOrder[0..N-2]`,
setting `lb.preAcceptsSent` after each send. -/
def bcastPreAcceptOf (σ : RState) (x : InstId) (m : PreAccept) : Bcast :=
  { x := x, m := .preAccept m, peers := σ.peerOrder.take (nR - 1), need := 2 * fR - 1, sent := 0,
    trackPA := true }

/-- `bcastAccept` (thrifty): the first `N / 2` alive peers of `PreferredPeerOrder[0..N-2]`. -/
def bcastAcceptOf (σ : RState) (x : InstId) (m : Accept) : Bcast :=
  { x := x, m := .accept m, peers := σ.peerOrder.take (nR - 1), need := nR / 2, sent := 0,
    trackPA := false }

/-- `bcastCommit`: every alive peer of `PreferredPeerOrder[0..N-2]`. -/
def bcastCommitOf (σ : RState) (x : InstId) (m : Commit) : Bcast :=
  { x := x, m := .commit m, peers := σ.peerOrder.take (nR - 1), need := nR - 1, sent := 0,
    trackPA := false }

/-- The replica's state after a broadcast's read of `alive` = `a` (the send's
`lb.preAcceptsSent = sent`). -/
def bcastRep (σ : RState) (b : Bcast) (a : Bool) : RState :=
  if a = true ∧ b.trackPA = true ∧ b.peers ≠ [] then setPreAcceptsSent σ b.x (b.sent + 1) else σ

/-- `makeBallot(replica, instance)` computed without overflow (`Int`): above `inst.bal` and the
bookkeeping's `lastTriedBallot` (at least 0), the next ballot owned by `r.Id`, raised past
`maxRecvBallot` (by steps of `N`) when `IsLeader`. -/
def makeBallotZ (σ : RState) (bal lastTried : w32) : Int :=
  let b := max (max (sint.Z bal) (sint.Z lastTried)) 0
  let n := (b / nR + 1) * nR + σ.id
  let mrb := sint.Z σ.maxRecvBallot
  if σ.isLeader ∧ n < mrb then n + nR * ((mrb - n + nR - 1) / nR) else n

/-! ## The handlers written in full -/

/-- `handlePreAccept(preAccept)`. -/
def hPreAccept (σ : RState) (m : PreAccept) : RState × List Out :=
  let x : InstId := ⟨toN m.replica, toN m.inst⟩
  let σ := if σ.maxSeq.sle m.seq then { σ with maxSeq := m.seq + 1 } else σ
  let σ := bumpRecvBallot σ m.ballot
  let σ := bumpCrt σ x.q m.inst
  let (σ, inst) := getOrDefault σ x
  if m.ballot.slt inst.bal then (σ, [])
  else
    let inst := { inst with bal := m.ballot }
    let (σ, inst, evs) :=
      if stGe inst.status stACCEPTED then
        if inst.cmds = none then
          let inst := { inst with cmds := some m.command }
          let σ := updateConflicts (σ.setInst x inst) m.command x.q m.inst m.seq
          (σ, inst, [Out.ev (.record x m.command)])
        else (σ.setInst x inst, inst, [])
      else
        let (seq, deps, changed) := updateAttributes σ m.command m.seq m.deps
        let status := if changed then stPREACCEPTED else stPREACCEPTED_EQ
        let inst := { inst with cmds := some m.command, seq := seq, deps := deps,
                                bal := m.ballot, vbal := m.ballot, status := status }
        let σ := updateConflicts (σ.setInst x inst) m.command x.q m.inst m.seq
        (σ, inst, [Out.ev (.vote x m.ballot status ⟨m.command, seq, deps⟩),
                   Out.ev (.attrsRec x m.command deps)])
    let reply : PreAcceptReply :=
      { replica := m.replica, inst := m.inst, ballot := inst.bal, vballot := inst.vbal,
        seq := inst.seq, deps := inst.deps, committedDeps := σ.committedList,
        status := inst.status }
    (σ, evs ++ [Out.send (toN m.leaderId) (.preAcceptReply reply)])

/-- `handleAccept(accept)` (fix R-ACC: records the commands and ACCEPTED; fix R-AREP: a rejected
Accept gets no reply). -/
def hAccept (σ : RState) (m : Accept) : RState × List Out :=
  let x : InstId := ⟨toN m.replica, toN m.inst⟩
  let σ := bumpRecvBallot σ m.ballot
  let σ := bumpCrt σ x.q m.inst
  let (σ, inst) := getOrDefault σ x
  if m.ballot.slt inst.bal then (σ, [])
  else
    let (σ, inst, evs) :=
      if stGe inst.status stCOMMITTED then (σ, inst, [])
      else
        let inst := { inst with cmds := some m.command, deps := m.deps, seq := m.seq,
                                bal := m.ballot, vbal := m.ballot, status := stACCEPTED }
        (σ.setInst x inst, inst,
          [Out.ev (.vote x m.ballot stACCEPTED ⟨m.command, m.seq, m.deps⟩)])
    (σ, evs ++ [Out.send (toN m.leaderId)
      (.acceptReply { replica := m.replica, inst := m.inst, ballot := inst.bal })])

/-- `handleCommit(commit)`. The leader of the instance, on a committed no-op while it still holds
the instance's client proposals, re-proposes them (`r.ProposeChan <- p`) and drops them. (A `nil`
`inst.lb` there would be a nil dereference in Go: the invariant's `wf` says an own instance has
its bookkeeping; the model skips the re-proposal.) -/
def hCommit (σ : RState) (m : Commit) : RState × List Out :=
  let x : InstId := ⟨toN m.replica, toN m.inst⟩
  let σ := bumpCrt σ x.q m.inst
  let σ := bumpRecvBallot σ m.ballot
  let (σ, inst) := getOrDefault σ x
  if stGe inst.status stCOMMITTED then (σ, [])
  else if m.ballot.slt inst.bal then (σ, [])
  else
    let (inst, reprops) :=
      if x.q = σ.id ∧ m.command.length = 1 ∧ ((m.command.head?.map (·.op)) = some opNONE) then
        match inst.lb with
        | some lb =>
          match lb.clientProposals with
          | some ps =>
            ({ inst with lb := some { lb with clientProposals := none } },
              ps.map Out.repropose)
          | none => (inst, [])
        | none => (inst, [])
      else (inst, [])
    let inst := { inst with bal := m.ballot, vbal := m.ballot, cmds := some m.command,
                            seq := m.seq, deps := m.deps, status := stCOMMITTED }
    let σ := σ.setInst x inst
    let σ := updateConflicts σ m.command x.q m.inst m.seq
    let σ := updateCommitted σ x.q
    (σ, reprops ++ [Out.ev (.record x m.command),
      Out.ev (.commit x m.ballot ⟨m.command, m.seq, m.deps⟩)])

/-- `handlePrepare(prepare)`: joins a higher ballot and answers with its state (`inst.Cmds` may be
`nil`: the reply's command list is then empty on the wire). -/
def hPrepare (σ : RState) (m : Prepare) : RState × List Out :=
  let x : InstId := ⟨toN m.replica, toN m.inst⟩
  let σ := bumpRecvBallot σ m.ballot
  let (σ, inst) := getOrDefault σ x
  let inst := if inst.bal.slt m.ballot then { inst with bal := m.ballot } else inst
  let σ := σ.setInst x inst
  let reply : PrepareReply :=
    { acceptorId := W32 σ.id, replica := m.replica, inst := m.inst, ballot := inst.bal,
      vballot := inst.vbal, status := inst.status, command := inst.cmds.getD [],
      seq := inst.seq, deps := inst.deps }
  (σ, [Out.send (toN m.leaderId) (.prepareReply reply)])

/-- `BeTheLeader` (under the instance lock, fix E1): `IsLeader = true`. -/
def hBeTheLeader (σ : RState) : RState := { σ with isLeader := true }

/-! ## The handlers written by the model prover

Mirroring the Go functions statement by statement, in the style of the four above (ghost events
at the statements they describe: `makeBallot` in `makeBallot` and at `handlePropose`; `phase1`,
`vote` (the proposer's own) and `attrsRec` in `startPhase1`; `vote`/`accept` where the code sets
ACCEPTED and calls `bcastAccept`; `commit` where it sets COMMITTED, with `fastCommit` on the fast
path). Every `bcast*` is the handler's last output, `Out.bcast` of the matching `bcast*Of` (the
handler's state is the one the broadcast builds its message from). A `nil` instance or bookkeeping
the Go code dereferences (a nil-pointer panic: `Inv.replyTargets` excludes it) leaves the state
as it is after the statements before the dereference. -/

/-- The row of `r.Id` is full (`handlePropose`'s R-CAP test). -/
def rowFull (σ : RState) : Bool :=
  (W32 (MAX_INSTANCE - 1 : Nat)).sle (σ.crtInstance σ.id + 1)

/-- `isInitialBallot(ballot, replica, instance)`: `ballot == replica`. -/
def isInitialBallot (ballot replica : w32) : Bool := ballot == replica

/-- `nextBallot(inst, lastTried)` (`inst.bal = bal`): the ballot, if it fits an `int32`. -/
def nextBallot (σ : RState) (bal lastTried : w32) : Option w32 :=
  if (2 ^ 31 - 1 : Int) < makeBallotZ σ bal lastTried then none
  else some (W32 (makeBallotZ σ bal lastTried))

/-- `mergeAttributes(seq1, deps1, seq2, deps2)`: the larger seq, the pointwise larger deps (every
row: fix R-ROW3), and whether both were equal. (The in-place write into `deps1` is the model's
value result: see the file's docstring, "Aliasing".) -/
def mergeAttributes (seq1 : w32) (deps1 : List w32) (seq2 : w32) (deps2 : List w32) :
    w32 × List w32 × Bool :=
  let eqS : Bool := seq1 == seq2
  let seq := if seq1 ≠ seq2 ∧ seq1.slt seq2 then seq2 else seq1
  let r := (List.range nR).foldl (fun (acc : List w32 × Bool) q =>
    let a := acc.1.getD q (W32 0)
    let b := deps2.getD q (W32 0)
    if a ≠ b then (if a.slt b then acc.1.set q b else acc.1, false) else acc) (deps1, true)
  (seq, r.1, eqS && r.2)

/-- `equal(deps1, deps2)`: equal on the indices of `deps1`. -/
def depsEqual (deps1 deps2 : List w32) : Bool :=
  (List.range deps1.length).all (fun i => deps1.getD i (W32 0) == deps2.getD i (W32 0))

/-- The `PreAccept` `bcastPreAccept` builds from the bookkeeping `lb` of `replica.instance`. -/
def preAcceptOf (σ : RState) (replica inst : w32) (lb : LbRec) : PreAccept :=
  { leaderId := W32 σ.id, replica := replica, inst := inst, ballot := lb.lastTriedBallot,
    command := lb.cmds.getD [], seq := lb.seq, deps := lb.deps }

/-- The `Accept` `bcastAccept` builds from `lb`. -/
def acceptOf (σ : RState) (replica inst : w32) (lb : LbRec) : Accept :=
  { leaderId := W32 σ.id, replica := replica, inst := inst, ballot := lb.lastTriedBallot,
    command := lb.cmds.getD [], seq := lb.seq, deps := lb.deps }

/-- The `Commit` `bcastCommit` builds from `lb` (its ballot is `lb.ballot`). -/
def commitOf (σ : RState) (replica inst : w32) (lb : LbRec) : Commit :=
  { leaderId := W32 σ.id, replica := replica, inst := inst, ballot := lb.ballot,
    command := lb.cmds.getD [], seq := lb.seq, deps := lb.deps }

/-- The value `lb` holds. -/
def lbVal (lb : LbRec) : Val := ⟨lb.cmds.getD [], lb.seq, lb.deps⟩

/-- `startPhase1(cmds, replica, instance, ballot, proposals)` for `x = replica.instance`: fresh
attributes (`updateAttributes` from seq 0 and deps all `-1`), a new instance (PREACCEPTED at
`ballot`, the proposer's vote) with a new bookkeeping (`newLeaderBookkeeping(proposals, deps,
comDeps, deps, ballot, cmds, PREACCEPTED, -1)`: `lb.seq = -1`, `lb.ballot = -1`; `preparing`
false), `updateConflicts`, `maxSeq`, `bcastPreAccept`. -/
def startPhase1 (σ : RState) (cmds : List WCmd) (x : InstId) (replica n ballot : w32)
    (proposals : Option (List Proposal)) : RState × List Out :=
  let a := updateAttributes σ cmds (W32 0) (List.replicate nR (W32 (-1)))
  let seq := a.1
  let deps := a.2.1
  let lb : LbRec :=
    { clientProposals := proposals, ballot := W32 (-1), allEqual := true,
      preAcceptOKs := W64 0, acceptOKs := W64 0, nacks := W64 0, prepareReplies := [],
      preparing := false, tryingToPreAccept := false, lastTriedBallot := ballot,
      cmds := some cmds, status := stPREACCEPTED, seq := W32 (-1), deps := deps,
      leaderResponded := false, preAcceptsSent := W64 0 }
  let inst : InstRec :=
    { cmds := some cmds, bal := ballot, vbal := ballot, status := stPREACCEPTED, seq := seq,
      deps := deps, lb := some lb, id := x }
  let σ := σ.setInst x inst
  let σ := updateConflicts σ cmds x.q n seq
  let σ := if σ.maxSeq.sle seq then { σ with maxSeq := seq } else σ
  (σ, [Out.ev (.phase1 x ballot (lbVal lb)),
       Out.ev (.vote x ballot stPREACCEPTED ⟨cmds, seq, deps⟩),
       Out.ev (.attrsRec x cmds deps),
       Out.bcast (bcastPreAcceptOf σ x (preAcceptOf σ replica n lb))])

/-- `handlePropose` on the batch `batch` (the proposal the run loop took and the
`len(ProposeChan)` that followed it; a full row drops the first one: fix R-CAP), then
`startPhase1(cmds, r.Id, crtInstance[r.Id], r.Id, proposals)` (its `bcastPreAccept`:
`bcastPreAcceptOf`, `lb.preAcceptsSent = 0` until the broadcast's steps). -/
def hPropose (σ : RState) (batch : List Proposal) : RState × List Out :=
  if rowFull σ then (σ, [])
  else
    let n := σ.crtInstance σ.id + 1
    let σ := { σ with crtInstance := upd σ.crtInstance σ.id n }
    let x : InstId := ⟨σ.id, toN n⟩
    let r := startPhase1 σ (batch.map (·.cmd)) x (W32 σ.id) n (W32 σ.id) (some batch)
    (r.1, Out.ev (.makeBallot x (W32 σ.id)) :: r.2)

/-- The nack branch of `handlePreAcceptReply`/`handleAcceptReply` (`lb.nacks++`; past `N >> 1`
nacks, under `IsLeader`, `makeBallot` and `bcastPrepare`). -/
def nackBranch (σ : RState) (x : InstId) (inst : InstRec) (lb : LbRec) : RState × List Out :=
  let lb := { lb with nacks := lb.nacks + 1 }
  if (W64 (nR / 2)).slt (lb.nacks + 1) ∧ σ.isLeader = true then
    let (lb, evs) := match nextBallot σ inst.bal lb.lastTriedBallot with
      | some n => ({ lb with lastTriedBallot := n }, [Out.ev (.makeBallot x n)])
      | none => (lb, [])
    let σ := σ.setInst x { inst with lb := some lb }
    (σ, evs ++ [Out.bcast (bcastPrepareOf σ x lb.lastTriedBallot)])
  else (σ.setInst x { inst with lb := some lb }, [])

/-- `handlePreAcceptReply` (fixes R-FQ, R-LEAD, R-FINAL; the fast path on `2F - 1` equal
replies at the initial ballot, the slow path, `mergeAttributes` merging and comparing every row,
the leader's own included (fix R-ROW3), writing into `lb.deps` (and only `lb.deps`, see
`lbDepsOwned`); `bcastCommit`/`bcastAccept`; the nack branch's `makeBallot` +
`bcastPrepare` under `IsLeader`, dead: no reply carries a ballot above `lastTriedBallot`,
`Inv.lbInv`). `allCommitted` is true (`N ≤ 7`); `Dreply` is on (no client reply). Both paths set
`inst.bal = lb.ballot` as the code does (see questions.md, G2). -/
def hPreAcceptReply (σ : RState) (m : PreAcceptReply) : RState × List Out :=
  let x : InstId := ⟨toN m.replica, toN m.inst⟩
  match σ.inst x with
  | none => (σ, [])
  | some inst =>
  match inst.lb with
  | none => (σ, [])
  | some lb =>
  let σ := bumpRecvBallot σ m.ballot
  if stGe inst.status stCOMMITTED then (σ, [])
  else if lb.lastTriedBallot.slt inst.bal then (σ, [])
  else if m.ballot.slt lb.lastTriedBallot then (σ, [])
  else if lb.lastTriedBallot.slt m.ballot then nackBranch σ x inst lb
  else if ¬ (lb.status = stPREACCEPTED ∨ lb.status = stPREACCEPTED_EQ) then (σ, [])
  else
    let lb := { lb with preAcceptOKs := lb.preAcceptOKs + 1 }
    let lb := if lb.ballot.slt m.vballot then
      { lb with ballot := m.vballot, seq := m.seq, deps := m.deps, status := m.status } else lb
    let isInit := isInitialBallot lb.lastTriedBallot m.replica
    let mg := mergeAttributes lb.seq lb.deps m.seq m.deps
    let lb := { lb with allEqual := lb.allEqual && mg.2.2 }
    let lb := if lb.status.sle stPREACCEPTED_EQ then { lb with deps := mg.2.1, seq := mg.1 } else lb
    let precondition := lb.allEqual && isInit
    let slowQuorum := (W64 (nR / 2)).sle lb.preAcceptOKs &&
      Bool.or (!precondition) (lb.preAcceptsSent.sle lb.preAcceptOKs)
    if (W64 (2 * fR - 1)).sle lb.preAcceptOKs && precondition then
      let lb := { lb with status := stCOMMITTED }
      let inst := { inst with status := stCOMMITTED, bal := lb.ballot, cmds := lb.cmds,
                              deps := lb.deps, seq := lb.seq, lb := some lb }
      let σ := updateCommitted (σ.setInst x inst) x.q
      (σ, [Out.ev (.commit x lb.ballot (lbVal lb)), Out.ev (.fastCommit x (lbVal lb)),
           Out.bcast (bcastCommitOf σ x (commitOf σ m.replica m.inst lb))])
    else if slowQuorum then
      let lb := { lb with status := stACCEPTED }
      let inst := { inst with status := stACCEPTED, bal := lb.ballot, cmds := lb.cmds,
                              deps := lb.deps, seq := lb.seq, lb := some lb }
      let σ := σ.setInst x inst
      (σ, [Out.ev (.vote x inst.vbal stACCEPTED (lbVal lb)),
           Out.ev (.accept x lb.lastTriedBallot (lbVal lb)),
           Out.bcast (bcastAcceptOf σ x (acceptOf σ m.replica m.inst lb))])
    else (σ.setInst x { inst with lb := some lb }, [])

/-- `handleAcceptReply` (fixes R-LEAD, R-FINAL). The commit records the instance's value; the
Commit carries `lb`'s. -/
def hAcceptReply (σ : RState) (m : AcceptReply) : RState × List Out :=
  let x : InstId := ⟨toN m.replica, toN m.inst⟩
  match σ.inst x with
  | none => (σ, [])
  | some inst =>
  match inst.lb with
  | none => (σ, [])
  | some lb =>
  let σ := bumpRecvBallot σ m.ballot
  if lb.status ≠ stACCEPTED ∨ stGe inst.status stCOMMITTED then (σ, [])
  else if lb.lastTriedBallot.slt inst.bal then (σ, [])
  else if lb.lastTriedBallot ≠ m.ballot then (σ, [])
  else if lb.lastTriedBallot.slt m.ballot then nackBranch σ x inst lb
  else
    let lb := { lb with acceptOKs := lb.acceptOKs + 1 }
    if (W64 (nR / 2)).slt (lb.acceptOKs + 1) then
      let lb := { lb with status := stCOMMITTED }
      let inst := { inst with status := stCOMMITTED, lb := some lb }
      let σ := updateCommitted (σ.setInst x inst) x.q
      (σ, [Out.ev (.commit x inst.bal (⟨inst.cmds.getD [], inst.seq, inst.deps⟩ : Val)),
           Out.bcast (bcastCommitOf σ x (commitOf σ m.replica m.inst lb))])
    else (σ.setInst x { inst with lb := some lb }, [])

/-- `handlePrepareReply`'s `isPreAccepted`. -/
def isPreAcceptedAt (maxVbal : w32) (e : PReply) : Bool :=
  e.m.vballot == maxVbal && Bool.or (e.m.status == stPREACCEPTED) (e.m.status == stPREACCEPTED_EQ)

/-- Sub-case 3's candidate test: `e` is a pre-accepted reply of a replica other than the
leader, and at least `N / 2` such replies are identical to it. -/
def subCase3Ok (reps : List PReply) (maxVbal : w32) (e : PReply) : Bool :=
  isPreAcceptedAt maxVbal e && e.m.acceptorId != e.m.replica &&
    decide (nR / 2 ≤ (reps.filter (fun o => isPreAcceptedAt maxVbal o &&
      o.m.acceptorId != o.m.replica && o.m.seq == e.m.seq && depsEqual o.m.deps e.m.deps)).length)

/-- The explicit prepare's decision on the replies `reps` (`maxVbal` the highest `VBallot`,
`lr` = `lb.leaderResponded` after the loop): the sub-case and the chosen reply. -/
def prepDecide (reps : List PReply) (maxVbal : w32) (lr : Bool) (replica : w32) :
    Nat × Option PReply :=
  match reps.find? (fun e => stGe e.m.status stCOMMITTED) with
  | some e => (1, some e)
  | none =>
  match reps.find? (fun e => e.m.vballot == maxVbal && e.m.status == stACCEPTED) with
  | some e => (2, some e)
  | none =>
  match (if isInitialBallot maxVbal replica && !lr then reps.find? (subCase3Ok reps maxVbal)
         else none) with
  | some e => (3, some e)
  | none =>
  match reps.find? (isPreAcceptedAt maxVbal) with
  | some e => (5, some e)
  | none => (6, none)

/-- `handlePrepareReply` (fixes R-DUP, R-PREP, R-FINAL; sub-cases 1, 2, 3, 5, 6; sub-case 5/6's
`startPhase1` at `lb.lastTriedBallot` with `lb.clientProposals`). With fix R-PROM (finding G1,
questions.md): after the committed test, a replica that promised a ballot above
`lb.lastTriedBallot` (`inst.bal > lb.lastTriedBallot`) ends its recovery (`lb.preparing = false`)
without deciding. -/
def hPrepareReply (σ : RState) (m : PrepareReply) : RState × List Out :=
  let x : InstId := ⟨toN m.replica, toN m.inst⟩
  match σ.inst x with
  | none => (σ, [])
  | some inst =>
  match inst.lb with
  | none => (σ, [])
  | some lb =>
  let σ := bumpRecvBallot σ m.ballot
  if lb.preparing = false then (σ, [])
  else if stGe inst.status stCOMMITTED then
    (σ.setInst x { inst with lb := some { lb with preparing := false } }, [])
  else if lb.lastTriedBallot.slt inst.bal then
    (σ.setInst x { inst with lb := some { lb with preparing := false } }, [])
  else if m.ballot ≠ lb.lastTriedBallot then
    (σ.setInst x { inst with lb := some { lb with nacks := lb.nacks + 1 } }, [])
  else if lb.prepareReplies.any (fun e => e.m.acceptorId == m.acceptorId) then (σ, [])
  else
    let reps := lb.prepareReplies ++ [⟨m, false⟩]
    let lb := { lb with prepareReplies := reps }
    if reps.length < (nR + 1) / 2 then (σ.setInst x { inst with lb := some lb }, [])
    else
      let lr := Bool.or lb.leaderResponded <| reps.any (fun e => e.m.acceptorId == e.m.replica)
      let maxVbal := reps.foldl (fun mx e => if mx.slt e.m.vballot then e.m.vballot else mx)
        (W32 (-1))
      let d := prepDecide reps maxVbal lr m.replica
      let lb := { lb with preparing := false, leaderResponded := lr, ballot := maxVbal }
      let lb := match d.2 with
        | some e => { lb with cmds := if e.cmdsNil then none else some e.m.command,
                              seq := e.m.seq, deps := e.m.deps, status := e.m.status }
        | none => { lb with cmds := some noop, status := stNONE }
      let inst := { inst with cmds := lb.cmds, bal := lb.lastTriedBallot,
                              vbal := lb.lastTriedBallot, seq := lb.seq, deps := lb.deps,
                              status := lb.status }
      if d.1 = 1 then
        let lb := { lb with status := stCOMMITTED }
        let inst := { inst with status := stCOMMITTED, lb := some lb }
        let σ := updateCommitted (σ.setInst x inst) x.q
        (σ, [Out.ev (.commit x inst.bal (⟨inst.cmds.getD [], inst.seq, inst.deps⟩ : Val))])
      else if d.1 = 2 ∨ d.1 = 3 then
        let lb := { lb with status := stACCEPTED }
        let inst := { inst with status := stACCEPTED, lb := some lb }
        let σ := σ.setInst x inst
        (σ, [Out.ev (.vote x lb.lastTriedBallot stACCEPTED (lbVal lb)),
             Out.ev (.accept x lb.lastTriedBallot (lbVal lb)),
             Out.bcast (bcastAcceptOf σ x (acceptOf σ m.replica m.inst lb))])
      else
        let σ := σ.setInst x { inst with lb := some lb }
        startPhase1 σ (lb.cmds.getD []) x m.replica m.inst lb.lastTriedBallot lb.clientProposals

/-- `handleTryPreAccept`: never invoked (no replica sends TryPreAccept: D2, `Inv.noTPA`; the
run loop's dispatch of one is discharged by that conjunct), so not mirrored: the state is left
as it is. -/
def hTryPreAccept (σ : RState) (_m : TryPreAccept) : RState × List Out := (σ, [])

/-- `handleTryPreAcceptReply`: never invoked (`Inv.noTPA`; it would also read the package global
`deferMap`, which `RState` does not hold), so not mirrored. -/
def hTryPreAcceptReply (σ : RState) (_m : TryPreAcceptReply) : RState × List Out := (σ, [])

/-- `startRecoveryForInstance(x.q, x.i)` (fixes R-BAL: `makeBallot` above `inst.bal` and
`lb.lastTriedBallot`; R-VBAL: only `inst.bal` set; B10: no recovery when the next owned ballot
would exceed `MaxInt32`; the own `PrepareReply` in `lb.prepareReplies`; `bcastPrepare`). The
request's ids are in range (`Step.recover`). (The overflow guard is placed after the
`nil`/committed tests, where `makeBallot` would run: `makeBallot` reads the fresh bookkeeping's
`lastTriedBallot = 0`, so the would-be ballot is `makeBallotZ σ inst.bal 0`.) -/
def hRecover (σ : RState) (x : InstId) : RState × List Out :=
  let (σ, inst) := getOrDefault σ x
  if stGe inst.status stCOMMITTED ∧ inst.cmds ≠ none then (σ, [])
  else if (2 ^ 31 - 1 : Int) < makeBallotZ σ inst.bal (W32 0) then (σ, [])
  else
    let n : w32 := W32 (makeBallotZ σ inst.bal (W32 0))
    let preply : PrepareReply :=
      { acceptorId := W32 σ.id, replica := W32 x.q, inst := W32 x.i, ballot := n,
        vballot := inst.vbal, status := inst.status, command := inst.cmds.getD [],
        seq := inst.seq, deps := inst.deps }
    let lb : LbRec :=
      { clientProposals := inst.lb.bind (·.clientProposals), ballot := inst.vbal,
        allEqual := true, preAcceptOKs := W64 0, acceptOKs := W64 0, nacks := W64 0,
        prepareReplies := [⟨preply, inst.cmds = none⟩], preparing := true,
        tryingToPreAccept := false, lastTriedBallot := n, cmds := inst.cmds,
        status := inst.status, seq := inst.seq, deps := inst.deps,
        leaderResponded := decide (σ.id = x.q), preAcceptsSent := W64 0 }
    let σ := σ.setInst x { inst with lb := some lb, bal := n }
    (σ, [Out.ev (.makeBallot x n), Out.ev (.selfReply preply), Out.bcast (bcastPrepareOf σ x n)])

/-- The run loop's dispatch of a delivered peer message (the beacons are not the epaxos
lock's: `ReplyBeacon` under `r.M`, no protocol state). -/
def hMsg (σ : RState) (m : Msg) : RState × List Out :=
  match m with
  | .prepare p => hPrepare σ p
  | .prepareReply p => hPrepareReply σ p
  | .preAccept p => hPreAccept σ p
  | .preAcceptReply p => hPreAcceptReply σ p
  | .accept p => hAccept σ p
  | .acceptReply p => hAcceptReply σ p
  | .commit p => hCommit σ p
  | .tryPreAccept p => hTryPreAccept σ p
  | .tryPreAcceptReply p => hTryPreAcceptReply σ p
  | .beacon _ => (σ, [])
  | .beaconReply _ => (σ, [])

/-! ## The executor -/

/-- `x` is EXECUTED at the replica. -/
def RState.executed (σ : RState) (x : InstId) : Prop :=
  ∃ w, σ.inst x = some w ∧ w.status = stEXECUTED

/-- `x` is COMMITTED with commands (what `strongconnect` requires of a node it visits). -/
def RState.ready (σ : RState) (x : InstId) : Prop :=
  ∃ w, σ.inst x = some w ∧ w.status = stCOMMITTED ∧ w.cmds ≠ none

/-- The edge `x → y` that `strongconnect` follows: `y.i ≤ x.deps[y.q]` (every instance of row
`y.q` up to `deps[y.q]`; instances up to `ExecedUpTo[y.q]` are executed and skipped). -/
def RState.depEdge (σ : RState) (x y : InstId) : Prop :=
  ∃ w, σ.inst x = some w ∧ y.q < nR ∧ (y.i : Int) ≤ sint.Z (w.deps.getD y.q (W32 (-1)))

/-- `C` is a component `strongconnect` executes: non-empty, distinct, committed with commands,
closed (every edge out of `C` reaches an executed instance or `C`), strongly connected inside
`C`. (A closed strongly connected set is a sink component of the graph of the non-executed
instances: exactly what Tarjan pops when the whole subtree succeeded.) -/
def sccReady (σ : RState) (C : List InstId) : Prop :=
  C ≠ [] ∧ C.Nodup ∧ (∀ x ∈ C, σ.ready x) ∧
  (∀ x ∈ C, ∀ y, σ.depEdge x y → σ.executed y ∨ y ∈ C) ∧
  (∀ x ∈ C, ∀ y ∈ C, x = y ∨ Relation.TransGen (fun a b => σ.depEdge a b ∧ a ∈ C ∧ b ∈ C) x y)

/-- `nodeArray.Less` (fix E2): `(Seq, replica, instance)` lexicographically. -/
def sccLe (σ : RState) (a b : InstId) : Bool :=
  let sa := ((σ.inst a).map (·.seq)).getD 0
  let sb := ((σ.inst b).map (·.seq)).getD 0
  sa.slt sb || (sa == sb && (decide (a.q < b.q) || (a.q == b.q && decide (a.i ≤ b.i))))

/-- The component in execution order. -/
def sccSort (σ : RState) (C : List InstId) : List InstId := C.mergeSort (sccLe σ)

/-- `Command.Execute` on the store, as the executor calls it: a PUT stores the value (and
returns `NIL`), a GET returns the key's value or `NIL`, a SCAN the values of the keys of its
range present (`rangeKeys`), in key order, concatenated; anything else returns `NIL` (NONE is
skipped by the executor). -/
def execCmd (st : w64 → Option (List w8)) (c : WCmd) : (w64 → Option (List w8)) × List w8 :=
  if c.op = opPUT then (upd st c.key (some c.val), [])
  else if c.op = opGET then (st, (st c.key).getD [])
  else if c.op = opSCAN then (st, ((rangeKeys c).filterMap st).flatten)
  else (st, [])

/-- One iteration of `strongconnect`'s per-command loop (`Dreply` is true): command `idx` of
instance `w`. NONE does nothing; with `w.lb.clientProposals` non-nil, `Execute` and
`ReplyProposeTS` to `clientProposals[idx]`; otherwise a PUT is executed (a GET is not). (Fix B8:
the executor's ghost steps are per command, each loop iteration giving the credits its escrow
needs.) -/
def execCmdAt (σ : RState) (w : InstRec) (idx : Nat) : RState × List Out :=
  let c := (w.cmds.getD []).getD idx default
  if c.op = opNONE then (σ, [])
  else match w.lb.bind (·.clientProposals) with
    | some ps =>
      let r := execCmd σ.store c
      ({ σ with store := r.1 }, [Out.reply (ps.getD idx default) r.2])
    | none =>
      if c.op = opPUT then ({ σ with store := (execCmd σ.store c).1 }, []) else (σ, [])

/-- `w.Status = EXECUTED` after an instance's commands. -/
def execDone (σ : RState) (x : InstId) : RState :=
  match σ.inst x with
  | some w => σ.setInst x { w with status := stEXECUTED }
  | none => σ

/-- The scan's `ExecedUpTo[q] = inst` step over an executed instance. -/
def execBump (σ : RState) (q : Nat) : RState :=
  { σ with execedUpTo := upd σ.execedUpTo q (σ.execedUpTo q + 1) }

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
