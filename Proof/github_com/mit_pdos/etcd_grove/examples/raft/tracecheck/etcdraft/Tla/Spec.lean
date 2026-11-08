/-
Lean-first (no Rocq counterpart).

# raft's TLA+ specification in Lean: `etcdraft.tla` (2026-11-08)

The state, `Init`, every action and the next-state relations of `etcdraft.tla`, mirroring the Go
transcription's `spec.go` (package `etcdraft`) function by function (`Types.lean` says how). An
action is `EvalM (Option State)`: `none` when not enabled, an `EvalError` where TLC fails
evaluating it (the Go panics); an action with several successors gives them all (a list).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Tla.Types

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

/-- An evaluation TLC fails (Go: `EvalError`): what, and its numbers. -/
structure EvalError where
  what : String
  a : Int := 0
  b : Int := 0
  c : Int := 0
  deriving DecidableEq, Repr, Inhabited

/-- Evaluations that may fail as TLC's do. -/
abbrev EvalM := Except EvalError

/-- `SubSeq`, failing where TLC does (Go: `SubSeq`'s panic). -/
def subSeqM (s : List Entry) (m n : Int) : EvalM (List Entry) :=
  match subSeq s m n with
  | some l => pure l
  | none => throw { what := "SubSeq past a sequence's end (length, from, to)", a := s.length, b := m, c := n }

/-- A server's configuration, `[jointConfig |-> <<incoming, outgoing>>, learners |-> ...]`. -/
structure Config where
  incoming : SetIds
  outgoing : SetIds
  learners : SetIds
  deriving DecidableEq, Repr, Inhabited

/-- A server's durable state, `durableState[i]`. -/
structure Durable where
  currentTerm : Int
  votedFor : ID
  log : Int
  commitIndex : Int
  config : Config
  deriving DecidableEq, Repr, Inhabited

/-- The per-server variables of server `i` (Go: `Server`). `matchIndex` is the function
`matchIndex[i]` (0 where the Go's map has no key). -/
structure Server where
  currentTerm : Int
  state : Role
  votedFor : ID
  log : List Entry
  commitIndex : Int
  votesResponded : SetIds
  votesGranted : SetIds
  matchIndex : ID → Int
  pendingConfChangeIndex : Int
  config : Config
  durable : Durable

instance : Inhabited Server :=
  ⟨{ currentTerm := 0, state := follower, votedFor := nil, log := [], commitIndex := 0, votesResponded := [], votesGranted := [], matchIndex := fun _ => 0, pendingConfChangeIndex := 0, config := default, durable := default }⟩

/-- A state of the specification (Go: `State`): the constant `Server` and the variables.
`s i` is server `i`'s variables (`i ∈ server`). -/
structure State where
  server : SetIds
  s : ID → Server
  messages : Bag
  pendingMessages : Bag
  reconfigCount : Int

instance : Inhabited State := ⟨{ server := [], s := (fun _ => default), messages := [], pendingMessages := [], reconfigCount := 0 }⟩

/-- Equality of server variables, `matchIndex` compared on the servers `srv` (Go: `Server.equal`). -/
def Server.eq (v w : Server) (srv : SetIds) : Bool :=
  v.currentTerm == w.currentTerm && v.state == w.state && v.votedFor == w.votedFor &&
  v.commitIndex == w.commitIndex && v.pendingConfChangeIndex == w.pendingConfChangeIndex &&
  v.log == w.log && v.votesResponded == w.votesResponded && v.votesGranted == w.votesGranted &&
  v.config == w.config && v.durable == w.durable && srv.all (fun j => v.matchIndex j == w.matchIndex j)

/-- `vars = vars` (TLC's view `vars`; Go: `State.Equal`). -/
def State.eq (s t : State) : Bool :=
  s.server == t.server && s.reconfigCount == t.reconfigCount && s.messages.eq t.messages &&
  s.pendingMessages.eq t.pendingMessages && s.server.all (fun i => (s.s i).eq (t.s i) s.server)

/-- `s` with server `i`'s variables `f`'d (Go: `State.mut` then writes). -/
def State.upd (st : State) (i : ID) (f : Server → Server) : State :=
  { st with s := fun j => if j = i then f (st.s i) else st.s j }

/-- The record `PersistState` and `InitDurableState` write (Go: `durableOf`). -/
def durableOf (v : Server) : Durable :=
  { currentTerm := v.currentTerm, votedFor := v.votedFor, log := v.log.length, commitIndex := v.commitIndex, config := v.config }

/-- `Init`, with the constants `InitServer` and `Server` (Go: `Init`). -/
def init (initServer server : SetIds) : State :=
  let v : Server :=
    { currentTerm := 0, state := follower, votedFor := nil, log := [], commitIndex := 0, votesResponded := [], votesGranted := [], matchIndex := fun _ => 0, pendingConfChangeIndex := 0, config := { incoming := initServer, outgoing := [], learners := [] }, durable := default }
  { server := server, s := (fun _ => { v with durable := durableOf v }), messages := [], pendingMessages := [], reconfigCount := 0 }

/-! ## Helpers -/

/-- `Send(m)`. -/
def State.send (st : State) (m : Msg) : State := { st with pendingMessages := st.pendingMessages.with m }

/-- `Discard(m)`. -/
def State.discard (st : State) (m : Msg) : State := { st with messages := st.messages.without m }

/-- `Reply(response, request)`. -/
def State.reply (st : State) (response request : Msg) : State :=
  { st with pendingMessages := st.pendingMessages.with response, messages := st.messages.without request }

/-- `PendingMessages(i)`. -/
def State.pendingFrom (st : State) (i : ID) : Bag := st.pendingMessages.filterMsgs (fun m => m.source == i)

/-- `GetConfig(i)`. -/
def State.getConfig (st : State) (i : ID) : SetIds := (st.s i).config.incoming

/-- `IsJointConfig(i)`. -/
def State.isJointConfig (st : State) (i : ID) : Bool := !(st.s i).config.outgoing.isEmpty

/-- `GetLearners(i)`. -/
def State.getLearners (st : State) (i : ID) : SetIds := (st.s i).config.learners

/-- `config' = ApplyConfigUpdate(i, k)` (the `k`-th entry's value's `newconf` and `learners`). -/
def State.applyConfigUpdate (st : State) (i : ID) (k : Nat) : State :=
  let (nc, ln) := match ((st.s i).log[k - 1]?).map Entry.value with
    | some (.conf nc ln) => (nc, ln)
    | _ => ([], [])
  st.upd i (fun v => { v with config := { incoming := nc, outgoing := [], learners := ln } })

/-- `CommitTo(i, c)`. -/
def State.commitTo (st : State) (i : ID) (c : Int) : State :=
  st.upd i (fun v => { v with commitIndex := max v.commitIndex c })

/-- `CurrentLeaders`. -/
def State.currentLeaders (st : State) : SetIds := st.server.filter (fun i => (st.s i).state == leader)

/-- `PersistState(i)`. -/
def State.persistState (st : State) (i : ID) : State := st.upd i (fun v => { v with durable := durableOf v })

/-! ## State transitions -/

/-- `Restart(i)`. -/
def State.restart (st : State) (i : ID) : EvalM State := do
  let v := st.s i
  let log ← subSeqM v.log 1 v.durable.log
  let st' := { st with pendingMessages := st.pendingMessages.minus (st.pendingFrom i) }
  pure <| st'.upd i (fun v => { v with
    state := follower, votesResponded := [], votesGranted := [], matchIndex := fun _ => 0,
    pendingConfChangeIndex := 0, currentTerm := v.durable.currentTerm, commitIndex := v.durable.commitIndex,
    votedFor := v.durable.votedFor, log := log, config := v.durable.config })

/-- `Timeout(i)`. -/
def State.timeout (st : State) (i : ID) : Option State :=
  let v := st.s i
  if (v.state == follower || v.state == candidate) && (st.getConfig i).contains i then
    some <| st.upd i (fun v => { v with state := candidate, currentTerm := v.currentTerm + 1, votedFor := i, votesResponded := [], votesGranted := [] })
  else none

/-- `RequestVote(i, j)`. -/
def State.requestVote (st : State) (i j : ID) : Option State :=
  let v := st.s i
  if v.state == candidate && (((st.getConfig i).union (st.getLearners i)).minus v.votesResponded).contains j then
    if i != j then
      some <| st.send { type := .requestVoteRequest, term := v.currentTerm, lastLogTerm := lastTerm v.log, lastLogIndex := v.log.length, source := i, dest := j }
    else
      some <| st.send { type := .requestVoteResponse, term := v.currentTerm, voteGranted := true, source := i, dest := i }
  else none

/-- `AppendEntriesInRangeToPeer(subtype, i, j, <<b, e>>)` (right open). -/
def State.appendEntriesInRangeToPeer (st : State) (subtype : String) (i j : ID) (b e : Int) :
    EvalM (Option State) := do
  let v := st.s i
  if i == j || b > e || v.state != leader || !((st.getConfig i).union (st.getLearners i)).contains j then
    return none
  let prevLogIndex := b - 1
  let prevLogTerm :=
    if prevLogIndex > 0 && prevLogIndex ≤ v.log.length then
      ((v.log[(prevLogIndex - 1).toNat]?).map Entry.term).getD 0
    else 0
  let lastEntry := min (v.log.length : Int) (e - 1)
  let entries ← subSeqM v.log b lastEntry
  let commit :=
    if subtype == "heartbeat" then min v.commitIndex (v.matchIndex j) else min v.commitIndex lastEntry
  return some <| st.send { type := .appendEntriesRequest, subtype := subtype, term := v.currentTerm, prevLogIndex := prevLogIndex, prevLogTerm := prevLogTerm, entries := entries, commitIndex := commit, source := i, dest := j }

/-- `AppendEntriesToSelf(i)`. -/
def State.appendEntriesToSelf (st : State) (i : ID) : Option State :=
  let v := st.s i
  if v.state != leader then none
  else some <| st.send { type := .appendEntriesResponse, subtype := "app", term := v.currentTerm, success := true, matchIndex := v.log.length, source := i, dest := i }

/-- `AppendEntries(i, j, range)`. -/
def State.appendEntries (st : State) (i j : ID) (b e : Int) : EvalM (Option State) :=
  st.appendEntriesInRangeToPeer "app" i j b e

/-- `Heartbeat(i, j)`. -/
def State.heartbeat (st : State) (i j : ID) : EvalM (Option State) :=
  st.appendEntriesInRangeToPeer "heartbeat" i j 1 1

/-- `SendSnapshot(i, j, index)`. -/
def State.sendSnapshot (st : State) (i j : ID) (index : Int) : EvalM (Option State) :=
  st.appendEntriesInRangeToPeer "snapshot" i j 1 (index + 1)

/-- `BecomeLeader(i)`. -/
def State.becomeLeader (st : State) (i : ID) : Option State :=
  let v := st.s i
  if v.state == candidate && isQuorum v.votesGranted (st.getConfig i) then
    some <| st.upd i (fun v => { v with state := leader, matchIndex := fun j => if j = i then (v.log.length : Int) else 0 })
  else none

/-- `Replicate(i, v, t)` (its enabling conditions the caller's): `log'`. -/
def State.replicate (st : State) (i : ID) (val : Value) (typ : EntryType) : State :=
  st.upd i (fun v => { v with log := v.log ++ [{ term := v.currentTerm, type := typ, value := val }] })

/-- `ClientRequest(i, v)`. -/
def State.clientRequest (st : State) (i : ID) (val : Int) : Option State :=
  if (st.s i).state != leader then none else some (st.replicate i (.val val) .value)

/-- `AdvanceCommitIndex(i)`. -/
def State.advanceCommitIndex (st : State) (i : ID) : Option State :=
  let v := st.s i
  if v.state != leader then none
  else
    let cfg := st.getConfig i
    let agree (index : Nat) : SetIds := cfg.filter (fun k => decide (v.matchIndex k ≥ index))
    let maxAgree := (List.range v.log.length).foldl
      (fun acc n => if isQuorum (agree (n + 1)) cfg then n + 1 else acc) 0
    let newCommitIndex :=
      if maxAgree > 0 && ((v.log[maxAgree - 1]?).map Entry.term) == some v.currentTerm then (maxAgree : Int)
      else v.commitIndex
    some (st.commitTo i newCommitIndex)

/-- The common body of `AddNewServer`, `AddLearner`, `DeleteServer` (their enabling conditions the
callers'). -/
def State.reconfigure (st : State) (i : ID) (newconf learners : SetIds) : State :=
  if (st.s i).pendingConfChangeIndex == 0 then
    let st' := st.replicate i (.conf newconf learners) .config
    st'.upd i (fun v => { v with pendingConfChangeIndex := v.log.length })
  else st.replicate i .emptySeq .value

/-- `AddNewServer(i, j)`. -/
def State.addNewServer (st : State) (i j : ID) : Option State :=
  if (st.s i).state != leader || (st.getConfig i).contains j || st.isJointConfig i then none
  else some (st.reconfigure i ((st.getConfig i).add j) (st.getLearners i))

/-- `AddLearner(i, j)`. -/
def State.addLearner (st : State) (i j : ID) : Option State :=
  if (st.s i).state != leader || ((st.getConfig i).union (st.getLearners i)).contains j || st.isJointConfig i then
    none
  else some (st.reconfigure i (st.getConfig i) ((st.getLearners i).add j))

/-- `DeleteServer(i, j)`. -/
def State.deleteServer (st : State) (i j : ID) : Option State :=
  if (st.s i).state != leader || !((st.getConfig i).union (st.getLearners i)).contains j || st.isJointConfig i then
    none
  else some (st.reconfigure i ((st.getConfig i).remove j) ((st.getLearners i).remove j))

/-- `ApplySimpleConfChange(i)`; `SelectLastInSubSeq(log[i], 1, commitIndex[i], ...)` fails past the
log's end, as TLC does. -/
def State.applySimpleConfChange (st : State) (i : ID) : EvalM (Option State) := do
  if st.isJointConfig i then return none
  let v := st.s i
  if v.commitIndex > v.log.length then
    throw { what := "SelectLastInSubSeq past the log's end (length, to)", a := v.log.length, b := v.commitIndex }
  let k : Nat := (List.range v.commitIndex.toNat).foldl
    (fun (acc : Nat) n => if ((v.log[n]?).map Entry.type) == some .config then n + 1 else acc) 0
  if !(k > 0 && (k : Int) ≤ v.commitIndex) then return none
  let st' := st.applyConfigUpdate i k
  if v.state == leader && v.pendingConfChangeIndex ≥ k then
    return some <| { st' with reconfigCount := st.reconfigCount + 1 }.upd i
      (fun v => { v with pendingConfChangeIndex := 0 })
  return some st'

/-- `Ready(i)`. -/
def State.ready (st : State) (i : ID) : State :=
  let st' := st.persistState i
  let msgs := st.pendingFrom i
  { st' with messages := msgs.plus st.messages, pendingMessages := st.pendingMessages.minus msgs }

/-- `BecomeFollowerOfTerm(i, t)`. -/
def State.becomeFollowerOfTerm (st : State) (i : ID) (term : Int) : State :=
  st.upd i (fun v => { v with currentTerm := term, state := follower, votedFor := if v.currentTerm != term then nil else v.votedFor })

/-- `StepDownToFollower(i)`. -/
def State.stepDownToFollower (st : State) (i : ID) : Option State :=
  let v := st.s i
  if v.state == leader || v.state == candidate then some (st.becomeFollowerOfTerm i v.currentTerm) else none

/-! ## Message handlers: `i` the recipient, `j` the sender, `m` the message -/

/-- `HandleRequestVoteRequest(i, j, m)`. -/
def State.handleRequestVoteRequest (st : State) (i j : ID) (m : Msg) : Option State :=
  let v := st.s i
  let logOk := m.lastLogTerm > lastTerm v.log ||
    (m.lastLogTerm == lastTerm v.log && m.lastLogIndex ≥ v.log.length)
  let grant := m.term == v.currentTerm && logOk && (v.votedFor == nil || v.votedFor == j)
  if !(m.term ≤ v.currentTerm) then none
  else
    let st' := if grant then st.upd i (fun v => { v with votedFor := j }) else st
    some <| st'.reply { type := .requestVoteResponse, term := v.currentTerm, voteGranted := grant, source := i, dest := j } m

/-- `HandleRequestVoteResponse(i, j, m)`. -/
def State.handleRequestVoteResponse (st : State) (i j : ID) (m : Msg) : Option State :=
  let v := st.s i
  if m.term != v.currentTerm then none
  else
    let st' := st.upd i (fun w => { w with votesResponded := v.votesResponded.add j, votesGranted := if m.voteGranted then v.votesGranted.add j else w.votesGranted })
    some (st'.discard m)

/-- `RejectAppendEntriesRequest(i, j, m, logOk)`. -/
def State.rejectAppendEntriesRequest (st : State) (i j : ID) (m : Msg) (logOk : Bool) : Option State :=
  let v := st.s i
  if !(m.term < v.currentTerm || (m.term == v.currentTerm && v.state == follower && !logOk)) then none
  else some <| st.reply { type := .appendEntriesResponse, subtype := "app", term := v.currentTerm, success := false, matchIndex := 0, source := i, dest := j } m

/-- `ReturnToFollowerState(i, m)`. -/
def State.returnToFollowerState (st : State) (i : ID) (m : Msg) : Option State :=
  let v := st.s i
  if m.term != v.currentTerm || v.state != candidate then none
  else some (st.upd i (fun v => { v with state := follower }))

/-- `HasNoConflict(i, index, ents)`. -/
def State.hasNoConflict (st : State) (i : ID) (index : Int) (ents : List Entry) : Bool :=
  let log := (st.s i).log
  index ≤ log.length + 1 &&
    (List.range ents.length).all (fun k =>
      -- k is TLA+'s k - 1
      !(index + k ≤ log.length) ||
        ((log[(index + k - 1).toNat]?).map Entry.term) == ((ents[k]?).map Entry.term))

/-- `AppendEntriesAlreadyDone(i, j, index, m)`. -/
def State.appendEntriesAlreadyDone (st : State) (i j : ID) (index : Int) (m : Msg) : Option State :=
  let v := st.s i
  if !(index ≤ v.commitIndex ||
      (index > v.commitIndex && (m.entries.isEmpty ||
        (!m.entries.isEmpty && m.prevLogIndex + m.entries.length ≤ v.log.length &&
          st.hasNoConflict i index m.entries)))) then none
  else
    let st' :=
      if index ≤ v.commitIndex then (if m.subtype == "heartbeat" then st.commitTo i m.commitIndex else st)
      else st.commitTo i (min m.commitIndex (m.prevLogIndex + m.entries.length))
    let matchIndex :=
      if m.subtype == "heartbeat" || index > v.commitIndex then m.prevLogIndex + m.entries.length else v.commitIndex
    some <| st'.reply { type := .appendEntriesResponse, subtype := m.subtype, term := v.currentTerm, success := true, matchIndex := matchIndex, source := i, dest := j } m

/-- `ConflictAppendEntriesRequest(i, index, m)`. -/
def State.conflictAppendEntriesRequest (st : State) (i : ID) (index : Int) (m : Msg) : EvalM (Option State) := do
  let v := st.s i
  if !(!m.entries.isEmpty && index > v.commitIndex && !st.hasNoConflict i index m.entries) then return none
  let log ← subSeqM v.log 1 (v.log.length - 1)
  return some (st.upd i (fun v => { v with log := log }))

/-- `NoConflictAppendEntriesRequest(i, index, m)`. -/
def State.noConflictAppendEntriesRequest (st : State) (i : ID) (index : Int) (m : Msg) :
    EvalM (Option State) := do
  let v := st.s i
  if !(!m.entries.isEmpty && index > v.commitIndex && st.hasNoConflict i index m.entries) then return none
  let suffix ← subSeqM m.entries (v.log.length - index + 2) m.entries.length
  return some (st.upd i (fun v => { v with log := v.log ++ suffix }))

/-- The successors of a list of optional successors. -/
def somes (l : List (Option State)) : List State := l.filterMap id

/-- `AcceptAppendEntriesRequest(i, j, logOk, m)`. -/
def State.acceptAppendEntriesRequest (st : State) (i j : ID) (logOk : Bool) (m : Msg) : EvalM (List State) := do
  let v := st.s i
  if m.term != v.currentTerm || v.state != follower || !logOk then return []
  let index := m.prevLogIndex + 1
  let c ← st.conflictAppendEntriesRequest i index m
  let n ← st.noConflictAppendEntriesRequest i index m
  return somes [st.appendEntriesAlreadyDone i j index m, c, n]

/-- `HandleAppendEntriesRequest(i, j, m)`. -/
def State.handleAppendEntriesRequest (st : State) (i j : ID) (m : Msg) : EvalM (List State) := do
  let v := st.s i
  let logOk := m.prevLogIndex == 0 ||
    (m.prevLogIndex > 0 && m.prevLogIndex ≤ v.log.length &&
      some m.prevLogTerm == ((v.log[(m.prevLogIndex - 1).toNat]?).map Entry.term))
  if !(m.term ≤ v.currentTerm) then return []
  let acc ← st.acceptAppendEntriesRequest i j logOk m
  return somes [st.rejectAppendEntriesRequest i j m logOk, st.returnToFollowerState i m] ++ acc

/-- `HandleAppendEntriesResponse(i, j, m)`. -/
def State.handleAppendEntriesResponse (st : State) (i j : ID) (m : Msg) : Option State :=
  let v := st.s i
  if m.term != v.currentTerm then none
  else
    let st' := if m.success then
        st.upd i (fun w => { w with
          matchIndex := fun k => if k = j then max (v.matchIndex j) m.matchIndex else w.matchIndex k })
      else st
    some (st'.discard m)

/-- `UpdateTerm(i, j, m)`. -/
def State.updateTerm (st : State) (i _j : ID) (m : Msg) : Option State :=
  if !(m.term > (st.s i).currentTerm) then none else some (st.becomeFollowerOfTerm i m.term)

/-- `DropStaleResponse(i, j, m)`. -/
def State.dropStaleResponse (st : State) (i _j : ID) (m : Msg) : Option State :=
  if !(m.term < (st.s i).currentTerm) then none else some (st.discard m)

/-- `Receive(m) == ReceiveDirect(m)`: every successor. `m`'s destination must be a server. -/
def State.receive (st : State) (m : Msg) : EvalM (List State) := do
  let i := m.dest
  let j := m.source
  if !st.server.contains i then return []
  let upd := somes [st.updateTerm i j m]
  match m.type with
  | .requestVoteRequest => return upd ++ somes [st.handleRequestVoteRequest i j m]
  | .requestVoteResponse =>
    return upd ++ somes [st.dropStaleResponse i j m, st.handleRequestVoteResponse i j m]
  | .appendEntriesRequest => return upd ++ (← st.handleAppendEntriesRequest i j m)
  | .appendEntriesResponse =>
    return upd ++ somes [st.dropStaleResponse i j m, st.handleAppendEntriesResponse i j m]

/-- `DuplicateMessage(m)`. -/
def State.duplicateMessage (st : State) (m : Msg) : Option State :=
  if st.messages.count m == 0 then none else some { st with messages := st.messages.with m }

/-- `DropMessage(m)`. -/
def State.dropMessage (st : State) (m : Msg) : State := st.discard m

/-! ## The next-state relations: every successor (with repetitions) -/

/-- The successors an `EvalM (Option State)` per element gives. -/
def collectM {α : Type} (l : List α) (f : α → EvalM (Option State)) : EvalM (List State) :=
  l.foldlM (fun acc a => do return acc ++ somes [← f a]) []

/-- The indices `lo..hi` as integers. -/
def intRange (lo hi : Int) : List Int :=
  (List.range (hi - lo + 1).toNat).map (fun (k : Nat) => lo + (k : Int))

/-- `NextAsync`. -/
def State.nextAsync (st : State) : EvalM (List State) := do
  let srv := st.server
  let pairs := srv.flatMap (fun i => srv.map (fun j => (i, j)))
  let rv := somes (pairs.map (fun p => st.requestVote p.1 p.2))
  let lead := srv.flatMap (fun i => somes [st.becomeLeader i, st.clientRequest i 0, st.advanceCommitIndex i])
  let app ← collectM (pairs.flatMap (fun p =>
      let lo := (st.s p.1).matchIndex p.2 + 1
      let hi := ((st.s p.1).log.length : Int) + 1
      (intRange lo hi).flatMap (fun b => (intRange lo hi).map (fun e => (p, b, e)))))
    (fun x => st.appendEntries x.1.1 x.1.2 x.2.1 x.2.2)
  let toSelf := somes (srv.map (fun i => st.appendEntriesToSelf i))
  let hb ← collectM pairs (fun p => st.heartbeat p.1 p.2)
  let snaps ← collectM (pairs.flatMap (fun p => (intRange 1 (st.s p.1).commitIndex).map (fun ix => (p, ix))))
    (fun x => st.sendSnapshot x.1.1 x.1.2 x.2)
  let recv ← st.messages.domain.foldlM (fun acc m => do return acc ++ (← st.receive m)) []
  let rest := srv.flatMap (fun i => somes [st.timeout i, some (st.ready i), st.stepDownToFollower i])
  return rv ++ lead ++ app ++ toSelf ++ (hb ++ snaps) ++ recv ++ rest

/-- `NextCrash`. -/
def State.nextCrash (st : State) : EvalM (List State) := st.server.mapM st.restart

/-- `NextUnreliable`. -/
def State.nextUnreliable (st : State) : List State :=
  st.messages.domain.flatMap (fun m =>
    if st.messages.count m == 1 then somes [st.duplicateMessage m, some (st.dropMessage m)] else [])

/-- `Next`. -/
def State.next (st : State) : EvalM (List State) := do
  return (← st.nextAsync) ++ (← st.nextCrash) ++ st.nextUnreliable

/-- `NextDynamic`. -/
def State.nextDynamic (st : State) : EvalM (List State) := do
  let srv := st.server
  let pairs := srv.flatMap (fun i => srv.map (fun j => (i, j)))
  let conf := pairs.flatMap (fun p => somes [st.addNewServer p.1 p.2, st.addLearner p.1 p.2, st.deleteServer p.1 p.2])
  let apply ← collectM srv st.applySimpleConfChange
  return (← st.next) ++ conf ++ apply

end Etcdraft
end EtcdGrove
end Perennial
