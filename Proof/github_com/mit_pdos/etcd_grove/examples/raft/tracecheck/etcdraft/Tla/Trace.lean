/-
Lean-first (no Rocq counterpart).

# raft's TLA+ trace specification in Lean: `Traceetcdraft.tla` (2026-11-08)

The trace specification whose behaviors step through a trace of raft's events, mirroring the Go
transcription's `trace.go` function by function: the events, the constants the specification
derives from the trace (`TraceServer`, `BootstrapLogIndices`, `LastBootstrapLog`, `TraceInit`),
the `...IfLogged` actions with their state validation, `SkipUnusedLogline`, `TraceNext`, and the
steps of one line (`stepLine`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Tla.Invariants

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

/-! ## Events (raft's `TracingEvent`, as the checker reads it: Go's `Event`) -/

structure EventState where
  term : Int
  vote : String
  commit : Int
  deriving DecidableEq, Repr, Inhabited

structure EventMsg where
  type : String
  term : Int
  «from» : String
  to : String
  entries : Int
  logTerm : Int
  index : Int
  commit : Int
  vote : String
  reject : Bool
  rejectHint : Int
  deriving DecidableEq, Repr, Inhabited

structure EventChange where
  nid : String
  action : String
  deriving DecidableEq, Repr, Inhabited

/-- A configuration change's record; `none` where JSON omits an empty list. -/
structure EventConfChange where
  changes : Option (List EventChange)
  newconf : Option (List String)
  deriving DecidableEq, Repr, Inhabited

structure EventProps where
  cc : Option EventConfChange
  deriving DecidableEq, Repr, Inhabited

structure Event where
  name : String
  nid : String
  state : EventState
  role : String
  log : Int
  conf : List String × List String
  msg : Option EventMsg
  prop : Option EventProps
  deriving DecidableEq, Repr, Inhabited

/-! ## Reading ids -/

/-- The server a trace's id string denotes, if it is a decimal number in canonical form below
`2^64` (Go: `parseID`). -/
def parseID (s : String) : Option ID :=
  let cs := s.toList
  if cs.isEmpty || cs.length > 20 || (cs.length > 1 && cs.head? == some '0') then none
  else if cs.all Char.isDigit then
    let n := cs.foldl (fun (acc : Nat) c => acc * 10 + (c.toNat - '0'.toNat)) 0
    if n < 2 ^ 64 then some n else none
  else none

/-- Go: `toSet`. -/
def toSet (ids : List String) : Option SetIds := (ids.mapM parseID).map SetIds.mk

/-- `RaftMsgType`. -/
def raftMsgType : String → Option MsgType
  | "MsgApp" => some .appendEntriesRequest
  | "MsgAppResp" => some .appendEntriesResponse
  | "MsgVote" => some .requestVoteRequest
  | "MsgVoteResp" => some .requestVoteResponse
  | "MsgHeartbeat" => some .appendEntriesRequest
  | "MsgHeartbeatResp" => some .appendEntriesResponse
  | "MsgSnap" => some .appendEntriesRequest
  | "MsgPreVote" => some .preVoteRequest
  | "MsgPreVoteResp" => some .preVoteResponse
  | _ => none

/-- `RaftMsgSubtype`. -/
def raftMsgSubtype : String → Option String
  | "MsgHeartbeat" => some "heartbeat"
  | "MsgHeartbeatResp" => some "heartbeat"
  | "MsgApp" => some "app"
  | "MsgAppResp" => some "app"
  | "MsgSnap" => some "snapshot"
  | _ => none

/-- `ReceiveMessageTraceNames`. -/
def isReceiveName (n : String) : Bool :=
  n == "ReceiveAppendEntriesRequest" || n == "ReceiveAppendEntriesResponse" ||
  n == "ReceiveRequestVoteRequest" || n == "ReceiveRequestVoteResponse" || n == "ReceiveSnapshot"

/-- Go: `isMessageEvent`. -/
def isMessageEvent (n : String) : Bool :=
  isReceiveName n || n == "SendAppendEntriesRequest" || n == "SendAppendEntriesResponse" ||
  n == "SendRequestVoteRequest" || n == "SendRequestVoteResponse" || n == "IgnoreRequestVoteRequest"

/-- A trace line with its ids parsed (Go: `line`). -/
structure Line where
  ev : Event
  nid : ID
  vote : ID
  role : Role
  conf : SetIds × SetIds
  «from» : ID
  to : ID
  deriving Inhabited

/-- Why a trace is refused (Go: `TraceError`). -/
structure TraceError where
  what : String
  line : Nat
  n : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A trace and the constants it determines (Go: `Trace`). -/
structure Trace where
  lines : List Line
  server : SetIds
  initSrv : SetIds
  bootstrap : List Bool
  init : State

def Trace.len (t : Trace) : Nat := t.lines.length

/-- `TraceLog[l]` (1-indexed). -/
def Trace.line (t : Trace) (l : Nat) : Line := t.lines.getD (l - 1) default

/-- Parses one event into a line, checking what TLC would fail reading (Go: `NewTrace`'s loop). -/
def parseLine (k : Nat) (ev : Event) : Except TraceError Line := do
  let some nid := parseID ev.nid | throw { what := "nid not an id", line := k + 1, n := 0 }
  let some vote := parseID ev.state.vote | throw { what := "vote not an id", line := k + 1, n := 0 }
  let some c0 := toSet ev.conf.1 | throw { what := "conf not a list of ids", line := k + 1, n := 0 }
  let some c1 := toSet ev.conf.2 | throw { what := "conf not a list of ids", line := k + 1, n := 0 }
  if isMessageEvent ev.name && ev.msg.isNone then
    throw { what := "a message event without a message", line := k + 1, n := 0 }
  if let some m := ev.msg then
    if (raftMsgType m.type).isNone then
      throw { what := "message type outside RaftMsgType", line := k + 1, n := 0 }
  if ev.name == "ChangeConf" then
    match ev.prop.bind EventProps.cc with
    | none => throw { what := "ChangeConf without a configuration change", line := k + 1, n := 0 }
    | some cc =>
      if cc.changes == some [] then
        throw { what := "ChangeConf with an empty change list", line := k + 1, n := 0 }
  let (fr, to) ← match ev.msg with
    | none => pure (0, 0)
    | some m => do
      let some f := parseID m.from | throw { what := "from not an id", line := k + 1, n := 0 }
      let some t := parseID m.to | throw { what := "to not an id", line := k + 1, n := 0 }
      pure (f, t)
  return { ev := ev, nid := nid, vote := vote, role := ev.role, conf := (c0, c1), «from» := fr, to := to }

/-- `isBootstrapName`. -/
def isBootstrapName (n : String) : Bool := n == "InitState" || n == "BecomeFollower" || n == "ApplyConfChange"

/-- The server a `ChangeConf` adds (its first change, an `AddNewServer` or `AddLearner`), for
`TraceServer`. -/
def addedServer (ln : Line) : Except TraceError (Option ID) :=
  if ln.ev.name != "ChangeConf" then pure none
  else match (ln.ev.prop.bind EventProps.cc).bind EventConfChange.changes with
    | some (c :: _) =>
      if c.action == "AddNewServer" || c.action == "AddLearner" then
        match parseID c.nid with
        | some j => pure (some j)
        | none => throw { what := "a change's nid not an id", line := 0, n := 0 }
      else pure none
    | _ => pure none

/-- The last bootstrap line of server `i`, 0 if none (`Max(BootstrapLogIndicesForServer(i))`), and
whether each line is a bootstrap line of `i`. -/
def bootstrapOf (lines : List Line) (i : ID) : List Bool × Nat :=
  let idx : List (Nat × Line) := (List.range lines.length).map (fun k => (k + 1, lines.getD k default))
  let first : Nat :=
    ((idx.find? (fun (p : Nat × Line) => p.2.nid == i && isBootstrapName p.2.ev.name)).map Prod.fst).getD 0
  let firstNon : Nat :=
    ((idx.find? (fun (p : Nat × Line) => p.2.nid == i && !isBootstrapName p.2.ev.name)).map Prod.fst).getD 0
  let upper : Nat := if firstNon != 0 then firstNon - 1 else lines.length
  let isB (p : Nat × Line) : Bool := decide (max first 1 ≤ p.1) && decide (p.1 ≤ upper) && p.2.nid == i
  (idx.map isB, idx.foldl (fun (acc : Nat) p => if isB p then p.1 else acc) 0)

/-- The trace specification of `events` for raft's `PreVote` and `CheckQuorum` (Go: `NewTraceWith`). -/
def newTraceWith (events : List Event) (preVote checkQuorum : Bool) : Except TraceError Trace := do
  if events.isEmpty then throw { what := "empty trace", line := 0, n := 0 }
  let lines ← ((List.range events.length).zip events).mapM (fun p => parseLine p.1 p.2)
  let added ← lines.mapM addedServer
  let server := SetIds.mk (lines.map Line.nid ++ added.filterMap id)
  let per := server.map (fun i => (i, bootstrapOf lines i))
  let bootstrap := (List.range lines.length).map (fun k => per.any (fun p => p.2.1.getD k false))
  let last (i : ID) : Nat := ((per.find? (fun p => p.1 == i)).map (fun p => p.2.2)).getD 0
  if let some p := per.find? (fun p => p.2.2 == 0) then
    throw { what := "a server without a bootstrap line", line := 0, n := p.1 }
  -- BootstrappedConfig(i)
  let bootstrappedConfig (i : ID) : Except TraceError SetIds :=
    let ln := lines.getD (last i - 1) default
    if ln.ev.name == "ApplyConfChange" then
      match (ln.ev.prop.bind EventProps.cc).bind EventConfChange.newconf with
      | none => throw { what := "a last bootstrap ApplyConfChange without newconf", line := last i, n := 0 }
      | some nc => match toSet nc with
        | some c => pure c
        | none => throw { what := "newconf not a list of ids", line := last i, n := 0 }
    else pure ln.conf.1
  let initSrv ← bootstrappedConfig (lines.getD 0 default).nid
  if !initSrv.subset server then throw { what := "TraceInitServer not a subset of TraceServer", line := 0, n := 0 }
  let cfgs ← server.mapM (fun i => do return (i, ← bootstrappedConfig i))
  let cfgOf (i : ID) : SetIds := ((cfgs.find? (fun p => p.1 == i)).map Prod.snd).getD []
  -- BootstrapEntryConf(i, j): the configuration of server i's j-th bootstrap ApplyConfChange line
  -- with a newconf (raft's Bootstrap adds one peer per entry), BootstrappedConfig(i) if it has fewer
  let bconfs ← server.mapM (fun i => do
    let flags := ((per.find? (fun p => p.1 == i)).map (fun p => p.2.1)).getD []
    let cs ← ((List.range lines.length).filter (fun k => flags.getD k false)).filterMapM (fun k => do
      let ln := lines.getD k default
      if ln.ev.name != "ApplyConfChange" then return none
      match (ln.ev.prop.bind EventProps.cc).bind EventConfChange.newconf with
      | none => return none
      | some nc => match toSet nc with
        | some c => return some c
        | none => throw { what := "newconf not a list of ids", line := k + 1, n := 0 })
    return (i, cs))
  let bconfOf (i : ID) : List SetIds := ((bconfs.find? (fun p => p.1 == i)).map Prod.snd).getD []
  let serverOf (i : ID) : Server :=
    let lb := lines.getD (last i - 1) default
    let cfg := cfgOf i
    let v : Server :=
      { currentTerm := lb.ev.state.term, state := lb.role, votedFor := lb.vote, lead := nil,
        log := (List.range lb.ev.log.toNat).map (fun k =>
          { term := 1, type := .config, value := .conf ((bconfOf i).getD k cfg) [] }),
        commitIndex := lb.ev.state.commit, votesResponded := [], votesGranted := [],
        matchIndex := fun _ => 0, pendingConfChangeIndex := 0,
        config := { incoming := cfg, outgoing := [], learners := [] }, durable := default }
    { v with durable := durableOf v }
  let st : State :=
    { server := server, s := (fun i => serverOf i), messages := [], pendingMessages := [], reconfigCount := 0,
      preVote := preVote, checkQuorum := checkQuorum }
  return { lines := lines, server := server, initSrv := initSrv, bootstrap := bootstrap, init := st }

/-- The trace specification of `events`, `PreVote` and `CheckQuorum` off (Go: `NewTrace`). -/
def newTrace (events : List Event) : Except TraceError Trace := newTraceWith events false false

/-! ## States of the trace specification -/

/-- A state of the trace specification: the variables, `l` and `pl` (Go: `TState`). -/
structure TState where
  s : State
  l : Nat
  pl : Nat

instance : Inhabited TState := ⟨{ s := default, l := 0, pl := 0 }⟩

/-- Equality as TLC's view `<<vars, l>>` sees it (`pl` not in the view; Go: `TState.Equal`). -/
def TState.eq (ts us : TState) : Bool := ts.l == us.l && ts.s.eq us.s

/-- Whether a state equal to `ts` is in `tss` (Go: `indexOf ... >= 0`). -/
def memEq (tss : List TState) (ts : TState) : Bool := tss.any (fun us => us.eq ts)

/-- `TraceInit`. -/
def Trace.initState (t : Trace) : TState := { s := t.init, l := 1, pl := 0 }

/-! ## The logline predicates -/

/-- `LoglineIsEvent(e)`. -/
def Trace.isEvent (t : Trace) (ts : TState) (e : String) : Bool := ts.l ≤ t.len && (t.line ts.l).ev.name == e

/-- `LoglineIsMessageEvent(e, i, j)`. -/
def Trace.isMessageEvent (t : Trace) (ts : TState) (e : String) (i j : ID) : Bool :=
  t.isEvent ts e && (t.line ts.l).ev.msg.isSome && (t.line ts.l).from == i && (t.line ts.l).to == j

/-- `LoglineIsNodeEvent(e, i)`. -/
def Trace.isNodeEvent (t : Trace) (ts : TState) (e : String) (i : ID) : Bool :=
  t.isEvent ts e && (t.line ts.l).nid == i

/-- `LoglineIsAppendEntriesRequest(m)`. -/
def Line.isAppendEntriesRequest (ln : Line) (m : Msg) : Bool :=
  match ln.ev.msg with
  | none => false
  | some ev =>
    m.type == .appendEntriesRequest && raftMsgType ev.type == some m.type &&
    raftMsgSubtype ev.type == some m.subtype && m.dest == ln.to && m.source == ln.from && m.term == ev.term &&
    (m.subtype == "snapshot" || m.commitIndex == ev.commit) &&
    (m.subtype == "heartbeat" || (m.prevLogTerm == ev.logTerm && m.prevLogIndex == ev.index)) &&
    (m.entries.length : Int) == ev.entries

/-- `LoglineIsAppendEntriesResponse(m)`. -/
def Line.isAppendEntriesResponse (ln : Line) (m : Msg) : Bool :=
  match ln.ev.msg with
  | none => false
  | some ev =>
    m.type == .appendEntriesResponse && raftMsgType ev.type == some m.type &&
    raftMsgSubtype ev.type == some m.subtype && m.dest == ln.to && m.source == ln.from && m.term == ev.term &&
    m.success == !ev.reject && (ev.reject || m.subtype == "heartbeat" || m.matchIndex == ev.index)

/-- `LoglineIsRequestVoteRequest(m)`. -/
def Line.isRequestVoteRequest (ln : Line) (m : Msg) : Bool :=
  match ln.ev.msg with
  | none => false
  | some ev =>
    (m.type == .requestVoteRequest || m.type == .preVoteRequest) && raftMsgType ev.type == some m.type && m.dest == ln.to &&
    m.source == ln.from && m.term == ev.term && m.lastLogIndex == ev.index && m.lastLogTerm == ev.logTerm

/-- `LoglineIsRequestVoteResponse(m)`. -/
def Line.isRequestVoteResponse (ln : Line) (m : Msg) : Bool :=
  match ln.ev.msg with
  | none => false
  | some ev =>
    (m.type == .requestVoteResponse || m.type == .preVoteResponse) && raftMsgType ev.type == some m.type &&
    m.dest == ln.to && m.source == ln.from && m.term == ev.term && m.voteGranted == !ev.reject

/-- The conjunction `ValidatePreStates`/`ValidatePostStates` check of server `i` in `st`. -/
def Line.stateMatches (ln : Line) (st : State) (i : ID) : Bool :=
  st.server.contains i &&
  (st.s i).currentTerm == ln.ev.state.term && (st.s i).state == ln.role && (st.s i).votedFor == ln.vote &&
  ((st.s i).log.length : Int) == ln.ev.log && (st.s i).commitIndex == ln.ev.state.commit &&
  (st.s i).config.incoming == ln.conf.1 && (st.s i).config.outgoing == ln.conf.2

/-- `ValidatePreStates(i)`: only on the line's first visit. -/
def Trace.validatePreStates (t : Trace) (ts : TState) (i : ID) : Bool :=
  ts.pl != ts.l - 1 || (t.line ts.l).stateMatches ts.s i

/-- `ValidatePostStates(i)`, of the successor `s2`. -/
def Trace.validatePostStates (t : Trace) (ts : TState) (s2 : State) (i : ID) : Bool :=
  (t.line ts.l).stateMatches s2 i

/-- `OneMoreMessage(msg)`, from `s` to `s2`. -/
def oneMoreMessage (s s2 : State) (m : Msg) : Bool :=
  let before := s.pendingMessages.count m
  let after := s2.pendingMessages.count m
  (before == 0 && after == 1) || (before > 0 && after == before + 1)

/-- `OneLessMessage(msg)`, from `s` to `s2`. -/
def oneLessMessage (s s2 : State) (m : Msg) : Bool :=
  let before := s.messages.count m
  let after := s2.messages.count m
  (before == 1 && after == 0) || (before > 0 && after + 1 == before)

/-- `\E m \in DOMAIN pendingMessages' : p(m) /\ OneMoreMessage(m)`. -/
def newPending (s s2 : State) (p : Msg → Bool) : Bool :=
  s2.pendingMessages.domain.any (fun m => p m && oneMoreMessage s s2 m)

/-! ## The `IfLogged` actions: their successors' variables -/

/-- `RequestVoteIfLogged(i, j)`. -/
def Trace.requestVoteIfLogged (t : Trace) (ts : TState) (i j : ID) : List State :=
  if !(t.isMessageEvent ts "SendRequestVoteRequest" i j ||
      (t.isMessageEvent ts "SendRequestVoteResponse" i j && i == j)) then []
  else
    let ln := t.line ts.l
    (somes [ts.s.requestVote i j, ts.s.requestPreVote i j]).filter (fun s2 =>
      t.validatePostStates ts s2 i &&
        newPending ts.s s2 (fun m => ln.isRequestVoteRequest m || (ln.isRequestVoteResponse m && m.source == m.dest)))

/-- `BecomeLeaderIfLogged(i)`. -/
def Trace.becomeLeaderIfLogged (t : Trace) (ts : TState) (i : ID) : List State :=
  if !t.isNodeEvent ts "BecomeLeader" i then []
  else match ts.s.becomeLeader i with
    | none => []
    | some s2 =>
      if t.validatePostStates ts s2 i && (t.line ts.l).ev.role == leader && (s2.s i).state == leader then [s2]
      else []

/-- `ClientRequestIfLogged(i, v)`. -/
def Trace.clientRequestIfLogged (t : Trace) (ts : TState) (i : ID) (v : Int) : List State :=
  if !t.isNodeEvent ts "Replicate" i then [] else somes [ts.s.clientRequest i v]

/-- `AdvanceCommitIndexIfLogged(i)`. -/
def Trace.advanceCommitIndexIfLogged (t : Trace) (ts : TState) (i : ID) : List State :=
  if !t.isNodeEvent ts "Commit" i then []
  else match ts.s.advanceCommitIndex i with
    | none => []
    | some s2 =>
      if t.validatePostStates ts s2 i && (t.line ts.l).ev.role == leader && (ts.s.s i).state == leader then [s2]
      else []

/-- `ValidateAfterAppendEntries(i, j)` (and `ValidateAfterHeartbeat`, the same). -/
def Trace.validateAfterAppendEntries (t : Trace) (ts : TState) (s2 : State) (i : ID) : Bool :=
  t.validatePostStates ts s2 i && newPending ts.s s2 (t.line ts.l).isAppendEntriesRequest

/-- `AppendEntriesIfLogged(i, j, <<b, e>>)`. -/
def Trace.appendEntriesIfLogged (t : Trace) (ts : TState) (i j : ID) (b e : Int) : EvalM (List State) := do
  if !t.isMessageEvent ts "SendAppendEntriesRequest" i j then return []
  let some ev := (t.line ts.l).ev.msg | return []
  if !(ev.type == "MsgApp" && b == ev.index + 1 && e == b + ev.entries) then return []
  match ← ts.s.appendEntries i j b e with
  | none => return []
  | some s2 => return if t.validateAfterAppendEntries ts s2 i then [s2] else []

/-- `HeartbeatIfLogged(i, j)`. -/
def Trace.heartbeatIfLogged (t : Trace) (ts : TState) (i j : ID) : EvalM (List State) := do
  if !t.isMessageEvent ts "SendAppendEntriesRequest" i j then return []
  if ((t.line ts.l).ev.msg.map EventMsg.type) != some "MsgHeartbeat" then return []
  match ← ts.s.heartbeat i j with
  | none => return []
  | some s2 => return if t.validateAfterAppendEntries ts s2 i then [s2] else []

/-- `SendSnapshotIfLogged(i, j, index)`. -/
def Trace.sendSnapshotIfLogged (t : Trace) (ts : TState) (i j : ID) (index : Int) : EvalM (List State) := do
  if !t.isMessageEvent ts "SendAppendEntriesRequest" i j then return []
  let some ev := (t.line ts.l).ev.msg | return []
  if !(ev.type == "MsgSnap" && index == ev.entries) then return []
  match ← ts.s.sendSnapshot i j index with
  | none => return []
  | some s2 => return if t.validateAfterAppendEntries ts s2 i then [s2] else []

/-- `AppendEntriesToSelfIfLogged(i)`. -/
def Trace.appendEntriesToSelfIfLogged (t : Trace) (ts : TState) (i : ID) : List State :=
  if !t.isMessageEvent ts "SendAppendEntriesResponse" i i then []
  else match ts.s.appendEntriesToSelf i with
    | none => []
    | some s2 =>
      let ln := t.line ts.l
      if t.validatePostStates ts s2 i &&
          newPending ts.s s2 (fun m => ln.isAppendEntriesResponse m && m.source == m.dest)
      then [s2] else []

/-- `PreTimeoutIfLogged(i)`. -/
def Trace.preTimeoutIfLogged (t : Trace) (ts : TState) (i : ID) : List State :=
  if !t.isNodeEvent ts "BecomePreCandidate" i then []
  else match ts.s.preTimeout i with
    | none => []
    | some s2 => if t.validatePostStates ts s2 i then [s2] else []

/-- `\E m \in DOMAIN messages : IgnoreInLeaseIfLogged(m)`. -/
def Trace.ignoreInLeaseIfLogged (t : Trace) (ts : TState) : List State :=
  if !t.isEvent ts "IgnoreRequestVoteRequest" then []
  else
    let ln := t.line ts.l
    ts.s.messages.domain.flatMap (fun m =>
      if ln.isRequestVoteRequest m && t.validatePreStates ts m.dest then somes [ts.s.ignoreInLease m] else [])

/-- `TimeoutIfLogged(i)`. -/
def Trace.timeoutIfLogged (t : Trace) (ts : TState) (i : ID) : List State :=
  if !t.isNodeEvent ts "BecomeCandidate" i then []
  else match ts.s.timeout i with
    | none => []
    | some s2 =>
      let ln := t.line ts.l
      if ln.ev.role == candidate && ln.nid == i && (s2.s i).state == candidate &&
          (s2.s i).currentTerm == ln.ev.state.term then [s2] else []

/-- The line's only change, if it has exactly one: its action and node (Go: `line.confChange`). -/
def Line.confChange (ln : Line) : Option (String × ID) :=
  match (ln.ev.prop.bind EventProps.cc).bind EventConfChange.changes with
  | some [c] => (parseID c.nid).map (fun j => (c.action, j))
  | _ => none

/-- `AddNewServerIfLogged`, `AddLearnerIfLogged`, `DeleteServerIfLogged`, by action. -/
def Trace.changeConfIfLogged (t : Trace) (ts : TState) (i j : ID) (action : String) : List State :=
  if !t.isNodeEvent ts "ChangeConf" i then []
  else match (t.line ts.l).confChange with
    | some (a, n) =>
      if a != action || n != j then []
      else if action == "AddNewServer" then somes [ts.s.addNewServer i j]
      else if action == "AddLearner" then somes [ts.s.addLearner i j]
      else if action == "RemoveServer" then somes [ts.s.deleteServer i j]
      else []
    | none => []

/-- `ApplySimpleConfChangeIfLogged(i)`. -/
def Trace.applySimpleConfChangeIfLogged (t : Trace) (ts : TState) (i : ID) : EvalM (List State) := do
  if !t.isNodeEvent ts "ApplyConfChange" i then return []
  return somes [← ts.s.applySimpleConfChange i]

/-- `ReadyIfLogged(i)`. -/
def Trace.readyIfLogged (t : Trace) (ts : TState) (i : ID) : List State :=
  if !t.isNodeEvent ts "Ready" i then [] else [ts.s.ready i]

/-- `RestartIfLogged(i)`. -/
def Trace.restartIfLogged (t : Trace) (ts : TState) (i : ID) : EvalM (List State) := do
  if !t.isNodeEvent ts "InitState" i then return []
  let s2 := ts.s.restart i
  return if t.validatePostStates ts s2 i then [s2] else []

/-- `LoglineIsBecomeFollowerInUpdateTermOrReturnToFollower`. -/
def Trace.isBecomeFollowerInUpdateTermOrReturnToFollower (t : Trace) (ts : TState) : Bool :=
  if !t.isEvent ts "BecomeFollower" then false
  else
    let ln := t.line ts.l
    -- k == SelectLastInSubSeq(TraceLog, 1, l-1, LAMBDA x: x.event.nid = logline.event.nid)
    let k := (List.range (ts.l - 1)).foldl
      (fun (acc : Nat) n => if (t.line (n + 1)).ev.nid == ln.ev.nid then n + 1 else acc) 0
    if k == 0 then false
    else
      let pk := (t.line k).ev
      match pk.msg with
      | none => false
      | some pm =>
        (isReceiveName pk.name && pk.state.term < pm.term && pm.term == ln.ev.state.term) ||
        (pk.name == "ReceiveAppendEntriesRequest" && pk.state.term == pm.term && pm.term == ln.ev.state.term &&
          (pk.role == candidate || pk.role == preCandidate))

/-- `StepDownToFollowerIfLogged(i)`. -/
def Trace.stepDownToFollowerIfLogged (t : Trace) (ts : TState) (i : ID) : List State :=
  if !t.isNodeEvent ts "BecomeFollower" i || t.isBecomeFollowerInUpdateTermOrReturnToFollower ts then []
  else match ts.s.stepDownToFollower i with
    | none => []
    | some s2 => if t.validatePostStates ts s2 i then [s2] else []

/-- `SkipUnusedLogline` (its `UNCHANGED vars`: the same state). -/
def Trace.skipUnusedLogline (t : Trace) (ts : TState) : Bool :=
  let ev := (t.line ts.l).ev
  let fromNeTo := (ev.msg.map (fun m => m.from != m.to)).getD false
  (t.isEvent ts "SendAppendEntriesResponse" && fromNeTo) ||
  (t.isEvent ts "SendRequestVoteResponse" && fromNeTo) ||
  t.isBecomeFollowerInUpdateTermOrReturnToFollower ts || t.isEvent ts "ReduceNextIndex"

/-! ## `TraceNext` -/

/-- The pairs of servers. -/
def Trace.pairs (t : Trace) : List (ID × ID) := t.server.flatMap (fun i => t.server.map (fun j => (i, j)))

/-- `TraceNextNonReceiveActions` without its `StepToNextTrace`: the successors' variables
(Go: `nonReceive`). -/
def Trace.nonReceive (t : Trace) (ts : TState) : EvalM (List State) := do
  let ev := (t.line ts.l).ev
  let srv := t.server
  let out ← match ev.name with
    | "SendRequestVoteRequest" | "SendRequestVoteResponse" =>
      pure (t.pairs.flatMap (fun p => t.requestVoteIfLogged ts p.1 p.2))
    | "BecomeLeader" => pure (srv.flatMap (t.becomeLeaderIfLogged ts))
    | "Replicate" => pure (srv.flatMap (fun i => t.clientRequestIfLogged ts i 0))
    | "Commit" => pure (srv.flatMap (t.advanceCommitIndexIfLogged ts))
    | "SendAppendEntriesRequest" =>
      match ev.msg.map EventMsg.type with
      | some "MsgApp" =>
        t.pairs.foldlM (fun acc p => do
          let lo := (ts.s.s p.1).matchIndex p.2 + 1
          let hi := ((ts.s.s p.1).log.length : Int) + 1
          (intRange lo hi).foldlM (fun acc b =>
            (intRange lo hi).foldlM (fun acc e => do
              return acc ++ (← t.appendEntriesIfLogged ts p.1 p.2 b e)) acc) acc) []
      | some "MsgHeartbeat" =>
        t.pairs.foldlM (fun acc p => do return acc ++ (← t.heartbeatIfLogged ts p.1 p.2)) []
      | some "MsgSnap" =>
        t.pairs.foldlM (fun acc p =>
          (intRange 1 (ts.s.s p.1).commitIndex).foldlM (fun acc ix => do
            return acc ++ (← t.sendSnapshotIfLogged ts p.1 p.2 ix)) acc) []
      | _ => pure []
    | "SendAppendEntriesResponse" => pure (srv.flatMap (t.appendEntriesToSelfIfLogged ts))
    | "BecomeCandidate" => pure (srv.flatMap (t.timeoutIfLogged ts))
    | "BecomePreCandidate" => pure (srv.flatMap (t.preTimeoutIfLogged ts))
    | "IgnoreRequestVoteRequest" => pure (t.ignoreInLeaseIfLogged ts)
    | "ChangeConf" =>
      pure (["AddNewServer", "AddLearner", "RemoveServer"].flatMap (fun a =>
        t.pairs.flatMap (fun p => t.changeConfIfLogged ts p.1 p.2 a)))
    | "ApplyConfChange" => srv.foldlM (fun acc i => do return acc ++ (← t.applySimpleConfChangeIfLogged ts i)) []
    | "Ready" => pure (srv.flatMap (t.readyIfLogged ts))
    | "InitState" => srv.foldlM (fun acc i => do return acc ++ (← t.restartIfLogged ts i)) []
    | "BecomeFollower" => pure (srv.flatMap (t.stepDownToFollowerIfLogged ts))
    | _ => pure []
  return if t.skipUnusedLogline ts then out ++ [ts.s] else out

/-- `TraceNextReceiveActions`: the successors, each with its `l` and `pl` (Go: `receive`). -/
def Trace.receive (t : Trace) (ts : TState) : EvalM (List TState) := do
  let ln := t.line ts.l
  if !isReceiveName ln.ev.name then return []
  ts.s.messages.domain.foldlM (fun acc m => do
    let isMatch :=
      if ln.ev.name == "ReceiveAppendEntriesRequest" || ln.ev.name == "ReceiveSnapshot" then
        ln.isAppendEntriesRequest m
      else if ln.ev.name == "ReceiveAppendEntriesResponse" then ln.isAppendEntriesResponse m
      else if ln.ev.name == "ReceiveRequestVoteRequest" then ln.isRequestVoteRequest m
      else ln.isRequestVoteResponse m
    if !isMatch || !t.validatePreStates ts m.dest then return acc
    let succ ← ts.s.receive m
    return acc ++ succ.map (fun s2 =>
      -- StepToNextTraceIfMessageIsProcessed(m)
      if oneLessMessage ts.s s2 m then { s := s2, l := ts.l + 1, pl := ts.l }
      else { s := s2, l := ts.l, pl := ts.l })) []

/-- `TraceNext`: every successor of `ts` (Go: `Trace.Next`). -/
def Trace.next (t : Trace) (ts : TState) : EvalM (List TState) := do
  if ts.l > t.len || ts.l == 0 then return []
  if t.bootstrap.getD (ts.l - 1) false then return [{ s := ts.s, l := ts.l + 1, pl := ts.l }]
  let nr ← t.nonReceive ts
  let rv ← t.receive ts
  return nr.map (fun s2 => { s := s2, l := ts.l + 1, pl := ts.l }) ++ rv

/-- What `stepLine` found besides the states (Go: `StepInfo`). -/
structure StepInfo where
  branched : Bool := false
  violation : Option String := none

/-- The fuel of `stepLine`'s loop, meant as a bound on the steps one line can take from `ts` (a
received message's: at most one term update, one return to follower, one truncation per log
entry, one append, and the handling), which the Go loop needs no bound for. That it always suffices
is open (`notes/trace-validation-plan.md`, Q7); where it would not, `stepLine` stops early. -/
def lineFuel (ts : TState) : Nat :=
  ts.s.server.foldl (fun acc i => acc + (ts.s.s i).log.length) 0 + 8

/-- One round of `stepLine`'s loop over the frontier: `(out, visited, next, info)` updated. -/
def Trace.stepRound (t : Trace) (l0 : Nat) (invariants : Bool) (frontier : List TState)
    (st : List TState × List TState × StepInfo) : EvalM (List TState × List TState × List TState × StepInfo) :=
  frontier.foldlM (fun (acc : List TState × List TState × List TState × StepInfo) f => do
    let (out, visited, next, info) := acc
    if info.violation.isSome then return acc
    let succ ← t.next f
    let (out, visited, next, fresh, info) ← succ.foldlM
      (fun (acc : List TState × List TState × List TState × List TState × StepInfo) s2 => do
        let (out, visited, next, fresh, info) := acc
        if info.violation.isSome then return acc
        let (out, visited, next, isNew) :=
          if s2.l == l0 + 1 then
            if memEq out s2 then (out, visited, next, false) else (out ++ [s2], visited, next, true)
          else if memEq visited s2 then (out, visited, next, false)
          else (out, visited ++ [s2], next ++ [s2], true)
        if !isNew then return (out, visited, next, fresh, info)
        let fresh := if memEq fresh s2 then fresh else fresh ++ [s2]
        let info ← if invariants then do
            match ← s2.s.violated with
            | some v => pure { info with violation := some v }
            | none => pure info
          else pure info
        return (out, visited, next, fresh, info))
      (out, visited, next, [], info)
    -- (as the Go's `StepLine`, which returns at a violation before it looks at `fresh`)
    return (out, visited, next,
      if info.violation.isNone && fresh.length > 1 then { info with branched := true } else info))
    (st.1, st.2.1, [], st.2.2)

/-- `stepLine`'s loop, with fuel. -/
def Trace.stepLoop (t : Trace) (l0 : Nat) (invariants : Bool) :
    Nat → List TState → List TState × List TState × StepInfo → EvalM (List TState × StepInfo)
  | 0, _, st => return (st.1, st.2.2)
  | fuel + 1, frontier, st => do
    if frontier.isEmpty then return (st.1, st.2.2)
    let (out, visited, next, info) ← t.stepRound l0 invariants frontier st
    if info.violation.isSome then return (out, info)
    t.stepLoop l0 invariants fuel next (out, visited, info)

/-- Every state with `l = ts.l + 1` that `TraceNext` reaches from `ts` in one or more steps,
deduplicated by `TState.eq`, with whether some state had more than one new successor and the
first state reached violating an invariant (when checked) (Go: `Trace.StepLine`). -/
def Trace.stepLine (t : Trace) (ts : TState) (invariants : Bool) : EvalM (List TState × StepInfo) :=
  t.stepLoop ts.l invariants (lineFuel ts) [ts] ([], [ts], {})

end Etcdraft
end EtcdGrove
end Perennial
