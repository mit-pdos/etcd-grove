package etcdraft

import (
	"strconv"
)

// This file transcribes Traceetcdraft.tla: the trace specification whose behaviors step through
// a trace of raft's events, one line at a time (a received message's line possibly in several
// steps), each step an action of etcdraft.tla that the line selects and whose states the line's
// logged values constrain.

// Event is a trace line's event, as raft's `with_tla` build logs it (raft's TracingEvent).
type Event struct {
	Name  string      `json:"name"`
	NID   string      `json:"nid"`
	State EventState  `json:"state"`
	Role  string      `json:"role"`
	Log   int         `json:"log"`
	Conf  [2][]string `json:"conf"`
	Msg   *EventMsg   `json:"msg,omitempty"`
	Prop  *EventProps `json:"prop,omitempty"`
}

// EventState is an event's node state (raft's TracingState).
type EventState struct {
	Term   int    `json:"term"`
	Vote   string `json:"vote"`
	Commit int    `json:"commit"`
}

// EventMsg is an event's message (raft's TracingMessage).
type EventMsg struct {
	Type       string `json:"type"`
	Term       int    `json:"term"`
	From       string `json:"from"`
	To         string `json:"to"`
	Entries    int    `json:"entries"`
	LogTerm    int    `json:"logTerm"`
	Index      int    `json:"index"`
	Commit     int    `json:"commit"`
	Vote       string `json:"vote"`
	Reject     bool   `json:"reject"`
	RejectHint int    `json:"rejectHint"`
}

// EventProps is an event's properties: a configuration change's (raft's TracingConfChange).
// Changes and NewConf are nil when absent (raft omits them when empty).
type EventProps struct {
	CC *EventConfChange `json:"cc,omitempty"`
}

// EventConfChange is a configuration change's record (raft's TracingConfChange).
type EventConfChange struct {
	Changes *[]EventChange `json:"changes,omitempty"`
	NewConf *[]string      `json:"newconf,omitempty"`
}

// EventChange is one change of a configuration change (raft's SingleConfChange).
type EventChange struct {
	NID    string `json:"nid"`
	Action string `json:"action"`
}

// isMessageEvent says whether a line of this name is a message's (its msg is read).
func isMessageEvent(name string) bool {
	return ReceiveMessageTraceNames[name] || name == "SendAppendEntriesRequest" ||
		name == "SendAppendEntriesResponse" || name == "SendRequestVoteRequest" || name == "SendRequestVoteResponse" ||
		name == "IgnoreRequestVoteRequest"
}

// parseID is the server a trace's id string denotes (Nil for "0"), ok false unless s is a decimal
// number in canonical form (as raft's strconv.FormatUint writes it: TLA+ compares the strings, so
// "01" and "1" are different servers there) below 2^64.
func parseID(s string) (ID, bool) {
	if len(s) == 0 || len(s) > 20 || (len(s) > 1 && s[0] == '0') {
		return 0, false
	}
	var id ID
	for k := 0; k < len(s); k++ {
		c := s[k]
		if c < '0' || c > '9' {
			return 0, false
		}
		d := ID(c - '0')
		if id > (^ID(0)-d)/10 {
			return 0, false
		}
		id = id*10 + d
	}
	return id, true
}

// TraceError is why NewTrace refuses a trace (where TLC would fail reading it, or a premise of the
// trace specification fails): What, at line Line (0: the whole trace), about server or value N.
type TraceError struct {
	What string
	Line int
	N    uint64
}

func (e *TraceError) Error() string {
	return "trace: line " + strconv.Itoa(e.Line) + ": " + e.What + " (" + strconv.FormatUint(e.N, 10) + ")"
}

func traceError(what string, line int, n uint64) error {
	return &TraceError{What: what, Line: line, N: n}
}

func toSet(ids []string) (Set, bool) {
	var out []ID
	for _, s := range ids {
		id, ok := parseID(s)
		if !ok {
			return nil, false
		}
		out = append(out, id)
	}
	return NewSet(out...), true
}

// RaftMsgType is `RaftMsgType`.
var RaftMsgType = map[string]MsgType{
	"MsgApp": AppendEntriesRequest, "MsgAppResp": AppendEntriesResponse,
	"MsgVote": RequestVoteRequest, "MsgVoteResp": RequestVoteResponse,
	"MsgHeartbeat": AppendEntriesRequest, "MsgHeartbeatResp": AppendEntriesResponse,
	"MsgSnap":    AppendEntriesRequest,
	"MsgPreVote": PreVoteRequest, "MsgPreVoteResp": PreVoteResponse,
}

// RaftMsgSubtype is `RaftMsgSubtype`.
var RaftMsgSubtype = map[string]string{
	"MsgHeartbeat": "heartbeat", "MsgHeartbeatResp": "heartbeat",
	"MsgApp": "app", "MsgAppResp": "app",
	"MsgSnap": "snapshot",
}

// ReceiveMessageTraceNames is `ReceiveMessageTraceNames`.
var ReceiveMessageTraceNames = map[string]bool{
	"ReceiveAppendEntriesRequest": true, "ReceiveAppendEntriesResponse": true,
	"ReceiveRequestVoteRequest": true, "ReceiveRequestVoteResponse": true, "ReceiveSnapshot": true,
}

// line is a trace line with its ids parsed.
type line struct {
	ev       *Event
	nid      ID
	vote     ID
	role     Role
	conf     [2]Set // ConfFromLog
	from, to ID     // the message's, if any
}

// Trace is a trace and the constants of Traceetcdraft.tla it determines: TraceServer,
// BootstrapLogIndices, LastBootstrapLog, TraceInitServer and the initial state TraceInit.
type Trace struct {
	lines     []line // TraceLog (lines[l-1] is TraceLog[l])
	Server    Set    // TraceServer
	InitSrv   Set    // TraceInitServer
	bootstrap []bool // bootstrap[l-1]: l \in BootstrapLogIndices
	init      *State
	// PreVote and CheckQuorum are the specification's constants (TracePreVote, TraceCheckQuorum:
	// raft's configuration, which the trace does not record).
	PreVote, CheckQuorum bool
}

// Len is Len(TraceLog).
func (t *Trace) Len() int { return len(t.lines) }

// Event is TraceLog[l].event.
func (t *Trace) Event(l int) *Event { return t.lines[l-1].ev }

// NewTrace builds the trace specification of events, PreVote and CheckQuorum off.
func NewTrace(events []Event) (*Trace, error) { return NewTraceWith(events, false, false) }

// NewTraceWith builds the trace specification of events, for raft's PreVote and CheckQuorum.
func NewTraceWith(events []Event, preVote, checkQuorum bool) (*Trace, error) {
	if len(events) == 0 {
		return nil, traceError("empty trace", 0, 0)
	}
	t := &Trace{PreVote: preVote, CheckQuorum: checkQuorum}
	for k := range events {
		ev := &events[k]
		ln := line{ev: ev, role: ParseRole(ev.Role)}
		var ok bool
		if ln.nid, ok = parseID(ev.NID); !ok {
			return nil, traceError("nid not an id", k+1, 0)
		}
		if ln.vote, ok = parseID(ev.State.Vote); !ok {
			return nil, traceError("vote not an id", k+1, 0)
		}
		for h := 0; h < 2; h++ {
			if ln.conf[h], ok = toSet(ev.Conf[h]); !ok {
				return nil, traceError("conf not a list of ids", k+1, 0)
			}
		}
		// Where TLC fails evaluating the line: a message event without a message
		// (LoglineIsMessageEvent reads logline.event.msg), a message of a type outside
		// RaftMsgType's domain (stricter than TLC, which fails only where it reads RaftMsgType of
		// it; raft logs no other), a ChangeConf without a configuration change or with an empty
		// change list (TraceServer reads x.event.prop.cc, and changes[1]).
		if isMessageEvent(ev.Name) && ev.Msg == nil {
			return nil, traceError("a message event without a message", k+1, 0)
		}
		if ev.Msg != nil {
			if _, ok := RaftMsgType[ev.Msg.Type]; !ok {
				return nil, traceError("message type outside RaftMsgType", k+1, 0)
			}
		}
		if ev.Name == "ChangeConf" {
			if ev.Prop == nil || ev.Prop.CC == nil {
				return nil, traceError("ChangeConf without a configuration change", k+1, 0)
			}
			if ev.Prop.CC.Changes != nil && len(*ev.Prop.CC.Changes) == 0 {
				return nil, traceError("ChangeConf with an empty change list", k+1, 0)
			}
		}
		if ev.Msg != nil {
			if ln.from, ok = parseID(ev.Msg.From); !ok {
				return nil, traceError("from not an id", k+1, 0)
			}
			if ln.to, ok = parseID(ev.Msg.To); !ok {
				return nil, traceError("to not an id", k+1, 0)
			}
		}
		t.lines = append(t.lines, ln)
	}

	// TraceServer: every line's node, and the node a ChangeConf adds (its first change's).
	var server []ID
	for _, ln := range t.lines {
		server = append(server, ln.nid)
		ev := ln.ev
		if ev.Name == "ChangeConf" && ev.Prop != nil && ev.Prop.CC != nil && ev.Prop.CC.Changes != nil &&
			len(*ev.Prop.CC.Changes) > 0 {
			c := (*ev.Prop.CC.Changes)[0]
			if c.Action == "AddNewServer" || c.Action == "AddLearner" {
				j, ok := parseID(c.NID)
				if !ok {
					return nil, traceError("a change's nid not an id", 0, 0)
				}
				server = append(server, j)
			}
		}
	}
	t.Server = NewSet(server...)

	// BootstrapLogIndices and LastBootstrapLog.
	isBootstrapName := func(n string) bool {
		return n == "InitState" || n == "BecomeFollower" || n == "ApplyConfChange"
	}
	t.bootstrap = make([]bool, len(t.lines))
	last := map[ID]int{}
	for _, i := range t.Server {
		first, firstNon := 0, 0 // SelectInSeq: the first index, 0 if none
		for l := 1; l <= len(t.lines); l++ {
			ln := t.lines[l-1]
			if ln.nid != i {
				continue
			}
			if first == 0 && isBootstrapName(ln.ev.Name) {
				first = l
			}
			if firstNon == 0 && !isBootstrapName(ln.ev.Name) {
				firstNon = l
			}
		}
		upper := len(t.lines)
		if firstNon != 0 {
			upper = firstNon - 1
		}
		for k := max(first, 1); k <= upper; k++ {
			if t.lines[k-1].nid == i {
				t.bootstrap[k-1] = true
				last[i] = k
			}
		}
		if last[i] == 0 {
			// TLC fails: Max of the empty set (a server with no bootstrap line)
			return nil, traceError("a server without a bootstrap line", 0, i)
		}
	}

	// BootstrapEntryConf(i, j): the configuration of server i's j-th bootstrap ApplyConfChange line
	// with a newconf (raft's Bootstrap adds one peer per entry), BootstrappedConfig(i) if it has
	// fewer.
	bootstrapConfs := func(i ID) ([]Set, error) {
		var out []Set
		for l := 1; l <= len(t.lines); l++ {
			ln := t.lines[l-1]
			if !t.bootstrap[l-1] || ln.nid != i || ln.ev.Name != "ApplyConfChange" || ln.ev.Prop == nil ||
				ln.ev.Prop.CC == nil || ln.ev.Prop.CC.NewConf == nil {
				continue
			}
			cfg, ok := toSet(*ln.ev.Prop.CC.NewConf)
			if !ok {
				return nil, traceError("newconf not a list of ids", l, 0)
			}
			out = append(out, cfg)
		}
		return out, nil
	}

	// BootstrappedConfig(i)
	bootstrappedConfig := func(i ID) (Set, error) {
		ln := t.lines[last[i]-1]
		if ln.ev.Name == "ApplyConfChange" {
			// TLC fails reading a missing newconf (raft omits an empty one)
			if ln.ev.Prop == nil || ln.ev.Prop.CC == nil || ln.ev.Prop.CC.NewConf == nil {
				return nil, traceError("a last bootstrap ApplyConfChange without newconf", last[i], 0)
			}
			cfg, ok := toSet(*ln.ev.Prop.CC.NewConf)
			if !ok {
				return nil, traceError("newconf not a list of ids", last[i], 0)
			}
			return cfg, nil
		}
		return ln.conf[0], nil
	}
	var err error
	if t.InitSrv, err = bootstrappedConfig(t.lines[0].nid); err != nil {
		return nil, err
	}
	if !t.InitSrv.Subset(t.Server) { // ASSUME TraceInitServer \subseteq TraceServer
		return nil, traceError("TraceInitServer not a subset of TraceServer", 0, 0)
	}

	// TraceInit's Init, with InitServerVars, InitLogVars and InitConfigVars replaced by the
	// trace's (TraceInitServerVars, TraceInitLogVars, TraceInitConfigVars).
	s := &State{Server: t.Server, S: map[ID]*Server{}, PreVote: preVote, CheckQuorum: checkQuorum}
	for _, i := range t.Server {
		lb := t.lines[last[i]-1]
		cfg, err := bootstrappedConfig(i)
		if err != nil {
			return nil, err
		}
		confs, err := bootstrapConfs(i)
		if err != nil {
			return nil, err
		}
		log := make([]Entry, lb.ev.Log)
		for k := range log {
			c := cfg
			if k < len(confs) {
				c = confs[k]
			}
			log[k] = Entry{Term: 1, Type: ConfigEntry, Value: Value{Kind: ConfRecord, NewConf: c, Learners: nil}}
		}
		v := &Server{
			CurrentTerm: lb.ev.State.Term,
			State:       lb.role,
			VotedFor:    lb.vote,
			Log:         log,
			CommitIndex: lb.ev.State.Commit,
			MatchIndex:  map[ID]int{},
			Config:      Config{Joint: [2]Set{cfg, nil}},
		}
		v.Durable = durableOf(v)
		s.S[i] = v
	}
	t.init = s
	return t, nil
}

// TState is a state of the trace specification: the specification's variables and the trace
// position l (and pl, the previous step's l).
type TState struct {
	S  *State
	L  int
	PL int
}

// Equal is equality as TLC's view `TraceView == <<vars, l>>` sees it (pl is not in the view).
func (ts TState) Equal(us TState) bool { return ts.L == us.L && ts.S.Equal(us.S) }

// indexOf is the position of a state Equal to ts in tss, or -1.
func indexOf(tss []TState, ts TState) int {
	for k, us := range tss {
		if us.Equal(ts) {
			return k
		}
	}
	return -1
}

// Init is `TraceInit`.
func (t *Trace) Init() TState { return TState{S: t.init, L: 1, PL: 0} }

// ---------------------------------------------------------------------------------------------
// The logline predicates. They read the line l of the state they are given.

func (t *Trace) logline(ts TState) *line { return &t.lines[ts.L-1] }

// loglineIsEvent is `LoglineIsEvent(e)`.
func (t *Trace) loglineIsEvent(ts TState, e string) bool {
	return ts.L <= len(t.lines) && t.logline(ts).ev.Name == e
}

// loglineIsMessageEvent is `LoglineIsMessageEvent(e, i, j)`.
func (t *Trace) loglineIsMessageEvent(ts TState, e string, i, j ID) bool {
	if !t.loglineIsEvent(ts, e) {
		return false
	}
	ln := t.logline(ts)
	return ln.ev.Msg != nil && ln.from == i && ln.to == j
}

// loglineIsNodeEvent is `LoglineIsNodeEvent(e, i)`.
func (t *Trace) loglineIsNodeEvent(ts TState, e string, i ID) bool {
	return t.loglineIsEvent(ts, e) && t.logline(ts).nid == i
}

func (ln *line) msgType() (MsgType, bool) {
	if ln.ev.Msg == nil {
		return 0, false
	}
	mt, ok := RaftMsgType[ln.ev.Msg.Type]
	return mt, ok
}

// loglineIsAppendEntriesRequest is `LoglineIsAppendEntriesRequest(m)`.
func (ln *line) isAppendEntriesRequest(m *Msg) bool {
	mt, ok := ln.msgType()
	if m.Type != AppendEntriesRequest || !ok || m.Type != mt {
		return false
	}
	ev := ln.ev.Msg
	sub, ok := RaftMsgSubtype[ev.Type]
	if !ok || m.Subtype != sub || m.Dest != ln.to || m.Source != ln.from || m.Term != ev.Term {
		return false
	}
	if m.Subtype != "snapshot" && m.CommitIndex != ev.Commit {
		return false
	}
	if m.Subtype != "heartbeat" && (m.PrevLogTerm != ev.LogTerm || m.PrevLogIndex != ev.Index) {
		return false
	}
	return len(m.Entries) == ev.Entries
}

// isAppendEntriesResponse is `LoglineIsAppendEntriesResponse(m)`.
func (ln *line) isAppendEntriesResponse(m *Msg) bool {
	mt, ok := ln.msgType()
	if m.Type != AppendEntriesResponse || !ok || m.Type != mt {
		return false
	}
	ev := ln.ev.Msg
	sub, ok := RaftMsgSubtype[ev.Type]
	if !ok || m.Subtype != sub || m.Dest != ln.to || m.Source != ln.from || m.Term != ev.Term {
		return false
	}
	if m.Success != !ev.Reject {
		return false
	}
	if !ev.Reject && m.Subtype != "heartbeat" && m.MatchIndex != ev.Index {
		return false
	}
	return true
}

// isRequestVoteRequest is `LoglineIsRequestVoteRequest(m)`.
func (ln *line) isRequestVoteRequest(m *Msg) bool {
	mt, ok := ln.msgType()
	if !(m.Type == RequestVoteRequest || m.Type == PreVoteRequest) || !ok || m.Type != mt {
		return false
	}
	ev := ln.ev.Msg
	return m.Dest == ln.to && m.Source == ln.from && m.Term == ev.Term && m.LastLogIndex == ev.Index &&
		m.LastLogTerm == ev.LogTerm
}

// isRequestVoteResponse is `LoglineIsRequestVoteResponse(m)`.
func (ln *line) isRequestVoteResponse(m *Msg) bool {
	mt, ok := ln.msgType()
	if !(m.Type == RequestVoteResponse || m.Type == PreVoteResponse) || !ok || m.Type != mt {
		return false
	}
	ev := ln.ev.Msg
	return m.Dest == ln.to && m.Source == ln.from && m.Term == ev.Term && m.VoteGranted == !ev.Reject
}

// stateMatches is the conjunction ValidatePreStates and ValidatePostStates check of server i's
// variables in s against the line.
func (ln *line) stateMatches(s *State, i ID) bool {
	v, ok := s.S[i]
	if !ok {
		return false
	}
	return v.CurrentTerm == ln.ev.State.Term && v.State == ln.role && v.VotedFor == ln.vote &&
		len(v.Log) == ln.ev.Log && v.CommitIndex == ln.ev.State.Commit &&
		v.Config.Joint[0].Equal(ln.conf[0]) && v.Config.Joint[1].Equal(ln.conf[1])
}

// validatePreStates is `ValidatePreStates(i)`: only on the line's first visit.
func (t *Trace) validatePreStates(ts TState, i ID) bool {
	if ts.PL != ts.L-1 {
		return true
	}
	return t.logline(ts).stateMatches(ts.S, i)
}

// validatePostStates is `ValidatePostStates(i)`, of the successor s.
func (t *Trace) validatePostStates(ts TState, s *State, i ID) bool {
	return t.logline(ts).stateMatches(s, i)
}

// oneMoreMessage is `OneMoreMessage(msg)`, from s to s2 (pendingMessages).
func oneMoreMessage(s, s2 *State, m *Msg) bool {
	before, after := s.PendingMessages.Count(m), s2.PendingMessages.Count(m)
	return (before == 0 && after == 1) || (before > 0 && after == before+1)
}

// oneLessMessage is `OneLessMessage(msg)`, from s to s2 (messages).
func oneLessMessage(s, s2 *State, m *Msg) bool {
	before, after := s.Messages.Count(m), s2.Messages.Count(m)
	return (before == 1 && after == 0) || (before > 0 && after == before-1)
}

// newPending is `\E m \in DOMAIN pendingMessages' : p(m) /\ OneMoreMessage(m)`.
func newPending(s, s2 *State, p func(*Msg) bool) bool {
	for _, m := range s2.PendingMessages.Domain() {
		if p(m) && oneMoreMessage(s, s2, m) {
			return true
		}
	}
	return false
}

// ---------------------------------------------------------------------------------------------
// The IfLogged actions: each returns its successors of ts's variables (nil when not enabled).

// requestVoteIfLogged is `RequestVoteIfLogged(i, j)`.
func (t *Trace) requestVoteIfLogged(ts TState, i, j ID) []*State {
	if !(t.loglineIsMessageEvent(ts, "SendRequestVoteRequest", i, j) ||
		(t.loglineIsMessageEvent(ts, "SendRequestVoteResponse", i, j) && i == j)) {
		return nil
	}
	ln := t.logline(ts)
	var out []*State
	for _, s2 := range nonNil(ts.S.RequestVote(i, j), ts.S.RequestPreVote(i, j)) {
		// ValidateAfterRequestVote(i, j)
		if t.validatePostStates(ts, s2, i) &&
			newPending(ts.S, s2, func(m *Msg) bool {
				return ln.isRequestVoteRequest(m) || (ln.isRequestVoteResponse(m) && m.Source == m.Dest)
			}) {
			out = append(out, s2)
		}
	}
	return out
}

// preTimeoutIfLogged is `PreTimeoutIfLogged(i)`.
func (t *Trace) preTimeoutIfLogged(ts TState, i ID) []*State {
	if !t.loglineIsNodeEvent(ts, "BecomePreCandidate", i) {
		return nil
	}
	s2 := ts.S.PreTimeout(i)
	if s2 == nil || !t.validatePostStates(ts, s2, i) {
		return nil
	}
	return []*State{s2}
}

// ignoreInLeaseIfLogged is `\E m \in DOMAIN messages : IgnoreInLeaseIfLogged(m)`.
func (t *Trace) ignoreInLeaseIfLogged(ts TState) []*State {
	if !t.loglineIsEvent(ts, "IgnoreRequestVoteRequest") {
		return nil
	}
	ln := t.logline(ts)
	var out []*State
	for _, m := range ts.S.Messages.Domain() {
		if !ln.isRequestVoteRequest(m) || !t.validatePreStates(ts, m.Dest) {
			continue
		}
		out = append(out, nonNil(ts.S.IgnoreInLease(m))...)
	}
	return out
}

// becomeLeaderIfLogged is `BecomeLeaderIfLogged(i)`.
func (t *Trace) becomeLeaderIfLogged(ts TState, i ID) []*State {
	if !t.loglineIsNodeEvent(ts, "BecomeLeader", i) {
		return nil
	}
	s2 := ts.S.BecomeLeader(i)
	// ValidateAfterBecomeLeader(i)
	if s2 == nil || !t.validatePostStates(ts, s2, i) || t.logline(ts).ev.Role != Leader.String() ||
		s2.S[i].State != Leader {
		return nil
	}
	return []*State{s2}
}

// clientRequestIfLogged is `ClientRequestIfLogged(i, v)`.
func (t *Trace) clientRequestIfLogged(ts TState, i ID, v int) []*State {
	if !t.loglineIsNodeEvent(ts, "Replicate", i) {
		return nil
	}
	return nonNil(ts.S.ClientRequest(i, v))
}

// advanceCommitIndexIfLogged is `AdvanceCommitIndexIfLogged(i)`.
func (t *Trace) advanceCommitIndexIfLogged(ts TState, i ID) []*State {
	if !t.loglineIsNodeEvent(ts, "Commit", i) {
		return nil
	}
	s2 := ts.S.AdvanceCommitIndex(i)
	// ValidateAfterAdvanceCommitIndex(i)
	if s2 == nil || !t.validatePostStates(ts, s2, i) || t.logline(ts).ev.Role != Leader.String() ||
		ts.S.S[i].State != Leader {
		return nil
	}
	return []*State{s2}
}

// validateAfterAppendEntries is `ValidateAfterAppendEntries(i, j)` (and ValidateAfterHeartbeat,
// the same).
func (t *Trace) validateAfterAppendEntries(ts TState, s2 *State, i ID) bool {
	ln := t.logline(ts)
	return t.validatePostStates(ts, s2, i) && newPending(ts.S, s2, ln.isAppendEntriesRequest)
}

// appendEntriesIfLogged is `AppendEntriesIfLogged(i, j, range)`, range = <<b, e>>.
func (t *Trace) appendEntriesIfLogged(ts TState, i, j ID, b, e int) []*State {
	if !t.loglineIsMessageEvent(ts, "SendAppendEntriesRequest", i, j) {
		return nil
	}
	ev := t.logline(ts).ev.Msg
	if ev.Type != "MsgApp" || b != ev.Index+1 || e != b+ev.Entries {
		return nil
	}
	s2 := ts.S.AppendEntries(i, j, b, e)
	if s2 == nil || !t.validateAfterAppendEntries(ts, s2, i) {
		return nil
	}
	return []*State{s2}
}

// heartbeatIfLogged is `HeartbeatIfLogged(i, j)`.
func (t *Trace) heartbeatIfLogged(ts TState, i, j ID) []*State {
	if !t.loglineIsMessageEvent(ts, "SendAppendEntriesRequest", i, j) || t.logline(ts).ev.Msg.Type != "MsgHeartbeat" {
		return nil
	}
	s2 := ts.S.Heartbeat(i, j)
	if s2 == nil || !t.validateAfterAppendEntries(ts, s2, i) {
		return nil
	}
	return []*State{s2}
}

// sendSnapshotIfLogged is `SendSnapshotIfLogged(i, j, index)`.
func (t *Trace) sendSnapshotIfLogged(ts TState, i, j ID, index int) []*State {
	if !t.loglineIsMessageEvent(ts, "SendAppendEntriesRequest", i, j) {
		return nil
	}
	ev := t.logline(ts).ev.Msg
	if ev.Type != "MsgSnap" || index != ev.Entries {
		return nil
	}
	s2 := ts.S.SendSnapshot(i, j, index)
	if s2 == nil || !t.validateAfterAppendEntries(ts, s2, i) {
		return nil
	}
	return []*State{s2}
}

// appendEntriesToSelfIfLogged is `AppendEntriesToSelfIfLogged(i)`.
func (t *Trace) appendEntriesToSelfIfLogged(ts TState, i ID) []*State {
	if !t.loglineIsMessageEvent(ts, "SendAppendEntriesResponse", i, i) {
		return nil
	}
	s2 := ts.S.AppendEntriesToSelf(i)
	ln := t.logline(ts)
	// ValidateAfterAppendEntriesToSelf(i)
	if s2 == nil || !t.validatePostStates(ts, s2, i) ||
		!newPending(ts.S, s2, func(m *Msg) bool { return ln.isAppendEntriesResponse(m) && m.Source == m.Dest }) {
		return nil
	}
	return []*State{s2}
}

// timeoutIfLogged is `TimeoutIfLogged(i)`.
func (t *Trace) timeoutIfLogged(ts TState, i ID) []*State {
	if !t.loglineIsNodeEvent(ts, "BecomeCandidate", i) {
		return nil
	}
	s2 := ts.S.Timeout(i)
	ln := t.logline(ts)
	// ValidateAfterTimeout(i)
	if s2 == nil || ln.ev.Role != Candidate.String() || ln.nid != i || s2.S[i].State != Candidate ||
		s2.S[i].CurrentTerm != ln.ev.State.Term {
		return nil
	}
	return []*State{s2}
}

// confChange is the line's only change, if it has exactly one: `Len(logline.event.prop.cc.changes)
// = 1` and its action and node.
func (ln *line) confChange() (string, ID, bool) {
	ev := ln.ev
	if ev.Prop == nil || ev.Prop.CC == nil || ev.Prop.CC.Changes == nil || len(*ev.Prop.CC.Changes) != 1 {
		return "", 0, false
	}
	c := (*ev.Prop.CC.Changes)[0]
	j, ok := parseID(c.NID)
	if !ok {
		return "", 0, false
	}
	return c.Action, j, true
}

// changeConfIfLogged is `AddNewServerIfLogged(i, j)`, `AddLearnerIfLogged(i, j)` and
// `DeleteServerIfLogged(i, j)`, by action.
func (t *Trace) changeConfIfLogged(ts TState, i, j ID, action string) []*State {
	if !t.loglineIsNodeEvent(ts, "ChangeConf", i) {
		return nil
	}
	a, n, ok := t.logline(ts).confChange()
	if !ok || a != action || n != j {
		return nil
	}
	switch action {
	case "AddNewServer":
		return nonNil(ts.S.AddNewServer(i, j))
	case "AddLearner":
		return nonNil(ts.S.AddLearner(i, j))
	case "RemoveServer":
		return nonNil(ts.S.DeleteServer(i, j))
	}
	return nil
}

// applySimpleConfChangeIfLogged is `ApplySimpleConfChangeIfLogged(i)`.
func (t *Trace) applySimpleConfChangeIfLogged(ts TState, i ID) []*State {
	if !t.loglineIsNodeEvent(ts, "ApplyConfChange", i) {
		return nil
	}
	return nonNil(ts.S.ApplySimpleConfChange(i))
}

// readyIfLogged is `ReadyIfLogged(i)`.
func (t *Trace) readyIfLogged(ts TState, i ID) []*State {
	if !t.loglineIsNodeEvent(ts, "Ready", i) {
		return nil
	}
	return []*State{ts.S.Ready(i)}
}

// restartIfLogged is `RestartIfLogged(i)`.
func (t *Trace) restartIfLogged(ts TState, i ID) []*State {
	if !t.loglineIsNodeEvent(ts, "InitState", i) {
		return nil
	}
	s2 := ts.S.Restart(i)
	if !t.validatePostStates(ts, s2, i) {
		return nil
	}
	return []*State{s2}
}

// isBecomeFollowerInUpdateTermOrReturnToFollower is
// `LoglineIsBecomeFollowerInUpdateTermOrReturnToFollower`.
func (t *Trace) isBecomeFollowerInUpdateTermOrReturnToFollower(ts TState) bool {
	if !t.loglineIsEvent(ts, "BecomeFollower") {
		return false
	}
	ln := t.logline(ts)
	// k == SelectLastInSubSeq(TraceLog, 1, l-1, LAMBDA x: x.event.nid = logline.event.nid)
	k := 0
	for n := 1; n <= ts.L-1; n++ {
		if t.lines[n-1].ev.NID == ln.ev.NID {
			k = n
		}
	}
	if k == 0 {
		return false
	}
	pk := t.lines[k-1].ev
	if ReceiveMessageTraceNames[pk.Name] && pk.Msg != nil && pk.State.Term < pk.Msg.Term &&
		pk.Msg.Term == ln.ev.State.Term {
		return true
	}
	return pk.Name == "ReceiveAppendEntriesRequest" && pk.Msg != nil && pk.State.Term == pk.Msg.Term &&
		pk.Msg.Term == ln.ev.State.Term && (pk.Role == Candidate.String() || pk.Role == PreCandidate.String())
}

// stepDownToFollowerIfLogged is `StepDownToFollowerIfLogged(i)`.
func (t *Trace) stepDownToFollowerIfLogged(ts TState, i ID) []*State {
	if !t.loglineIsNodeEvent(ts, "BecomeFollower", i) || t.isBecomeFollowerInUpdateTermOrReturnToFollower(ts) {
		return nil
	}
	s2 := ts.S.StepDownToFollower(i)
	if s2 == nil || !t.validatePostStates(ts, s2, i) {
		return nil
	}
	return []*State{s2}
}

// skipUnusedLogline is `SkipUnusedLogline` (its UNCHANGED vars: the same state).
func (t *Trace) skipUnusedLogline(ts TState) bool {
	ln := t.logline(ts)
	return (t.loglineIsEvent(ts, "SendAppendEntriesResponse") && ln.ev.Msg != nil && ln.ev.Msg.From != ln.ev.Msg.To) ||
		(t.loglineIsEvent(ts, "SendRequestVoteResponse") && ln.ev.Msg != nil && ln.ev.Msg.From != ln.ev.Msg.To) ||
		t.isBecomeFollowerInUpdateTermOrReturnToFollower(ts) ||
		t.loglineIsEvent(ts, "ReduceNextIndex")
}

// ---------------------------------------------------------------------------------------------
// TraceNext

// nonReceive is `TraceNextNonReceiveActions` without its StepToNextTrace: the successors'
// variables.
func (t *Trace) nonReceive(ts TState) []*State {
	ln := t.logline(ts)
	srv := t.Server
	var out []*State
	switch ln.ev.Name {
	case "SendRequestVoteRequest", "SendRequestVoteResponse":
		for _, i := range srv {
			for _, j := range srv {
				out = append(out, t.requestVoteIfLogged(ts, i, j)...)
			}
		}
	case "BecomeLeader":
		for _, i := range srv {
			out = append(out, t.becomeLeaderIfLogged(ts, i)...)
		}
	case "Replicate":
		for _, i := range srv {
			out = append(out, t.clientRequestIfLogged(ts, i, 0)...)
		}
	case "Commit":
		for _, i := range srv {
			out = append(out, t.advanceCommitIndexIfLogged(ts, i)...)
		}
	case "SendAppendEntriesRequest":
		if ln.ev.Msg == nil {
			break
		}
		switch ln.ev.Msg.Type {
		case "MsgApp":
			for _, i := range srv {
				for _, j := range srv {
					lo, hi := ts.S.S[i].MatchIndex[j]+1, len(ts.S.S[i].Log)+1
					for b := lo; b <= hi; b++ {
						for e := lo; e <= hi; e++ {
							out = append(out, t.appendEntriesIfLogged(ts, i, j, b, e)...)
						}
					}
				}
			}
		case "MsgHeartbeat":
			for _, i := range srv {
				for _, j := range srv {
					out = append(out, t.heartbeatIfLogged(ts, i, j)...)
				}
			}
		case "MsgSnap":
			for _, i := range srv {
				for _, j := range srv {
					for index := 1; index <= ts.S.S[i].CommitIndex; index++ {
						out = append(out, t.sendSnapshotIfLogged(ts, i, j, index)...)
					}
				}
			}
		}
	case "SendAppendEntriesResponse":
		for _, i := range srv {
			out = append(out, t.appendEntriesToSelfIfLogged(ts, i)...)
		}
	case "BecomeCandidate":
		for _, i := range srv {
			out = append(out, t.timeoutIfLogged(ts, i)...)
		}
	case "BecomePreCandidate":
		for _, i := range srv {
			out = append(out, t.preTimeoutIfLogged(ts, i)...)
		}
	case "IgnoreRequestVoteRequest":
		out = append(out, t.ignoreInLeaseIfLogged(ts)...)
	case "ChangeConf":
		for _, action := range []string{"AddNewServer", "AddLearner", "RemoveServer"} {
			for _, i := range srv {
				for _, j := range srv {
					out = append(out, t.changeConfIfLogged(ts, i, j, action)...)
				}
			}
		}
	case "ApplyConfChange":
		for _, i := range srv {
			out = append(out, t.applySimpleConfChangeIfLogged(ts, i)...)
		}
	case "Ready":
		for _, i := range srv {
			out = append(out, t.readyIfLogged(ts, i)...)
		}
	case "InitState":
		for _, i := range srv {
			out = append(out, t.restartIfLogged(ts, i)...)
		}
	case "BecomeFollower":
		for _, i := range srv {
			out = append(out, t.stepDownToFollowerIfLogged(ts, i)...)
		}
	}
	if t.skipUnusedLogline(ts) {
		out = append(out, ts.S)
	}
	return out
}

// receive is `TraceNextReceiveActions`: the successors, each with its l and pl.
func (t *Trace) receive(ts TState) []TState {
	if !ReceiveMessageTraceNames[t.logline(ts).ev.Name] {
		return nil
	}
	ln := t.logline(ts)
	var out []TState
	for _, m := range ts.S.Messages.Domain() {
		// ReceiveIfLogged(m) == LoglineIsReceivedMessage(m) /\ ValidatePreStates(m.mdest) /\ Receive(m)
		var matches bool
		switch ln.ev.Name {
		case "ReceiveAppendEntriesRequest", "ReceiveSnapshot":
			matches = ln.isAppendEntriesRequest(m)
		case "ReceiveAppendEntriesResponse":
			matches = ln.isAppendEntriesResponse(m)
		case "ReceiveRequestVoteRequest":
			matches = ln.isRequestVoteRequest(m)
		case "ReceiveRequestVoteResponse":
			matches = ln.isRequestVoteResponse(m)
		}
		if !matches || !t.validatePreStates(ts, m.Dest) {
			continue
		}
		for _, s2 := range ts.S.Receive(m) {
			// StepToNextTraceIfMessageIsProcessed(m)
			if oneLessMessage(ts.S, s2, m) {
				out = append(out, TState{S: s2, L: ts.L + 1, PL: ts.L})
			} else {
				out = append(out, TState{S: s2, L: ts.L, PL: ts.L})
			}
		}
	}
	return out
}

// Next is `TraceNext`: every successor of ts.
func (t *Trace) Next(ts TState) []TState {
	if ts.L > len(t.lines) {
		return nil
	}
	if t.bootstrap[ts.L-1] {
		return []TState{{S: ts.S, L: ts.L + 1, PL: ts.L}}
	}
	var out []TState
	for _, s2 := range t.nonReceive(ts) {
		out = append(out, TState{S: s2, L: ts.L + 1, PL: ts.L})
	}
	return append(out, t.receive(ts)...)
}

// StepInfo is what StepLine found besides the states: whether some state had more than one new
// successor (TLC's TraceMatched fails then: its search queue holds more than one state), and the
// first state violating an invariant (when checked), with the invariant's name.
type StepInfo struct {
	Branched  bool
	Violation string
	Bad       *State
}

// StepLine is every state with l = ts.L+1 that TraceNext reaches from ts in one or more steps
// (more only for a received message, while it is not yet processed), deduplicated by Key. ts.L
// must be at most Len(TraceLog). With invariants, every state it reaches, the intermediate steps
// of a received message's line included, is checked against Invariants (as TLC checks every new
// state); it stops at the first violation. It panics with an EvalError where TLC would fail.
func (t *Trace) StepLine(ts TState, invariants bool) ([]TState, StepInfo) {
	var out []TState
	var info StepInfo
	frontier := []TState{ts}
	visited := []TState{ts}
	for len(frontier) > 0 {
		var next []TState
		for _, f := range frontier {
			var fresh []TState
			for _, s2 := range t.Next(f) {
				if s2.L == ts.L+1 {
					if indexOf(out, s2) >= 0 {
						continue
					}
					out = append(out, s2)
				} else {
					if indexOf(visited, s2) >= 0 {
						continue
					}
					visited = append(visited, s2)
					next = append(next, s2)
				}
				if indexOf(fresh, s2) < 0 {
					fresh = append(fresh, s2)
				}
				if invariants {
					if v := s2.S.Violated(); v != "" {
						info.Violation, info.Bad = v, s2.S
						return out, info
					}
				}
			}
			if len(fresh) > 1 {
				info.Branched = true
			}
		}
		frontier = next
	}
	return out, info
}
