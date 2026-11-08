package etcdraft

import (
	"fmt"
	"strings"
)

// Config is a server's configuration, `[jointConfig |-> <<incoming, outgoing>>, learners |-> ...]`.
type Config struct {
	Joint    [2]Set
	Learners Set
}

// Equal is `c = d`.
func (c Config) Equal(d Config) bool {
	return c.Joint[0].Equal(d.Joint[0]) && c.Joint[1].Equal(d.Joint[1]) && c.Learners.Equal(d.Learners)
}

// Durable is a server's durable state, `durableState[i]`.
type Durable struct {
	CurrentTerm int
	VotedFor    ID
	Log         int // the length of the log persisted
	CommitIndex int
	Config      Config
}

func (d Durable) equal(e Durable) bool {
	return d.CurrentTerm == e.CurrentTerm && d.VotedFor == e.VotedFor && d.Log == e.Log &&
		d.CommitIndex == e.CommitIndex && d.Config.Equal(e.Config)
}

// Server is the per-server variables of server i: `currentTerm[i]`, `state[i]`, `votedFor[i]`,
// `log[i]`, `commitIndex[i]`, `votesResponded[i]`, `votesGranted[i]`, `matchIndex[i]`,
// `pendingConfChangeIndex[i]`, `config[i]`, `durableState[i]`. A Server is never written once in
// a State; State.mut copies it.
type Server struct {
	CurrentTerm            int
	State                  Role
	VotedFor               ID
	Log                    []Entry
	CommitIndex            int
	VotesResponded         Set
	VotesGranted           Set
	MatchIndex             map[ID]int // a function on Server: missing keys are 0
	PendingConfChangeIndex int
	Config                 Config
	Durable                Durable
}

func (s *Server) copy() *Server {
	c := *s
	c.MatchIndex = make(map[ID]int, len(s.MatchIndex))
	for k, v := range s.MatchIndex {
		c.MatchIndex[k] = v
	}
	return &c
}

// State is a state of the specification: its variables.
type State struct {
	// Server is the constant Server (shared, never written).
	Server Set
	// S holds the per-server variables, one entry per server of Server.
	S               map[ID]*Server
	Messages        Bag // messages
	PendingMessages Bag // pendingMessages
	ReconfigCount   int // reconfigCount
}

// clone is a copy of s sharing its servers, which mut copies before they are written.
func (s *State) clone() *State {
	c := *s
	c.S = make(map[ID]*Server, len(s.S))
	for k, v := range s.S {
		c.S[k] = v
	}
	return &c
}

// mut is server i of s, copied (so that writing it changes s only). s must be a clone.
func (s *State) mut(i ID) *Server {
	c := s.S[i].copy()
	s.S[i] = c
	return c
}

// Key is a canonical encoding of s: two states are equal exactly when their keys are (TLC's
// view `vars`).
func (s *State) Key() string {
	var b strings.Builder
	for _, i := range s.Server {
		v := s.S[i]
		fmt.Fprintf(&b, "%d:%d,%d,%d,%d,%v,%v,", i, v.CurrentTerm, v.State, v.VotedFor, v.CommitIndex,
			[]ID(v.VotesResponded), []ID(v.VotesGranted))
		for _, j := range s.Server {
			fmt.Fprintf(&b, "%d.", v.MatchIndex[j])
		}
		fmt.Fprintf(&b, ",%d,%v%v%v,", v.PendingConfChangeIndex, []ID(v.Config.Joint[0]), []ID(v.Config.Joint[1]),
			[]ID(v.Config.Learners))
		d := v.Durable
		fmt.Fprintf(&b, "%d,%d,%d,%d,%v%v%v,", d.CurrentTerm, d.VotedFor, d.Log, d.CommitIndex,
			[]ID(d.Config.Joint[0]), []ID(d.Config.Joint[1]), []ID(d.Config.Learners))
		for _, e := range v.Log {
			writeEntry(&b, e)
		}
		b.WriteString(";")
	}
	fmt.Fprintf(&b, "rc%d;M", s.ReconfigCount)
	s.Messages.key(&b)
	b.WriteString(";P")
	s.PendingMessages.key(&b)
	return b.String()
}

// Equal is `vars = vars` of the two states.
func (s *State) Equal(t *State) bool { return s.Key() == t.Key() }

func (s *State) String() string {
	var b strings.Builder
	for _, i := range s.Server {
		v := s.S[i]
		fmt.Fprintf(&b, "%d: %v term %d vote %d log %d commit %d cfg %v/%v learners %v match %v responded %v granted %v pcc %d durable(t%d v%d l%d c%d)\n",
			i, v.State, v.CurrentTerm, v.VotedFor, len(v.Log), v.CommitIndex, v.Config.Joint[0], v.Config.Joint[1],
			v.Config.Learners, v.MatchIndex, v.VotesResponded, v.VotesGranted, v.PendingConfChangeIndex,
			v.Durable.CurrentTerm, v.Durable.VotedFor, v.Durable.Log, v.Durable.CommitIndex)
	}
	fmt.Fprintf(&b, "messages %d, pending %d, reconfigCount %d\n", s.Messages.Len(), s.PendingMessages.Len(), s.ReconfigCount)
	return b.String()
}

// Init is `Init`, with the constants InitServer and Server.
func Init(initServer, server Set) *State {
	s := &State{Server: server, S: map[ID]*Server{}}
	for _, i := range server {
		v := &Server{
			State:      Follower,
			VotedFor:   Nil,
			MatchIndex: map[ID]int{},
			Config:     Config{Joint: [2]Set{initServer, nil}},
		}
		v.Durable = durableOf(v)
		s.S[i] = v
	}
	return s
}

// durableOf is the record `PersistState` and `InitDurableState` write for a server.
func durableOf(v *Server) Durable {
	return Durable{CurrentTerm: v.CurrentTerm, VotedFor: v.VotedFor, Log: len(v.Log), CommitIndex: v.CommitIndex, Config: v.Config}
}

// ---------------------------------------------------------------------------------------------
// Helpers

// send is `Send(m) == SendDirect(m) == pendingMessages' = WithMessage(m, pendingMessages)`.
func (s *State) send(m *Msg) { s.PendingMessages = s.PendingMessages.With(m) }

// discard is `Discard(m) == DiscardDirect(m) == messages' = WithoutMessage(m, messages)`.
func (s *State) discard(m *Msg) { s.Messages = s.Messages.Without(m) }

// reply is `Reply(response, request) == ReplyDirect(response, request)`.
func (s *State) reply(response, request *Msg) {
	s.PendingMessages = s.PendingMessages.With(response)
	s.Messages = s.Messages.Without(request)
}

// pendingFrom is `PendingMessages(i)`: the pending messages sent by i.
func (s *State) pendingFrom(i ID) Bag {
	return s.PendingMessages.Filter(func(m *Msg) bool { return m.Source == i })
}

// GetConfig is `GetConfig(i) == GetJointConfig(i)[1]`.
func (s *State) GetConfig(i ID) Set { return s.S[i].Config.Joint[0] }

// IsJointConfig is `IsJointConfig(i) == GetJointConfig(i)[2] # {}`.
func (s *State) IsJointConfig(i ID) bool { return len(s.S[i].Config.Joint[1]) != 0 }

// GetLearners is `GetLearners(i) == config[i].learners`.
func (s *State) GetLearners(i ID) Set { return s.S[i].Config.Learners }

// applyConfigUpdate is `config' = ApplyConfigUpdate(i, k)`.
func (s *State) applyConfigUpdate(i ID, k int) {
	v := s.mut(i)
	e := v.Log[k-1]
	v.Config = Config{Joint: [2]Set{e.Value.NewConf, nil}, Learners: e.Value.Learners}
}

// commitTo is `CommitTo(i, c) == commitIndex' = [commitIndex EXCEPT ![i] = Max({@, c})]`.
func (s *State) commitTo(i ID, c int) {
	v := s.mut(i)
	if c > v.CommitIndex {
		v.CommitIndex = c
	}
}

// CurrentLeaders is `CurrentLeaders == {i \in Server : state[i] = Leader}`.
func (s *State) CurrentLeaders() Set {
	var ls Set
	for _, i := range s.Server {
		if s.S[i].State == Leader {
			ls = append(ls, i)
		}
	}
	return ls
}

// persistState is `PersistState(i)`.
func (s *State) persistState(i ID) {
	v := s.mut(i)
	v.Durable = durableOf(v)
}

// ---------------------------------------------------------------------------------------------
// State transitions. Each returns the successor state, or nil when the action is not enabled;
// an action with several successors returns them all.

// Restart is `Restart(i)`.
func (s *State) Restart(i ID) *State {
	t := s.clone()
	v := t.mut(i)
	v.State = Follower
	v.VotesResponded = nil
	v.VotesGranted = nil
	v.MatchIndex = map[ID]int{}
	v.PendingConfChangeIndex = 0
	t.PendingMessages = s.PendingMessages.Minus(s.pendingFrom(i)) // ClearPendingMessages(i)
	v.CurrentTerm = v.Durable.CurrentTerm
	v.CommitIndex = v.Durable.CommitIndex
	v.VotedFor = v.Durable.VotedFor
	v.Log = SubSeq(v.Log, 1, v.Durable.Log)
	v.Config = v.Durable.Config
	return t
}

// Timeout is `Timeout(i)`.
func (s *State) Timeout(i ID) *State {
	v := s.S[i]
	if !(v.State == Follower || v.State == Candidate) || !s.GetConfig(i).Has(i) {
		return nil
	}
	t := s.clone()
	w := t.mut(i)
	w.State = Candidate
	w.CurrentTerm = v.CurrentTerm + 1
	w.VotedFor = i
	w.VotesResponded = nil
	w.VotesGranted = nil
	return t
}

// RequestVote is `RequestVote(i, j)`.
func (s *State) RequestVote(i, j ID) *State {
	v := s.S[i]
	if v.State != Candidate || !s.GetConfig(i).Union(s.GetLearners(i)).Minus(v.VotesResponded).Has(j) {
		return nil
	}
	t := s.clone()
	if i != j {
		t.send(&Msg{Type: RequestVoteRequest, Term: v.CurrentTerm, LastLogTerm: LastTerm(v.Log),
			LastLogIndex: len(v.Log), Source: i, Dest: j})
	} else {
		t.send(&Msg{Type: RequestVoteResponse, Term: v.CurrentTerm, VoteGranted: true, Source: i, Dest: i})
	}
	return t
}

// AppendEntriesInRangeToPeer is `AppendEntriesInRangeToPeer(subtype, i, j, range)`, range =
// <<b, e>> (right open).
func (s *State) AppendEntriesInRangeToPeer(subtype string, i, j ID, b, e int) *State {
	v := s.S[i]
	if i == j || b > e || v.State != Leader || !s.GetConfig(i).Union(s.GetLearners(i)).Has(j) {
		return nil
	}
	prevLogIndex := b - 1
	prevLogTerm := 0
	if prevLogIndex > 0 && prevLogIndex <= len(v.Log) {
		prevLogTerm = v.Log[prevLogIndex-1].Term
	}
	lastEntry := min(len(v.Log), e-1)
	entries := SubSeq(v.Log, b, lastEntry)
	var commit int
	if subtype == "heartbeat" {
		commit = min(v.CommitIndex, v.MatchIndex[j])
	} else {
		commit = min(v.CommitIndex, lastEntry)
	}
	t := s.clone()
	t.send(&Msg{Type: AppendEntriesRequest, Subtype: subtype, Term: v.CurrentTerm, PrevLogIndex: prevLogIndex,
		PrevLogTerm: prevLogTerm, Entries: entries, CommitIndex: commit, Source: i, Dest: j})
	return t
}

// AppendEntriesToSelf is `AppendEntriesToSelf(i)`.
func (s *State) AppendEntriesToSelf(i ID) *State {
	v := s.S[i]
	if v.State != Leader {
		return nil
	}
	t := s.clone()
	t.send(&Msg{Type: AppendEntriesResponse, Subtype: "app", Term: v.CurrentTerm, Success: true,
		MatchIndex: len(v.Log), Source: i, Dest: i})
	return t
}

// AppendEntries is `AppendEntries(i, j, range)`.
func (s *State) AppendEntries(i, j ID, b, e int) *State {
	return s.AppendEntriesInRangeToPeer("app", i, j, b, e)
}

// Heartbeat is `Heartbeat(i, j)`.
func (s *State) Heartbeat(i, j ID) *State {
	return s.AppendEntriesInRangeToPeer("heartbeat", i, j, 1, 1)
}

// SendSnapshot is `SendSnapshot(i, j, index)`.
func (s *State) SendSnapshot(i, j ID, index int) *State {
	return s.AppendEntriesInRangeToPeer("snapshot", i, j, 1, index+1)
}

// BecomeLeader is `BecomeLeader(i)`.
func (s *State) BecomeLeader(i ID) *State {
	v := s.S[i]
	if v.State != Candidate || !IsQuorum(v.VotesGranted, s.GetConfig(i)) {
		return nil
	}
	t := s.clone()
	w := t.mut(i)
	w.State = Leader
	w.MatchIndex = map[ID]int{}
	for _, j := range s.Server {
		if j == i {
			w.MatchIndex[j] = len(v.Log)
		}
	}
	return t
}

// replicate is `Replicate(i, v, t)` (its enabling conditions are checked by the caller): log'.
func (s *State) replicate(i ID, val Value, typ EntryType) {
	v := s.mut(i)
	entry := Entry{Term: v.CurrentTerm, Type: typ, Value: val}
	v.Log = append(v.Log[:len(v.Log):len(v.Log)], entry)
}

// ClientRequest is `ClientRequest(i, v)`.
func (s *State) ClientRequest(i ID, val int) *State {
	if s.S[i].State != Leader {
		return nil
	}
	t := s.clone()
	t.replicate(i, Value{Kind: ValRecord, Val: val}, ValueEntry)
	return t
}

// AdvanceCommitIndex is `AdvanceCommitIndex(i)`.
func (s *State) AdvanceCommitIndex(i ID) *State {
	v := s.S[i]
	if v.State != Leader {
		return nil
	}
	cfg := s.GetConfig(i)
	agree := func(index int) Set {
		var a Set
		for _, k := range cfg {
			if v.MatchIndex[k] >= index {
				a = append(a, k)
			}
		}
		return a
	}
	maxAgree := 0 // Max(agreeIndexes), 0 when empty
	for index := 1; index <= len(v.Log); index++ {
		if IsQuorum(agree(index), cfg) {
			maxAgree = index
		}
	}
	newCommitIndex := v.CommitIndex
	if maxAgree > 0 && v.Log[maxAgree-1].Term == v.CurrentTerm {
		newCommitIndex = maxAgree
	}
	t := s.clone()
	t.commitTo(i, newCommitIndex)
	return t
}

// reconfigure is the common body of AddNewServer, AddLearner and DeleteServer (their enabling
// conditions are checked by the callers): a configuration entry if no change is pending, else
// the empty value.
func (s *State) reconfigure(i ID, newconf, learners Set) *State {
	t := s.clone()
	if s.S[i].PendingConfChangeIndex == 0 {
		t.replicate(i, Value{Kind: ConfRecord, NewConf: newconf, Learners: learners}, ConfigEntry)
		w := t.mut(i)
		w.PendingConfChangeIndex = len(w.Log)
	} else {
		t.replicate(i, Value{Kind: EmptySeq}, ValueEntry)
	}
	return t
}

// AddNewServer is `AddNewServer(i, j)`.
func (s *State) AddNewServer(i, j ID) *State {
	if s.S[i].State != Leader || s.GetConfig(i).Has(j) || s.IsJointConfig(i) {
		return nil
	}
	return s.reconfigure(i, s.GetConfig(i).Add(j), s.GetLearners(i))
}

// AddLearner is `AddLearner(i, j)`.
func (s *State) AddLearner(i, j ID) *State {
	if s.S[i].State != Leader || s.GetConfig(i).Union(s.GetLearners(i)).Has(j) || s.IsJointConfig(i) {
		return nil
	}
	return s.reconfigure(i, s.GetConfig(i), s.GetLearners(i).Add(j))
}

// DeleteServer is `DeleteServer(i, j)`.
func (s *State) DeleteServer(i, j ID) *State {
	if s.S[i].State != Leader || !s.GetConfig(i).Union(s.GetLearners(i)).Has(j) || s.IsJointConfig(i) {
		return nil
	}
	return s.reconfigure(i, s.GetConfig(i).Remove(j), s.GetLearners(i).Remove(j))
}

// ApplySimpleConfChange is `ApplySimpleConfChange(i)`.
func (s *State) ApplySimpleConfChange(i ID) *State {
	if s.IsJointConfig(i) {
		return nil
	}
	v := s.S[i]
	// k == SelectLastInSubSeq(log[i], 1, commitIndex[i], LAMBDA x: x.type = ConfigEntry)
	k := 0
	for n := 1; n <= v.CommitIndex && n <= len(v.Log); n++ {
		if v.Log[n-1].Type == ConfigEntry {
			k = n
		}
	}
	if !(k > 0 && k <= v.CommitIndex) {
		return nil
	}
	t := s.clone()
	t.applyConfigUpdate(i, k)
	if v.State == Leader && v.PendingConfChangeIndex >= k {
		t.ReconfigCount = s.ReconfigCount + 1
		t.mut(i).PendingConfChangeIndex = 0
	}
	return t
}

// Ready is `Ready(i)`.
func (s *State) Ready(i ID) *State {
	t := s.clone()
	t.persistState(i)
	msgs := s.pendingFrom(i) // SendPendingMessages(i)
	t.Messages = msgs.Plus(s.Messages)
	t.PendingMessages = s.PendingMessages.Minus(msgs)
	return t
}

// becomeFollowerOfTerm is `BecomeFollowerOfTerm(i, t)`.
func (s *State) becomeFollowerOfTerm(i ID, term int) {
	v := s.mut(i)
	old := v.CurrentTerm
	v.CurrentTerm = term
	v.State = Follower
	if old != term {
		v.VotedFor = Nil
	}
}

// StepDownToFollower is `StepDownToFollower(i)`.
func (s *State) StepDownToFollower(i ID) *State {
	v := s.S[i]
	if !(v.State == Leader || v.State == Candidate) {
		return nil
	}
	t := s.clone()
	t.becomeFollowerOfTerm(i, v.CurrentTerm)
	return t
}

// ---------------------------------------------------------------------------------------------
// Message handlers: i = recipient, j = sender, m = message.

// HandleRequestVoteRequest is `HandleRequestVoteRequest(i, j, m)`.
func (s *State) HandleRequestVoteRequest(i, j ID, m *Msg) *State {
	v := s.S[i]
	logOk := m.LastLogTerm > LastTerm(v.Log) || (m.LastLogTerm == LastTerm(v.Log) && m.LastLogIndex >= len(v.Log))
	grant := m.Term == v.CurrentTerm && logOk && (v.VotedFor == Nil || v.VotedFor == j)
	if !(m.Term <= v.CurrentTerm) {
		return nil
	}
	t := s.clone()
	if grant {
		t.mut(i).VotedFor = j
	}
	t.reply(&Msg{Type: RequestVoteResponse, Term: v.CurrentTerm, VoteGranted: grant, Source: i, Dest: j}, m)
	return t
}

// HandleRequestVoteResponse is `HandleRequestVoteResponse(i, j, m)`.
func (s *State) HandleRequestVoteResponse(i, j ID, m *Msg) *State {
	v := s.S[i]
	if m.Term != v.CurrentTerm {
		return nil
	}
	t := s.clone()
	w := t.mut(i)
	w.VotesResponded = v.VotesResponded.Add(j)
	if m.VoteGranted {
		w.VotesGranted = v.VotesGranted.Add(j)
	}
	t.discard(m)
	return t
}

// RejectAppendEntriesRequest is `RejectAppendEntriesRequest(i, j, m, logOk)`.
func (s *State) RejectAppendEntriesRequest(i, j ID, m *Msg, logOk bool) *State {
	v := s.S[i]
	if !(m.Term < v.CurrentTerm || (m.Term == v.CurrentTerm && v.State == Follower && !logOk)) {
		return nil
	}
	t := s.clone()
	t.reply(&Msg{Type: AppendEntriesResponse, Subtype: "app", Term: v.CurrentTerm, Success: false, MatchIndex: 0,
		Source: i, Dest: j}, m)
	return t
}

// ReturnToFollowerState is `ReturnToFollowerState(i, m)`.
func (s *State) ReturnToFollowerState(i ID, m *Msg) *State {
	v := s.S[i]
	if m.Term != v.CurrentTerm || v.State != Candidate {
		return nil
	}
	t := s.clone()
	t.mut(i).State = Follower
	return t
}

// HasNoConflict is `HasNoConflict(i, index, ents)`.
func (s *State) HasNoConflict(i ID, index int, ents []Entry) bool {
	log := s.S[i].Log
	if index > len(log)+1 {
		return false
	}
	for k := 1; k <= len(ents); k++ {
		if index+k-1 <= len(log) && log[index+k-2].Term != ents[k-1].Term {
			return false
		}
	}
	return true
}

// AppendEntriesAlreadyDone is `AppendEntriesAlreadyDone(i, j, index, m)`.
func (s *State) AppendEntriesAlreadyDone(i, j ID, index int, m *Msg) *State {
	v := s.S[i]
	if !(index <= v.CommitIndex ||
		(index > v.CommitIndex && (len(m.Entries) == 0 ||
			(len(m.Entries) != 0 && m.PrevLogIndex+len(m.Entries) <= len(v.Log) && s.HasNoConflict(i, index, m.Entries))))) {
		return nil
	}
	t := s.clone()
	if index <= v.CommitIndex {
		if m.Subtype == "heartbeat" {
			t.commitTo(i, m.CommitIndex)
		}
	} else {
		t.commitTo(i, min(m.CommitIndex, m.PrevLogIndex+len(m.Entries)))
	}
	matchIndex := v.CommitIndex
	if m.Subtype == "heartbeat" || index > v.CommitIndex {
		matchIndex = m.PrevLogIndex + len(m.Entries)
	}
	t.reply(&Msg{Type: AppendEntriesResponse, Subtype: m.Subtype, Term: v.CurrentTerm, Success: true,
		MatchIndex: matchIndex, Source: i, Dest: j}, m)
	return t
}

// ConflictAppendEntriesRequest is `ConflictAppendEntriesRequest(i, index, m)`.
func (s *State) ConflictAppendEntriesRequest(i ID, index int, m *Msg) *State {
	v := s.S[i]
	if !(len(m.Entries) != 0 && index > v.CommitIndex && !s.HasNoConflict(i, index, m.Entries)) {
		return nil
	}
	t := s.clone()
	w := t.mut(i)
	w.Log = SubSeq(v.Log, 1, len(v.Log)-1)
	return t
}

// NoConflictAppendEntriesRequest is `NoConflictAppendEntriesRequest(i, index, m)`.
func (s *State) NoConflictAppendEntriesRequest(i ID, index int, m *Msg) *State {
	v := s.S[i]
	if !(len(m.Entries) != 0 && index > v.CommitIndex && s.HasNoConflict(i, index, m.Entries)) {
		return nil
	}
	t := s.clone()
	w := t.mut(i)
	suffix := SubSeq(m.Entries, len(v.Log)-index+2, len(m.Entries))
	w.Log = append(v.Log[:len(v.Log):len(v.Log)], suffix...)
	return t
}

// AcceptAppendEntriesRequest is `AcceptAppendEntriesRequest(i, j, logOk, m)`.
func (s *State) AcceptAppendEntriesRequest(i, j ID, logOk bool, m *Msg) []*State {
	v := s.S[i]
	if m.Term != v.CurrentTerm || v.State != Follower || !logOk {
		return nil
	}
	index := m.PrevLogIndex + 1
	return nonNil(s.AppendEntriesAlreadyDone(i, j, index, m), s.ConflictAppendEntriesRequest(i, index, m),
		s.NoConflictAppendEntriesRequest(i, index, m))
}

// HandleAppendEntriesRequest is `HandleAppendEntriesRequest(i, j, m)`.
func (s *State) HandleAppendEntriesRequest(i, j ID, m *Msg) []*State {
	v := s.S[i]
	logOk := m.PrevLogIndex == 0 ||
		(m.PrevLogIndex > 0 && m.PrevLogIndex <= len(v.Log) && m.PrevLogTerm == v.Log[m.PrevLogIndex-1].Term)
	if !(m.Term <= v.CurrentTerm) {
		return nil
	}
	return append(nonNil(s.RejectAppendEntriesRequest(i, j, m, logOk), s.ReturnToFollowerState(i, m)),
		s.AcceptAppendEntriesRequest(i, j, logOk, m)...)
}

// HandleAppendEntriesResponse is `HandleAppendEntriesResponse(i, j, m)`.
func (s *State) HandleAppendEntriesResponse(i, j ID, m *Msg) *State {
	v := s.S[i]
	if m.Term != v.CurrentTerm {
		return nil
	}
	t := s.clone()
	if m.Success {
		w := t.mut(i)
		w.MatchIndex[j] = max(v.MatchIndex[j], m.MatchIndex)
	}
	t.discard(m)
	return t
}

// UpdateTerm is `UpdateTerm(i, j, m)`.
func (s *State) UpdateTerm(i, j ID, m *Msg) *State {
	if !(m.Term > s.S[i].CurrentTerm) {
		return nil
	}
	t := s.clone()
	t.becomeFollowerOfTerm(i, m.Term)
	return t
}

// DropStaleResponse is `DropStaleResponse(i, j, m)`.
func (s *State) DropStaleResponse(i, j ID, m *Msg) *State {
	if !(m.Term < s.S[i].CurrentTerm) {
		return nil
	}
	t := s.clone()
	t.discard(m)
	return t
}

// Receive is `Receive(m) == ReceiveDirect(m)`: every successor. m is in DOMAIN messages (the
// callers' `\E m \in DOMAIN messages`); its destination must be a server.
func (s *State) Receive(m *Msg) []*State {
	i, j := m.Dest, m.Source
	if _, ok := s.S[i]; !ok {
		return nil
	}
	out := nonNil(s.UpdateTerm(i, j, m))
	switch m.Type {
	case RequestVoteRequest:
		out = append(out, nonNil(s.HandleRequestVoteRequest(i, j, m))...)
	case RequestVoteResponse:
		out = append(out, nonNil(s.DropStaleResponse(i, j, m), s.HandleRequestVoteResponse(i, j, m))...)
	case AppendEntriesRequest:
		out = append(out, s.HandleAppendEntriesRequest(i, j, m)...)
	case AppendEntriesResponse:
		out = append(out, nonNil(s.DropStaleResponse(i, j, m), s.HandleAppendEntriesResponse(i, j, m))...)
	}
	return out
}

// DuplicateMessage is `DuplicateMessage(m)`.
func (s *State) DuplicateMessage(m *Msg) *State {
	if s.Messages.Count(m) == 0 {
		return nil
	}
	t := s.clone()
	t.Messages = s.Messages.With(m)
	return t
}

// DropMessage is `DropMessage(m)`.
func (s *State) DropMessage(m *Msg) *State {
	t := s.clone()
	t.discard(m)
	return t
}

func nonNil(ss ...*State) []*State {
	var out []*State
	for _, s := range ss {
		if s != nil {
			out = append(out, s)
		}
	}
	return out
}

// ---------------------------------------------------------------------------------------------
// The next-state relations: every successor of s (with repetitions).

// NextAsync is `NextAsync`.
func (s *State) NextAsync() []*State {
	var out []*State
	for _, i := range s.Server {
		for _, j := range s.Server {
			out = append(out, nonNil(s.RequestVote(i, j))...)
		}
	}
	for _, i := range s.Server {
		out = append(out, nonNil(s.BecomeLeader(i), s.ClientRequest(i, 0), s.AdvanceCommitIndex(i))...)
	}
	for _, i := range s.Server {
		for _, j := range s.Server {
			lo, hi := s.S[i].MatchIndex[j]+1, len(s.S[i].Log)+1
			for b := lo; b <= hi; b++ {
				for e := lo; e <= hi; e++ {
					out = append(out, nonNil(s.AppendEntries(i, j, b, e))...)
				}
			}
		}
	}
	for _, i := range s.Server {
		out = append(out, nonNil(s.AppendEntriesToSelf(i))...)
	}
	for _, i := range s.Server {
		for _, j := range s.Server {
			out = append(out, nonNil(s.Heartbeat(i, j))...)
			for index := 1; index <= s.S[i].CommitIndex; index++ {
				out = append(out, nonNil(s.SendSnapshot(i, j, index))...)
			}
		}
	}
	for _, m := range s.Messages.Domain() {
		out = append(out, s.Receive(m)...)
	}
	for _, i := range s.Server {
		out = append(out, nonNil(s.Timeout(i), s.Ready(i), s.StepDownToFollower(i))...)
	}
	return out
}

// NextCrash is `NextCrash`.
func (s *State) NextCrash() []*State {
	var out []*State
	for _, i := range s.Server {
		out = append(out, s.Restart(i))
	}
	return out
}

// NextUnreliable is `NextUnreliable`.
func (s *State) NextUnreliable() []*State {
	var out []*State
	for _, m := range s.Messages.Domain() {
		if s.Messages.Count(m) == 1 {
			out = append(out, nonNil(s.DuplicateMessage(m), s.DropMessage(m))...)
		}
	}
	return out
}

// Next is `Next`.
func (s *State) Next() []*State {
	return append(append(s.NextAsync(), s.NextCrash()...), s.NextUnreliable()...)
}

// NextDynamic is `NextDynamic`.
func (s *State) NextDynamic() []*State {
	out := s.Next()
	for _, i := range s.Server {
		for _, j := range s.Server {
			out = append(out, nonNil(s.AddNewServer(i, j), s.AddLearner(i, j), s.DeleteServer(i, j))...)
		}
	}
	for _, i := range s.Server {
		out = append(out, nonNil(s.ApplySimpleConfChange(i))...)
	}
	return out
}
