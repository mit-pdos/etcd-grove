package raft

import (
	"errors"

	"go.etcd.io/raft/v3/raftpb"
)

var ErrWitnessStateModified = errors.New("witness state was modified")

type WitnessStorage interface {
	GetWitnessState() (WitnessState, error)
	Close()
}

type WitnessState interface {
	GetState() *raftpb.WitnessHardState
	Update(st *raftpb.WitnessHardState) error
}

type WitnessConfig struct {
	ID          uint64
	Storage     WitnessStorage
	CheckQuorum bool
	PreVote     bool
}

type Witness interface {
	Process(m WitnessMessage) (*raftpb.Message, error)
	Close()
}

type witness struct {
	id          uint64
	storage     WitnessStorage
	preVote     bool
	checkQuorum bool
	state       *raftpb.WitnessHardState
	lastError   error
}

func NewWitness(cfg WitnessConfig) Witness {
	return &witness{
		id:          cfg.ID,
		storage:     cfg.Storage,
		preVote:     cfg.PreVote,
		checkQuorum: cfg.CheckQuorum,
	}
}

func (w *witness) Close() {
	w.storage.Close()
}

func (w *witness) Process(m WitnessMessage) (*raftpb.Message, error) {
	switch m.Type {
	case raftpb.MsgApp, raftpb.MsgVote, raftpb.MsgPreVote, raftpb.MsgHeartbeat:
	default:
		return nil, nil
	}

	resp, handled := w.processNoUpdate(m)
	if handled {
		return resp, nil
	}

	for {
		state, err := w.storage.GetWitnessState()
		w.lastError = err
		if err != nil {
			return nil, err
		}
		w.state = state.GetState()

		resp, handled = w.processNoUpdate(m)
		if handled {
			return resp, nil
		}

		st := w.cloneState()
		if m.Term > st.GetState().GetTerm() {
			w.processMessageWithNewerTerm(m, st)
		}
		switch m.Type {
		case raftpb.MsgHeartbeat:
			resp = w.handleHeartbeat(m)
		case raftpb.MsgApp:
			resp = w.handleAppend(m, st)
		case raftpb.MsgPreVote, raftpb.MsgVote:
			resp = w.handleVote(m, st)
		default:
			return nil, nil
		}

		err = state.Update(st)
		if err != ErrWitnessStateModified {
			w.lastError = err
			if err != nil {
				return nil, err
			}
			return resp, nil
		}
	}
}

func (w *witness) isHealthy() bool {
	return w.lastError == nil
}

func (w *witness) processNoUpdate(m WitnessMessage) (*raftpb.Message, bool) {
	if !w.isHealthy() && m.Type == raftpb.MsgHeartbeat {
		return nil, true
	}

	if m.Term < w.state.GetState().GetTerm() {
		resp := w.processMessageWithOlderTerm(m)
		return resp, true
	}

	var resp *raftpb.Message
	handled := false
	if m.Term == w.state.GetState().GetTerm() {
		switch m.Type {
		case raftpb.MsgHeartbeat:
			resp = w.handleHeartbeat(m)
			handled = true
		case raftpb.MsgApp:
			resp, handled = w.handleAppendNoUpdate(m)
		}
	}

	return resp, handled
}

func (w *witness) processMessageWithOlderTerm(m WitnessMessage) *raftpb.Message {
	var resp *raftpb.Message
	if (w.checkQuorum || w.preVote) && (m.Type == raftpb.MsgHeartbeat || m.Type == raftpb.MsgApp) {
		resp = &raftpb.Message{To: new(m.From), Type: raftpb.MsgAppResp.Enum()}
	} else if m.Type == raftpb.MsgPreVote {
		resp = &raftpb.Message{To: new(m.From), Term: new(w.state.GetState().GetTerm()), Type: raftpb.MsgPreVoteResp.Enum(), Reject: new(true)}
	} else {
		resp = nil
	}

	return resp
}

func (w *witness) processMessageWithNewerTerm(m WitnessMessage, st *raftpb.WitnessHardState) {
	switch {
	case m.Type == raftpb.MsgPreVote:
	default:
		if m.Type == raftpb.MsgApp || m.Type == raftpb.MsgHeartbeat || m.Type == raftpb.MsgSnap {
			st.State.Term = new(m.Term)
			st.State.Vote = new(None)
			st.Lead = new(m.From)
		} else {
			st.State.Term = new(m.Term)
			st.State.Vote = new(None)
			st.Lead = new(None)
		}
	}
}

func (w *witness) cloneState() *raftpb.WitnessHardState {
	st := &raftpb.WitnessHardState{
		State: &raftpb.HardState{
			Term:   new(w.state.GetState().GetTerm()),
			Vote:   new(w.state.GetState().GetVote()),
			Commit: new(w.state.GetState().GetCommit()),
		},
		LastLogIndex:           new(w.state.GetLastLogIndex()),
		LastLogTerm:            new(w.state.GetLastLogTerm()),
		LastLogSubterm:         new(w.state.GetLastLogSubterm()),
		Lead:                   new(w.state.GetLead()),
		ReplicationSet:         make([]uint64, len(w.state.ReplicationSet)),
		ReplicationSetOutgoing: make([]uint64, len(w.state.ReplicationSetOutgoing)),
	}
	copy(st.ReplicationSet, w.state.ReplicationSet)
	copy(st.ReplicationSetOutgoing, w.state.ReplicationSetOutgoing)

	return st
}

func (w *witness) handleHeartbeat(m WitnessMessage) *raftpb.Message {
	return &raftpb.Message{
		Type:    raftpb.MsgHeartbeatResp.Enum(),
		Term:    new(w.state.GetState().GetTerm()),
		From:    new(w.id),
		To:      new(m.From),
		Context: m.Context,
	}
}

func (w *witness) handleAppendNoUpdate(m WitnessMessage) (*raftpb.Message, bool) {
	resp := &raftpb.Message{
		Type: raftpb.MsgAppResp.Enum(),
		To:   new(m.From),
		From: new(w.id),
		Term: new(w.state.GetState().GetTerm()),
	}

	handled := true
	if m.LastLogTerm == w.state.GetLastLogTerm() && m.LastLogSubterm == w.state.GetLastLogSubterm() {
		// leader commits upon quorum-1 acks if the replicated entry is of same subterm as witness
		resp.Index = new(m.LastLogIndex)
	} else if m.LastLogTerm < w.state.GetLastLogTerm() || (m.LastLogTerm == w.state.GetLastLogTerm() && m.LastLogSubterm < w.state.GetLastLogSubterm()) {
		// previous replicated entry
		resp.Index = new(w.state.GetLastLogIndex())
	} else {
		handled = false
	}

	return resp, handled
}

func (w *witness) handleAppend(m WitnessMessage, st *raftpb.WitnessHardState) *raftpb.Message {
	resp, handled := w.handleAppendNoUpdate(m)
	if handled {
		return resp
	}

	st.LastLogTerm = new(m.LastLogTerm)
	st.LastLogSubterm = new(m.LastLogSubterm)
	st.LastLogIndex = new(m.LastLogIndex)
	st.ReplicationSet = m.ReplicationSet[0]
	st.ReplicationSetOutgoing = m.ReplicationSet[1]

	return &raftpb.Message{
		Type:  raftpb.MsgAppResp.Enum(),
		To:    new(m.From),
		From:  new(w.id),
		Term:  new(w.state.GetState().GetTerm()),
		Index: new(st.GetLastLogIndex()),
	}
}

func (w *witness) handleVote(m WitnessMessage, st *raftpb.WitnessHardState) *raftpb.Message {
	var msgType raftpb.MessageType
	if m.Type == raftpb.MsgPreVote {
		msgType = raftpb.MsgPreVoteResp
	} else {
		msgType = raftpb.MsgVoteResp
	}
	resp := &raftpb.Message{
		Type: msgType.Enum(),
		To:   new(m.From),
		From: new(w.id),
	}

	canVote := st.GetState().GetVote() == m.From || (st.GetState().GetVote() == 0 && st.GetLead() == 0) || (m.Type == raftpb.MsgPreVote && m.Term > st.GetState().GetTerm())
	reject := true
	if canVote {
		reject = false
		if m.LastLogTerm < st.GetLastLogTerm() || (m.LastLogTerm == st.GetLastLogTerm() && m.LastLogSubterm < st.GetLastLogSubterm()) {
			reject = true
		} else if m.LastLogTerm == st.GetLastLogTerm() && m.LastLogSubterm == st.GetLastLogSubterm() {
			votesInSet := 0
			for _, x := range st.ReplicationSet {
				if _, ok := m.Votes[x]; ok {
					votesInSet++
				}
			}
			reject = votesInSet != len(m.Votes)
		}
	}

	if m.Type == raftpb.MsgVote && !reject {
		st.State.Vote = new(m.From)
	}

	resp.Reject = new(reject)

	if resp.GetReject() {
		resp.Term = new(st.GetState().GetTerm())
	} else {
		resp.Term = new(m.Term)
	}

	return resp
}
