package kv

import (
	"sync"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
)

// WitnessStore is the witness's durable state, held in process for the cluster: the state
// and a version, under a lock. A replica's raft.Witness reads it (GetWitnessState) and
// updates it by compare-and-swap: an update takes only if no other took since the read
// (raft's WitnessStorage contract; etcd-io/raft#133). States are copied in and out, so no
// two holders share one.
type WitnessStore struct {
	mu      sync.Mutex
	version uint64
	state   *pb.WitnessHardState
}

// witnessRead is one read of the store: the version it saw and the state then.
type witnessRead struct {
	s       *WitnessStore
	version uint64
	state   *pb.WitnessHardState
}

// NewWitnessStore is a witness that has seen nothing: term 0, no vote, no entry.
func NewWitnessStore() *WitnessStore {
	return &WitnessStore{state: &pb.WitnessHardState{State: &pb.HardState{}}}
}

// copyIDs is a fresh slice with ids' elements.
func copyIDs(ids []uint64) []uint64 {
	c := make([]uint64, len(ids))
	copy(c, ids)
	return c
}

// copyState is a fresh WitnessHardState with st's fields.
func copyState(st *pb.WitnessHardState) *pb.WitnessHardState {
	return &pb.WitnessHardState{
		State: &pb.HardState{
			Term:   new(st.GetState().GetTerm()),
			Vote:   new(st.GetState().GetVote()),
			Commit: new(st.GetState().GetCommit()),
		},
		LastLogIndex:           new(st.GetLastLogIndex()),
		LastLogTerm:            new(st.GetLastLogTerm()),
		LastLogSubterm:         new(st.GetLastLogSubterm()),
		Lead:                   new(st.GetLead()),
		ReplicationSet:         copyIDs(st.GetReplicationSet()),
		ReplicationSetOutgoing: copyIDs(st.GetReplicationSetOutgoing()),
	}
}

// GetWitnessState reads the store.
func (s *WitnessStore) GetWitnessState() (raft.WitnessState, error) {
	s.mu.Lock()
	r := &witnessRead{s: s, version: s.version, state: copyState(s.state)}
	s.mu.Unlock()
	return r, nil
}

// Close does nothing: the store lives as long as the cluster.
func (s *WitnessStore) Close() {}

// GetState is the state the read saw.
func (r *witnessRead) GetState() *pb.WitnessHardState {
	return r.state
}

// Update stores st if the store is still at the version the read saw, and says
// raft.ErrWitnessStateModified otherwise.
func (r *witnessRead) Update(st *pb.WitnessHardState) error {
	s := r.s
	s.mu.Lock()
	if s.version != r.version {
		s.mu.Unlock()
		return raft.ErrWitnessStateModified
	}
	s.state = copyState(st)
	s.version++
	s.mu.Unlock()
	return nil
}

// StartClusterWitness starts a cluster of the regular voters and the witness: a replica on a
// raft node of each regular voter, as StartCluster does, each with its own raft.Witness on
// one shared WitnessStore. Check-quorum is on: it is what makes a leader replace an
// unresponsive voter by the witness in its replication set. It returns the replicas, in the
// order of voters.
func StartClusterWitness(voters []uint64, witness uint64) []*KV {
	members := append(copyIDs(voters), witness)
	peers := make(map[uint64]raft.Node)
	storages := make(map[uint64]*Storage)
	for _, id := range voters {
		st := &Storage{MemoryStorage: raft.NewMemoryStorage(), voters: members, witness: witness}
		peers[id] = raft.RestartNode(&raft.Config{
			ID:                id,
			ElectionTick:      10,
			HeartbeatTick:     1,
			Storage:           st,
			MaxSizePerMsg:     1 << 20,
			MaxInflightMsgs:   256,
			Logger:            quietLogger{},
			CheckQuorum:       true,
			StepDownOnRemoval: true,
		})
		storages[id] = st
	}
	tr := &transfers{left: timeouts}
	send := func(ms []*pb.Message) {
		deliver(peers, tr, ms)
	}
	ws := NewWitnessStore()
	var kvs []*KV
	for _, id := range voters {
		w := raft.NewWitness(raft.WitnessConfig{ID: witness, Storage: ws, CheckQuorum: true})
		kvs = append(kvs, newKV(id, peers[id], storages[id], send, w))
		go tick(peers[id])
	}
	return kvs
}
