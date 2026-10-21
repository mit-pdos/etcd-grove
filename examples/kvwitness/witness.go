package kv

import (
	"sync"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
)

// WitnessStore is the witness's durable state, held in process for the cluster, under a lock.
// A replica's raft.Witness reads it (GetWitnessState) and updates it by compare-and-swap: an
// update takes only if the stored state is still the one read (raft's WitnessStorage contract;
// etcd-io/raft#133). A state, once stored, is never changed (an update stores a new one, which
// the witness no longer writes once it has handed it over): so a read hands out the stored
// state itself, and an update compares the state stored with the one read by identity.
type WitnessStore struct {
	mu    sync.Mutex
	state *pb.WitnessHardState
}

// witnessRead is one read of the store: the state stored then.
type witnessRead struct {
	s     *WitnessStore
	state *pb.WitnessHardState
}

// NewWitnessStore is a witness that has seen nothing: term 0, no vote, no entry.
func NewWitnessStore() *WitnessStore {
	return &WitnessStore{state: &pb.WitnessHardState{State: &pb.HardState{}}}
}

// GetWitnessState reads the store.
func (s *WitnessStore) GetWitnessState() (raft.WitnessState, error) {
	s.mu.Lock()
	r := &witnessRead{s: s, state: s.state}
	s.mu.Unlock()
	return r, nil
}

// Close does nothing: the store lives as long as the cluster.
func (s *WitnessStore) Close() {}

// GetState is the state the read saw.
func (r *witnessRead) GetState() *pb.WitnessHardState {
	return r.state
}

// Update stores st if the store still holds the state the read saw, and says
// raft.ErrWitnessStateModified otherwise.
func (r *witnessRead) Update(st *pb.WitnessHardState) error {
	s := r.s
	s.mu.Lock()
	if s.state != r.state {
		s.mu.Unlock()
		return raft.ErrWitnessStateModified
	}
	s.state = st
	s.mu.Unlock()
	return nil
}

// copyIDs is a fresh slice with ids' elements.
func copyIDs(ids []uint64) []uint64 {
	c := make([]uint64, len(ids))
	copy(c, ids)
	return c
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
