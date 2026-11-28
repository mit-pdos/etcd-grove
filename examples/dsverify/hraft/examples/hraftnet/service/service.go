// Package service is a hraft kit server's state machine, one register (dsverify-lab hr3's store),
// and its API service: what the kit's clients and its orchestrator's admin ask of a server, over
// net/rpc (examples/hraftnet).
package service

import (
	"io"
	"strconv"
	"sync"
	"time"

	"github.com/hashicorp/raft"
	"github.com/hashicorp/raft/examples/snapstore"
)

// --- the state machine

// A command is its kind (CmdPut or CmdGet), the 8-byte id of the operation that made it (unique
// per client and operation: opID), then, for a put, the value. A command too short to hold its
// id is a get (the FSM never fails on a command).
const (
	CmdPut byte   = 'P'
	CmdGet byte   = 'G'
	CmdHdr uint64 = 9
)

// result is the FSM's answer to a command: the register's value (found: it has one) after a
// get; nothing after a put.
type result struct {
	found bool
	value string
}

// Store is a server's FSM: the register, and the index of the last command applied (or of the
// restored snapshot's).
type Store struct {
	mu      sync.Mutex
	index   uint64
	present bool
	value   string
}

// NewStore is an empty register.
func NewStore() *Store {
	return &Store{}
}

// encodeState is the store's state as a string: "0" with no value, else "1" and the value.
func encodeState(present bool, value string) string {
	if !present {
		return "0"
	}
	return "1" + value
}

func (s *Store) Apply(l *raft.Log) interface{} {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.index = l.Index
	if uint64(len(l.Data)) >= CmdHdr && l.Data[0] == CmdPut {
		s.present = true
		s.value = string(l.Data[CmdHdr:])
		return result{}
	}
	return result{found: s.present, value: s.value}
}

// StoreConfiguration makes the store a raft.ConfigurationStore: raft hands it every committed
// configuration entry, in index order with the commands. The register ignores them.
func (s *Store) StoreConfiguration(index uint64, c raft.Configuration) {}

// read is the register's value now (a read of the FSM's state outside the log).
func (s *Store) read() result {
	s.mu.Lock()
	defer s.mu.Unlock()
	return result{found: s.present, value: s.value}
}

// snapshot is the store's state at a point (raft calls Persist later, on another goroutine).
type snapshot struct {
	index   uint64
	present bool
	value   string
}

// Persist writes the index of the last command applied, "|", and the encoded state.
func (sn *snapshot) Persist(sink raft.SnapshotSink) error {
	b := []byte(strconv.Itoa(int(sn.index)) + "|" + encodeState(sn.present, sn.value))
	if _, err := sink.Write(b); err != nil {
		_ = sink.Cancel()
		return err
	}
	return sink.Close()
}

func (sn *snapshot) Release() {}

func (s *Store) Snapshot() (raft.FSMSnapshot, error) {
	s.mu.Lock()
	defer s.mu.Unlock()
	return &snapshot{index: s.index, present: s.present, value: s.value}, nil
}

// Restore makes the store's state the snapshot's. Raft hands it only snapshots Persist wrote: it
// panics on any other.
func (s *Store) Restore(r io.ReadCloser) error {
	b, err := snapstore.ReadAll(r)
	_ = r.Close()
	if err != nil {
		return err
	}
	k := 0
	for k < len(b) && b[k] != '|' {
		k++
	}
	if k == 0 || k+1 >= len(b) {
		panic("restore: a malformed snapshot")
	}
	index, err := strconv.Atoi(string(b[:k]))
	if err != nil || index < 0 {
		panic("restore: a malformed snapshot")
	}
	st := string(b[k+1:])
	s.mu.Lock()
	defer s.mu.Unlock()
	s.index = uint64(index)
	s.present = st[0] == '1'
	s.value = st[1:]
	return nil
}

// --- the API service: what clients and the orchestrator's admin ask of a server

// Apply's statuses.
const (
	StatusDone     uint64 = 1 // committed and applied: Found and V are the FSM's answer
	StatusNoEffect uint64 = 2 // not appended to any log
	StatusUnknown  uint64 = 3 // appended, perhaps committed; or no outcome in time
)

// ApplyArgs is a command for the log.
type ApplyArgs struct {
	Data []byte
}

// ApplyReply is a command's outcome.
type ApplyReply struct {
	Status uint64
	Found  bool
	V      string
}

// Read's ways (ReadArgs.Way).
const (
	WayBarrier uint64 = 1 // after a Barrier
	WayVerify  uint64 = 2 // with VerifyLeader, after a barrier of the server's current term
)

// ReadArgs asks for a read of the FSM outside the log, in one of the ways.
type ReadArgs struct {
	Way uint64
}

// ReadReply is a read's answer (Ok: the read took place).
type ReadReply struct {
	Ok    bool
	Found bool
	V     string
}

// AdminArgs names a server by its raft ID and address (for LeadershipTransfer, an empty ID: the
// server raft picks).
type AdminArgs struct {
	ID   string
	Addr string
}

// AdminReply says whether the request succeeded.
type AdminReply struct {
	Ok bool
}

// API is a server's API service (registered as "API").
type API struct {
	r       *raft.Raft
	fsm     *Store
	enqueue time.Duration // the timeout of raft's calls that take one
	wait    time.Duration // the most a request waits for a raft future

	mu        sync.Mutex
	barrierIn uint64 // a term in which a Barrier of this server returned without error (0: none yet)
}

// New is the API of raft r over the state machine fsm: raft's calls that take a timeout get
// enqueue, and a request waits for a raft future at most wait.
func New(r *raft.Raft, fsm *Store, enqueue time.Duration, wait time.Duration) *API {
	return &API{r: r, fsm: fsm, enqueue: enqueue, wait: wait}
}

// waitFuture is f's error, and false if it does not come within d.
func waitFuture(f raft.Future, d time.Duration) (error, bool) {
	errCh := make(chan error, 1)
	go func() {
		errCh <- f.Error()
	}()
	select {
	case err := <-errCh:
		return err, true
	case <-time.After(d):
		return nil, false
	}
}

// Apply appends a command to the log and waits for its outcome.
func (a *API) Apply(args *ApplyArgs, reply *ApplyReply) error {
	f := a.r.Apply(args.Data, a.enqueue)
	err, ok := waitFuture(f, a.wait)
	if !ok {
		reply.Status = StatusUnknown
		return nil
	}
	if err == raft.ErrNotLeader || err == raft.ErrEnqueueTimeout || err == raft.ErrLeadershipTransferInProgress {
		reply.Status = StatusNoEffect
		return nil
	}
	if err != nil {
		reply.Status = StatusUnknown
		return nil
	}
	res := f.Response().(result)
	reply.Status = StatusDone
	reply.Found = res.found
	reply.V = res.value
	return nil
}

// Read reads the FSM's state outside the log, in one of two ways; Ok when it did. WayBarrier:
// a Barrier returns once every entry before it is applied here, and it commits only while this
// server leads with a quorum in its term. WayVerify (Consul's consistent reads): the FSM must
// already have applied a barrier of the server's current term, and VerifyLeader confirms, after
// the read began, that a quorum still follows this server in that term; a term change in between
// makes the read fail. A read that fails has no effect.
func (a *API) Read(args *ReadArgs, reply *ReadReply) error {
	r := a.r
	if args.Way == WayBarrier {
		if err, ok := waitFuture(r.Barrier(a.enqueue), a.wait); !ok || err != nil {
			return nil
		}
	} else {
		term := r.CurrentTerm()
		a.mu.Lock()
		have := a.barrierIn == term
		a.mu.Unlock()
		if !have {
			if err, ok := waitFuture(r.Barrier(a.enqueue), a.wait); !ok || err != nil {
				return nil
			}
			if r.CurrentTerm() != term {
				return nil
			}
			a.mu.Lock()
			a.barrierIn = term
			a.mu.Unlock()
		}
		if err, ok := waitFuture(r.VerifyLeader(), a.wait); !ok || err != nil {
			return nil
		}
		if r.CurrentTerm() != term {
			return nil
		}
	}
	res := a.fsm.read()
	reply.Ok = true
	reply.Found = res.found
	reply.V = res.value
	return nil
}

// done says whether f succeeded in time.
func (a *API) done(f raft.Future) bool {
	err, ok := waitFuture(f, a.wait)
	return ok && err == nil
}

func (a *API) AddVoter(args *AdminArgs, reply *AdminReply) error {
	reply.Ok = a.done(a.r.AddVoter(raft.ServerID(args.ID), raft.ServerAddress(args.Addr), 0, a.enqueue))
	return nil
}

func (a *API) AddNonvoter(args *AdminArgs, reply *AdminReply) error {
	reply.Ok = a.done(a.r.AddNonvoter(raft.ServerID(args.ID), raft.ServerAddress(args.Addr), 0, a.enqueue))
	return nil
}

func (a *API) DemoteVoter(args *AdminArgs, reply *AdminReply) error {
	reply.Ok = a.done(a.r.DemoteVoter(raft.ServerID(args.ID), 0, a.enqueue))
	return nil
}

func (a *API) RemoveServer(args *AdminArgs, reply *AdminReply) error {
	reply.Ok = a.done(a.r.RemoveServer(raft.ServerID(args.ID), 0, a.enqueue))
	return nil
}

// LeadershipTransfer asks this server to hand its leadership to the server args names (an empty
// ID: to the server raft picks).
func (a *API) LeadershipTransfer(args *AdminArgs, reply *AdminReply) error {
	if args.ID == "" {
		reply.Ok = a.done(a.r.LeadershipTransfer())
	} else {
		reply.Ok = a.done(a.r.LeadershipTransferToServer(raft.ServerID(args.ID), raft.ServerAddress(args.Addr)))
	}
	return nil
}

// StatusReply is what a server knows of the cluster: whether it leads (State), the leader it
// knows of (LeaderWithID: an empty ID if none), and how many servers and voters its latest
// configuration has (GetConfiguration; Configured: it answered in time).
type StatusReply struct {
	Leader     bool
	LeaderID   string
	Configured bool
	Servers    uint64
	Voters     uint64
}

// Status answers what this server knows of the cluster (args is not read). LeaderWithID runs on a
// goroutine of its own, which the method waits for (the same behavior: the fresh goroutine is what
// gives its read lock a thread in the proof, since net/rpc's method goroutine lends none; as
// rpctransport's deliver).
func (a *API) Status(args *AdminArgs, reply *StatusReply) error {
	reply.Leader = a.r.State() == raft.Leader
	idCh := make(chan raft.ServerID, 1)
	go func() {
		_, id := a.r.LeaderWithID()
		idCh <- id
	}()
	reply.LeaderID = string(<-idCh)
	f := a.r.GetConfiguration()
	if err, ok := waitFuture(f, a.wait); ok && err == nil {
		reply.Configured = true
		for _, srv := range f.Configuration().Servers {
			reply.Servers++
			if srv.Suffrage == raft.Voter {
				reply.Voters++
			}
		}
	}
	return nil
}

// Snapshot asks this server to take a snapshot now (it compacts its log).
func (a *API) Snapshot(args *AdminArgs, reply *AdminReply) error {
	reply.Ok = a.done(a.r.Snapshot())
	return nil
}
