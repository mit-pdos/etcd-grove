// Deterministic schedule: a server restarted over a snapshot whose log store is empty (after an
// InstallSnapshot discarded its log) re-processes the configuration entries of a delayed
// AppendEntries that its snapshot covers, and its latest configuration rolls back.
//
// Server F (real raft) with peers played by this test: A (leader of term 2), B, D.
//
//  1. F is bootstrapped with C1 = {F, A, B} (entry 1, term 1).
//  2. A, leader of term 2, has the log 1: C1, 2: Cx = {F, A}, 3: C2 = {F, A, B, D}, 4: command,
//     all committed, and has compacted it; it sends F its snapshot at (4, 2) with C2 (index 3). F's
//     log does not hold (4, 2), so F discards it (up to the store's own last index); F's latest
//     configuration is C2.
//  3. F restarts from its stores: the snapshot at (4, 2) and a log store whose last index is below
//     the snapshot's. NewRaft restores the snapshot (configurations: C2 at 3) but sets lastLog from
//     the log store, below 4.
//  4. A's AppendEntries sent before step 2 (prev = 0, entries 1-2, a reordered message of term 2)
//     arrives. prev = 0 is not checked; entry 2's index exceeds lastLogIdx, so F stores it again and
//     processConfigurationLogEntry re-applies it: latest := Cx at 2, older than its snapshot's C2.
//
// The test fails when F's latest configuration after step 4 is not C2 (it holds the committed C2
// in its snapshot; Cx is an older configuration that its log replaces).
package repro

import (
	"bytes"
	"errors"
	"io"
	"testing"
	"time"

	"github.com/hashicorp/raft"
)

type fsm struct{}

func (f *fsm) Apply(*raft.Log) interface{}         { return nil }
func (f *fsm) Snapshot() (raft.FSMSnapshot, error) { return nil, errors.New("no") }
func (f *fsm) Restore(r io.ReadCloser) error       { _, err := io.ReadAll(r); _ = r.Close(); return err }

type trans struct{ consumer chan raft.RPC }

func (t *trans) Consumer() <-chan raft.RPC                                { return t.consumer }
func (t *trans) LocalAddr() raft.ServerAddress                            { return "F" }
func (t *trans) SetHeartbeatHandler(cb func(raft.RPC))                    {}
func (t *trans) EncodePeer(id raft.ServerID, a raft.ServerAddress) []byte { return []byte(a) }
func (t *trans) DecodePeer(b []byte) raft.ServerAddress                   { return raft.ServerAddress(b) }
func (t *trans) AppendEntriesPipeline(raft.ServerID, raft.ServerAddress) (raft.AppendPipeline, error) {
	return nil, raft.ErrPipelineReplicationNotSupported
}
func (t *trans) AppendEntries(raft.ServerID, raft.ServerAddress, *raft.AppendEntriesRequest, *raft.AppendEntriesResponse) error {
	return errors.New("peer unreachable")
}
func (t *trans) RequestPreVote(raft.ServerID, raft.ServerAddress, *raft.RequestPreVoteRequest, *raft.RequestPreVoteResponse) error {
	return errors.New("peer unreachable")
}
func (t *trans) RequestVote(raft.ServerID, raft.ServerAddress, *raft.RequestVoteRequest, *raft.RequestVoteResponse) error {
	return errors.New("peer unreachable")
}
func (t *trans) InstallSnapshot(raft.ServerID, raft.ServerAddress, *raft.InstallSnapshotRequest, *raft.InstallSnapshotResponse, io.Reader) error {
	return errors.New("peer unreachable")
}
func (t *trans) TimeoutNow(raft.ServerID, raft.ServerAddress, *raft.TimeoutNowRequest, *raft.TimeoutNowResponse) error {
	return errors.New("peer unreachable")
}

func deliver(t *testing.T, tr *trans, cmd interface{}, data io.Reader) raft.RPCResponse {
	resp := make(chan raft.RPCResponse, 1)
	tr.consumer <- raft.RPC{Command: cmd, Reader: data, RespChan: resp}
	select {
	case r := <-resp:
		return r
	case <-time.After(5 * time.Second):
		t.Fatal("F did not respond")
	}
	return raft.RPCResponse{}
}

func servers(ids ...string) raft.Configuration {
	c := raft.Configuration{}
	for _, s := range ids {
		c.Servers = append(c.Servers, raft.Server{Suffrage: raft.Voter, ID: raft.ServerID(s), Address: raft.ServerAddress(s)})
	}
	return c
}

func latest(t *testing.T, r *raft.Raft) raft.Configuration {
	f := r.GetConfiguration()
	if err := f.Error(); err != nil {
		t.Fatal(err)
	}
	return f.Configuration()
}

func TestRestartOverSnapshotWithEmptyLogRollsBackConfiguration(t *testing.T) {
	conf := raft.DefaultConfig()
	conf.LocalID = "F"
	// F stays a follower for the whole test
	conf.HeartbeatTimeout = time.Minute
	conf.ElectionTimeout = time.Minute
	conf.LeaderLeaseTimeout = time.Minute
	logs, stable, snaps := raft.NewInmemStore(), raft.NewInmemStore(), raft.NewInmemSnapshotStore()
	c1 := servers("F", "A", "B")
	cx := servers("F", "A")
	c2 := servers("F", "A", "B", "D")
	tr := &trans{consumer: make(chan raft.RPC)}
	// 1. bootstrap with C1
	if err := raft.BootstrapCluster(conf, logs, stable, snaps, tr, c1); err != nil {
		t.Fatal(err)
	}
	r, err := raft.NewRaft(conf, &fsm{}, logs, stable, snaps, tr)
	if err != nil {
		t.Fatal(err)
	}
	// 2. A's snapshot at (4, 2), configuration C2 at 3
	hdrA := raft.RPCHeader{ProtocolVersion: raft.ProtocolVersionMax, ID: []byte("A"), Addr: []byte("A")}
	snap := []byte("state after entries 1-4")
	rr := deliver(t, tr, &raft.InstallSnapshotRequest{RPCHeader: hdrA, SnapshotVersion: raft.SnapshotVersionMax, Term: 2,
		Leader: []byte("A"), LastLogIndex: 4, LastLogTerm: 2, Configuration: raft.EncodeConfiguration(c2),
		ConfigurationIndex: 3, Size: int64(len(snap))}, bytes.NewReader(snap))
	if is, ok := rr.Response.(*raft.InstallSnapshotResponse); rr.Error != nil || !ok || !is.Success {
		t.Fatalf("F did not install A's snapshot: %v %+v", rr.Error, rr.Response)
	}
	if n := len(latest(t, r).Servers); n != 4 {
		t.Fatalf("after the install F's latest configuration has %d servers, not C2's 4", n)
	}
	if err := r.Shutdown().Error(); err != nil {
		t.Fatal(err)
	}
	if last, _ := logs.LastIndex(); last != 0 {
		t.Logf("note: F's log store's last index after the install is %d", last)
	}

	// 3. restart from the same stores
	tr2 := &trans{consumer: make(chan raft.RPC)}
	r2, err := raft.NewRaft(conf, &fsm{}, logs, stable, snaps, tr2)
	if err != nil {
		t.Fatal(err)
	}
	defer r2.Shutdown()
	if n := len(latest(t, r2).Servers); n != 4 {
		t.Fatalf("after the restart F's latest configuration has %d servers, not C2's 4", n)
	}

	// 4. A's delayed AppendEntries of term 2: prev = 0, entries 1 (C1, term 1) and 2 (Cx, term 2)
	es := []*raft.Log{
		{Index: 1, Term: 1, Type: raft.LogConfiguration, Data: raft.EncodeConfiguration(c1)},
		{Index: 2, Term: 2, Type: raft.LogConfiguration, Data: raft.EncodeConfiguration(cx)},
	}
	rr = deliver(t, tr2, &raft.AppendEntriesRequest{RPCHeader: hdrA, Term: 2, Leader: []byte("A"), PrevLogEntry: 0,
		PrevLogTerm: 0, Entries: es, LeaderCommitIndex: 2}, nil)
	ae, ok := rr.Response.(*raft.AppendEntriesResponse)
	if rr.Error != nil || !ok {
		t.Fatalf("F's response: %v %+v", rr.Error, rr.Response)
	}
	got := latest(t, r2)
	if len(got.Servers) != 4 {
		t.Fatalf("F (snapshot at (4, 2) with the committed C2 = {F, A, B, D}) took A's delayed entries 1-2 (success %v) "+
			"and rolled its latest configuration back to %v", ae.Success, got.Servers)
	}
}
