package raft

import (
	"errors"
	"fmt"
	"io"
	"testing"
	"time"
)

// The two fmt.Errorf sites rewritten to format explicitly (notes/dsv-hraft.md, deviations):
// their messages name the same values as before.

func TestCheckConfigurationMessage(t *testing.T) {
	c := Configuration{Servers: []Server{{Voter, "a", "x"}, {Nonvoter, "", "y"}, {ServerSuffrage(7), "c", "z"}}}
	if err := checkConfiguration(c); err.Error() != fmt.Sprintf("empty ID in configuration: %v", c) {
		t.Fatal(err)
	}
	c.Servers[1].ID = "b"
	c.Servers[1].Address = ""
	if err := checkConfiguration(c); err.Error() != fmt.Sprintf("empty address in configuration: %v", c.Servers[1]) {
		t.Fatal(err)
	}
	c = Configuration{Servers: []Server{{Nonvoter, "a", "x"}, {Staging, "b", "y"}}}
	if err := checkConfiguration(c); err.Error() != fmt.Sprintf("need at least one voter in configuration: %v", c) {
		t.Fatal(err)
	}
}

// stubTransport: a transport for a single-server cluster, which sends nothing.
type stubTransport struct{ ch chan RPC }

var errStub = errors.New("stub transport")

func (s *stubTransport) Consumer() <-chan RPC     { return s.ch }
func (s *stubTransport) LocalAddr() ServerAddress { return "addr1" }
func (s *stubTransport) AppendEntriesPipeline(ServerID, ServerAddress) (AppendPipeline, error) {
	return nil, errStub
}
func (s *stubTransport) AppendEntries(ServerID, ServerAddress, *AppendEntriesRequest, *AppendEntriesResponse) error {
	return errStub
}
func (s *stubTransport) RequestVote(ServerID, ServerAddress, *RequestVoteRequest, *RequestVoteResponse) error {
	return errStub
}
func (s *stubTransport) InstallSnapshot(ServerID, ServerAddress, *InstallSnapshotRequest, *InstallSnapshotResponse, io.Reader) error {
	return errStub
}
func (s *stubTransport) EncodePeer(id ServerID, addr ServerAddress) []byte { return []byte(addr) }
func (s *stubTransport) DecodePeer(b []byte) ServerAddress                 { return ServerAddress(b) }
func (s *stubTransport) SetHeartbeatHandler(func(RPC))                     {}
func (s *stubTransport) TimeoutNow(ServerID, ServerAddress, *TimeoutNowRequest, *TimeoutNowResponse) error {
	return errStub
}

type nopFSM struct{}

func (nopFSM) Apply(*Log) interface{}         { return nil }
func (nopFSM) Snapshot() (FSMSnapshot, error) { return nil, errStub }
func (nopFSM) Restore(r io.ReadCloser) error  { return r.Close() }

// leaderLoop's "cannot find replication state" names the server's ID (before: the pointer to it,
// which %v printed as an address).
func TestLeaderLoopTransferMessage(t *testing.T) {
	conf := DefaultConfig()
	conf.LocalID = "id1"
	logs, snaps, trans := NewInmemStore(), NewInmemSnapshotStore(), &stubTransport{ch: make(chan RPC)}
	boot := Configuration{Servers: []Server{{Voter, "id1", "addr1"}}}
	if err := BootstrapCluster(conf, logs, logs, snaps, trans, boot); err != nil {
		t.Fatal(err)
	}
	r, err := NewRaft(conf, nopFSM{}, logs, logs, snaps, trans)
	if err != nil {
		t.Fatal(err)
	}
	defer r.Shutdown()
	for r.State() != Leader {
		time.Sleep(10 * time.Millisecond)
	}
	if err := r.LeadershipTransferToServer("nosuch", "addr9").Error(); err == nil || err.Error() != "cannot find replication state for nosuch" {
		t.Fatal(err)
	}
}
