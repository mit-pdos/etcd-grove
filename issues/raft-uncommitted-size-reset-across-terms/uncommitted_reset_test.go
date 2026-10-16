// Reproduction for issues/raft-uncommitted-size-reset-across-terms.md (etcd-io/raft#11).
//
// Drop this file into the root package (go.etcd.io/raft/v3) of the raft fork
// upamanyus/etcd, branch raft37-goose-lean, at commit 509271dac (raft v3.7.0 plus
// the fork's fix), and run
//
//	go test -run TestUncommittedTailUnboundedAcrossTerms .
//
// It uses the package's own test helpers (newNetworkWithConfig, network.ignore).
// The test asserts the bound MaxUncommittedEntriesSize is meant to give (the
// uncommitted tail at a leader is at most the limit plus one proposal) and FAILS at
// the pin: each time node 1 regains leadership, reset() zeroes uncommittedSize while
// the entries it appended in earlier terms are still uncommitted in its log.
package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

func TestUncommittedTailUnboundedAcrossTerms(t *testing.T) {
	testEntry := &pb.Entry{Data: []byte("testdata")}
	const perTerm = 16
	limit := uint64(perTerm * payloadSize(testEntry))

	nt := newNetworkWithConfig(func(c *Config) {
		c.MaxUncommittedEntriesSize = limit
		c.MaxInflightMsgs = 1024
	}, nil, nil, nil)
	// No replication: nothing proposed is ever committed (a leader without a quorum
	// of followers that keep up, as in an unstable cluster).
	nt.ignore(pb.MsgApp)

	hup := func(id uint64) {
		nt.send(&pb.Message{From: new(id), To: new(id), Type: pb.MsgHup.Enum()})
	}
	n1 := nt.peers[1].(*raft)
	n2 := nt.peers[2].(*raft)

	const rounds = 5
	for round := 0; round < rounds; round++ {
		hup(1)
		if n1.state != StateLeader {
			t.Fatalf("round %d: node 1 is %v, want leader", round, n1.state)
		}
		// Propose until the leader drops a proposal.
		for i := 0; ; i++ {
			err := n1.Step(&pb.Message{From: new(uint64(1)), To: new(uint64(1)),
				Type: pb.MsgProp.Enum(), Entries: []*pb.Entry{testEntry}})
			if err == ErrProposalDropped {
				break
			}
			if err != nil {
				t.Fatal(err)
			}
			if i > 10*perTerm {
				t.Fatalf("round %d: no proposal dropped", round)
			}
		}
		n1.readMessages()

		tail, err := n1.raftLog.entries(n1.raftLog.committed+1, noLimit)
		if err != nil {
			t.Fatal(err)
		}
		size := uint64(payloadsSize(tail))
		t.Logf("round %d: term %d, uncommitted tail %d bytes (limit %d), uncommittedSize %d",
			round, n1.Term, size, limit, n1.uncommittedSize)
		if size > limit+uint64(payloadSize(testEntry)) {
			t.Errorf("round %d: leader's uncommitted tail is %d bytes, above MaxUncommittedEntriesSize %d",
				round, size, limit)
		}

		// Node 2 takes over (node 3 votes for it), and node 1 is a follower again;
		// node 1's uncommitted entries stay in its log (node 2's MsgApp are dropped).
		hup(2)
		if n2.state != StateLeader {
			t.Fatalf("round %d: node 2 is %v, want leader", round, n2.state)
		}
	}
}
