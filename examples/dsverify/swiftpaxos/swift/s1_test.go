package swift

import "testing"

// S1: a follower must adopt the leader's dependencies before the leader's
// fast ack completes a quorum; otherwise it commits and executes the command
// with its own dependencies.
//
// Five replicas, ballot 0 (leader 0, fast quorum {0, 1, 2}, slow quorum 3);
// the test is replica 1. Replica 1 got c's proposal before d's (c's own
// dependencies: none); the leader got d first and ordered c after d. Replica 1
// has accepted d (the leader's fast ack), not committed it. The slow acks of
// replicas 2 and 3 for c reach replica 1 before the leader's fast ack
// (other connections). With the leader's fast ack, the slow quorum {0, 2, 3}
// is complete: c commits with the leader's dependencies {d} and must not
// execute before d, which replica 1 has not executed.
func TestIssueS1_AdoptLeaderDepsBeforeCommit(t *testing.T) {
	seqDescs(t)
	r := newTestReplica(t, 5, 1, 0, false)
	c, d := cid(1, 0), cid(2, 0)

	propose(r, put(c, 7, "c"))
	propose(r, put(d, 7, "d"))
	r.getCmdDescSeq(d, &MFastAck{Replica: 0, Ballot: 0, CmdId: d, Dep: []CommandId{},
		Checksum: []SHash{{}}}, nil, nil, false)
	r.getCmdDesc(c, &MLightSlowAck{Replica: 2, Ballot: 0, CmdId: c}, nil)
	r.getCmdDesc(c, &MLightSlowAck{Replica: 3, Ballot: 0, CmdId: c}, nil)
	r.getCmdDescSeq(c, &MFastAck{Replica: 0, Ballot: 0, CmdId: c, Dep: []CommandId{d},
		Checksum: []SHash{{}}}, nil, nil, false)

	if r.delivered.Has(c.String()) {
		t.Fatalf("c executed before its dependency d (committed with the follower's own dependencies)")
	}
	desc := r.getCmdDesc(c, nil, nil)
	if desc == nil || desc.phase != COMMIT || !desc.dep.Equals(Dep{d}) {
		t.Fatalf("c should be committed with the leader's dependencies {d}: %+v", desc)
	}
}
