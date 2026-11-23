package swift

import "testing"

// N2 (found here; the paper's rule, fastAckFromLeader's TODO "∀ id' ∈ d.
// phase[id'] ∈ {ACCEPT, COMMIT}"): a follower accepts the leader's proposal of
// a command (adopts its dependencies, slow ack) only after it has accepted
// each dependency. Otherwise a slow quorum can choose c while the recovery
// quorum's acceptors of c do not know its dependency d (its proposal is still
// on its way): the new ballot cannot keep d before c, whose result the
// leader computed after d.
//
// Replica 1 of three, ballot 0: c's proposal and the leader's fast ack for c
// (dependencies {d}) arrive; d's proposal has not.
func TestIssueN2_AcceptAfterDependencies(t *testing.T) {
	seqDescs(t)
	r := newTestReplica(t, 3, 1, 0, false)
	c, d := cid(1, 0), cid(2, 0)
	propose(r, put(c, 7, "c"))
	r.getCmdDescSeq(c, &MFastAck{Replica: 0, Ballot: 0, CmdId: c, Dep: []CommandId{d},
		Checksum: []SHash{{}}}, nil, nil, false)
	if desc := r.getCmdDesc(c, nil, nil); desc.phase == ACCEPT || len(r.batcher.lightSlowAcks) != 0 {
		t.Fatalf("c accepted (phase %d, slow acks %d) before its dependency d",
			desc.phase, len(r.batcher.lightSlowAcks))
	}
}

// N2: the waiting ack is taken again once the dependency is accepted.
func TestIssueN2_AcceptedOnceDependencyIs(t *testing.T) {
	seqDescs(t)
	r := newTestReplica(t, 3, 1, 0, false)
	c, d := cid(1, 0), cid(2, 0)
	propose(r, put(c, 7, "c"))
	r.getCmdDescSeq(c, &MFastAck{Replica: 0, Ballot: 0, CmdId: c, Dep: []CommandId{d},
		Checksum: []SHash{{}}}, nil, nil, false)
	propose(r, put(d, 7, "d"))
	r.getCmdDescSeq(d, &MFastAck{Replica: 0, Ballot: 0, CmdId: d, Dep: []CommandId{},
		Checksum: []SHash{{}}}, nil, nil, false)
	runOnce(r) // N2-loop: the run loop's step takes the recheck
	if !r.delivered.Has(c.String()) || !r.delivered.Has(d.String()) {
		t.Fatalf("c and d should be committed and executed (N = 3: leader and replica 1)")
	}
}

// N2-nofast: when the leader's ack for c arrives before c's proposal and, at
// the proposal, waits under N2 for c's dependency (desc.waitingAck), the
// follower sends no fast ack for c (c takes the slow path, as when Recall sets
// desc.slowPath); it accepts, and the run loop's recheck commits, once the
// dependency is accepted.
func TestN2NoFast_NoFastAckWhileLeaderAckWaits(t *testing.T) {
	seqDescs(t)
	r := newTestReplica(t, 3, 1, 0, false)
	c, d := cid(1, 0), cid(2, 0)
	r.getCmdDescSeq(c, &MFastAck{Replica: 0, Ballot: 0, CmdId: c, Dep: []CommandId{d},
		Checksum: []SHash{{}}}, nil, nil, false)
	propose(r, put(c, 7, "c"))
	if desc := r.getCmdDesc(c, nil, nil); desc.waitingAck == nil {
		t.Fatalf("the leader's ack for c should wait for d")
	}
	if n := len(r.batcher.fastAcks); n != 0 {
		t.Fatalf("a fast ack for c was sent (%d) while the leader's ack waits", n)
	}
	propose(r, put(d, 7, "d"))
	for len(r.batcher.fastAcks) > 0 {
		<-r.batcher.fastAcks // d's fast ack
	}
	r.getCmdDescSeq(d, &MFastAck{Replica: 0, Ballot: 0, CmdId: d, Dep: []CommandId{},
		Checksum: []SHash{{}}}, nil, nil, false)
	runOnce(r)
	if !r.delivered.Has(c.String()) || !r.delivered.Has(d.String()) {
		t.Fatalf("c and d should be committed and executed (N = 3: leader and replica 1)")
	}
	if n := len(r.batcher.fastAcks); n != 0 {
		t.Fatalf("a fast ack for c was sent (%d)", n)
	}
}
