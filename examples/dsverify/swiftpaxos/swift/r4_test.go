package swift

import "testing"

// R4: a proposal of a command already proposed (handleSync re-sends
// proposals; a client's proposal can arrive after the command came with an
// MSync) must not be handled again: run's propose case added it again to the
// key's dependencies (later commands then depend on it instead of on the
// commands proposed in between) and, for a delivered command, called Fatal
// (which returns here).
//
// Replica 1 of three (follower; MaxDescRoutines = 0): p1, p2, p1 again, p3,
// all puts of one key. p3 must depend on p2.
func TestIssueR4_DuplicateProposalIgnored(t *testing.T) {
	seqDescs(t)
	r := newTestReplica(t, 3, 1, 0, false)
	p1, p2, p3 := cid(1, 0), cid(2, 0), cid(3, 0)
	r.handleProposal(put(p1, 4, "a"))
	r.handleProposal(put(p2, 4, "b"))
	r.handleProposal(put(p1, 4, "a"))
	r.handleProposal(put(p3, 4, "c"))
	d := r.getCmdDesc(p3, nil, nil)
	if d == nil || !d.proposeDep.Equals(Dep{p2}) {
		t.Fatalf("p3's dependencies: %v, want [p2]", d.proposeDep)
	}
}
