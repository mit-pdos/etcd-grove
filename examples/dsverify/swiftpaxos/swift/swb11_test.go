package swift

import (
	"testing"
	"time"
)

// swb11Ids gives a dependency d and a command x in different shards of cmdDescs (and of
// delivered): the descriptor goroutine's accesses to d's shard then order nothing with the run
// loop's accesses to x's shard.
func swb11Ids(r *Replica) (CommandId, CommandId) {
	d := cid(1, 1)
	for s := int32(2); ; s++ {
		x := cid(2, s)
		if r.cmdDescs.GetShard(d.String()) != r.cmdDescs.GetShard(x.String()) {
			return d, x
		}
	}
}

// SWB-11: a descriptor's proposeDep, hs and seqnum are its owner's (its goroutine's). A
// recovery's syncEntry for x is taken by x's descriptor goroutine (handleSyncEntry writes
// proposeDep; deliver waits for the dependency d); the client's late proposal of x then reaches
// the run loop's getCmdDescWith. Before the fix, its Upsert callback read (and, if nil, wrote)
// proposeDep/hs/seqnum of the running descriptor under the shard lock only: a data race with
// handleSyncEntry's write. Run with -race.
func TestIssueSWB11_ProposeFieldsByOwner(t *testing.T) {
	if !raceOn {
		t.Skip("needs -race")
	}
	r := newTestReplica(t, 3, 1, 0, false)
	if MaxDescRoutines == 0 {
		t.Fatal("needs descriptor goroutines")
	}
	d, x := swb11Ids(r)
	px := put(x, 7, "x")
	desc := r.getCmdDesc(x, &syncEntry{propose: px, cmd: px.Command, dep: Dep{d}}, nil)
	if desc.seq {
		t.Fatal("x's descriptor is sequential")
	}
	// let x's goroutine take its syncEntry (a sleep orders nothing for the race detector)
	time.Sleep(100 * time.Millisecond)
	r.handleProposal(put(x, 7, "x")) // the run loop: the client's proposal of x
	r.stopDescs()
	if !desc.proposeDep.Equals(Dep{d}) {
		t.Fatalf("proposeDep = %v, want the MSync's %v (first writer)", desc.proposeDep, Dep{d})
	}
}

// SWB-11 (behaviour kept): a proposal whose descriptor goroutine was stopped before it took the
// proposal is reported by a recovery with the dependencies computed at the proposal (as when the
// run loop set proposeDep itself).
func TestIssueSWB11_PendingProposalDepReported(t *testing.T) {
	r := newTestReplica(t, 3, 1, 0, false)
	if MaxDescRoutines == 0 {
		t.Fatal("needs descriptor goroutines")
	}
	y, x := cid(1, 1), cid(2, 1)
	r.handleProposal(put(y, 7, "y"))
	r.getCmdDesc(x, nil, nil)
	r.stopDescs()
	r.handleProposal(put(x, 7, "x")) // x's descriptor is stopped: the proposal stays in msgs
	m := &MNewLeaderAckN{}
	r.fillNewLeaderAckN(m)
	found := false
	for i, c := range m.CmdIds {
		if c == x {
			found = true
			if m.Phases[i] != START || !Dep(m.Deps[i].Dep).Equals(Dep{y}) {
				t.Fatalf("x reported in phase %d with %v, want START with %v", m.Phases[i],
					m.Deps[i].Dep, Dep{y})
			}
		}
	}
	if !found {
		t.Fatal("x not reported")
	}
}
