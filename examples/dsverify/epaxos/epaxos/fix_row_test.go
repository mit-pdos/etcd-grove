package epaxos

import "testing"

// rowSchedule: replica 0 commits δ = 0.0 (PUT k1) with 1 and 2, then proposes γ = 0.1 (PUT k1;
// its PreAccepts are lost). Replica rec recovers γ with {rec, 0, x}: the leader replied, so
// sub-case 5 runs Phase 1 at rec's ballot, which reaches the acceptors acc (rec's other links are
// down). γ's committed deps must cover δ: the deps of a Phase 1 cover every interfering instance
// the ballot's leader and its acceptors know, row 0 included (only the instance's own leader,
// which knows its whole row, may be trusted for it).
func rowSchedule(t *testing.T, rec, x int32, acc []int32) {
	c := newCluster(t, 5)
	c.r[0].Alive[3], c.r[0].Alive[4] = false, false
	c.propose(0, put(1, "a"))
	c.settle(instOf(0, 0), among(0, 1, 2))
	if !committed(c.inst(0, 0, 0)) {
		t.Fatalf("setup: 0 did not commit 0.0: %s", instString(c.inst(0, 0, 0)))
	}
	c.drop(instOf(0, 0))
	c.r[0].Alive[3], c.r[0].Alive[4] = true, true
	c.propose(0, put(1, "b"))
	c.drop(instOf(0, 1))

	for q := int32(0); q < 5; q++ {
		c.r[rec].Alive[q] = q != rec && (q == 0 || q == x || q == acc[0] || q == acc[1])
	}
	c.recover(rec, 0, 1)
	c.run(kind("Prepare"), toAny(0, x))
	c.drop(kind("Prepare"))
	for q := int32(0); q < 5; q++ {
		c.r[rec].Alive[q] = q == acc[0] || q == acc[1]
	}
	c.run(kind("PrepareReply"), to(rec))
	c.drop(kind("PreAccept"), not(toAny(acc...)))
	c.settle(instOf(0, 1), among(append([]int32{rec}, acc...)...))
	if !committed(c.inst(rec, 0, 1)) {
		t.Fatalf("replica %d did not commit 0.1: %s", rec, instString(c.inst(rec, 0, 1)))
	}
	if e := c.depsError(); e != "" {
		t.Fatal(e)
	}
}

// TestRecoveryPhase1AcceptorsCoverLeaderRow: 4 does not know δ; its acceptors 1 and 2 do.
func TestRecoveryPhase1AcceptorsCoverLeaderRow(t *testing.T) { rowSchedule(t, 4, 3, []int32{1, 2}) }

// TestRecoveryPhase1LeaderCoversLeaderRow: 1 knows δ; its acceptors 3 and 4 do not.
func TestRecoveryPhase1LeaderCoversLeaderRow(t *testing.T) { rowSchedule(t, 1, 3, []int32{3, 4}) }
