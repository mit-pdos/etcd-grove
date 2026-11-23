package swift

import "testing"

// S8 (descriptors, found here): a descriptor returned to the pool (pool level
// 1 or 2) must not be used after. A leader's sequential descriptor executes
// its command when it is proposed (optimistic execution), takes its history
// slot and is freed in deliver; handlePropose then went on with its own fast
// ack on the freed descriptor (phase ACCEPT, message sets), which another
// goroutine's newDesc may have taken from the pool for another command.
//
// The leader proposes c; the descriptor the pool gives next (the freed one)
// must be as deliver left it, not written after.
func TestIssueS8b_NoUseAfterFree(t *testing.T) {
	if raceOn {
		t.Skip("sync.Pool drops objects at random under -race")
	}
	seqDescs(t)
	r := newTestReplica(t, 3, 0, 0, true)
	r.poolLevel = 1
	r.descPool.New = func() interface{} { return &commandDesc{} }
	propose(r, put(cid(1, 0), 6, "x"))
	d := r.descPool.Get().(*commandDesc)
	if d.phase == ACCEPT {
		t.Fatalf("the freed descriptor was written after it was freed (phase ACCEPT)")
	}
}
