package swift

import (
	"testing"
	"time"
)

// SWB-15: getCmdDescWith used to read desc.seq and desc.msgs and send after its Upsert had
// returned, outside the shard's lock. Meanwhile the descriptor's goroutine may retire on its
// history slot, free it to the pool, and another command's newDesc reuse it: a data race on
// seq/msgs (Go's memory model), and since newDesc kept (and drained) the same msgs channel, the
// message reached the other command's goroutine. After the fix getCmdDescWith captures seq and
// msgs under the shard's lock and newDesc makes fresh channels.
//
// Schedule: the run loop's getCmdDescWith(x, m) has passed its Upsert on x's descriptor D (its
// channel C: the fixed code captures it there; the old code reads D.msgs later, and D.msgs is C
// in every incarnation of D). x's goroutine retires (slot), D goes to the pool and is reused
// for y. The run loop's send of m (a proposal of x) on C: y's descriptor must not take it.
func TestIssueSWB15_StaleSendAfterReuse(t *testing.T) {
	r := newTestReplica(t, 3, 1, 0, false)
	if MaxDescRoutines == 0 {
		t.Fatal("needs descriptor goroutines")
	}
	r.poolLevel = 1
	r.descPool.New = func() interface{} { return &commandDesc{} }
	// with -race, sync.Pool drops some Puts: try until dx is reused
	for i := int32(1); i <= 50; i++ {
		x, y := cid(1, i), cid(2, i)
		dx := r.getCmdDesc(x, nil, nil)
		if dx.seq {
			t.Fatal("x's descriptor is sequential")
		}
		c := dx.msgs // the channel getCmdDescWith(x, m) sends m on

		dx.msgs <- int(i) // x's history slot: its goroutine retires and frees dx
		for start := time.Now(); r.cmdDescs.Has(x.String()); {
			if time.Since(start) > 10*time.Second {
				t.Fatal("x's descriptor did not retire")
			}
			time.Sleep(time.Millisecond)
		}
		time.Sleep(20 * time.Millisecond) // its goroutine's last steps (freeDesc)

		dy := r.getCmdDesc(y, nil, nil) // reuses dx, from the pool
		if dy != dx {
			r.stopDescs()
			continue
		}
		if dy.seq {
			t.Fatal("y's descriptor is sequential")
		}
		c <- &proposeMsg{p: put(x, 7, "x")} // the run loop's late send for x
		time.Sleep(100 * time.Millisecond)
		r.stopDescs()
		if dy.propose != nil {
			t.Fatalf("y's descriptor took x's proposal (%v.%d)", dy.propose.ClientId,
				dy.propose.CommandId)
		}
		return
	}
	t.Skip("the pool never handed the descriptor out again")
}
