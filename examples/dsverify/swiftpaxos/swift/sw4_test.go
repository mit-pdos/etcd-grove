package swift

import (
	"sync"
	"testing"

	"github.com/imdea-software/swiftpaxos/replica/defs"
	"github.com/imdea-software/swiftpaxos/state"
)

// beTheLeaderRecovers calls BeTheLeader and says whether it took the "delivered something"
// branch (the one that asks the run loop to recover: a ballot on r.recover).
func beTheLeaderRecovers(t *testing.T, r *Replica) bool {
	reply := defs.NewBeTheLeaderReply()
	if err := r.BeTheLeader(&defs.BeTheLeaderArgs{}, reply); err != nil {
		t.Fatal(err)
	}
	select {
	case <-r.recover:
		if reply.Leader != r.Id && !(r.Id == 0 && reply.Leader == -2) {
			t.Fatalf("BeTheLeader recovered but reported leader %d, not %d", reply.Leader, r.Id)
		}
		return true
	default:
		return false
	}
}

// SW4 (verification workaround P2-A): BeTheLeader reads deliveredAny instead of
// delivered.IsEmpty(); outside deliver's and handleSync's windows the two agree.
func TestBeTheLeaderDeliveredAny(t *testing.T) {
	seqDescs(t)
	r := newTestReplica(t, 3, 0, 0, true)
	check := func(when string, want bool) {
		t.Helper()
		if got := r.deliveredAny.Load(); got != want || got == r.delivered.IsEmpty() {
			t.Fatalf("%s: deliveredAny %v, delivered empty %v, want deliveredAny %v",
				when, got, r.delivered.IsEmpty(), want)
		}
		if got := beTheLeaderRecovers(t, r); got != want {
			t.Fatalf("%s: BeTheLeader recovered %v, want %v", when, got, want)
		}
	}
	check("fresh replica", false)

	// replica 0, the leader of ballot 0, delivers c when it proposes it (optimistic execution)
	c := cid(1, 0)
	propose(r, put(c, 6, "x"))
	if !r.delivered.Has(c.String()) {
		t.Fatal("c not delivered")
	}
	check("after deliver", true)

	// an MSync without commands empties delivered
	r.handleSync(&MSync{Replica: 1, Ballot: 4, Phases: map[CommandId]int{},
		Cmds: map[CommandId]state.Command{}, Deps: map[CommandId]Dep{}})
	check("after an empty MSync", false)

	// an MSync with a committed command: removed, then delivered again from the history
	r.status = RECOVERING
	d := cid(2, 0)
	r.handleSync(&MSync{Replica: 1, Ballot: 7,
		Phases: map[CommandId]int{d: COMMIT},
		Cmds:   map[CommandId]state.Command{d: {Op: state.PUT, K: 6, V: state.Value("d")}},
		Deps:   map[CommandId]Dep{d: {}}})
	if !r.delivered.Has(d.String()) {
		t.Fatal("d not delivered by the MSync")
	}
	check("after an MSync with d", true)
}

// SW4 (verification workaround P2-B): the check routineCount >= MaxDescRoutines and the
// increment are one cntL critical section, so concurrent descriptor creators (the run loop and
// descriptor goroutines creating a dependency's descriptor) never have more than
// MaxDescRoutines descriptor goroutines live. Many goroutines create distinct descriptors at
// once; the descriptors get no message, so their goroutines stay live until stopDescs. A
// sampler reads routineCount under cntL throughout; the count is checked again at the end.
// Run with -race.
func TestRoutineCountBound(t *testing.T) {
	old := MaxDescRoutines
	t.Cleanup(func() { MaxDescRoutines = old })
	for _, max := range []int{0, 1, 2, 5} {
		MaxDescRoutines = max
		for round := 0; round < 20; round++ {
			r := newTestReplica(t, 3, 1, 0, false)
			const creators = 32
			var start, wg sync.WaitGroup
			start.Add(1)
			stop := make(chan struct{})
			sampled := make(chan int, 1)
			go func() { // the sampler
				worst := 0
				for {
					r.cntL.Lock()
					n := r.routineCount
					r.cntL.Unlock()
					if n > worst {
						worst = n
					}
					select {
					case <-stop:
						sampled <- worst
						return
					default:
					}
				}
			}()
			for i := 0; i < creators; i++ {
				wg.Add(1)
				go func(i int) {
					defer wg.Done()
					start.Wait()
					c := cid(int32(1+i), int32(round))
					if d := r.getCmdDesc(c, nil, nil); d == nil {
						t.Errorf("no descriptor for %v", c)
					}
				}(i)
			}
			start.Done()
			wg.Wait()
			close(stop)
			worst := <-sampled
			r.cntL.Lock()
			n := r.routineCount
			r.cntL.Unlock()
			live := 0
			r.cmdDescs.IterCb(func(_ string, v interface{}) {
				if !v.(*commandDesc).seq {
					live++
				}
			})
			r.stopDescs()
			if n > max || worst > max || live != n {
				t.Fatalf("MaxDescRoutines %d, round %d: routineCount %d (sampled up to %d), "+
					"%d non-sequential descriptors", max, round, n, worst, live)
			}
			if want := max; creators >= max && n != want {
				t.Fatalf("MaxDescRoutines %d, round %d: routineCount %d, want %d", max, round, n, want)
			}
		}
	}
}
