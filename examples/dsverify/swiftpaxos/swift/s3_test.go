package swift

import (
	"sync"
	"testing"

	"github.com/imdea-software/swiftpaxos/state"
)

// S3: a command must execute only after the commands it depends on have
// executed. deliver marked a command delivered and then executed it; a
// successor delivered by another descriptor goroutine in between saw its
// dependency delivered and executed first.
//
// c (put k=1) and s (put k=2, depending on c) are committed; their
// descriptors' goroutines deliver them concurrently, s's as soon as it sees c
// delivered (as deliverChan's notification would let it). The store must end
// with s's value. Repeated: the window is small.
func TestIssueS3_ExecuteAfterDependencies(t *testing.T) {
	bad := 0
	for i := 0; i < 20000 && bad == 0; i++ {
		r := newTestReplica(t, 3, 1, 0, false)
		c, s := cid(1, 0), cid(2, 0)
		dc := r.newDesc()
		dc.propose, dc.cmd, dc.phase = put(c, 5, "1"), state.Command{Op: state.PUT, K: 5, V: state.Value("1")}, COMMIT
		ds := r.newDesc()
		ds.propose, ds.cmd, ds.phase = put(s, 5, "2"), state.Command{Op: state.PUT, K: 5, V: state.Value("2")}, COMMIT
		ds.dep = Dep{c}

		var wg sync.WaitGroup
		wg.Add(2)
		go func() {
			defer wg.Done()
			for !r.delivered.Has(c.String()) {
			}
			r.deliver(ds, s)
		}()
		go func() {
			defer wg.Done()
			r.deliver(dc, c)
		}()
		wg.Wait()
		v := (&state.Command{Op: state.GET, K: 5}).Execute(r.State)
		if string(v) != "2" {
			bad++
			t.Errorf("run %d: s executed before its dependency c (store has %q)", i, v)
		}
	}
}
