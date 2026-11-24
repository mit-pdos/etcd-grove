package swift

import (
	"sync"
	"testing"
	"time"

	cmap "github.com/orcaman/concurrent-map"
)

// shardIdx is the index of key's shard in m (the order IterCb visits it).
func shardIdx(m cmap.ConcurrentMap, key string) int {
	s := m.GetShard(key)
	for i := range m {
		if m[i] == s {
			return i
		}
	}
	return -1
}

// SW-F1: stopDescs must not return while a descriptor goroutine runs (its
// contract: handleNewLeader and handleSync then write the descriptors' fields
// and free them; Go's memory model). It visits cmdDescs shard by shard; a
// descriptor goroutine G1 it has not stopped yet can create a dependency's
// descriptor (and its goroutine G2) in a shard it has already visited
// (handleSyncEntry or getFastAndSlowAcksHandler: getCmdDesc(dep, nil, nil)).
//
// Deterministic schedule: d's shard comes before x's. x's descriptor has a
// goroutine (G1). A descriptor f in d's shard tells the test when stopDescs
// has entered that shard; the test holds x's shard's lock, so stopDescs has
// not reached G1. G1 then handles a message with dependency d: d's
// descriptor is inserted in its shard after stopDescs's visit (it needs the
// shard's write lock). The test lets stopDescs go on; when it returns, every
// descriptor in cmdDescs must be stopped (or sequential).
func TestIssueSWF1_StopDescsStopsNewDescs(t *testing.T) {
	old := MaxDescRoutines
	MaxDescRoutines = 100
	defer func() { MaxDescRoutines = old }()

	r := newTestReplica(t, 3, 1, 0, false)
	m := r.cmdDescs

	// d, x, and a key f in d's shard, with shard(d) < shard(x)
	d := cid(1, 0)
	var x CommandId
	found := false
	for s := int32(1); s < 10000 && !found; s++ {
		x = cid(2, s)
		found = shardIdx(m, d.String()) < shardIdx(m, x.String())
	}
	var fkey string
	for s := int32(0); s < 100000; s++ {
		k := cid(3, s).String()
		if shardIdx(m, k) == shardIdx(m, d.String()) {
			fkey = k
			break
		}
	}
	if !found || fkey == "" {
		t.Fatal("no keys with the shard order needed")
	}

	// G1: x's descriptor goroutine
	gx := r.getCmdDesc(x, nil, nil)

	// f: a descriptor whose stop requests the test answers
	f := &commandDesc{active: true, stopChan: make(chan *sync.WaitGroup, 8)}
	m.Set(fkey, f)
	atD := make(chan struct{})
	go func() {
		wg := <-f.stopChan
		f.active = false
		close(atD)
		wg.Done()
	}()

	xs := m.GetShard(x.String())
	xs.Lock()
	done := make(chan struct{})
	go func() {
		r.stopDescs()
		close(done)
	}()
	<-atD // stopDescs is in (or past) d's shard, not yet in x's

	// (getCmdDesc's send, without its Upsert: the test holds x's shard)
	gx.msgs <- &syncEntry{
		propose: put(x, 6, "v"),
		cmd:     put(x, 6, "v").Command,
		dep:     Dep{d},
	}
	for start := time.Now(); !m.Has(d.String()); {
		if time.Since(start) > 10*time.Second {
			xs.Unlock()
			t.Fatal("x's descriptor did not create d's")
		}
		time.Sleep(time.Millisecond)
	}
	xs.Unlock()

	select {
	case <-done:
	case <-time.After(10 * time.Second):
		t.Fatal("stopDescs did not return")
	}

	running := []string{}
	m.IterCb(func(k string, v interface{}) {
		desc := v.(*commandDesc)
		if desc.active && !desc.seq {
			running = append(running, k)
		}
	})
	if len(running) != 0 {
		r.stopDescs() // the test's own clean-up
		t.Fatalf("descriptor goroutines still running after stopDescs: %v", running)
	}
}
