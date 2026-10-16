// Reproduction of issues/leasing-get-inflight-write.md (etcd-io/etcd#20704, its bugs 2 and 4),
// at the level of the leasing cache.
//
// Package leasing, file client/v3/leasing/get_inflight_write_test.go of go.etcd.io/etcd (module
// go.etcd.io/etcd/client/v3), at the etcd pin of etc/goose.py: 107edf7e4 (branch goose-lean of
// upamanyus/etcd).
//
// Run, in client/v3:
//
//	GOTOOLCHAIN=go1.27.1 go test ./leasing -run '^(TestTriageGetServesEvictedEntry|TestTriageGetIgnoresFirstWriter)$' -count=1
//
// Both tests fail at the pin (show the bugs): "Get served the evicted entry: ..." and "Get
// returned "v2" while Put1 is still in flight".
package leasing

import (
	"context"
	"testing"
	"time"

	v3pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/mvccpb"
	v3 "go.etcd.io/etcd/client/v3"
)

func newTestCache() *leaseCache {
	return &leaseCache{entries: make(map[string]*leaseKey), revokes: make(map[string]time.Time)}
}

func cachedResp(rev int64) *v3.GetResponse {
	return &v3.GetResponse{
		Header: &v3pb.ResponseHeader{Revision: rev},
		Kvs:    []*mvccpb.KeyValue{{Key: []byte("k"), Value: []byte("v"), CreateRevision: 2, ModRevision: 2, Version: 1}},
		Count:  1,
	}
}
// etcd-io/etcd#20704 bug 2: a Get waiting on a write's waiter channel serves the
// entry that the failed write evicted (tryModifyOp's error path: Evict, close(wc)).
func TestTriageGetServesEvictedEntry(t *testing.T) {
	lc := newTestCache()
	lc.Add("k", cachedResp(2), v3.OpGet("k"))
	wc, _ := lc.Lock("k") // a Put in flight
	done := make(chan *v3.GetResponse)
	go func() {
		r, _ := lc.Get(context.Background(), v3.OpGet("k"))
		done <- r
	}()
	time.Sleep(50 * time.Millisecond) // the Get has found the entry and waits on wc
	lc.Evict("k")                     // the Put's Txn returned an error (outcome unknown)
	close(wc)
	r := <-done
	if r != nil {
		t.Errorf("Get served the evicted entry: %v (the in-flight Put may have committed)", r.Kvs)
	}
}

// etcd-io/etcd#20704 bug 4: a second write replaces the waiter channel; once it
// closes, a Get no longer waits for the first write, still in flight.
func TestTriageGetIgnoresFirstWriter(t *testing.T) {
	lc := newTestCache()
	lc.Add("k", cachedResp(2), v3.OpGet("k"))
	wc1, _ := lc.Lock("k") // Put1 in flight (it may already have committed at etcd)
	wc2, _ := lc.Lock("k") // Put2
	lc.mu.Lock()
	lc.Update([]byte("k"), []byte("v2"), &v3pb.ResponseHeader{Revision: 3}) // Put2 committed at 3
	lc.mu.Unlock()
	close(wc2)
	ctx, cancel := context.WithTimeout(context.Background(), 100*time.Millisecond)
	defer cancel()
	r, _ := lc.Get(ctx, v3.OpGet("k"))
	if r != nil {
		t.Errorf("Get returned %q while Put1 is still in flight", r.Kvs[0].Value)
	}
	close(wc1)
}
