// Reproduction of issues/leasing-delete-keeps-count.md (etcd-io/etcd#22417).
//
// Package leasing, file client/v3/leasing/delete_keeps_count_test.go of go.etcd.io/etcd (module
// go.etcd.io/etcd/client/v3), at the etcd pin of etc/goose.py: 107edf7e4 (branch goose-lean of
// upamanyus/etcd).
//
// Run, in client/v3:
//
//	GOTOOLCHAIN=go1.27.1 go test ./leasing -run '^TestTriageDeleteKeepsCount$' -count=1
//
// Fails at the pin (shows the bug): logs "after delete: len(Kvs)=0 Count=1", then "Kvs empty
// but Count=1".
package leasing

import (
	"context"
	"testing"
	"time"

	v3pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/mvccpb"
	v3 "go.etcd.io/etcd/client/v3"
)

// A cached Delete clears Kvs but keeps Count.
func TestTriageDeleteKeepsCount(t *testing.T) {
	lc := &leaseCache{entries: make(map[string]*leaseKey), revokes: make(map[string]time.Time)}
	lc.Add("k", &v3.GetResponse{
		Header: &v3pb.ResponseHeader{Revision: 2},
		Kvs:    []*mvccpb.KeyValue{{Key: []byte("k"), Value: []byte("v"), CreateRevision: 2, ModRevision: 2, Version: 1}},
		Count:  1,
	}, v3.OpGet("k"))
	lc.Delete("k", &v3pb.ResponseHeader{Revision: 3})
	resp, ok := lc.Get(context.Background(), v3.OpGet("k"))
	if !ok || resp == nil {
		t.Fatalf("not served from cache")
	}
	t.Logf("after delete: len(Kvs)=%d Count=%d", len(resp.Kvs), resp.Count)
	if len(resp.Kvs) == 0 && resp.Count != 0 {
		t.Errorf("Kvs empty but Count=%d", resp.Count)
	}
}
