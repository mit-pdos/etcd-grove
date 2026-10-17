// Review probe (fork copy of ~/etcd-pr/etcd-21600 HEAD): the cancel response
// that Cache.Watch sends when attachPrevKV fails has Header == nil (the fork's
// clientv3.WatchResponse.Header is a *pb.ResponseHeader; clientv3 and the
// cache's other responses always set it).
package cache

import (
	"context"
	"testing"
	"time"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/mvccpb"
	clientv3 "go.etcd.io/etcd/client/v3"
)

func TestReviewForkPrevKVCancelNilHeader(t *testing.T) {
	nilHeaders, closed := 0, 0
	for i := 0; i < 40; i++ {
		initial := &clientv3.GetResponse{
			Header: &pb.ResponseHeader{Revision: 2},
			Kvs:    []*mvccpb.KeyValue{{Key: []byte("/a"), Value: []byte("v1"), CreateRevision: 2, ModRevision: 2, Version: 1}},
		}
		mw := newMockWatcher(16)
		c, err := New(&clientv3.Client{Watcher: mw, KV: newKVStub(initial)}, "")
		if err != nil {
			t.Fatal(err)
		}
		mw.triggerCreatedNotify()
		<-mw.registered
		rctx, rcancel := context.WithTimeout(t.Context(), 2*time.Second)
		if err := c.WaitReady(rctx); err != nil {
			t.Fatal(err)
		}
		wctx, wcancel := context.WithCancel(t.Context())
		ch := c.Watch(wctx, "", clientv3.WithPrefix(), clientv3.WithPrevKV())
		mw.responses <- clientv3.WatchResponse{Header: &pb.ResponseHeader{}, Events: []*mvccpb.Event{{
			Type: mvccpb.Event_PUT,
			Kv:   &mvccpb.KeyValue{Key: []byte("/a"), Value: []byte("v2"), CreateRevision: 2, ModRevision: 100, Version: 2},
		}}}
		time.Sleep(20 * time.Millisecond) // let attachPrevKV block in waitForRev(99)
		wcancel()
		select {
		case resp, ok := <-ch:
			if !ok {
				closed++
			} else if resp.Canceled && resp.Header == nil {
				nilHeaders++
				t.Logf("iter %d: cancel response %q with Header == nil (resp.Header.Revision would panic)", i, resp.CancelReason)
			}
		case <-time.After(2 * time.Second):
			t.Logf("iter %d: no response within 2s (lost wakeup?)", i)
		}
		rcancel()
		c.Close()
	}
	t.Logf("nil-header cancel responses: %d, closed without response: %d", nilHeaders, closed)
	if nilHeaders > 0 {
		t.Errorf("Cache.Watch sent %d Canceled responses with a nil Header", nilHeaders)
	}
}
