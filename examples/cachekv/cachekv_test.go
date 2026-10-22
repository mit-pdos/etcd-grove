package cachekv

import (
	"context"
	"testing"
	"time"

	"go.etcd.io/etcd/api/v3/mvccpb"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/common"
)

// TestMainRun runs Main for real: one member in a fresh data directory (Main's DataDir is
// relative), 4 writers of 25 Puts each; the check must pass. Then it asks the member Main left
// running whether the Puts took effect (so that the check was not vacuous).
func TestMainRun(t *testing.T) {
	t.Chdir(t.TempDir())
	if r := Main(4, 25); r != Ok {
		t.Fatalf("got %v", r)
	}

	cli, err := clientv3.New(clientv3.Config{Endpoints: []string{clientAddr}, Logger: zap.NewNop()})
	if err != nil {
		t.Fatal(err)
	}
	defer cli.Close()
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	resp, err := cli.Get(ctx, prefix, clientv3.WithPrefix())
	if err != nil {
		t.Fatal(err)
	}
	if resp.Header.Revision != 101 {
		t.Fatalf("Main's Puts did not all take effect: revision %d", resp.Header.Revision)
	}
	t.Logf("revision %d after Main, keys %d", resp.Header.Revision, len(resp.Kvs))
}

// TestCollect checks collect on hand-made channels: it stops at the first event at or above upTo,
// and reports false on a cancel (a compaction's, a rejection's) or a closed channel before it.
func TestCollect(t *testing.T) {
	ev := func(rev int64, key string) *clientv3.Event {
		return &clientv3.Event{Kv: &mvccpb.KeyValue{Key: []byte(key), Value: []byte("a"), ModRevision: rev}}
	}
	run := func(upTo int64, resps ...clientv3.WatchResponse) ([]common.Event, bool) {
		ch := make(chan clientv3.WatchResponse, len(resps))
		for _, r := range resps {
			ch <- r
		}
		close(ch)
		return collect(ch, upTo)
	}
	if evs, ok := run(3, clientv3.WatchResponse{Events: []*clientv3.Event{ev(2, "ck/k0")}},
		clientv3.WatchResponse{Events: []*clientv3.Event{ev(3, "ck/k1")}}); !ok || len(evs) != 2 {
		t.Fatalf("got %v %v", evs, ok)
	}
	if _, ok := run(3, clientv3.WatchResponse{Events: []*clientv3.Event{ev(2, "ck/k0")}},
		clientv3.WatchResponse{Canceled: true, CompactRevision: 3}); ok {
		t.Fatal("a compaction's cancel: ok")
	}
	if _, ok := run(3, clientv3.WatchResponse{Canceled: true}); ok {
		t.Fatal("a rejection: ok")
	}
	if _, ok := run(3, clientv3.WatchResponse{Events: []*clientv3.Event{ev(2, "ck/k0")}}); ok {
		t.Fatal("closed early: ok")
	}
}
