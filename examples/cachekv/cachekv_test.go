package cachekv

import (
	"context"
	"errors"
	"testing"
	"time"

	"go.etcd.io/etcd/api/v3/mvccpb"
	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
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
	// the auto-compactor ran during Main: the first write's revision (2) is already compacted when
	// Main returns
	if _, err := cli.Get(ctx, prefix, clientv3.WithPrefix(), clientv3.WithRev(2)); !errors.Is(err, rpctypes.ErrCompacted) {
		t.Fatalf("a read at revision 2 right after Main: %v, want ErrCompacted", err)
	}
	// the auto-compactor runs: within a few periods it compacts the last revision (the store's a
	// period before), so a read at the revision before it fails with ErrCompacted
	deadline := time.Now().Add(5 * time.Second)
	for {
		rctx, rcancel := context.WithTimeout(context.Background(), 5*time.Second)
		_, err := cli.Get(rctx, prefix, clientv3.WithPrefix(), clientv3.WithRev(resp.Header.Revision-1))
		rcancel()
		if errors.Is(err, rpctypes.ErrCompacted) {
			break
		}
		if err != nil {
			t.Fatal(err)
		}
		if time.Now().After(deadline) {
			t.Fatal("the periodic compactor did not compact within 5s")
		}
		time.Sleep(10 * time.Millisecond)
	}
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

// TestCheckGet checks checkGet on hand-made answers: the last values pass; a stale value, a
// missing key or an extra key panics.
func TestCheckGet(t *testing.T) {
	evs := []common.Event{
		{Rev: 2, Key: "ck/k0", Val: "a", Put: true},
		{Rev: 3, Key: "ck/k1", Val: "b", Put: true},
		{Rev: 4, Key: "ck/k0", Val: "c", Put: true},
	}
	kv := func(k, v string) *mvccpb.KeyValue { return &mvccpb.KeyValue{Key: []byte(k), Value: []byte(v)} }
	panics := func(f func()) (p bool) {
		defer func() { p = recover() != nil }()
		f()
		return false
	}
	if panics(func() { checkGet(evs, 4, []*mvccpb.KeyValue{kv("ck/k0", "c"), kv("ck/k1", "b")}) }) {
		t.Fatal("checkGet rejected the last values")
	}
	if panics(func() { checkGet(evs, 3, []*mvccpb.KeyValue{kv("ck/k0", "a"), kv("ck/k1", "b")}) }) {
		t.Fatal("checkGet rejected the values at revision 3")
	}
	for name, kvs := range map[string][]*mvccpb.KeyValue{
		"stale":   {kv("ck/k0", "a"), kv("ck/k1", "b")},
		"missing": {kv("ck/k0", "c")},
		"extra":   {kv("ck/k0", "c"), kv("ck/k1", "b"), kv("ck/k2", "d")},
	} {
		if !panics(func() { checkGet(evs, 4, kvs) }) {
			t.Fatalf("checkGet accepted the %s answer", name)
		}
	}
}
