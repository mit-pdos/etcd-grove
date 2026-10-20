package watchkv

import (
	"context"
	"testing"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.uber.org/zap"
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

// mustPanic runs f and fails the test unless it panics.
func mustPanic(t *testing.T, name string, f func()) {
	t.Helper()
	defer func() {
		if recover() == nil {
			t.Errorf("%s: no panic", name)
		}
	}()
	f()
}

// TestCheck checks the checker on hand-made histories: a good one passes; a delete, a repeated or
// decreasing revision, a gap, a put no writer attempted, a successful Put missing or different
// each panic.
func TestCheck(t *testing.T) {
	tried := []kv{{"wk/k0", "a"}, {"wk/k1", "b"}, {"wk/k0", "c"}}
	oks := []putRec{{2, "wk/k0", "a"}, {4, "wk/k0", "c"}}
	good := []event{{2, "wk/k0", "a", true}, {3, "wk/k1", "b", true}, {4, "wk/k0", "c", true}}
	check(good, tried, oks)
	check(nil, tried, nil)

	mustPanic(t, "delete", func() {
		check([]event{{2, "wk/k0", "a", false}}, tried, nil)
	})
	mustPanic(t, "repeat", func() {
		check([]event{{2, "wk/k0", "a", true}, {2, "wk/k1", "b", true}}, tried, nil)
	})
	mustPanic(t, "gap", func() {
		check([]event{{2, "wk/k0", "a", true}, {4, "wk/k1", "b", true}}, tried, nil)
	})
	mustPanic(t, "start", func() {
		check([]event{{3, "wk/k0", "a", true}}, tried, nil)
	})
	mustPanic(t, "unattempted", func() {
		check([]event{{2, "wk/k2", "d", true}}, tried, nil)
	})
	mustPanic(t, "missing", func() {
		check(good[:2], tried, oks)
	})
	mustPanic(t, "different", func() {
		check(good, tried, []putRec{{3, "wk/k0", "a"}})
	})
}

// TestMaxRev checks maxRev.
func TestMaxRev(t *testing.T) {
	if m := maxRev(nil); m != 0 {
		t.Fatalf("maxRev(nil) = %d", m)
	}
	if m := maxRev([]putRec{{5, "a", "b"}, {9, "a", "b"}, {7, "a", "b"}}); m != 9 {
		t.Fatalf("maxRev = %d", m)
	}
}
