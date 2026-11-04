package compactor

import (
	"context"
	"os"
	"os/exec"
	"strconv"
	"strings"
	"sync"
	"testing"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.uber.org/zap"
	"k8s.io/apiserver/pkg/storage/etcd3"
	"k8s.io/utils/clock"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// TestCompactor runs Main once, in a fresh data directory (the member's DataDir is relative), then
// asks the member Main left running whether the compactors ran: compact_rev_key holds a revision,
// and a watch from revision 1 is compacted (some round compacted).
func TestCompactor(t *testing.T) {
	t.Chdir(t.TempDir())
	Main()

	cli, err := clientv3.New(clientv3.Config{Endpoints: []string{clientAddr}, Logger: zap.NewNop()})
	if err != nil {
		t.Fatal(err)
	}
	defer cli.Close()
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	resp, err := cli.Get(ctx, compactRevKey)
	if err != nil {
		t.Fatal(err)
	}
	if len(resp.Kvs) != 1 {
		t.Fatalf("Main's compactors did not write %s", compactRevKey)
	}
	v, err := strconv.ParseInt(string(resp.Kvs[0].Value), 10, 64)
	if err != nil || v <= 0 {
		t.Fatalf("%s holds %q, want a positive revision", compactRevKey, resp.Kvs[0].Value)
	}
	wctx, wcancel := context.WithCancel(context.Background())
	defer wcancel()
	crev, ok := etcdstart.CompactRev(cli.Watch(wctx, writeKey, clientv3.WithRev(1)))
	if !ok {
		t.Fatalf("no compaction: a watch from revision 1 is not compacted")
	}
	t.Logf("%s = %d (version %d), compacted at %d, store at %d", compactRevKey, v,
		resp.Kvs[0].Version, crev, resp.Header.Revision)
}

// keyPut is one put of compact_rev_key, as the history watch saw it.
type keyPut struct {
	val int64     // its value
	rev int64     // its revision
	at  time.Time // when the watch delivered it
}

// startMember starts a member at the given addresses, in compaction mode with etcd's compactor
// off, and returns a client of it.
func startMember(t *testing.T, name, peer, client string) *clientv3.Client {
	t.Chdir(t.TempDir())
	lg := zap.NewNop()
	s, err := etcdstart.StartCompactingServer(name, peer, client, 0, lg)
	if err != nil {
		t.Fatal(err)
	}
	if err := etcdstart.Serve(s, client); err != nil {
		t.Fatal(err)
	}
	cli, err := etcdstart.NewClient(client, lg)
	if err != nil {
		t.Fatal(err)
	}
	if !ready(cli) {
		t.Fatal("the member does not serve")
	}
	return cli
}

// TestHistory runs Main's workload (the writer, three API servers) on a member of its own, with a
// watch of compact_rev_key registered before the first round, and checks what Main cannot state in terms
// of the specs:
//
//   - the key's values increase, each below the revision it was put at (a revision reached before
//     the put);
//   - successive puts are at least an interval apart, up to scheduling (a winner's previous round
//     saw the previous put, then it waited an interval): history is kept for an interval before a
//     compaction;
//   - the store is compacted at one of the key's values (a recorded revision).
func TestHistory(t *testing.T) {
	addr := "127.0.0.1:23977"
	cli := startMember(t, "k8scompactorh", "127.0.0.1:23987", addr)
	defer cli.Close()

	wctx, wcancel := context.WithCancel(context.Background())
	defer wcancel()
	// From the store's next revision (no WithRev): a synced watcher, which a compaction does not
	// cancel (one from an older revision is cancelled if a compaction passes it before it catches
	// up); registered (Watch returns before it is) before the workload starts.
	wch := cli.Watch(wctx, compactRevKey, clientv3.WithCreatedNotify())
	if created := <-wch; !created.Created {
		t.Fatalf("history watch: %v", created.Err())
	}
	var puts []keyPut
	var mu sync.Mutex
	watchDone := make(chan struct{})
	go func() {
		defer close(watchDone)
		for wresp := range wch {
			if wresp.Err() != nil {
				t.Errorf("history watch: %v", wresp.Err())
				return
			}
			for _, e := range wresp.Events {
				v, err := strconv.ParseInt(string(e.Kv.Value), 10, 64)
				if err != nil {
					t.Errorf("%s put %q", compactRevKey, e.Kv.Value)
					return
				}
				mu.Lock()
				puts = append(puts, keyPut{val: v, rev: e.Kv.ModRevision, at: time.Now()})
				mu.Unlock()
			}
		}
	}()

	go writer(cli)
	var wg sync.WaitGroup
	for i := 0; i < servers; i++ {
		c, err := etcdstart.NewClient(addr, zap.NewNop())
		if err != nil {
			t.Fatal(err)
		}
		defer c.Close()
		wg.Add(1)
		go func() {
			apiserver(c)
			wg.Done()
		}()
	}
	wg.Wait()
	time.Sleep(10 * interval) // the watch delivers the last puts
	wcancel()
	<-watchDone

	mu.Lock()
	defer mu.Unlock()
	if len(puts) < 2 {
		t.Fatalf("only %d puts of %s", len(puts), compactRevKey)
	}
	vals := map[int64]bool{}
	for i, p := range puts {
		vals[p.val] = true
		if p.val >= p.rev {
			t.Errorf("put %d: value %d not below its revision %d", i, p.val, p.rev)
		}
		if i == 0 {
			if p.val != 0 {
				t.Errorf("the first put's value %d, want 0 (the first round's revision)", p.val)
			}
			continue
		}
		q := puts[i-1]
		if p.val <= q.val {
			t.Errorf("put %d: value %d not above the previous %d", i, p.val, q.val)
		}
		if p.val < q.rev {
			t.Errorf("put %d: value %d below the previous put's revision %d", i, p.val, q.rev)
		}
		if gap := p.at.Sub(q.at); gap < interval/2 {
			t.Errorf("put %d: %v after the previous one, want about %v", i, gap, interval)
		}
	}

	cctx, ccancel := context.WithCancel(context.Background())
	defer ccancel()
	crev, ok := etcdstart.CompactRev(cli.Watch(cctx, writeKey, clientv3.WithRev(1)))
	if !ok {
		t.Fatalf("no compaction")
	}
	if !vals[crev] {
		t.Errorf("compacted at %d, not a value of %s (%v)", crev, compactRevKey, puts)
	}
	t.Logf("%d puts of %s (value@revision: %v); compacted at %d", len(puts), compactRevKey, putsString(puts), crev)
}

// putsString shows the puts as value@revision.
func putsString(puts []keyPut) string {
	var b strings.Builder
	for i, p := range puts {
		if i > 0 {
			b.WriteString(" ")
		}
		b.WriteString(strconv.FormatInt(p.val, 10) + "@" + strconv.FormatInt(p.rev, 10))
	}
	return b.String()
}

// missingKeyEnv selects TestMissingKey's child process.
const missingKeyEnv = "K8SCOMPACTOR_MISSING_KEY"

// TestMissingKey is the variant of the workload in which compact_rev_key disappears
// (nonissues/k8s-apiserver-compactor-missing-key-panic.md, kubernetes#139252): once a compactor has
// written it, the key is deleted, and the compactor's next round panics (Compact's else branch
// indexes the empty Get response). The panic kills the process, so the variant runs in a child
// process; the test checks that it crashed with an index out of range in Compact.
func TestMissingKey(t *testing.T) {
	if os.Getenv(missingKeyEnv) == "1" {
		missingKeyChild(t)
		return
	}
	cmd := exec.Command(os.Args[0], "-test.run=^TestMissingKey$", "-test.v")
	cmd.Env = append(os.Environ(), missingKeyEnv+"=1")
	out, err := cmd.CombinedOutput()
	if err == nil {
		t.Fatalf("the compactor survived the key's deletion:\n%s", out)
	}
	if !strings.Contains(string(out), "index out of range") || !strings.Contains(string(out), "etcd3.Compact") {
		t.Fatalf("the child failed otherwise (%v):\n%s", err, out)
	}
	t.Logf("the compactor panicked:\n%s", firstLines(string(out), "panic:", 3))
}

// missingKeyChild runs one compactor until it has written compact_rev_key, deletes the key, and
// waits for the compactor's next rounds (it panics in one).
func missingKeyChild(t *testing.T) {
	addr := "127.0.0.1:23978"
	cli := startMember(t, "k8scompactorm", "127.0.0.1:23988", addr)
	c := etcd3.NewCompactor(cli, interval, clock.RealClock{}, nil)
	defer c.Stop()
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	for {
		resp, err := cli.Get(ctx, compactRevKey)
		if err != nil {
			t.Fatal(err)
		}
		if len(resp.Kvs) != 0 {
			break
		}
		time.Sleep(interval / 4)
	}
	if _, err := cli.Delete(ctx, compactRevKey); err != nil {
		t.Fatal(err)
	}
	time.Sleep(20 * interval)
	t.Logf("no panic after deleting %s", compactRevKey)
}

// firstLines returns n lines of s from the first one containing prefix.
func firstLines(s, prefix string, n int) string {
	i := strings.Index(s, prefix)
	if i < 0 {
		return ""
	}
	ls := strings.SplitN(s[i:], "\n", n+1)
	if len(ls) > n {
		ls = ls[:n]
	}
	return strings.Join(ls, "\n")
}
