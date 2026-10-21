package linkv3p

import (
	"context"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.uber.org/zap"
)

// TestMemberIDs checks D21e (A)'s premise on the member ids etcd computes for Main's cluster (from
// the peer URLs and the cluster token): their 16 low bits are distinct and not 0. It prints the
// ids in the order bootstrap sorts them (the proof's BootFacts).
func TestMemberIDs(t *testing.T) {
	urls, err := types.NewURLsMap("linkv3p-1=http://" + peerAddr1 + ",linkv3p-2=http://" + peerAddr2 +
		",linkv3p-3=http://" + peerAddr3)
	if err != nil {
		t.Fatal(err)
	}
	cl, err := membership.NewClusterFromURLsMap(zap.NewNop(), "linkv3p", urls)
	if err != nil {
		t.Fatal(err)
	}
	seen := map[uint64]bool{}
	for _, id := range cl.MemberIDs() {
		low := uint64(id) & 0xffff
		t.Logf("member %x (%s): low 16 bits %#x", uint64(id), cl.Member(id).Name, low)
		if low == 0 || seen[low] {
			t.Fatalf("member %x: low 16 bits %#x zero or repeated", uint64(id), low)
		}
		seen[low] = true
	}
}

// isolate returns the steps that, after delay, cut member m from the two others.
func isolate(delay time.Duration, m int) []Step {
	var steps []Step
	for o := 0; o < 3; o++ {
		if o != m {
			steps = append(steps, Step{Delay: delay, Cut: true, A: m, B: o})
			delay = 0
		}
	}
	return steps
}

// heal returns the steps that, after delay, mend member m's links to the two others.
func heal(delay time.Duration, m int) []Step {
	var steps []Step
	for o := 0; o < 3; o++ {
		if o != m {
			steps = append(steps, Step{Delay: delay, A: m, B: o})
			delay = 0
		}
	}
	return steps
}

// TestMainRun runs Main for real: three members in a fresh directory (the members' DataDirs are
// relative), 8 clients of 150 operations each, on a schedule that isolates each member in turn
// for three seconds, half a second apart (so the leader, whichever it is, is isolated once at
// least, its followers elect another and it steps down: CheckQuorum; an operation at an isolated
// member fails after the request timeout, 7s, which stretches the workload over the schedule),
// and porcupine's verdict must be Ok. Then it asks each member, which Main left running, for the
// keys (so that the history was not all errors, and the three members, mended, agree), the raft
// term (past the first election's: a re-election happened) and the member count. (The keys may
// all be deleted at the end: the workload has deletes; the revision says the writes took effect.)
func TestMainRun(t *testing.T) {
	t.Chdir(t.TempDir())
	var sched []Step
	for m := 0; m < 3; m++ {
		sched = append(sched, isolate(500*time.Millisecond, m)...)
		sched = append(sched, heal(3*time.Second, m)...)
	}
	start := time.Now()
	if r := Main(8, 150, sched); r != porcupine.Ok {
		t.Fatalf("got %v", r)
	}
	t.Logf("Main took %v", time.Since(start))

	var kvs string
	for i, addr := range []string{clientAddr1, clientAddr2, clientAddr3} {
		cli, err := clientv3.New(clientv3.Config{Endpoints: []string{addr}, Logger: zap.NewNop()})
		if err != nil {
			t.Fatal(err)
		}
		ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		resp, err := cli.Get(ctx, "k", clientv3.WithPrefix())
		if err != nil {
			cancel()
			t.Fatalf("member %d: %v", i+1, err)
		}
		if resp.Header.Revision < 10 {
			t.Fatalf("member %d: Main's writes did not take effect: revision %d, %v", i+1,
				resp.Header.Revision, resp.Kvs)
		}
		if resp.Header.RaftTerm < 3 {
			t.Fatalf("member %d: raft term %d: no re-election happened", i+1, resp.Header.RaftTerm)
		}
		s := ""
		for _, kv := range resp.Kvs {
			s += string(kv.Key) + "=" + string(kv.Value) + ";"
		}
		if i == 0 {
			kvs = s
		} else if s != kvs {
			t.Fatalf("member %d reads %q, member 1 %q", i+1, s, kvs)
		}
		ml, err := cli.MemberList(ctx)
		if err != nil {
			t.Fatal(err)
		}
		if len(ml.Members) != 3 {
			t.Fatalf("expected 3 members, got %d", len(ml.Members))
		}
		t.Logf("member %d: revision %d, raft term %d, keys %d", i+1, resp.Header.Revision,
			resp.Header.RaftTerm, len(resp.Kvs))
		cancel()
		cli.Close()
	}
}
