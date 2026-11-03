package restart3

import (
	"context"
	"fmt"
	"strings"
	"sync"
	"testing"
	"time"

	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"
)

// TestMemberIDs checks D21e (A)'s premise on the member ids etcd computes for Main's cluster (from
// the peer URLs and the cluster token): their 16 low bits are distinct and not 0.
func TestMemberIDs(t *testing.T) {
	urls, err := types.NewURLsMap("restart3-1=http://" + peerAddr1 + ",restart3-2=http://" +
		peerAddr2 + ",restart3-3=http://" + peerAddr3)
	if err != nil {
		t.Fatal(err)
	}
	cl, err := membership.NewClusterFromURLsMap(zap.NewNop(), "restart3", urls)
	if err != nil {
		t.Fatal(err)
	}
	seen := map[uint64]bool{}
	for _, id := range cl.MemberIDs() {
		low := uint64(id) & 0xffff
		t.Logf("member %x: low 16 bits %#x", uint64(id), low)
		if low == 0 || seen[low] {
			t.Fatalf("member %x: low 16 bits %#x zero or repeated", uint64(id), low)
		}
		seen[low] = true
	}
}

// The events counts counts, each by the message etcd logs for it. Those from the restart on are
// counted apart: the restart begins with the first message only a member booting from its WAL logs
// (recoverSnapshot's, when it opens the backend, then bootstrapWALFromSnapshot's).
const (
	cntRestart  = "restarting local member"                // the WAL replayed
	cntWALSnap  = "constructed a snapshot from WAL record" // a snapshot found in the WAL
	cntSnapSent = "sending merged snapshot"                // a leader sends a follower a snapshot
	cntSnapDone = "applied snapshot"                       // a follower installed one
	cntCompact  = "compacted Raft logs"                    // raft's log compacted
	// a member booting from its WAL that holds no snapshot
	cntNoWALSnap = "No snapshot found. Recovering WAL from scratch"
)

var cntEvents = []string{cntRestart, cntWALSnap, cntSnapSent, cntSnapDone, cntCompact}

// counts is a zap core that logs nothing and counts the messages of cntEvents, at every level,
// before and after the first restart.
type counts struct {
	mu        *sync.Mutex
	restarted *bool
	before    map[string]int
	after     map[string]int
}

func newCounts() counts {
	return counts{mu: &sync.Mutex{}, restarted: new(bool), before: map[string]int{},
		after: map[string]int{}}
}

func (c counts) Enabled(zapcore.Level) bool        { return true }
func (c counts) With([]zapcore.Field) zapcore.Core { return c }
func (c counts) Sync() error                       { return nil }

func (c counts) Check(e zapcore.Entry, ce *zapcore.CheckedEntry) *zapcore.CheckedEntry {
	return ce.AddCore(e, c)
}

func (c counts) Write(e zapcore.Entry, _ []zapcore.Field) error {
	c.mu.Lock()
	defer c.mu.Unlock()
	// the restart's first messages: recoverSnapshot's (when the backend is opened), then
	// bootstrapWALFromSnapshot's
	if strings.Contains(e.Message, cntWALSnap) || strings.Contains(e.Message, cntNoWALSnap) ||
		strings.Contains(e.Message, cntRestart) {
		*c.restarted = true
	}
	for _, k := range cntEvents {
		if strings.Contains(e.Message, k) {
			if *c.restarted {
				c.after[k]++
			} else {
				c.before[k]++
			}
		}
	}
	return nil
}

func (c counts) get(after bool, k string) int {
	c.mu.Lock()
	defer c.mu.Unlock()
	if after {
		return c.after[k]
	}
	return c.before[k]
}

func (c counts) report() string {
	c.mu.Lock()
	defer c.mu.Unlock()
	return fmt.Sprintf("before the restart: %v; from the restart on: %v", c.before, c.after)
}

// TestRun runs Run once, in a fresh directory (the members' DataDirs are relative), with a logger
// that counts what the members did, and fails if the run did not test what it is meant to: a member
// restarted from its WAL, which held a snapshot, and was sent and installed a snapshot after it.
// Run returns without its check if a step fails, so the test then asks members 2 and 3, which Run
// left running, for the key (the last Put's value: the run got through) and the member count.
func TestRun(t *testing.T) {
	t.Chdir(t.TempDir())
	c := newCounts()
	start := time.Now()
	Run(zap.New(c))
	t.Logf("Run took %v", time.Since(start))
	t.Log(c.report())

	// the restarted member is member 3 or member 2 (Run stops a follower): ask both, member 1 aside
	cli, err := clientv3.New(clientv3.Config{Endpoints: []string{clientAddr3, clientAddr2},
		Logger: zap.NewNop()})
	if err != nil {
		t.Fatal(err)
	}
	defer cli.Close()
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	resp, err := cli.Get(ctx, "k")
	if err != nil {
		t.Fatalf("members 2 and 3: %v", err)
	}
	if len(resp.Kvs) != 1 || string(resp.Kvs[0].Value) != "v2" {
		t.Fatalf("members 2 and 3 read %v, not the last Put's v2", resp.Kvs)
	}
	ml, err := cli.MemberList(ctx)
	if err != nil {
		t.Fatal(err)
	}
	if len(ml.Members) != 3 {
		t.Fatalf("expected 3 members, got %d", len(ml.Members))
	}

	if c.get(true, cntRestart) == 0 {
		t.Errorf("no member restarted from its WAL")
	}
	if c.get(true, cntWALSnap) == 0 {
		t.Errorf("the restarted member's WAL held no snapshot")
	}
	if c.get(true, cntSnapSent) == 0 {
		t.Errorf("no snapshot was sent after the restart")
	}
	if c.get(true, cntSnapDone) == 0 {
		t.Errorf("no snapshot was installed after the restart")
	}
}
