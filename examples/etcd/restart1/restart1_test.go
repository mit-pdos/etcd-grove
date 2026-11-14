package restart1

import (
	"fmt"
	"strings"
	"sync"
	"testing"
	"time"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"
)

// TestMemberID checks D21e (A)'s premise on the member id etcd computes for Main's cluster (from the
// peer URL and the cluster token): its 16 low bits are not 0.
func TestMemberID(t *testing.T) {
	urls, err := types.NewURLsMap(name + "=http://" + peerAddr)
	if err != nil {
		t.Fatal(err)
	}
	cl, err := membership.NewClusterFromURLsMap(zap.NewNop(), name, urls)
	if err != nil {
		t.Fatal(err)
	}
	for _, id := range cl.MemberIDs() {
		low := uint64(id) & 0xffff
		t.Logf("member %x: low 16 bits %#x", uint64(id), low)
		if low == 0 {
			t.Fatalf("member %x: low 16 bits zero", uint64(id))
		}
	}
}

// The events counted, each by the message etcd logs for it. Those from the restart on are counted
// apart: the restart begins with the first message only a member booting from its WAL logs
// (recoverSnapshot's, when it opens the backend, then bootstrapWALFromSnapshot's).
const (
	cntRestart = "restarting local member"                // the WAL replayed (field commit-index)
	cntWALSnap = "constructed a snapshot from WAL record" // a snapshot in the WAL (snapshot-index)
	// the backend kept, at its consistent index (consistent-index) at or above the WAL's snapshot's
	// (snapshot-index)
	cntSkipSnap = "Skipping snapshot backend"
	// the backend replaced by the snapshot's: never in a graceful one-member restart
	cntRecSnap   = "Recovering from snapshot backend"
	cntNoWALSnap = "No snapshot found. Recovering WAL from scratch" // a WAL with no snapshot
	cntSaveSnap  = "saved snapshot"                                 // a disk snapshot taken
	cntSnapSent  = "sending merged snapshot"                        // never: no peer
)

var cntEvents = []string{cntRestart, cntWALSnap, cntSkipSnap, cntRecSnap, cntNoWALSnap, cntSaveSnap,
	cntSnapSent}

// counts is a zap core that logs nothing and counts the messages of cntEvents, at every level,
// before and after the restart, and keeps the integer fields of the last such message after it.
type counts struct {
	mu        *sync.Mutex
	restarted *bool
	before    map[string]int
	after     map[string]int
	fields    map[string]map[string]int64
}

func newCounts() counts {
	return counts{mu: &sync.Mutex{}, restarted: new(bool), before: map[string]int{},
		after: map[string]int{}, fields: map[string]map[string]int64{}}
}

func (c counts) Enabled(zapcore.Level) bool        { return true }
func (c counts) With([]zapcore.Field) zapcore.Core { return c }
func (c counts) Sync() error                       { return nil }

func (c counts) Check(e zapcore.Entry, ce *zapcore.CheckedEntry) *zapcore.CheckedEntry {
	return ce.AddCore(e, c)
}

func (c counts) Write(e zapcore.Entry, fs []zapcore.Field) error {
	c.mu.Lock()
	defer c.mu.Unlock()
	if strings.Contains(e.Message, cntWALSnap) || strings.Contains(e.Message, cntNoWALSnap) ||
		strings.Contains(e.Message, cntRestart) {
		*c.restarted = true
	}
	for _, k := range cntEvents {
		if strings.Contains(e.Message, k) {
			if *c.restarted {
				c.after[k]++
				m := map[string]int64{}
				for _, f := range fs {
					switch f.Type {
					case zapcore.Uint64Type, zapcore.Int64Type, zapcore.Int32Type,
						zapcore.Uint32Type:
						m[f.Key] = f.Integer
					}
				}
				c.fields[k] = m
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

func (c counts) field(k string, f string) (int64, bool) {
	c.mu.Lock()
	defer c.mu.Unlock()
	v, ok := c.fields[k][f]
	return v, ok
}

func (c counts) report() string {
	c.mu.Lock()
	defer c.mu.Unlock()
	return fmt.Sprintf("before the restart: %v; from the restart on: %v; fields: %v", c.before,
		c.after, c.fields)
}

// TestRun runs Run once, in a fresh directory (the member's DataDir is relative), with a logger
// that counts what the member did, and fails unless Run's check ran (it panics if it fails) and the
// run tested what it is meant to: disk snapshots taken before the stop; the restart replayed a WAL
// holding a snapshot record above index 0 (sigma.b > 0); the backend kept, at a consistent index
// above the bootstrap entries and at or above the snapshot's (it logs how many entries were
// replayed past the snapshot and skipped); the WAL's commit index at least the
// bootstrap entries plus the Puts; no snapshot sent.
func TestRun(t *testing.T) {
	t.Chdir(t.TempDir())
	c := newCounts()
	start := time.Now()
	ok := Run(zap.New(c))
	t.Logf("Run took %v", time.Since(start))
	t.Log(c.report())
	if !ok {
		t.Fatalf("Run returned before its check")
	}

	if c.get(false, cntSaveSnap) == 0 {
		t.Errorf("no disk snapshot taken before the stop")
	}
	if c.get(true, cntRestart) != 1 {
		t.Errorf("the member did not restart from its WAL exactly once")
	}
	if c.get(true, cntWALSnap) != 1 || c.get(true, cntNoWALSnap) != 0 {
		t.Errorf("the restarted member's WAL held no snapshot")
	}
	si, ok1 := c.field(cntWALSnap, "snapshot-index")
	if !ok1 || si <= 0 {
		t.Errorf("the WAL's snapshot is at index %d (found: %v), not above 0", si, ok1)
	}
	if c.get(true, cntSkipSnap) != 1 || c.get(true, cntRecSnap) != 0 {
		t.Errorf("the backend was not kept at its consistent index")
	}
	ci, ok2 := c.field(cntSkipSnap, "consistent-index")
	if !ok2 || ci <= NBoot || ci < si {
		t.Errorf("the backend's consistent index %d (found: %v) is not above NBoot = %d and at or "+
			"above the snapshot's index %d", ci, ok2, NBoot, si)
	}
	// not a failure: the last snapshot can be at the last applied entry (NPuts)
	t.Logf("entries replayed past the WAL's snapshot and skipped at the consistent index: %d",
		ci-si)
	ri, ok3 := c.field(cntRestart, "commit-index")
	if !ok3 || ri < NBoot+NPuts {
		t.Errorf("the WAL's commit index %d (found: %v) is below NBoot + NPuts = %d", ri, ok3,
			NBoot+NPuts)
	}
	if c.get(false, cntSnapSent)+c.get(true, cntSnapSent) != 0 {
		t.Errorf("a snapshot was sent")
	}
}
