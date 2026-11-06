package leasecatchup

import (
	"fmt"
	"strconv"
	"strings"
	"sync"
	"testing"
	"time"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"
)

// The events the test counts, each by the message etcd or raft logs for it (etcd's at info level,
// raft's too), as examples/etcd/partition's TestMainRun counts them.
const (
	cntSnapSent     = "sending merged snapshot" // etcd: a leader sends a follower a snapshot (field "to")
	cntSnapApplied  = "applied snapshot"        // etcd: a follower installed a received snapshot
	cntLeaseRestore = "restored lease store"    // etcd: applySnapshot recovered the lessor from it
	cntRaftRestore  = "] restored snapshot ["   // raft: "<id> [commit: c] restored snapshot [index: i, term: t]"
)

// A snapshot raft restored: the member's id (hex, as types.ID prints it) and the snapshot's index.
type restore struct {
	member string
	index  uint64
}

// runCounts is a zap core that logs nothing and records the events above, at every level.
type runCounts struct {
	mu       *sync.Mutex
	n        map[string]int
	sentTo   map[string]int // snapshots sent, by the receiving member's id
	restores *[]restore     // raft's restores, in order
}

func newRunCounts() runCounts {
	return runCounts{mu: &sync.Mutex{}, n: map[string]int{}, sentTo: map[string]int{},
		restores: &[]restore{}}
}

func (c runCounts) Enabled(zapcore.Level) bool        { return true }
func (c runCounts) With([]zapcore.Field) zapcore.Core { return c }
func (c runCounts) Sync() error                       { return nil }

func (c runCounts) Check(e zapcore.Entry, ce *zapcore.CheckedEntry) *zapcore.CheckedEntry {
	return ce.AddCore(e, c)
}

// parseRestore parses raft's "<id> [commit: c] restored snapshot [index: i, term: t]".
func parseRestore(msg string) (restore, bool) {
	sp := strings.IndexByte(msg, ' ')
	k := strings.Index(msg, "[index: ")
	if sp < 0 || k < 0 {
		return restore{}, false
	}
	rest := msg[k+len("[index: "):]
	e := strings.IndexByte(rest, ',')
	if e < 0 {
		return restore{}, false
	}
	i, err := strconv.ParseUint(rest[:e], 10, 64)
	if err != nil {
		return restore{}, false
	}
	return restore{member: msg[:sp], index: i}, true
}

func (c runCounts) Write(e zapcore.Entry, fs []zapcore.Field) error {
	// raft logs a restore twice, in restore ("<id> [commit: c, lastindex: l, lastterm: t] restored
	// snapshot [...]") and in handleSnapshot ("<id> [commit: c] restored snapshot [...]"): the
	// latter is counted
	if strings.Contains(e.Message, cntRaftRestore) && strings.Contains(e.Message, "lastindex") {
		return nil
	}
	c.mu.Lock()
	defer c.mu.Unlock()
	for _, k := range []string{cntSnapSent, cntSnapApplied, cntLeaseRestore, cntRaftRestore} {
		if strings.Contains(e.Message, k) {
			c.n[k]++
		}
	}
	if strings.Contains(e.Message, cntSnapSent) {
		for _, f := range fs {
			if f.Key == "to" {
				c.sentTo[f.String]++
			}
		}
	}
	if strings.Contains(e.Message, cntRaftRestore) {
		if r, ok := parseRestore(e.Message); ok {
			*c.restores = append(*c.restores, r)
		}
	}
	return nil
}

// memberIDs returns the ids etcd computes for config's members (from the peer URLs and the token),
// in member order, as types.ID prints them.
func memberIDs(t *testing.T) []string {
	cfg := config()
	urls, err := types.NewURLsMap(cfg.Name1 + "=http://" + cfg.Peer1 + "," + cfg.Name2 + "=http://" +
		cfg.Peer2 + "," + cfg.Name3 + "=http://" + cfg.Peer3)
	if err != nil {
		t.Fatal(err)
	}
	cl, err := membership.NewClusterFromURLsMap(zap.NewNop(), cfg.Token, urls)
	if err != nil {
		t.Fatal(err)
	}
	ids := make([]string, 3)
	for _, id := range cl.MemberIDs() {
		for i, name := range []string{cfg.Name1, cfg.Name2, cfg.Name3} {
			if cl.Member(id).Name == name {
				ids[i] = id.String()
			}
		}
	}
	return ids
}

// TestMemberIDs checks the premise on the member ids etcd computes for Main's cluster
// (examples/etcd/partition's TestMemberIDs): their 16 low bits are distinct and not 0.
func TestMemberIDs(t *testing.T) {
	seen := map[uint64]bool{}
	for i, s := range memberIDs(t) {
		id, err := strconv.ParseUint(s, 16, 64)
		if err != nil {
			t.Fatal(err)
		}
		low := id & 0xffff
		t.Logf("member %d: id %s, low 16 bits %#x", i+1, s, low)
		if low == 0 || seen[low] {
			t.Fatalf("member %d: low 16 bits %#x zero or repeated", i+1, low)
		}
		seen[low] = true
	}
}

// TestMainRun runs Main's body (run) for real, in a fresh directory (the members' DataDirs are
// relative), with a logger that records what the members did, where Main has none. Its check must
// pass (no panic), and member 3 must have listed the last filler (run returns Checked). Then it
// reports the counts, and fails if the run did not test what it is meant to: a snapshot sent to
// member 3, raft on member 3 restoring a snapshot that holds the fillers (its index above the
// fillers' count: the log before the cut is shorter), and member 3 restoring a lease store from a
// snapshot (etcd's message names no member: more restores than snapshots sent to the others).
//
// Why fillers grants suffice: with SnapCount 1 the leader takes a disk snapshot every second
// applied entry and then compacts raft's log to SnapCatchUp (1) entry below it, so two applied
// fillers past member 3's index compact it out, and the leader must send a snapshot -- unless a
// snapshot it sent earlier (to a member that lagged at the start) is in flight or within its 30s
// releaseDelayAfterSnapshot, which pauses compaction ("skip compaction since there is an inflight
// snapshot"); the fillers are applied well within that window then. The report says how often the
// leader sent which member a snapshot.
func TestMainRun(t *testing.T) {
	t.Chdir(t.TempDir())
	ids := memberIDs(t)
	rc := newRunCounts()
	start := time.Now()
	r := run(zap.New(rc))
	t.Logf("run took %v, result %d", time.Since(start), r)
	// run returns once member 3's lessor is recovered; applySnapshot logs "applied snapshot" when it
	// ends, after the KV store's restore: wait (bounded) for it
	for i := 0; i < 50; i++ {
		rc.mu.Lock()
		done := rc.n[cntSnapApplied] >= rc.n[cntLeaseRestore]
		rc.mu.Unlock()
		if done {
			break
		}
		time.Sleep(100 * time.Millisecond)
	}
	rc.mu.Lock()
	defer rc.mu.Unlock()
	var sent []string
	for i, id := range ids {
		sent = append(sent, fmt.Sprintf("member %d (%s): %d", i+1, id, rc.sentTo[id]))
	}
	var rs []string
	maxIdx3 := uint64(0)
	for _, x := range *rc.restores {
		m := "?"
		for i, id := range ids {
			if id == x.member {
				m = strconv.Itoa(i + 1)
			}
		}
		rs = append(rs, fmt.Sprintf("member %s at %d", m, x.index))
		if x.member == ids[2] && x.index > maxIdx3 {
			maxIdx3 = x.index
		}
	}
	t.Logf("counts: %q %d (%s); %q %d; %q %d; raft restores %d [%s]",
		cntSnapSent, rc.n[cntSnapSent], strings.Join(sent, ", "),
		cntSnapApplied, rc.n[cntSnapApplied], cntLeaseRestore, rc.n[cntLeaseRestore],
		rc.n[cntRaftRestore], strings.Join(rs, ", "))
	if r != Checked {
		t.Fatalf("run returned %d, want %d (Checked)", r, Checked)
	}
	if rc.sentTo[ids[2]] == 0 {
		t.Errorf("no snapshot was sent to member 3")
	}
	if maxIdx3 <= fillers {
		t.Errorf("member 3 restored no snapshot holding the fillers (highest index %d, fillers %d)",
			maxIdx3, fillers)
	}
	// a member restores a lease store only from a snapshot sent to it: more restores than
	// snapshots sent to members 1 and 2 means member 3 restored one
	if rc.n[cntLeaseRestore] <= rc.sentTo[ids[0]]+rc.sentTo[ids[1]] {
		t.Errorf("member 3 restored no lease store (%d restores, %d snapshots sent to the others)",
			rc.n[cntLeaseRestore], rc.sentTo[ids[0]]+rc.sentTo[ids[1]])
	}
}
