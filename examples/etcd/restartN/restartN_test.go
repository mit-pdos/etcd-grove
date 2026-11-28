package restartN

import (
	"fmt"
	"math/rand"
	"net"
	"os"
	"strconv"
	"strings"
	"sync"
	"testing"
	"time"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/walarea"
)

// maxMembers is the bound of the theorem's member count.
const maxMembers = 1000

// idMembers is the member count up to which TestMemberIDs checks the ids (at Token): etcd_safe's
// bound on this cluster (examples/etcd/all, whose TestMemberIDs checks them also against its other
// clusters' ids). Above it the theorem's premises on the ids are not checked, and may be false.
const idMembers = 300

// idsOf returns the member ids etcd computes for Main(k)'s cluster at the token token (from the peer
// URLs and the token, as bootstrap does), without starting it.
func idsOf(t *testing.T, token string, k uint64) []types.ID {
	ms := etcdstart.Members("restartN", k, PeerBase, ClientBase)
	urls := types.URLsMap{}
	for _, m := range ms {
		u, err := types.NewURLs([]string{"http://" + m.Peer})
		if err != nil {
			t.Fatal(err)
		}
		urls[m.Name] = u
	}
	cl, err := membership.NewClusterFromURLsMap(zap.NewNop(), token, urls)
	if err != nil {
		t.Fatal(err)
	}
	return cl.MemberIDs()
}

// idsOk reports whether the ids' 16 low bits are distinct and not 0 (BootCore, D21e (A)).
func idsOk(ids []types.ID) bool {
	seen := map[uint64]bool{}
	for _, id := range ids {
		low := uint64(id) & 0xffff
		if low == 0 || seen[low] {
			return false
		}
		seen[low] = true
	}
	return true
}

// TestMemberIDs checks the theorem's premise on the member ids (BootCore: their 16 low bits distinct
// and not 0, D21e (A)) for every member count 1 <= k <= idMembers, from the ids etcd computes for
// Main(k)'s cluster at Token. It starts no cluster. (The ids of a cluster of k members are those of
// the first k members of a larger one, so the check at idMembers implies the others; every k is
// checked anyway.)
func TestMemberIDs(t *testing.T) {
	for k := uint64(1); k <= idMembers; k++ {
		ids := idsOf(t, Token, k)
		if uint64(len(ids)) != k {
			t.Fatalf("k=%d: %d ids", k, len(ids))
		}
		if !idsOk(ids) {
			t.Fatalf("k=%d: the ids' low 16 bits are zero or repeated", k)
		}
	}
}

// TestFindToken (run with RESTARTN_FIND_TOKEN=1) prints the first "restartN-<i>" at which the ids
// of the idMembers-member cluster pass TestMemberIDs' check.
func TestFindToken(t *testing.T) {
	if os.Getenv("RESTARTN_FIND_TOKEN") == "" {
		t.Skip("set RESTARTN_FIND_TOKEN=1")
	}
	for i := 0; ; i++ {
		tok := "restartN-" + strconv.Itoa(i)
		if idsOk(idsOf(t, tok, idMembers)) {
			t.Logf("token %s", tok)
			return
		}
	}
}

// The events counted, each by the message etcd logs for it (restart3's). Those from the restart on are
// counted apart: the restart begins with the first message only a member booting from its WAL logs.
const (
	cntRestart   = "restarting local member"
	cntWALSnap   = "constructed a snapshot from WAL record"
	cntSkipSnap  = "Skipping snapshot backend"
	cntRecSnap   = "Recovering from snapshot backend"
	cntNoWALSnap = "No snapshot found. Recovering WAL from scratch"
	cntSaveSnap  = "saved snapshot"
	cntSnapSent  = "sending merged snapshot"
	cntSnapDone  = "applied snapshot"
	cntCompact   = "compacted Raft logs"
)

// cntBootCluster is what bootstrap logs right before bootstrapCluster (bootstrap.go:92), whose first-start
// branch sends GET /members to every other member's peer URL (isMemberBootstrapped).
const cntBootCluster = "bootstrapping cluster"

var cntEvents = []string{cntRestart, cntWALSnap, cntSkipSnap, cntRecSnap, cntNoWALSnap, cntSaveSnap,
	cntSnapSent, cntSnapDone, cntCompact}

// counts is a zap core that logs nothing and counts the messages of cntEvents, at every level,
// before and after the restart, and keeps the integer fields of the last such message after it. At
// each first boot's cntBootCluster (before the restart) it dials every peer address of peers and
// counts the boots (probes) and the addresses that accepted (served).
type counts struct {
	mu        *sync.Mutex
	restarted *bool
	before    map[string]int
	after     map[string]int
	fields    map[string]map[string]int64
	peers     []string
	probes    *int
	served    *int
}

func newCounts(peers []string) counts {
	return counts{mu: &sync.Mutex{}, restarted: new(bool), before: map[string]int{},
		after: map[string]int{}, fields: map[string]map[string]int64{}, peers: peers,
		probes: new(int), served: new(int)}
}

// probe dials every peer address and returns how many accepted.
func (c counts) probe() int {
	n := 0
	for _, a := range c.peers {
		conn, err := net.DialTimeout("tcp", a, time.Second)
		if err == nil {
			n++
			conn.Close()
		}
	}
	return n
}

func (c counts) Enabled(zapcore.Level) bool        { return true }
func (c counts) With([]zapcore.Field) zapcore.Core { return c }
func (c counts) Sync() error                       { return nil }

func (c counts) Check(e zapcore.Entry, ce *zapcore.CheckedEntry) *zapcore.CheckedEntry {
	return ce.AddCore(e, c)
}

func (c counts) Write(e zapcore.Entry, fs []zapcore.Field) error {
	if e.Message == cntBootCluster {
		c.mu.Lock()
		first := !*c.restarted
		c.mu.Unlock()
		if first {
			n := c.probe()
			c.mu.Lock()
			*c.probes++
			*c.served += n
			c.mu.Unlock()
		}
	}
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

// TestRun runs Run once with k members, in a fresh directory (the members' DataDirs are relative), with
// a logger that counts what the members did, and fails unless Run's check ran (it panics if it fails)
// and the run tested what it is meant to: each of the k first boots ran while no peer address accepted
// a connection (so its GET /members found no listener); disk snapshots taken before the stop; exactly one member
// restarted from its WAL, which held a snapshot record above index 0; its WAL's commit index at least
// the bootstrap entries (k) plus the Puts before the stop; raft's log compacted; and the snapshot
// catch-up: a merged snapshot sent and a snapshot installed after the restart. k is RESTARTN_MEMBERS
// if set, else chosen at random from {3, 5, 7}. Each run needs its own process (go test -c, then the
// binary once per run): Run leaves the members running.
func TestRun(t *testing.T) {
	k := uint64([]int{3, 5, 7}[rand.Intn(3)])
	if s := os.Getenv("RESTARTN_MEMBERS"); s != "" {
		v, err := strconv.ParseUint(s, 10, 64)
		if err != nil {
			t.Fatal(err)
		}
		k = v
	}
	t.Logf("k = %d", k)
	t.Chdir(t.TempDir())
	walarea.ResetFamily(t, "restartN") // the members' WAL areas (wal-link P2)
	var peers []string
	for _, m := range etcdstart.Members("restartN", k, PeerBase, ClientBase) {
		peers = append(peers, m.Peer)
	}
	c := newCounts(peers)
	start := time.Now()
	ok := Run(k, zap.New(c))
	t.Logf("Run took %v", time.Since(start))
	t.Log(c.report())
	if !ok {
		t.Fatalf("Run returned before its check")
	}
	c.mu.Lock()
	probes, served := *c.probes, *c.served
	c.mu.Unlock()
	t.Logf("first boots probed: %d, peer addresses accepting at them: %d", probes, served)
	if probes != int(k) {
		t.Errorf("%d first boots logged %q, not k = %d", probes, cntBootCluster, k)
	}
	if served != 0 {
		t.Errorf("a first boot found %d peer addresses accepting connections", served)
	}
	if c.get(false, cntSaveSnap) == 0 {
		t.Errorf("no disk snapshot taken before the stop")
	}
	if c.get(true, cntRestart) != 1 {
		t.Errorf("not exactly one member restarted from its WAL")
	}
	if c.get(true, cntWALSnap) != 1 || c.get(true, cntNoWALSnap) != 0 {
		t.Errorf("the restarted member's WAL held no snapshot")
	}
	si, ok1 := c.field(cntWALSnap, "snapshot-index")
	if !ok1 || si <= 0 {
		t.Errorf("the WAL's snapshot is at index %d (found: %v), not above 0", si, ok1)
	}
	ri, ok3 := c.field(cntRestart, "commit-index")
	if !ok3 || ri < int64(k)+N1 {
		t.Errorf("the WAL's commit index %d (found: %v) is below k + N1 = %d", ri, ok3, int64(k)+N1)
	}
	if c.get(true, cntCompact) == 0 && c.get(false, cntCompact) == 0 {
		t.Errorf("raft's log never compacted")
	}
	if c.get(true, cntSnapSent) == 0 || c.get(true, cntSnapDone) == 0 {
		t.Errorf("no snapshot catch-up after the restart: merged snapshots sent %d, installed %d",
			c.get(true, cntSnapSent), c.get(true, cntSnapDone))
	}
	t.Logf("after the restart: merged snapshots sent %d, snapshots installed %d, backend kept %d, "+
		"backend recovered from a snapshot %d", c.get(true, cntSnapSent), c.get(true, cntSnapDone),
		c.get(true, cntSkipSnap), c.get(true, cntRecSnap))
}
