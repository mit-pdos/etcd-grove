// Package restart3probe is a scratch probe for notes/restart3-scope.md (not committed): restart3's
// shape (three members, a follower stopped and started again in place) under a snapshot setting
// chosen by $PROBE_CFG, counting what the members log and which incarnation's raft handler
// serves each peer request.
//
//	A  SnapCount 1,       CatchUp 1        (restart3's settings: snapshots and compaction)
//	B1 SnapCount 1,       CatchUp MaxUint64 (disk snapshots, raft log compacted at index 1 only)
//	B0 SnapCount MaxUint64, CatchUp MaxUint64 (no disk snapshot by count, compaction at 1 only)
package restart3probe

import (
	"context"
	"fmt"
	"math"
	"net"
	"net/http"
	"os"
	"sort"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"

	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/walarea"
)

const (
	peerAddr1   = "127.0.0.1:25731"
	peerAddr2   = "127.0.0.1:25732"
	peerAddr3   = "127.0.0.1:25733"
	clientAddr1 = "127.0.0.1:25734"
	clientAddr2 = "127.0.0.1:25735"
	clientAddr3 = "127.0.0.1:25736"
	NBoot       = 3
	NPre        = 5
	NDown       = 150 // > memorySnapshotCount (100): a memory snapshot and a compaction happen
)

// gen counts the requests one incarnation's raft handler serves, by path prefix, before and after
// its listener was closed.
type gen struct {
	closed atomic.Bool
	mu     sync.Mutex
	before map[string]int
	after  map[string]int
}

func newGen() *gen { return &gen{before: map[string]int{}, after: map[string]int{}} }

func pathKey(p string) string {
	switch {
	case strings.HasPrefix(p, "/raft/stream/"):
		return "stream"
	case p == "/raft/snapshot":
		return "snapshot"
	case p == "/raft/probing":
		return "probing"
	case p == "/raft":
		return "pipeline"
	}
	return p
}

func (g *gen) wrap(h http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		k := pathKey(r.URL.Path)
		g.mu.Lock()
		if g.closed.Load() {
			g.after[k]++
		} else {
			g.before[k]++
		}
		g.mu.Unlock()
		h.ServeHTTP(w, r)
	})
}

func (g *gen) String() string {
	g.mu.Lock()
	defer g.mu.Unlock()
	return fmt.Sprintf("before close %v, after close %v", g.before, g.after)
}

type member struct {
	s  *etcdserver.EtcdServer
	pl net.Listener
	g  *gen
}

func startMember(name string, peer types.URLs, peerAddr, client string, cluster types.URLsMap,
	snapCount, catchUp uint64, lg *zap.Logger) (*member, error) {
	s, err := etcdstart.BuildServer(name, peer, client, cluster, "probe3", snapCount, catchUp, lg)
	if err != nil {
		return nil, err
	}
	pl, err := net.Listen("tcp", peerAddr)
	if err != nil {
		return nil, err
	}
	g := newGen()
	go http.Serve(pl, g.wrap(s.RaftHandler()))
	s.Start()
	return &member{s: s, pl: pl, g: g}, nil
}

// counts: messages and some fields, before and after the restart's first message.
type counts struct {
	mu        *sync.Mutex
	restarted *bool
	before    map[string]int
	after     map[string]int
	fields    map[string][]string
}

var keys = []string{"restarting local member", "constructed a snapshot from WAL record",
	"sending merged snapshot", "applied snapshot", "compacted Raft logs", "saved snapshot to disk",
	"receiving database snapshot", "failed to process Raft message"}

func (c counts) Enabled(zapcore.Level) bool        { return true }
func (c counts) With([]zapcore.Field) zapcore.Core { return c }
func (c counts) Sync() error                       { return nil }
func (c counts) Check(e zapcore.Entry, ce *zapcore.CheckedEntry) *zapcore.CheckedEntry {
	return ce.AddCore(e, c)
}
func (c counts) Write(e zapcore.Entry, fs []zapcore.Field) error {
	c.mu.Lock()
	defer c.mu.Unlock()
	if strings.Contains(e.Message, "restarting local member") ||
		strings.Contains(e.Message, "constructed a snapshot from WAL record") {
		*c.restarted = true
	}
	for _, k := range keys {
		if strings.Contains(e.Message, k) {
			if *c.restarted {
				c.after[k]++
			} else {
				c.before[k]++
			}
			for _, f := range fs {
				if f.Key == "compact-index" || f.Key == "snapshot-index" {
					tag := "pre"
					if *c.restarted {
						tag = "post"
					}
					c.fields[k] = append(c.fields[k], fmt.Sprintf("%s:%d", tag, f.Integer))
				}
			}
		}
	}
	return nil
}

func uniq(xs []string) []string {
	m := map[string]bool{}
	for _, x := range xs {
		m[x] = true
	}
	out := []string{}
	for x := range m {
		out = append(out, x)
	}
	sort.Strings(out)
	return out
}

func put(cli *clientv3.Client, k, v string) error {
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	_, err := cli.Put(ctx, k, v)
	cancel()
	return err
}

func TestProbe(t *testing.T) {
	cfg := os.Getenv("PROBE_CFG")
	var snapCount, catchUp uint64
	switch cfg {
	case "A":
		snapCount, catchUp = 1, 1
	case "B1":
		snapCount, catchUp = 1, math.MaxUint64
	case "B0":
		snapCount, catchUp = math.MaxUint64, math.MaxUint64
	default:
		t.Skip("PROBE_CFG unset")
	}
	t.Chdir(t.TempDir())
	walarea.Reset(t, "p3-1", "p3-2", "p3-3") // the members' WAL areas (wal-link P2)
	c := counts{mu: &sync.Mutex{}, restarted: new(bool), before: map[string]int{},
		after: map[string]int{}, fields: map[string][]string{}}
	lg := zap.New(c)

	peer1 := types.URLs{{Scheme: "http", Host: peerAddr1}}
	peer2 := types.URLs{{Scheme: "http", Host: peerAddr2}}
	peer3 := types.URLs{{Scheme: "http", Host: peerAddr3}}
	cluster := types.URLsMap{"p3-1": peer1, "p3-2": peer2, "p3-3": peer3}
	m1, err := startMember("p3-1", peer1, peerAddr1, clientAddr1, cluster, snapCount, catchUp, lg)
	if err != nil {
		t.Fatal(err)
	}
	m2, err := startMember("p3-2", peer2, peerAddr2, clientAddr2, cluster, snapCount, catchUp, lg)
	if err != nil {
		t.Fatal(err)
	}
	m3, err := startMember("p3-3", peer3, peerAddr3, clientAddr3, cluster, snapCount, catchUp, lg)
	if err != nil {
		t.Fatal(err)
	}
	if err := etcdstart.Serve(m1.s, clientAddr1); err != nil {
		t.Fatal(err)
	}
	cli, err := etcdstart.NewClient(clientAddr1, lg)
	if err != nil {
		t.Fatal(err)
	}
	for i := 0; i < NPre; i++ {
		if err := put(cli, fmt.Sprintf("k%03d", i), "v"); err != nil {
			t.Fatal(err)
		}
	}
	m, name, peer, peerAddr, client := m3, "p3-3", peer3, peerAddr3, clientAddr3
	if m3.s.Leader() == m3.s.MemberID() {
		m, name, peer, peerAddr, client = m2, "p3-2", peer2, peerAddr2, clientAddr2
	}
	for m.s.AppliedIndex() < NBoot {
		time.Sleep(time.Millisecond)
	}
	m.s.HardStop()
	m.g.closed.Store(true)
	m.pl.Close()
	for i := NPre; i < NPre+NDown; i++ {
		if err := put(cli, fmt.Sprintf("k%03d", i), "v"); err != nil {
			t.Fatal(err)
		}
	}
	mR, err := startMember(name, peer, peerAddr, client, cluster, snapCount, catchUp, lg)
	if err != nil {
		t.Fatal(err)
	}
	if err := etcdstart.Serve(mR.s, client); err != nil {
		t.Fatal(err)
	}
	cliR, err := etcdstart.NewClient(client, lg)
	if err != nil {
		t.Fatal(err)
	}
	var resp *clientv3.GetResponse
	for try := 0; try < 20; try++ {
		ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
		resp, err = cliR.Get(ctx, "k", clientv3.WithPrefix())
		cancel()
		if err == nil {
			break
		}
		time.Sleep(100 * time.Millisecond)
	}
	if err != nil {
		t.Fatal(err)
	}
	time.Sleep(2 * time.Second) // let the old incarnation's kept connections show
	n := len(resp.Kvs)
	okv := true
	for _, kv := range resp.Kvs {
		if kv.Version != 1 {
			okv = false
		}
	}
	t.Logf("cfg %s: restarted %s; range %d pairs (want %d), all version 1: %v, revision %d (want %d)",
		cfg, name, n, NPre+NDown, okv, resp.Header.Revision, 1+NPre+NDown)
	c.mu.Lock()
	t.Logf("log before restart: %v", c.before)
	t.Logf("log from restart on: %v", c.after)
	for k, v := range c.fields {
		t.Logf("fields %q: %v", k, uniq(v))
	}
	c.mu.Unlock()
	t.Logf("old incarnation's raft handler: %v", m.g)
	t.Logf("new incarnation's raft handler: %v", mR.g)
	if n != NPre+NDown || !okv || resp.Header.Revision != int64(1+NPre+NDown) {
		t.Errorf("check failed")
	}
}
