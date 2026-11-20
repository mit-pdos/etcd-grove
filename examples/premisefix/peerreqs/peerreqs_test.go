// Package peerreqs is the evidence for part (b) of the closed-world clause of addrsUnclaimed
// (Proof/runtime/Start.lean), netAddrFree/netListenerAt (Proof/net/InvNet.lean) and
// net.Listen.wp_proof (Proof/net/Listen.lean), http-boundary-fix, 2026-11-14 (the independent
// review's blocker, from its scratch test): in a three-member etcdstart cluster (putget3's
// shape), the peer handlers receive, besides rafthttp's own requests, etcd's names-only peer
// requests: the prober's GET /raft/probing (answered 200 by probing.NewHandler) and the version
// monitor's GET /version (answered 404 by the RaftHandler's mux, which routes only /raft,
// /raft/stream/, /raft/snapshot and /raft/probing). Every request comes from the program itself.
package peerreqs

import (
	"net"
	"net/http"
	"sync"
	"testing"
	"time"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/walarea"
)

type statusRec struct {
	http.ResponseWriter
	st int
}

func (s *statusRec) WriteHeader(c int) { s.st = c; s.ResponseWriter.WriteHeader(c) }
func (s *statusRec) Flush() {
	if f, ok := s.ResponseWriter.(http.Flusher); ok {
		f.Flush()
	}
}

func TestPeerRequests(t *testing.T) {
	t.Chdir(t.TempDir())        // the members' data directories
	walarea.ResetFamily(t, "p") // the members' WAL areas (wal-link P2)
	lg := zap.NewNop()
	// the peer listeners first, each on a port the kernel picks, kept open until served: no port
	// fixed in advance (33811-33813 were, in the ephemeral range: another process's connection
	// could hold one, "bind: address already in use", 2026-11-17), none closed and re-taken
	lis := make([]net.Listener, 3)
	addrs := make([]string, 3)
	for i := range lis {
		l, err := net.Listen("tcp", "127.0.0.1:0")
		if err != nil {
			t.Fatal(err)
		}
		lis[i] = l
		addrs[i] = l.Addr().String()
	}
	names := []string{"p-1", "p-2", "p-3"}
	cluster := types.URLsMap{}
	peers := make([]types.URLs, 3)
	for i := range addrs {
		peers[i] = types.URLs{{Scheme: "http", Host: addrs[i]}}
		cluster[names[i]] = peers[i]
	}
	var mu sync.Mutex
	seen := map[string]map[int]int{}
	for i := range addrs {
		s, err := etcdstart.BuildServer(names[i], peers[i], "127.0.0.1:3382"+string(rune('1'+i)), cluster, "p",
			etcdstart.NoSnapCount, etcdstart.NoSnapCatchUp, lg)
		if err != nil {
			t.Fatal(err)
		}
		l := lis[i]
		h := s.RaftHandler()
		go http.Serve(l, http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			rec := &statusRec{ResponseWriter: w, st: 200}
			h.ServeHTTP(rec, r)
			k := r.Method + " " + r.URL.Path
			if len(r.URL.Path) > len("/raft/stream/") && r.URL.Path[:len("/raft/stream/")] == "/raft/stream/" {
				k = r.Method + " /raft/stream/..."
			}
			mu.Lock()
			if seen[k] == nil {
				seen[k] = map[int]int{}
			}
			seen[k][rec.st]++
			mu.Unlock()
		}))
		s.Start()
		defer s.Stop()
	}
	time.Sleep(8 * time.Second)
	mu.Lock()
	defer mu.Unlock()
	t.Logf("requests (method path: status: count): %v", seen)
	for k, sts := range seen {
		switch k {
		case "GET /version", "GET /members":
			for st := range sts {
				if st != 404 {
					t.Errorf("%s answered %d, want the mux's 404", k, st)
				}
			}
		case "GET /raft/probing", "GET /raft/stream/...", "POST /raft", "POST /raft/snapshot":
		default:
			t.Errorf("unexpected peer request %s", k)
		}
	}
	if len(seen["GET /raft/probing"]) == 0 {
		t.Errorf("no prober request seen")
	}
}
