// Package bootstrapdist is the Go evidence for the interim axiom bootstrap.wp_proof_dist
// (Proof/go_etcd_io/etcd/server/v3/etcdserver/bootstrapDist.lean, statement bootstrap.specDist):
// etcdserver's bootstrap, through NewServer, at etcd_safe's deployment shape (every member one peer
// URL http://addr and one client URL, a static initial cluster of every member's peer URL, a new
// cluster, a fresh data directory), at the etcd pin e94f33b50 (examples/go.mod).
//
// What it shows:
//   - TestBootThreeMembers: three members boot. Member a boots first, its peers unreachable
//     (isMemberBootstrapped's GETs are refused: it answers false and the boot goes on); then a's peer
//     handler (etcdhttp.NewPeerHandler) is served on a's peer address, and b and c boot, each sending
//     GET /members to a (counted) and getting a's member list, in which they have no client URL yet.
//   - TestBootPeerHangs: a peer accepts the connection and never answers: isMemberBootstrapped's GET
//     times out (the bootstrap timeout), it answers false and the boot goes on.
//   - TestBootErrors: bootstrap returns an error, without panicking, when its data directory cannot
//     be made (a regular file at the path), and when a peer's /members lists this member with client
//     URLs ("has already been bootstrapped": what a real peer answers once this member published).
//     The second case serves the peer's answer from a stand-in handler.
//
// Run with TMPDIR on a disk (each WAL preallocates 64 MB; a small /tmp quota makes wal.Create fail,
// and bootstrapNewWAL panics on that I/O error, which the file extension's no-error semantics excludes):
//
//	TMPDIR=/some/disk/dir go test ./axiomcx/bootstrapdist/ -v
//
// (BOOTDIST_LOG=1 logs etcd's messages.)
package bootstrapdist

import (
	"encoding/json"
	"net"
	"net/http"
	"os"
	"path/filepath"
	"strings"
	"sync/atomic"
	"testing"
	"time"

	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/etcdhttp"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.etcd.io/etcd/server/v3/features"
)

const token = "bootstrapdist"

// freeAddr returns a local address nothing listens on (the listener closed).
func freeAddr(t *testing.T) string {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	a := l.Addr().String()
	l.Close()
	return a
}

// cfgFor is etcdstart.newServer's configuration for member name of the cluster cl (one peer URL each),
// with its client address client, its data directory under dir.
func cfgFor(dir, name, client string, cl types.URLsMap) config.ServerConfig {
	lg := zap.NewNop()
	if os.Getenv("BOOTDIST_LOG") != "" {
		lg, _ = zap.NewDevelopment()
	}
	return config.ServerConfig{
		Name:                   name,
		DataDir:                filepath.Join(dir, name+".etcd"),
		InitialPeerURLsMap:     cl,
		PeerURLs:               cl[name],
		ClientURLs:             types.URLs{{Scheme: "http", Host: client}},
		InitialClusterToken:    token,
		NewCluster:             true,
		TickMs:                 100,
		ElectionTicks:          10,
		SnapshotCount:          etcdserver.DefaultSnapshotCount,
		SnapshotCatchUpEntries: 1 << 48,
		MaxTxnOps:              128,
		MaxRequestBytes:        1536 * 1024,
		AutoCompactionMode:     "revision",
		BootstrapTimeout:       2 * time.Second,
		Logger:                 lg,
		ServerFeatureGate:      features.NewDefaultServerFeatureGate(name, lg),
	}
}

func cluster(peers map[string]string) types.URLsMap {
	cl := types.URLsMap{}
	for n, a := range peers {
		cl[n] = types.URLs{{Scheme: "http", Host: a}}
	}
	return cl
}

func TestBootThreeMembers(t *testing.T) {
	dir := t.TempDir()
	peers := map[string]string{"a": freeAddr(t), "b": freeAddr(t), "c": freeAddr(t)}
	cl := cluster(peers)

	// a: its peers unreachable
	sa, err := etcdserver.NewServer(cfgFor(dir, "a", freeAddr(t), cl))
	if err != nil {
		t.Fatalf("a: NewServer: %v", err)
	}
	t.Logf("a booted, id %s, peers unreachable", sa.MemberID())

	// a's peer handler on a's peer address, counting the GET /members it serves
	var gets atomic.Int64
	ph := etcdhttp.NewPeerHandler(zap.NewNop(), sa)
	l, err := net.Listen("tcp", peers["a"])
	if err != nil {
		t.Fatal(err)
	}
	srv := &http.Server{Handler: http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.Method == http.MethodGet && r.URL.Path == "/members" {
			gets.Add(1)
		}
		ph.ServeHTTP(w, r)
	})}
	go srv.Serve(l)
	defer srv.Close()

	for _, n := range []string{"b", "c"} {
		before := gets.Load()
		s, err := etcdserver.NewServer(cfgFor(dir, n, freeAddr(t), cl))
		if err != nil {
			t.Fatalf("%s: NewServer: %v", n, err)
		}
		if gets.Load() == before {
			t.Fatalf("%s: bootstrap sent no GET /members to a", n)
		}
		t.Logf("%s booted, id %s, after %d GET /members served by a", n, s.MemberID(), gets.Load()-before)
	}
}

func TestBootErrors(t *testing.T) {
	// the data directory a regular file
	dir := t.TempDir()
	peers := map[string]string{"a": freeAddr(t), "b": freeAddr(t), "c": freeAddr(t)}
	cl := cluster(peers)
	cfg := cfgFor(dir, "a", freeAddr(t), cl)
	if err := os.WriteFile(cfg.DataDir, []byte("x"), 0o600); err != nil {
		t.Fatal(err)
	}
	_, err := etcdserver.NewServer(cfg)
	if err == nil {
		t.Fatalf("data directory a file: NewServer succeeded")
	}
	t.Logf("data directory a file: NewServer returned %v", err)

	// a peer lists this member with client URLs
	dir2 := t.TempDir()
	cfg2 := cfgFor(dir2, "a", freeAddr(t), cl)
	rcl, err := membership.NewClusterFromURLsMap(zap.NewNop(), token, cl)
	if err != nil {
		t.Fatal(err)
	}
	var membs []*membership.Member
	for _, m := range rcl.Members() {
		if m.Name == "a" {
			m.ClientURLs = []string{"http://" + freeAddr(t)}
		}
		membs = append(membs, m)
	}
	body, err := json.Marshal(membs)
	if err != nil {
		t.Fatal(err)
	}
	l, err := net.Listen("tcp", peers["b"])
	if err != nil {
		t.Fatal(err)
	}
	srv := &http.Server{Handler: http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("X-Etcd-Cluster-ID", rcl.ID().String())
		w.Header().Set("Content-Type", "application/json")
		w.Write(body)
	})}
	go srv.Serve(l)
	defer srv.Close()
	_, err = etcdserver.NewServer(cfg2)
	if err == nil || !strings.Contains(err.Error(), "already been bootstrapped") {
		t.Fatalf("published member: NewServer returned %v", err)
	}
	t.Logf("published member: NewServer returned %v", err)
}

func TestBootPeerHangs(t *testing.T) {
	dir := t.TempDir()
	peers := map[string]string{"a": freeAddr(t), "b": freeAddr(t), "c": freeAddr(t)}
	cl := cluster(peers)
	// b's peer address accepts and never answers
	l, err := net.Listen("tcp", peers["b"])
	if err != nil {
		t.Fatal(err)
	}
	defer l.Close()
	go func() {
		for {
			c, err := l.Accept()
			if err != nil {
				return
			}
			defer c.Close()
		}
	}()
	start := time.Now()
	s, err := etcdserver.NewServer(cfgFor(dir, "a", freeAddr(t), cl))
	if err != nil {
		t.Fatalf("a: NewServer: %v", err)
	}
	t.Logf("a booted, id %s, after %v with b hanging", s.MemberID(), time.Since(start))
}
