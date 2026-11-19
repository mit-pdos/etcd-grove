package authN

import (
	"context"
	"errors"
	"math/rand"
	"os"
	"strconv"
	"testing"
	"time"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/etcd/auth"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/walarea"
)

// maxMembers is the bound of etcd_authN_safe's member count.
const maxMembers = 1000

// idsOf returns the member ids etcd computes for Main(k)'s cluster (from the peer URLs and the
// cluster token, as bootstrap does), without starting it.
func idsOf(t *testing.T, k uint64) []types.ID {
	ms := etcdstart.Members("authN", k, PeerBase, ClientBase)
	urls := types.URLsMap{}
	for _, m := range ms {
		u, err := types.NewURLs([]string{"http://" + m.Peer})
		if err != nil {
			t.Fatal(err)
		}
		urls[m.Name] = u
	}
	cl, err := membership.NewClusterFromURLsMap(zap.NewNop(), Token, urls)
	if err != nil {
		t.Fatal(err)
	}
	return cl.MemberIDs()
}

// TestMemberIDs checks etcd_authN_safe's premise on the member ids (BootCore: their 16 low bits
// distinct and not 0) for every member count 1 <= k <= maxMembers, from the ids etcd computes for
// Main(k)'s cluster. It starts no cluster.
func TestMemberIDs(t *testing.T) {
	for k := uint64(1); k <= maxMembers; k++ {
		ids := idsOf(t, k)
		if uint64(len(ids)) != k {
			t.Fatalf("k=%d: %d ids", k, len(ids))
		}
		seen := map[uint64]bool{}
		for _, id := range ids {
			low := uint64(id) & 0xffff
			if low == 0 || seen[low] {
				t.Fatalf("k=%d: member %x: low 16 bits %#x zero or repeated", k, uint64(id), low)
			}
			seen[low] = true
		}
	}
}

// TestMembers checks Main's members' names and addresses at k = 3.
func TestMembers(t *testing.T) {
	ms := etcdstart.Members("authN", 3, PeerBase, ClientBase)
	want := []etcdstart.Member{
		{Name: "authN-0", Peer: "127.0.0.1:29000", Client: "127.0.0.1:30000"},
		{Name: "authN-1", Peer: "127.0.0.1:29001", Client: "127.0.0.1:30001"},
		{Name: "authN-2", Peer: "127.0.0.1:29002", Client: "127.0.0.1:30002"},
	}
	for i := range want {
		if ms[i] != want[i] {
			t.Fatalf("member %d: got %v, want %v", i, ms[i], want[i])
		}
	}
	if r := Main(0); r != auth.Failed {
		t.Fatalf("Main(0): got %v", r)
	}
}

// membersK is the member count of this run: AUTHN_MEMBERS if set, else a random odd count from
// {1, 3, 5, 7}.
func membersK(t *testing.T) uint64 {
	if s := os.Getenv("AUTHN_MEMBERS"); s != "" {
		k, err := strconv.ParseUint(s, 10, 64)
		if err != nil || k == 0 || k > maxMembers {
			t.Fatalf("AUTHN_MEMBERS=%q", s)
		}
		return k
	}
	return []uint64{1, 3, 5, 7}[rand.Intn(4)]
}

// TestMainRun runs Main(k) for real, k from membersK, in a fresh directory; the checks must pass.
// Then it asks member 0 that the cluster has k members, asks every member that the principals'
// requests are refused by the auth checks (not timeouts) and that an anonymous watch of c/ from
// revision 1 reports no event, and that u's permitted writes took effect (so that the history check
// was not vacuous).
func TestMainRun(t *testing.T) {
	k := membersK(t)
	t.Logf("authN: k=%d (rerun with AUTHN_MEMBERS=%d)", k, k)
	t.Chdir(t.TempDir())
	walarea.ResetFamily(t, "authN") // the members' WAL areas (wal-link P2)
	if r := Main(k); r != auth.Ok {
		t.Fatalf("got %v", r)
	}
	ms := etcdstart.Members("authN", k, PeerBase, ClientBase)

	lg := zap.NewNop()
	newCliAt := func(addr, user, pw string) *clientv3.Client {
		cli, err := clientv3.New(clientv3.Config{Endpoints: []string{addr}, Username: user,
			Password: pw, Logger: lg})
		if err != nil {
			t.Fatal(err)
		}
		t.Cleanup(func() { cli.Close() })
		return cli
	}
	ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
	defer cancel()

	root := newCliAt(ms[0].Client, "root", "root-pw")
	ml, err := root.MemberList(ctx)
	if err != nil {
		t.Fatal(err)
	}
	if uint64(len(ml.Members)) != k {
		t.Fatalf("expected %d members, got %d", k, len(ml.Members))
	}

	want := func(who string, err, kind error) {
		if !errors.Is(err, kind) {
			t.Errorf("%s: got %v, want %v", who, err, kind)
		}
	}
	for _, m := range ms {
		addr := m.Client
		u, v, anon := newCliAt(addr, "u", "u-pw"), newCliAt(addr, "v", "v-pw"), newCliAt(addr, "", "")
		_, err = u.Put(ctx, "c/u/x", "x")
		want(addr+": u outside", err, rpctypes.ErrPermissionDenied)
		_, err = v.Put(ctx, "a/v/x", "x")
		want(addr+": v", err, rpctypes.ErrPermissionDenied)
		_, err = anon.Put(ctx, "a/anon/x", "x")
		want(addr+": anon", err, rpctypes.ErrUserEmpty)
		_, err = anon.Get(ctx, "c/", clientv3.WithPrefix(), clientv3.WithSerializable())
		want(addr+": anon serializable read", err, rpctypes.ErrUserEmpty)
		wctx, wcancel := context.WithTimeout(ctx, 2*time.Second)
		for wresp := range anon.Watch(wctx, "c/", clientv3.WithPrefix(), clientv3.WithRev(1)) {
			if len(wresp.Events) > 0 {
				t.Errorf("%s: anonymous watch reported %d events", addr, len(wresp.Events))
			}
		}
		wcancel()
	}

	resp, err := root.Get(ctx, "", clientv3.WithPrefix())
	if err != nil {
		t.Fatal(err)
	}
	seen := map[string]bool{}
	for _, kv := range resp.Kvs {
		seen[string(kv.Key)] = true
	}
	for _, key := range []string{"a/u/0", "a/u/t", "z/end"} {
		if !seen[key] {
			t.Errorf("key %s missing after Main", key)
		}
	}
	for _, key := range []string{"c/u/0", "a/v/0", "a/anon/0", "a/bad/0"} {
		if seen[key] {
			t.Errorf("key %s present after Main", key)
		}
	}
	t.Logf("k=%d: revision %d after Main, keys %d", k, resp.Header.Revision, len(resp.Kvs))
}
