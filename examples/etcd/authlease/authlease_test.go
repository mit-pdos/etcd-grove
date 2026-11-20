package authlease

import (
	"context"
	"math/rand"
	"os"
	"strconv"
	"testing"
	"time"

	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.uber.org/zap"
	"google.golang.org/grpc/metadata"

	"github.com/mit-pdos/etcd-grove/examples/etcd/auth"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// maxMembers is the bound of etcd_authlease_safe's member count.
const maxMembers = 1000

// idsOf returns the member ids etcd computes for Main(k)'s cluster (from the peer URLs and the
// cluster token, as bootstrap does), in the members' order, without starting it.
func idsOf(t *testing.T, k uint64) []types.ID {
	ms := etcdstart.Members("authlease", k, PeerBase, ClientBase)
	ids := make([]types.ID, len(ms))
	urls := types.URLsMap{}
	for i, m := range ms {
		u, err := types.NewURLs([]string{"http://" + m.Peer})
		if err != nil {
			t.Fatal(err)
		}
		urls[m.Name] = u
		ids[i] = membership.NewMember(m.Name, u, Token, nil).ID
	}
	cl, err := membership.NewClusterFromURLsMap(zap.NewNop(), Token, urls)
	if err != nil {
		t.Fatal(err)
	}
	if len(cl.MemberIDs()) != len(ids) {
		t.Fatalf("k=%d: %d ids in the cluster", k, len(cl.MemberIDs()))
	}
	for _, id := range ids {
		if cl.Member(id) == nil {
			t.Fatalf("k=%d: member %x not in the cluster", k, uint64(id))
		}
	}
	return ids
}

// TestMemberIDs checks etcd_authlease_safe's premises on the member ids for every member count
// 1 <= k <= maxMembers: BootCore's (their 16 low bits distinct and not 0) and leaseIdsApart (their
// 15 low bits distinct). A member's id depends only on its peer URL and the token, so the ids of
// k members are the first k of maxMembers': checking maxMembers checks every k. It starts no
// cluster.
func TestMemberIDs(t *testing.T) {
	ids := idsOf(t, maxMembers)
	seen16 := map[uint64]bool{}
	seen15 := map[uint64]bool{}
	for i, id := range ids {
		l16 := uint64(id) & 0xffff
		l15 := uint64(id) & 0x7fff
		if l16 == 0 || seen16[l16] {
			t.Fatalf("member %d (%x): low 16 bits %#x zero or repeated", i, uint64(id), l16)
		}
		if seen15[l15] {
			t.Fatalf("member %d (%x): low 15 bits %#x repeated", i, uint64(id), l15)
		}
		seen16[l16] = true
		seen15[l15] = true
	}
	for _, k := range []uint64{1, 2, 3, 7, 500} {
		got := idsOf(t, k)
		for i := range got {
			if got[i] != ids[i] {
				t.Fatalf("k=%d: member %d's id %x, not the 1000 members' %x", k, i, got[i], ids[i])
			}
		}
	}
}

// TestMembers checks Main's members' names and addresses at k = 3, and Main(0).
func TestMembers(t *testing.T) {
	ms := etcdstart.Members("authlease", 3, PeerBase, ClientBase)
	want := []etcdstart.Member{
		{Name: "authlease-0", Peer: "127.0.0.1:16000", Client: "127.0.0.1:17000"},
		{Name: "authlease-1", Peer: "127.0.0.1:16001", Client: "127.0.0.1:17001"},
		{Name: "authlease-2", Peer: "127.0.0.1:16002", Client: "127.0.0.1:17002"},
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

// membersK is the member count of this run: AUTHLEASE_MEMBERS if set, else a random count from
// {1, 2, 3, 5, 7}.
func membersK(t *testing.T) uint64 {
	if s := os.Getenv("AUTHLEASE_MEMBERS"); s != "" {
		k, err := strconv.ParseUint(s, 10, 64)
		if err != nil || k == 0 || k > maxMembers {
			t.Fatalf("AUTHLEASE_MEMBERS=%q", s)
		}
		return k
	}
	return []uint64{1, 2, 3, 5, 7}[rand.Intn(5)]
}

// wantErr fails unless err is an error whose text contains one of subs.
func wantErr(t *testing.T, what string, err error, subs ...string) {
	t.Helper()
	if err == nil {
		t.Fatalf("%s: no error", what)
	}
	for _, s := range subs {
		if contains(err.Error(), s) {
			return
		}
	}
	t.Fatalf("%s: error %q, want one of %q", what, err, subs)
}

func contains(s, sub string) bool {
	for i := 0; i+len(sub) <= len(s); i++ {
		if s[i:i+len(sub)] == sub {
			return true
		}
	}
	return false
}

// TestMainRun runs Main(k) for real, k from membersK, in a fresh directory; the checks must pass.
// Then, at every member: the refusals are the auth checks' (not timeouts), also for
// KeepAliveOnce (which Main does not call); a lease granted through each member has an id whose
// bits 48-62 are the member id's 15 low bits; root's lease Lz still holds z/lease, and u's keys
// are gone.
func TestMainRun(t *testing.T) {
	k := membersK(t)
	t.Logf("authlease: k=%d (rerun with AUTHLEASE_MEMBERS=%d)", k, k)
	t.Chdir(t.TempDir())
	start := time.Now()
	if r := Main(k); r != auth.Ok {
		t.Fatalf("got %v", r)
	}
	t.Logf("Main(%d) took %v", k, time.Since(start))
	ms := etcdstart.Members("authlease", k, PeerBase, ClientBase)
	ids := idsOf(t, k)

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

	root0 := newCliAt(ms[0].Client, "root", rootPw)
	g, err := root0.Get(ctx, zKey)
	if err != nil || len(g.Kvs) != 1 || g.Kvs[0].Lease == 0 {
		t.Fatalf("z/lease: %v %v", g, err)
	}
	lz := clientv3.LeaseID(g.Kvs[0].Lease)
	for _, key := range []string{aKey, txnKey, xKey} {
		g, err := root0.Get(ctx, key)
		if err != nil || len(g.Kvs) != 0 {
			t.Fatalf("%s: %v %v", key, g, err)
		}
	}

	for i, m := range ms {
		u := newCliAt(m.Client, "u", uPw)
		v := newCliAt(m.Client, "v", vPw)
		anon := newCliAt(m.Client, "", "")
		root := newCliAt(m.Client, "root", rootPw)
		_, err := u.TimeToLive(ctx, lz, clientv3.WithAttachedKeys())
		wantErr(t, "u's TimeToLive(Lz, keys) at "+m.Name, err, "permission denied")
		_, err = u.Leases(ctx)
		wantErr(t, "u's Leases at "+m.Name, err, "permission denied")
		_, err = u.Revoke(ctx, lz)
		wantErr(t, "u's Revoke(Lz) at "+m.Name, err, "permission denied")
		_, err = u.KeepAliveOnce(ctx, lz)
		wantErr(t, "u's KeepAliveOnce(Lz) at "+m.Name, err, "permission denied")
		_, err = u.Put(ctx, xKey, "v", clientv3.WithLease(lz))
		wantErr(t, "u's Put(a/x, Lz) at "+m.Name, err, "permission denied")
		_, err = v.Leases(ctx)
		wantErr(t, "v's Leases at "+m.Name, err, "permission denied")
		_, err = anon.Grant(ctx, grantTTL)
		wantErr(t, "anon's Grant at "+m.Name, err, "user name is empty", "user name not found")
		_, err = anon.Leases(ctx)
		wantErr(t, "anon's Leases at "+m.Name, err, "user name is empty", "user name not found")
		_, err = anon.TimeToLive(ctx, lz)
		wantErr(t, "anon's TimeToLive(Lz) at "+m.Name, err, "user name is empty", "user name not found")
		_, err = anon.KeepAliveOnce(ctx, lz)
		wantErr(t, "anon's KeepAliveOnce(Lz) at "+m.Name, err, "user name is empty", "user name not found")
		bctx := metadata.AppendToOutgoingContext(ctx, "token", badToken)
		_, err = anon.Grant(bctx, grantTTL)
		wantErr(t, "bad's Grant at "+m.Name, err, "invalid auth token")
		_, err = anon.Revoke(bctx, lz)
		wantErr(t, "bad's Revoke at "+m.Name, err, "invalid auth token")

		// a grant through this member: its id's bits 48-62 are the member id's 15 low bits
		gr, err := root.Grant(ctx, grantTTL)
		if err != nil {
			t.Fatalf("root's Grant at %s: %v", m.Name, err)
		}
		if uint64(gr.ID)>>48 != uint64(ids[i])&0x7fff {
			t.Fatalf("lease %x granted at %s (id %x): prefix not the member's", gr.ID, m.Name,
				uint64(ids[i]))
		}
		if _, err := root.Revoke(ctx, gr.ID); err != nil {
			t.Fatalf("root's Revoke at %s: %v", m.Name, err)
		}
	}
	t.Logf("authlease: k=%d checked at every member", k)
}
