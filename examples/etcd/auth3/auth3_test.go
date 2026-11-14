package auth3

import (
	"bytes"
	"context"
	"errors"
	"testing"
	"time"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/etcd/auth"
)

// TestMemberIDs checks the premise on the member ids etcd computes for Main's cluster (from the
// peer URLs and the cluster token; putget3's TestMemberIDs, `BootFacts`): their 16 low bits are
// distinct and not 0.
func TestMemberIDs(t *testing.T) {
	urls, err := types.NewURLsMap("auth3-1=http://" + peerAddr1 + ",auth3-2=http://" + peerAddr2 +
		",auth3-3=http://" + peerAddr3)
	if err != nil {
		t.Fatal(err)
	}
	cl, err := membership.NewClusterFromURLsMap(zap.NewNop(), "auth3", urls)
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
	if len(seen) != 3 {
		t.Fatalf("got %d members", len(seen))
	}
}

// TestMainRun runs Main for real: three members in a fresh directory (their DataDirs are
// relative); the checks must pass. Then it asks the first member, which Main left running, that
// the cluster has three members, that the principals' requests were refused by the auth checks
// (not timeouts), and that u's permitted writes took effect (so that the history check was not
// vacuous).
func TestMainRun(t *testing.T) {
	t.Chdir(t.TempDir())
	if r := Main(); r != auth.Ok {
		t.Fatalf("got %v", r)
	}

	lg := zap.NewNop()
	newCli := func(user, pw string) *clientv3.Client {
		cli, err := clientv3.New(clientv3.Config{Endpoints: []string{clientAddr}, Username: user,
			Password: pw, Logger: lg})
		if err != nil {
			t.Fatal(err)
		}
		t.Cleanup(func() { cli.Close() })
		return cli
	}
	ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
	defer cancel()

	root := newCli("root", "root-pw")
	ml, err := root.MemberList(ctx)
	if err != nil {
		t.Fatal(err)
	}
	if len(ml.Members) != 3 {
		t.Fatalf("expected 3 members, got %d", len(ml.Members))
	}

	u, v, anon := newCli("u", "u-pw"), newCli("v", "v-pw"), newCli("", "")
	want := func(who string, err, kind error) {
		if !errors.Is(err, kind) {
			t.Errorf("%s: got %v, want %v", who, err, kind)
		}
	}
	_, err = u.Put(ctx, "c/u/x", "x")
	want("u outside", err, rpctypes.ErrPermissionDenied)
	_, err = v.Put(ctx, "a/v/x", "x")
	want("v", err, rpctypes.ErrPermissionDenied)
	_, err = anon.Put(ctx, "a/anon/x", "x")
	want("anon", err, rpctypes.ErrUserEmpty)

	resp, err := root.Get(ctx, "", clientv3.WithPrefix())
	if err != nil {
		t.Fatal(err)
	}
	seen := map[string]bool{}
	for _, kv := range resp.Kvs {
		seen[string(kv.Key)] = true
	}
	for _, k := range []string{"a/u/0", "a/u/t", "z/end"} {
		if !seen[k] {
			t.Errorf("key %s missing after Main", k)
		}
	}
	for _, k := range []string{"c/u/0", "a/v/0", "a/anon/0", "a/bad/0"} {
		if seen[k] {
			t.Errorf("key %s present after Main", k)
		}
	}
	t.Logf("revision %d after Main, keys %d", resp.Header.Revision, len(resp.Kvs))
}

// mainServers is Main (test-only: not translated), at the given addresses, returning the members'
// servers as well, so that a test can read the followers' state: the same members (startMember,
// the same cluster map shape and names), then auth.Run on the first.
func mainServers(p1, p2, p3, c1, c2, c3 string) (int, [3]*etcdserver.EtcdServer) {
	var ss [3]*etcdserver.EtcdServer
	lg := zap.NewNop()
	peer1 := types.URLs{{Scheme: "http", Host: p1}}
	peer2 := types.URLs{{Scheme: "http", Host: p2}}
	peer3 := types.URLs{{Scheme: "http", Host: p3}}
	cluster := types.URLsMap{"auth3-1": peer1, "auth3-2": peer2, "auth3-3": peer3}
	var err error
	if ss[0], err = startMember("auth3-1", peer1, p1, c1, cluster, lg); err != nil {
		return auth.Failed, ss
	}
	if ss[1], err = startMember("auth3-2", peer2, p2, c2, cluster, lg); err != nil {
		return auth.Failed, ss
	}
	if ss[2], err = startMember("auth3-3", peer3, p3, c3, cluster, lg); err != nil {
		return auth.Failed, ss
	}
	return auth.Run(ss[0], c1, lg), ss
}

// TestFollowersApplied runs Main's steps with the servers exposed (mainServers, on addresses of its
// own, so that it can run after TestMainRun, whose members keep theirs) and checks that the two
// followers applied what member 1 applied: once their applied indexes reach member 1's, each has
// auth enabled at member 1's auth revision, the users with member 1's roles, and member 1's keys
// and values at member 1's revision (a local read of each store, keys below 0x7f: every key Main writes, as a serializable read).
func TestFollowersApplied(t *testing.T) {
	t.Chdir(t.TempDir())
	r, ss := mainServers("127.0.0.1:24151", "127.0.0.1:24152", "127.0.0.1:24153",
		"127.0.0.1:24161", "127.0.0.1:24162", "127.0.0.1:24163")
	if r != auth.Ok {
		t.Fatalf("got %v", r)
	}
	s1 := ss[0]
	want := s1.AppliedIndex()
	deadline := time.Now().Add(20 * time.Second)
	for _, s := range ss[1:] {
		for s.AppliedIndex() < want && time.Now().Before(deadline) {
			time.Sleep(50 * time.Millisecond)
		}
		if s.AppliedIndex() < want {
			t.Fatalf("member %x: applied index %d, member 1's %d", uint64(s.MemberID()), s.AppliedIndex(), want)
		}
	}
	ctx := context.Background()
	all := func(s *etcdserver.EtcdServer) *mvcc.RangeResult {
		rr, err := s.KV().Range(ctx, []byte{0}, []byte{0x7f}, mvcc.RangeOptions{})
		if err != nil {
			t.Fatal(err)
		}
		return rr
	}
	r1 := all(s1)
	if len(r1.KVs) == 0 {
		t.Fatalf("member 1 has no keys")
	}
	for _, s := range ss[1:] {
		id := uint64(s.MemberID())
		if !s.AuthStore().IsAuthEnabled() {
			t.Errorf("member %x: auth not enabled", id)
		}
		if s.AuthStore().Revision() != s1.AuthStore().Revision() {
			t.Errorf("member %x: auth revision %d, member 1's %d", id, s.AuthStore().Revision(),
				s1.AuthStore().Revision())
		}
		for _, u := range []string{"root", "u", "v"} {
			g1, err1 := s1.AuthStore().UserGet(&pb.AuthUserGetRequest{Name: u})
			g, err := s.AuthStore().UserGet(&pb.AuthUserGetRequest{Name: u})
			if err1 != nil || err != nil || len(g.Roles) != len(g1.Roles) {
				t.Errorf("member %x: user %s: %v %v, %v %v", id, u, g, err, g1, err1)
			}
		}
		rr := all(s)
		if rr.Rev != r1.Rev || len(rr.KVs) != len(r1.KVs) {
			t.Fatalf("member %x: revision %d with %d keys, member 1's %d with %d", id, rr.Rev,
				len(rr.KVs), r1.Rev, len(r1.KVs))
		}
		for i := range rr.KVs {
			if !bytes.Equal(rr.KVs[i].Key, r1.KVs[i].Key) || !bytes.Equal(rr.KVs[i].Value, r1.KVs[i].Value) ||
				rr.KVs[i].ModRevision != r1.KVs[i].ModRevision {
				t.Errorf("member %x: key %d differs: %s=%s, member 1's %s=%s", id, i, rr.KVs[i].Key,
					rr.KVs[i].Value, r1.KVs[i].Key, r1.KVs[i].Value)
			}
		}
		t.Logf("member %x: applied %d, revision %d, %d keys, auth revision %d", id, s.AppliedIndex(),
			rr.Rev, len(rr.KVs), s.AuthStore().Revision())
	}
}
