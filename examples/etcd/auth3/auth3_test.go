package auth3

import (
	"context"
	"errors"
	"testing"
	"time"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
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
