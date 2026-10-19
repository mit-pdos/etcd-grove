package linkv3

import (
	"context"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.uber.org/zap"
)

// TestMemberIDs checks D21e (A)'s premise on the member ids etcd computes for Main's cluster (from
// the peer URLs and the cluster token): their 16 low bits are distinct and not 0. It prints the
// ids in the order bootstrap sorts them (the proof's BootFacts).
func TestMemberIDs(t *testing.T) {
	urls, err := types.NewURLsMap("linkv3-1=http://" + peerAddr1 + ",linkv3-2=http://" + peerAddr2 +
		",linkv3-3=http://" + peerAddr3)
	if err != nil {
		t.Fatal(err)
	}
	cl, err := membership.NewClusterFromURLsMap(zap.NewNop(), "linkv3", urls)
	if err != nil {
		t.Fatal(err)
	}
	seen := map[uint64]bool{}
	for _, id := range cl.MemberIDs() {
		low := uint64(id) & 0xffff
		t.Logf("member %x (%s): low 16 bits %#x", uint64(id), cl.Member(id).Name, low)
		if low == 0 || seen[low] {
			t.Fatalf("member %x: low 16 bits %#x zero or repeated", uint64(id), low)
		}
		seen[low] = true
	}
}

// TestMainRun runs Main for real: three members in a fresh directory (the members' DataDirs are
// relative), 8 clients of 50 operations each, and porcupine's verdict must be Ok; then it asks
// the first member, which Main left running, whether the puts took effect (so that the history
// was not all errors) and that the cluster has three members.
func TestMainRun(t *testing.T) {
	t.Chdir(t.TempDir())
	if r := Main(8, 50); r != porcupine.Ok {
		t.Fatalf("got %v", r)
	}

	cli, err := clientv3.New(clientv3.Config{Endpoints: []string{clientAddr}, Logger: zap.NewNop()})
	if err != nil {
		t.Fatal(err)
	}
	defer cli.Close()
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	resp, err := cli.Get(ctx, "k", clientv3.WithPrefix())
	if err != nil {
		t.Fatal(err)
	}
	if len(resp.Kvs) == 0 || resp.Header.Revision < 10 {
		t.Fatalf("Main's puts did not take effect: revision %d, %v", resp.Header.Revision, resp.Kvs)
	}
	ml, err := cli.MemberList(ctx)
	if err != nil {
		t.Fatal(err)
	}
	if len(ml.Members) != 3 {
		t.Fatalf("expected 3 members, got %d", len(ml.Members))
	}
	t.Logf("revision %d after Main, keys %d", resp.Header.Revision, len(resp.Kvs))
}
