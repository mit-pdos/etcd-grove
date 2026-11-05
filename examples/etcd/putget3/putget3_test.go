package putget3

import (
	"context"
	"testing"
	"time"

	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.uber.org/zap"
)

// TestMemberIDs checks D21e (A)'s premise on the member ids etcd computes for Main's cluster (from
// the peer URLs and the cluster token): their 16 low bits are distinct and not 0.
func TestMemberIDs(t *testing.T) {
	urls, err := types.NewURLsMap("putget3-1=http://" + peerAddr1 + ",putget3-2=http://" + peerAddr2 +
		",putget3-3=http://" + peerAddr3)
	if err != nil {
		t.Fatal(err)
	}
	cl, err := membership.NewClusterFromURLsMap(zap.NewNop(), "putget3", urls)
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
}

// TestPutGet3 runs Main once, in a fresh directory (the members' DataDirs are relative). Main
// returns without its check if a step fails, so the test then asks the first member, which Main
// left running, whether the Put took effect (a Put commits only with two of the three members
// reached over their raft handlers), and that the cluster has three members.
func TestPutGet3(t *testing.T) {
	t.Chdir(t.TempDir())
	Main()

	cli, err := clientv3.New(clientv3.Config{Endpoints: []string{clientAddr}, Logger: zap.NewNop()})
	if err != nil {
		t.Fatal(err)
	}
	defer cli.Close()
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	resp, err := cli.Get(ctx, "k")
	if err != nil {
		t.Fatal(err)
	}
	if len(resp.Kvs) != 1 || string(resp.Kvs[0].Value) != "v" {
		t.Fatalf("Main's Put did not take effect: %v", resp.Kvs)
	}
	ml, err := cli.MemberList(ctx)
	if err != nil {
		t.Fatal(err)
	}
	if len(ml.Members) != 3 {
		t.Fatalf("expected 3 members, got %d", len(ml.Members))
	}
}
