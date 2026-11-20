package putgetN

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

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/walarea"
)

// maxMembers is the bound of etcd_putgetN_safe's member count.
const maxMembers = 1000

// idsOf returns the member ids etcd computes for Main(k)'s cluster (from the peer URLs and the
// cluster token, as bootstrap does), without starting it.
func idsOf(t *testing.T, k uint64) []types.ID {
	ms := etcdstart.Members("putgetN", k, PeerBase, ClientBase)
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

// TestMemberIDs checks etcd_putgetN_safe's premise on the member ids (BootCore: their 16 low bits
// distinct and not 0, D21e (A)) for every member count 1 <= k <= maxMembers, from the ids etcd
// computes for Main(k)'s cluster. It starts no cluster.
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

// TestMembers checks Members' names and addresses at a few counts.
func TestMembers(t *testing.T) {
	ms := etcdstart.Members("putgetN", 3, PeerBase, ClientBase)
	want := []etcdstart.Member{
		{Name: "putgetN-0", Peer: "127.0.0.1:24000", Client: "127.0.0.1:25000"},
		{Name: "putgetN-1", Peer: "127.0.0.1:24001", Client: "127.0.0.1:25001"},
		{Name: "putgetN-2", Peer: "127.0.0.1:24002", Client: "127.0.0.1:25002"},
	}
	if len(ms) != len(want) {
		t.Fatalf("got %v", ms)
	}
	for i := range want {
		if ms[i] != want[i] {
			t.Fatalf("member %d: got %v, want %v", i, ms[i], want[i])
		}
	}
	if len(etcdstart.Members("putgetN", 0, PeerBase, ClientBase)) != 0 {
		t.Fatal("k=0: members")
	}
}

// TestPutGetN runs Main(k) once, in a fresh directory (the members' DataDirs are relative), for
// one member count k drawn at random from {1, 3, 5, 7} (PUTGETN_MEMBERS=<k> overrides it), logged
// first so that a failure can be rerun. Main returns without its check if a step fails, so the
// test then asks the first member, which Main left running, whether the Put took effect (it
// commits only with a majority of the k members reached over their raft handlers), and that the
// cluster has k members.
func TestPutGetN(t *testing.T) {
	ks := []uint64{1, 3, 5, 7}
	k := ks[rand.Intn(len(ks))]
	if s := os.Getenv("PUTGETN_MEMBERS"); s != "" {
		v, err := strconv.ParseUint(s, 10, 64)
		if err != nil || v < 1 || v > maxMembers {
			t.Fatalf("PUTGETN_MEMBERS=%q: not a member count in 1..%d", s, maxMembers)
		}
		k = v
	}
	t.Logf("putgetN: k=%d (rerun with PUTGETN_MEMBERS=%d)", k, k)
	t.Chdir(t.TempDir())
	walarea.ResetFamily(t, "putgetN") // the members' WAL areas (wal-link P2)
	Main(k)

	client := "127.0.0.1:" + strconv.FormatUint(ClientBase, 10)
	cli, err := clientv3.New(clientv3.Config{Endpoints: []string{client}, Logger: zap.NewNop()})
	if err != nil {
		t.Fatal(err)
	}
	defer cli.Close()
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
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
	if uint64(len(ml.Members)) != k {
		t.Fatalf("expected %d members, got %d", k, len(ml.Members))
	}
}
