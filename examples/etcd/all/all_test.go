package etcdall

// These tests use the drivers' fixed ports, member names and data directories (examples/etcd/...):
// do not run them at the same time as those packages' tests. CI runs no Go tests.

import (
	"fmt"
	"os"
	"sort"
	"strconv"
	"testing"
	"time"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/etcd/restartN"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/walarea"
)

// maxMembers is the driver's own bound on the k-member part's member count (k5).
const maxMembers = 1000

// idBound is etcd_robust_single_process's bound on the k-member part's member count (ParamsOk's 300,
// notes/etcd-unified-scope.md §2.2 B, decision N2): the member count up to which the 16 low bits of
// the ids of the process's every member are distinct (TestMemberIDs).
func idBound(pfx string) int {
	return 300
}

// A k-member part: its members are etcdstart.Members(pfx, k, peerBase, clientBase) at token; bridged
// says its members' gRPC APIs are behind bridges at bridgeBase+i, clientServed that its members'
// client addresses are listened on (restartN's are not).
type kPart struct {
	pfx          string
	peerBase     uint64
	clientBase   uint64
	token        string
	clientServed bool
	bridgeBase   uint64 // 0: no bridges
}

func kParts() []kPart {
	return []kPart{
		{"restartN", restartN.PeerBase, restartN.ClientBase, restartN.Token, false, 0},
	}
}

// A part of fixed members: each member's name and peer address, the cluster's token, and the
// addresses the part listens on. Copied from the driver (restart1's constants: unexported there).
type fixedPart struct {
	names   []string
	peers   []string
	token   string
	listens []string
}

func fixedParts() []fixedPart {
	return []fixedPart{
		// a one-member cluster: the token is the member's name, the peer address is not served
		{[]string{"restart1"}, []string{"127.0.0.1:23811"}, "restart1", nil},
	}
}

// memberID is the id etcd computes for a member named name with the one peer URL http://peer in a
// cluster with token token (as bootstrap does: it depends on the peer URL and the token only).
func memberID(t *testing.T, name string, peer string, token string) uint64 {
	u, err := types.NewURLs([]string{"http://" + peer})
	if err != nil {
		t.Fatal(err)
	}
	cl, err := membership.NewClusterFromURLsMap(zap.NewNop(), token, types.URLsMap{name: u})
	if err != nil {
		t.Fatal(err)
	}
	return uint64(cl.MemberIDs()[0])
}

// TestAddrs checks that the addresses the parts listen on are disjoint, at the k-member part's largest
// member count (a k-member part's addresses at k are a prefix of those at maxMembers), and that
// every port is at most 65535.
func TestAddrs(t *testing.T) {
	owner := map[string]string{}
	add := func(a string, who string) {
		if o, ok := owner[a]; ok {
			t.Errorf("address %s: %s and %s", a, o, who)
			return
		}
		owner[a] = who
	}
	for _, p := range kParts() {
		if p.peerBase+maxMembers-1 > 65535 || p.clientBase+maxMembers-1 > 65535 ||
			p.bridgeBase+maxMembers-1 > 65535 {
			t.Errorf("%s: a port above 65535", p.pfx)
		}
		for i, m := range etcdstart.Members(p.pfx, maxMembers, p.peerBase, p.clientBase) {
			add(m.Peer, m.Name+" peer")
			if p.clientServed {
				add(m.Client, m.Name+" client")
			}
			if p.bridgeBase != 0 {
				add("127.0.0.1:"+strconv.FormatUint(p.bridgeBase+uint64(i), 10), m.Name+" bridge")
			}
		}
	}
	for _, p := range fixedParts() {
		for _, a := range p.listens {
			add(a, p.token)
		}
	}
}

// idsOf returns the ids of the first maxMembers members of each k-member part (in the members'
// order) and the ids of the fixed parts' members.
func idsOf(t *testing.T) (map[string][]uint64, []uint64) {
	kids := map[string][]uint64{}
	for _, p := range kParts() {
		for _, m := range etcdstart.Members(p.pfx, maxMembers, p.peerBase, p.clientBase) {
			kids[p.pfx] = append(kids[p.pfx], memberID(t, m.Name, m.Peer, p.token))
		}
	}
	var fixed []uint64
	for _, p := range fixedParts() {
		for i := range p.names {
			fixed = append(fixed, memberID(t, p.names[i], p.peers[i], p.token))
		}
	}
	return kids, fixed
}

// lowOk reports whether the 16 low bits of ids are distinct and not 0.
func lowOk(ids []uint64) bool {
	seen := map[uint64]bool{}
	for _, id := range ids {
		low := id & 0xffff
		if low == 0 || seen[low] {
			return false
		}
		seen[low] = true
	}
	return true
}

// TestMemberIDs checks etcd_safe's premise Hlow (examples/k8s/all's, notes/etcd-unified-scope.md
// §2.2 B): the 16 low bits of the ids of the process's every member distinct and not 0, the
// k-member parts at their bounds (idBound; a part's members at k are the first k at its bound, so
// that checks every smaller k too). It also reports, for the record, the collisions with every
// k-member part at maxMembers (which no choice of tokens avoids: about 4000 values in 65536).
func TestMemberIDs(t *testing.T) {
	kids, fixed := idsOf(t)
	all := append([]uint64{}, fixed...)
	for _, p := range kParts() {
		all = append(all, kids[p.pfx][:idBound(p.pfx)]...)
	}
	if !lowOk(all) {
		t.Errorf("Hlow fails at the bounds")
	}
	byLow := map[uint64][]string{}
	for _, p := range kParts() {
		for i, id := range kids[p.pfx] {
			byLow[id&0xffff] = append(byLow[id&0xffff], fmt.Sprintf("%s-%d", p.pfx, i))
		}
	}
	for i, id := range fixed {
		byLow[id&0xffff] = append(byLow[id&0xffff], fmt.Sprintf("fixed#%d", i))
	}
	n := 0
	var lows []uint64
	for low, ws := range byLow {
		if len(ws) > 1 {
			n += len(ws) - 1
			lows = append(lows, low)
		}
	}
	sort.Slice(lows, func(i, j int) bool { return lows[i] < lows[j] })
	t.Logf("at k5 = %d: %d colliding members over %d low halves", maxMembers, n, len(lows))
	for _, low := range lows[:min(5, len(lows))] {
		t.Logf("  low %#04x: %v", low, byLow[low])
	}
}

// TestMainRun runs Main once, restartN at ETCDALL_K members (default 3), after resetting every
// member's WAL area and data directory.
// It passes if Main returns: a failed check is a panic. (A part whose start fails returns without
// its check; TestAddrs is what rules out a start failing on a taken address.)
func TestMainRun(t *testing.T) {
	k := uint64(3)
	if s := os.Getenv("ETCDALL_K"); s != "" {
		v, err := strconv.ParseUint(s, 10, 64)
		if err != nil || v < 3 || v > 300 {
			t.Fatalf("ETCDALL_K=%q: not a member count in 3..300", s)
		}
		k = v
	}
	t.Chdir(t.TempDir())
	walarea.ResetFamily(t, "restartN")
	walarea.Reset(t, "restart1")
	start := time.Now()
	Main(k)
	t.Logf("Main(k = %d) took %v", k, time.Since(start))
}
