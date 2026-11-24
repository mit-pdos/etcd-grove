// Package putgetk is the programs of putgetK_safe (notes/putget-dist-plan.md §13): putget_safe's
// deployment (examples/etcd/dist/putget) with a cluster of k members, each on a machine of its own,
// and one client machine, no machine crashing, over a network that may delay, cut or refuse any
// connection.
//
//   - Member(i, peers, clients) is member i's machine's program: member i of a new k-member cluster
//     (k = len(peers) = len(clients); member j named Name(j), its peer address peers[j], its client
//     address clients[j]; the token Token), built as the in-process examples/etcd/putgetN builds
//     each of its members (etcdstart.StartMember: etcdserver.NewServer with the initial cluster's map
//     of every member's one peer URL http://peers[j], its raft handler served by http.Serve on a
//     listener at its own peer address, then (*EtcdServer).Start), etcd's gRPC API served on a
//     listener at clients[i] (etcdstart.Serve), and the process kept alive. Every member's machine
//     runs it with the same two lists.
//   - Client(ep) is the client machine's program: putget.Client (a client of the one endpoint ep,
//     member 0's client address; a Put of putget.Key with putget.Value, a Get of putget.Key, and a
//     panic if the Get returns another value; an error from any step ends it without a check).
//
// As putget, not examples/etcd/dist/server (etcd_safe's member, stage D2): that program serves
// etcd's full peer handler (etcdhttp.NewPeerHandler, untranslated) and builds its configuration
// itself, where this member is etcdstart's, whose steps are proved in one process. What k > 1 adds
// across machines is rafthttp's traffic between the members' machines (phase 7 S5).
package putgetk

import (
	"crypto/sha1"
	"strconv"
	"time"

	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/types"

	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/putget"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// Token is the cluster's token (etcd's --initial-cluster-token). With the peer URLs it determines
// the member ids (MemberID), whose 16 low bits Valid checks distinct and not 0 (etcd's request ids
// carry them as the member's prefix).
const Token = "putgetk"

// Name is member i's name, also its data directory's and WAL area's base name
// (etcdstart.DataBase/Name(i).etcd, etcdstart.WALBase/Name(i).etcd): "putgetk-" and i in decimal.
func Name(i uint64) string {
	return "putgetk-" + strconv.FormatUint(i, 10)
}

// MemberID is the id etcd gives the member whose one peer URL is http://peer in the cluster Token
// (membership.NewMember's computeMemberID for one URL and no time: the SHA-1 of the URL followed by
// the token, its first 8 bytes big-endian). TestMemberIDEtcd checks it against etcd's own over many
// random configurations.
func MemberID(peer string) uint64 {
	h := sha1.Sum([]byte("http://" + peer + Token))
	var id uint64
	for j := 0; j < 8; j++ {
		id = id<<8 | uint64(h[j])
	}
	return id
}

// decimal reads s as a decimal number with no leading zero (at most 5 digits), or reports false.
func decimal(s string) (uint64, bool) {
	if len(s) == 0 || len(s) > 5 || (len(s) > 1 && s[0] == '0') {
		return 0, false
	}
	var n uint64
	for j := 0; j < len(s); j++ {
		c := s[j]
		if c < '0' || c > '9' {
			return 0, false
		}
		n = n*10 + uint64(c-'0')
	}
	return n, true
}

// AddrOK reports whether a is a valid address of the deployment (the net extension's addrOk): the
// canonical spelling a.b.c.d:p of an IPv4 address with a in 1-223, and a port p in 1-65535 outside
// Linux's default ephemeral range 32768-60999.
func AddrOK(a string) bool {
	var parts []string
	start := 0
	for j := 0; j < len(a); j++ {
		if a[j] == '.' || a[j] == ':' {
			if (len(parts) < 3 && a[j] != '.') || (len(parts) == 3 && a[j] != ':') || len(parts) > 3 {
				return false
			}
			parts = append(parts, a[start:j])
			start = j + 1
		}
	}
	parts = append(parts, a[start:])
	if len(parts) != 5 {
		return false
	}
	var n [5]uint64
	for j := 0; j < 5; j++ {
		v, ok := decimal(parts[j])
		if !ok {
			return false
		}
		n[j] = v
	}
	return 1 <= n[0] && n[0] < 224 && n[1] <= 255 && n[2] <= 255 && n[3] <= 255 &&
		1 <= n[4] && n[4] <= 65535 && (n[4] < 32768 || 60999 < n[4])
}

// Valid reports whether peers and clients configure a cluster etcd can run: at least one member, one
// client address per peer address, every address valid (AddrOK) and the 2k addresses distinct, and
// the member ids' 16 low bits distinct and not 0 (etcd's request and lease ids carry them as the
// member's prefix; two members with one prefix could issue one request id).
func Valid(peers []string, clients []string) bool {
	if len(peers) == 0 || len(peers) != len(clients) {
		return false
	}
	seen := map[string]bool{}
	for j := 0; j < len(peers); j++ {
		for _, a := range []string{peers[j], clients[j]} {
			if !AddrOK(a) || seen[a] {
				return false
			}
			seen[a] = true
		}
	}
	lows := map[uint64]bool{}
	for j := 0; j < len(peers); j++ {
		low := MemberID(peers[j]) & 0xffff
		if low == 0 || lows[low] {
			return false
		}
		lows[low] = true
	}
	return true
}

// holdForever keeps the process alive: the member serves until the machine is stopped.
func holdForever() {
	for {
		time.Sleep(time.Hour)
	}
}

// Member runs member i of the new cluster whose member j has the peer address peers[j] and the
// client address clients[j]. It returns at once unless i < len(peers) and the configuration is
// Valid; then: the initial cluster's map (each member's name
// to its one peer URL http://peers[j], as etcdstart.StartMembers builds it), member i started
// (etcdstart.StartMember: its raft handler served on a listener at peers[i], the server started),
// etcd's gRPC API served at clients[i], then the process kept alive. It returns only if a step fails.
func Member(i uint64, peers []string, clients []string) {
	if i >= uint64(len(peers)) || !Valid(peers, clients) {
		return
	}
	cluster := types.URLsMap{}
	for j := range peers {
		cluster[Name(uint64(j))] = types.URLs{{Scheme: "http", Host: peers[j]}}
	}
	s, err := etcdstart.StartMember(Name(i), cluster[Name(i)], peers[i], clients[i], cluster, Token,
		zap.NewNop())
	if err != nil {
		return
	}
	if err := etcdstart.Serve(s, clients[i]); err != nil {
		return
	}
	holdForever()
}

// Client is putget.Client against the one endpoint ep (member 0's client address, verbatim): it
// reports whether its check ran, and panics if the Get after an acknowledged Put returns another
// value.
func Client(ep string) bool {
	return putget.Client(ep)
}
