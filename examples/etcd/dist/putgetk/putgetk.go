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
	"strconv"
	"time"

	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/types"

	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/putget"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// Token is the cluster's token (etcd's --initial-cluster-token). With the peer URLs it determines
// the member ids (membership.NewMember: the SHA-1 of a member's peer URLs and the token), whose 16
// low bits the theorem's premise BootCore takes distinct and not 0 (etcd's request ids carry them as
// the member's prefix); TestMemberIDs checks it at the theorem's addresses.
const Token = "putgetk"

// Name is member i's name, also its data directory's and WAL area's base name
// (etcdstart.DataBase/Name(i).etcd, etcdstart.WALBase/Name(i).etcd): "putgetk-" and i in decimal.
func Name(i uint64) string {
	return "putgetk-" + strconv.FormatUint(i, 10)
}

// holdForever keeps the process alive: the member serves until the machine is stopped.
func holdForever() {
	for {
		time.Sleep(time.Hour)
	}
}

// Member runs member i (0 <= i < len(peers)) of the new cluster whose member j has the peer
// address peers[j] and the client address clients[j]: the initial cluster's map (each member's name
// to its one peer URL http://peers[j], as etcdstart.StartMembers builds it), member i started
// (etcdstart.StartMember: its raft handler served on a listener at peers[i], the server started),
// etcd's gRPC API served at clients[i], then the process kept alive. It returns only if a step fails.
func Member(i uint64, peers []string, clients []string) {
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
