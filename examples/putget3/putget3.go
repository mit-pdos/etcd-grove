// Package putget3 is putget (examples/putget) with a three-member cluster: three etcd members
// started in-process, each serving its raft handler on its own peer listener, a client connected
// to the first member, a Put of a key and a Get of the same key, and a check that the Get returns
// the Put's value (D21 stage M5, notes/decisions.md). Main panics if the check fails; the adequacy
// theorem is that it does not.
//
// Main calls the examples' shared start (examples/common): StartMember per member
// (etcdserver.NewServer over bootstrap's contract, the member's raft handler served on its peer
// URL's listener, (*EtcdServer).Start), then, for the first member only, what putget does: Serve
// (v3rpc.Server, net.Listen, (*grpc.Server).Serve on a goroutine), NewClient (clientv3.New, one
// endpoint), the client's Put and Get, each in a context with the examples' request timeout
// (context.WithTimeout of Background, cancelled after the call). An error from any step ends Main
// without a check, as in putget.
package putget3

import (
	"context"

	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/types"

	"github.com/mit-pdos/etcd-grove/examples/common"
)

// The members' peer addresses (each member's one peer URL is http://<addr>, served by that
// member's raft handler) and client addresses (only the first is served, to the client: a plain
// host:port, as in putget).
const (
	peerAddr1   = "127.0.0.1:23801"
	peerAddr2   = "127.0.0.1:23802"
	peerAddr3   = "127.0.0.1:23803"
	clientAddr  = "127.0.0.1:23791"
	clientAddr2 = "127.0.0.1:23792"
	clientAddr3 = "127.0.0.1:23793"
)

// Main starts the three members of a new cluster, puts key "k" with value "v" through the first,
// gets "k" from it and panics if the value is not "v".
func Main() {
	lg := zap.NewNop()
	peer1 := types.URLs{{Scheme: "http", Host: peerAddr1}}
	peer2 := types.URLs{{Scheme: "http", Host: peerAddr2}}
	peer3 := types.URLs{{Scheme: "http", Host: peerAddr3}}
	cluster := types.URLsMap{"putget3-1": peer1, "putget3-2": peer2, "putget3-3": peer3}

	s, err := common.StartMember("putget3-1", peer1, peerAddr1, clientAddr, cluster, "putget3", lg)
	if err != nil {
		return
	}
	if _, err := common.StartMember("putget3-2", peer2, peerAddr2, clientAddr2, cluster, "putget3", lg); err != nil {
		return
	}
	if _, err := common.StartMember("putget3-3", peer3, peerAddr3, clientAddr3, cluster, "putget3", lg); err != nil {
		return
	}

	if err := common.Serve(s, clientAddr); err != nil {
		return
	}

	cli, err := common.NewClient(clientAddr, lg)
	if err != nil {
		return
	}
	// each call in a context with the request timeout, cancelled after the call
	pctx, pcancel := context.WithTimeout(context.Background(), common.RequestTimeout)
	_, err = cli.Put(pctx, "k", "v")
	pcancel()
	if err != nil {
		return
	}
	gctx, gcancel := context.WithTimeout(context.Background(), common.RequestTimeout)
	resp, err := cli.Get(gctx, "k")
	gcancel()
	if err != nil {
		return
	}
	if len(resp.Kvs) == 0 || string(resp.Kvs[0].Value) != "v" {
		panic("putget3: Get did not return the Put's value")
	}
}
