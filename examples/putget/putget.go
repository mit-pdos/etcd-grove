// Package putget is the adequacy example of etcd's server and client: one etcd member started
// in-process, a client connected to it, a Put of a key and a Get of the same key, and a check
// that the Get returns the Put's value (open-work item 9, notes/STATUS.md). Main panics if the
// check fails; the adequacy theorem to prove is that it does not (not proved yet: notes/STATUS.md,
// "Item 9: the adequacy example", and notes/decisions.md, D19).
//
// Main calls only what the proofs specify: the examples' shared start (examples/common:
// StartServer, which configures the member and calls etcdserver.NewServer and (*EtcdServer).Start;
// Serve, v3rpc.Server, net.Listen and (*grpc.Server).Serve on a goroutine; NewClient,
// clientv3.New), the client's Put and Get, each in a context with the examples' request timeout
// (context.WithTimeout of Background, cancelled after the call). An error from any step ends Main without a check: the specs
// allow every step to fail (no leader in time, a dial error, ...), and the conclusion is about
// the Get's value when both succeed.
package putget

import (
	"context"

	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/common"
)

// The client address: the string net.Listen is given is the client's endpoint, verbatim (a plain
// host:port, no scheme: clientv3.New's premise plainEndpoint).
const clientAddr = "127.0.0.1:23790"

// Main starts one member of a new cluster, puts key "k" with value "v", gets "k" and panics if the
// value is not "v".
func Main() {
	lg := zap.NewNop()
	s, err := common.StartServer("putget", "127.0.0.1:23800", clientAddr, lg)
	if err != nil {
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
		panic("putget: Get did not return the Put's value")
	}
}
