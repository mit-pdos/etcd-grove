// Package putgetN is putget3 (examples/etcd/putget3) with any number of members
// (notes/clusterN-scope.md): k etcd members started in-process, each serving its raft handler on
// its own peer listener, a client connected to the first member, a Put of a key and a Get of the
// same key, and a check that the Get returns the Put's value. Main panics if the check fails; the
// adequacy theorem is that it does not, for every member count 1 <= k <= 1000.
//
// Main calls the examples' shared start (examples/lib/etcdstart): Members (member i is named
// putgetN-i, its peer address 127.0.0.1:(24000+i), its client address 127.0.0.1:(25000+i)),
// StartMembers (StartMember per member: etcdserver.NewServer over bootstrap's contract, the
// member's raft handler served on its peer URL's listener, (*EtcdServer).Start), then, for the
// first member only, what putget does: Serve, NewClient, the client's Put and Get, each in a
// context with the examples' request timeout. An error from any step ends Main without a check,
// as in putget.
package putgetN

import (
	"context"

	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// The members' address ranges: member i's peer address is 127.0.0.1:(PeerBase+i), its client
// address 127.0.0.1:(ClientBase+i) (only the first member's client address is served).
const (
	PeerBase   uint64 = 24000
	ClientBase uint64 = 25000
)

// Token is the cluster's token (etcd's --initial-cluster-token), from which, with its peer URL,
// etcd computes each member's id (membership.NewMember: the SHA-1 of the peer URLs and the token,
// so member i's id is the same in every cluster of more than i members). The theorem's premise on
// the ids (their 16 low bits distinct and not 0: etcd's request and lease ids carry them as the
// member's prefix) fails for some k <= 1000 at most tokens (at "putgetN" first at k = 214, the
// birthday bound of 16 bits); this token is the first "putgetN-<i>" at which it holds for every
// k <= 1000 (TestMemberIDs checks it).
const Token = "putgetN-1405"

// Main starts the k members of a new cluster, puts key "k" with value "v" through the first, gets
// "k" from it and panics if the value is not "v".
func Main(k uint64) {
	lg := zap.NewNop()
	ms := etcdstart.Members("putgetN", k, PeerBase, ClientBase)
	srvs, err := etcdstart.StartMembers(ms, Token, lg)
	if err != nil {
		return
	}
	if k == 0 {
		return
	}

	if err := etcdstart.Serve(srvs[0], ms[0].Client); err != nil {
		return
	}

	cli, err := etcdstart.NewClient(ms[0].Client, lg)
	if err != nil {
		return
	}
	// each call in a context with the request timeout, cancelled after the call
	pctx, pcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	_, err = cli.Put(pctx, "k", "v")
	pcancel()
	if err != nil {
		return
	}
	gctx, gcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	resp, err := cli.Get(gctx, "k")
	gcancel()
	if err != nil {
		return
	}
	if len(resp.Kvs) == 0 || string(resp.Kvs[0].Value) != "v" {
		panic("putgetN: Get did not return the Put's value")
	}
}
