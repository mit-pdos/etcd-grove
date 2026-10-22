// Package linkv3 is linkv (examples/linkv) over a three-member cluster: three etcd members started
// in-process as examples/putget3 starts them, each serving its raft handler on its own peer
// listener, a client connected to the first member, and linkv's workload (linkv.Check:
// lintest.Run with concurrent clients doing Put and Get of a few keys through that client,
// checked by porcupine against linkv's key-value model). Main panics if porcupine finds the
// history not linearizable; the theorem is that it does not (D20, D21).
//
// The workload is package linkv's (Gen, Apply, Model, Check), imported, so that their proofs
// carry over unchanged. The start of a member is putget3's, the examples' shared StartMember
// (examples/common), on linkv3's own member names, cluster token and ports.
package linkv3

import (
	"github.com/anishathalye/porcupine"
	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/types"

	"github.com/mit-pdos/etcd-grove/examples/common"
	"github.com/mit-pdos/etcd-grove/examples/linkv"
)

// The members' peer addresses (each member's one peer URL is http://<addr>, served by that
// member's raft handler) and client addresses (only the first is served, to the client: a plain
// host:port, clientv3.New's premise). Not putget's, putget3's or linkv's, so that the examples'
// tests can run at once.
const (
	peerAddr1   = "127.0.0.1:23821"
	peerAddr2   = "127.0.0.1:23822"
	peerAddr3   = "127.0.0.1:23823"
	clientAddr  = "127.0.0.1:23811"
	clientAddr2 = "127.0.0.1:23812"
	clientAddr3 = "127.0.0.1:23813"
)

// Main starts the three members of a new cluster, connects a client to the first and runs
// linkv.Check; it panics if porcupine finds the history illegal. An error from a step before
// Check ends Main without a check (the specs allow every step to fail).
func Main(clients int, ops int) porcupine.CheckResult {
	lg := zap.NewNop()
	peer1 := types.URLs{{Scheme: "http", Host: peerAddr1}}
	peer2 := types.URLs{{Scheme: "http", Host: peerAddr2}}
	peer3 := types.URLs{{Scheme: "http", Host: peerAddr3}}
	cluster := types.URLsMap{"linkv3-1": peer1, "linkv3-2": peer2, "linkv3-3": peer3}

	s, err := common.StartMember("linkv3-1", peer1, peerAddr1, clientAddr, cluster, "linkv3", lg)
	if err != nil {
		return porcupine.Unknown
	}
	if _, err := common.StartMember("linkv3-2", peer2, peerAddr2, clientAddr2, cluster, "linkv3", lg); err != nil {
		return porcupine.Unknown
	}
	if _, err := common.StartMember("linkv3-3", peer3, peerAddr3, clientAddr3, cluster, "linkv3", lg); err != nil {
		return porcupine.Unknown
	}

	if err := common.Serve(s, clientAddr); err != nil {
		return porcupine.Unknown
	}

	// etcd's default client configuration (its default retries): the members never answer with a
	// refusal (authentication off, voters), so a Put is sent at most once and the cluster applies it
	// at most once, while a read may be retried (decision D29).
	cli, err := common.NewClient(clientAddr, lg)
	if err != nil {
		return porcupine.Unknown
	}
	r := linkv.Check(cli, clients, ops, 0)
	if r == porcupine.Illegal {
		panic("linkv3: porcupine found the history not linearizable")
	}
	return r
}
