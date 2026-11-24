// Package putget is the two programs of putget_safe, etcd's first distributed theorem
// (notes/putget-dist-plan.md): one member machine and one client machine, neither of which
// crashes (the interim form of etcd_safe, notes/etcd-dist-plan.md Q7), over a network that may
// delay, cut or refuse any connection.
//
//   - Member(peer, client) is the member machine's program: the one member of a
//     new cluster (etcdstart.StartServer: NewServer and Start; its peer URL http://peer is not
//     served, the cluster has no other member), etcd's gRPC API served on a listener at client
//     (etcdstart.Serve), and the process kept alive. It is the in-process driver
//     examples/etcd/putget's server half on a machine of its own.
//   - Client(ep) is the client machine's program: a client of the member's client
//     address ep (etcdstart.NewClient), a Put of key k with value v, a Get of k, and a panic if the
//     Get returns another value: examples/etcd/putget's client half. An error from any step ends
//     it without a check (the dist rules, examples/etcd/dist/client's package doc: any non-OK gRPC
//     error is an unknown outcome, so a failed Put is never followed by a check).
//
// Not examples/etcd/dist/server: that program serves etcd's full peer handler
// (etcdhttp.NewPeerHandler, untranslated; net/http's server is phase 7 S5) and builds its
// configuration itself, where this member is etcdstart's, whose steps are proved. With one member,
// nothing dials the peer address, so the member needs no peer handler.
package putget

import (
	"context"
	"time"

	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// Name is the member's name, its cluster's token (etcdstart.StartServer's) and its data
// directory's and WAL area's base name (etcdstart.DataBase/Name.etcd, etcdstart.WALBase/Name.etcd).
const Name = "putgetd"

// The key the client puts and gets, and its value.
const (
	Key   = "k"
	Value = "v"
)

// holdForever keeps the process alive: the member serves until the machine is stopped.
func holdForever() {
	for {
		time.Sleep(time.Hour)
	}
}

// Member runs the one member of a new cluster with the peer address peer (its peer URL, not
// served) and the client address client, serving etcd's gRPC API there; it returns only if a step
// fails (then the client's calls fail: no listener at client, or one whose member never answers).
func Member(peer string, client string) {
	s, err := etcdstart.StartServer(Name, peer, client, zap.NewNop())
	if err != nil {
		return
	}
	if err := etcdstart.Serve(s, client); err != nil {
		return
	}
	holdForever()
}

// Client puts Key with Value through a client of the endpoint ep (the member's client address,
// verbatim), gets Key, and panics if the Get returns another value. It reports whether its check
// ran: false if a step failed first (each call in a context with the examples' request timeout,
// cancelled after the call).
func Client(ep string) bool {
	cli, err := etcdstart.NewClient(ep, zap.NewNop())
	if err != nil {
		return false
	}
	pctx, pcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	_, err = cli.Put(pctx, Key, Value)
	pcancel()
	if err != nil {
		return false
	}
	gctx, gcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	resp, err := cli.Get(gctx, Key)
	gcancel()
	if err != nil {
		return false
	}
	if len(resp.Kvs) == 0 || string(resp.Kvs[0].Value) != Value {
		panic("putget: Get did not return the Put's value")
	}
	return true
}
