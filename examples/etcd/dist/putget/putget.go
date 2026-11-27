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

// decimal is the value of s as a canonical decimal numeral (digits, at least one, no leading
// zero), at most max; false otherwise.
func decimal(s string, max uint64) (uint64, bool) {
	if len(s) == 0 || len(s) > 5 || (len(s) > 1 && s[0] == '0') {
		return 0, false
	}
	n := uint64(0)
	for i := 0; i < len(s); i++ {
		if s[i] < '0' || s[i] > '9' {
			return 0, false
		}
		n = n*10 + uint64(s[i]-'0')
	}
	return n, n <= max
}

// AddrOk says whether a is a well-formed address: the canonical spelling a.b.c.d:p of an IPv4
// address that is not in 0.0.0.0/8 and is below 224.0.0.0, with a port in 1-32767 or 61000-65535
// (outside Linux's default ephemeral range). It is the net extension's addrOk
// (GooseLang/Ext/Net/Deploy.lean): Member and Client check their addresses with it, so that the
// top-level theorem needs no premise on them. (A copy of examples/raft/kvnet's AddrOk.)
func AddrOk(a string) bool {
	var parts [5]string
	n := 0
	start := 0
	for i := 0; i <= len(a); i++ {
		end := i == len(a)
		if end || a[i] == '.' || a[i] == ':' {
			// three dots, then one colon, in that order
			if n >= 5 || (!end && a[i] == '.' && n >= 3) || (!end && a[i] == ':' && n != 3) || (end && n != 4) {
				return false
			}
			parts[n] = a[start:i]
			n++
			start = i + 1
		}
	}
	var v [5]uint64
	for i := 0; i < 5; i++ {
		x, ok := decimal(parts[i], 65535)
		if !ok {
			return false
		}
		v[i] = x
	}
	return 1 <= v[0] && v[0] < 224 && v[1] <= 255 && v[2] <= 255 && v[3] <= 255 &&
		1 <= v[4] && (v[4] < 32768 || 60999 < v[4])
}

// Member runs the one member of a new cluster with the peer address peer (its peer URL, not
// served) and the client address client, serving etcd's gRPC API there; it returns only if a step
// fails (then the client's calls fail: no listener at client, or one whose member never answers).
// It returns at once unless its two addresses are well formed (AddrOk) and distinct.
func Member(peer string, client string) {
	if !AddrOk(peer) || !AddrOk(client) || peer == client {
		return
	}
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
// cancelled after the call). It returns false at once unless ep is well formed (AddrOk).
func Client(ep string) bool {
	if !AddrOk(ep) {
		return false
	}
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
