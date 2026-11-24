// Package bridgeaddrleft: a counterexample to bridge.New's spec before 2026-11-24 (notes/decisions.md,
// "bridge.New consumes what sets the bridged address's protocols"). With etcd-dist's interim axioms (branch
// dist-putget-interim/2026-11-24: Client_Get_dist, etcdAddrAt := ∃σ, grpcAddrAt a (etcdSvc γE mid)) and the old
// bridge.New, it has a proof of no panic (notes/axiom-review/bridge-addrleft.md); it panics.
package bridgeaddrleft

import (
	"context"
	"net"

	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/third_party/bridge"
)

const (
	peerB   = "127.0.0.1:23820"
	clientB = "127.0.0.1:23821" // a real etcd member serves here (etcdstart.Serve, netAddrFree b)
	addrA   = "127.0.0.1:23822" // net.Listen(netAddrFree a) leaves netAddrLeft a -> etcdAddrAt a γE mid
)

func Main() {
	lg := zap.NewNop()
	s, err := etcdstart.StartServer("bridgeaddrleft", peerB, clientB, lg)
	if err != nil {
		return
	}
	if err := etcdstart.Serve(s, clientB); err != nil {
		return
	}
	l, err := net.Listen("tcp", addrA)
	if err != nil {
		return
	}
	bridge.New(clientB, l)
	cli, err := etcdstart.NewClient(addrA, lg)
	if err != nil {
		return
	}
	gctx, gcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	resp, err := cli.Get(gctx, "k")
	gcancel()
	if err != nil {
		return
	}
	// A5's post (err = nil): resp's first key-value has value "v".
	if len(resp.Kvs) == 0 || string(resp.Kvs[0].Value) != "v" {
		panic("bridgeaddrleft: Get did not return v")
	}
}
