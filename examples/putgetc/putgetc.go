// Package putgetc is putget with the auto-compactor on (notes/m2-plan.md): one etcd member started
// in-process with the compactor in periodic mode keeping a period of 10ms (since 2026-11-02; until
// then in revision mode keeping one revision, which examples/compactkv covers: a period that
// short compacts, during a run, every revision the store had 10ms before), a client connected to
// it, a Put of a key and a Get of the same key, and a check that the Get returns the Put's value.
// Main panics if the check fails; the theorem to prove is that it does not, whatever the compactor
// did meanwhile (a latest read is never compacted).
//
// As putget, Main calls only what the proofs specify (examples/common: StartPeriodicServer,
// Serve, NewClient; the client's Put and Get, each in a context with the examples' request
// timeout); an error from any step ends Main without a check.
package putgetc

import (
	"context"
	"time"

	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/common"
)

// The client address: the string net.Listen is given is the client's endpoint, verbatim (a plain
// host:port, no scheme: clientv3.New's premise plainEndpoint).
const clientAddr = "127.0.0.1:23791"

// The compactor's period.
const period = 10 * time.Millisecond

// Main starts one member of a new cluster with the auto-compactor on (periodic), puts key "k" with value
// "v", gets "k" and panics if the value is not "v".
func Main() {
	lg := zap.NewNop()
	s, err := common.StartPeriodicServer("putgetc", "127.0.0.1:23801", clientAddr, period, lg)
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
		panic("putgetc: Get did not return the Put's value")
	}
}
