// Package compactkv is putgetc (examples/putgetc) under compaction pressure: one etcd member
// started in-process with the auto-compactor in revision mode keeping one revision, a client
// connected to it, and rounds of a Put of a key, an explicit compaction through the client at the
// revision before the Put's, and a Get of the key, checking that the Get returns the round's
// value. Main panics if a check fails; the theorem to prove is that it does not, whatever the
// compactions (the client's and the auto-compactor's, racing) did meanwhile: a latest read is never
// compacted.
//
// The explicit compactions are what a test sees: the revision compactor polls every five minutes
// (v3compactor's revInterval), so in a run of Main it never fires, and putgetc's test compacts
// nothing. Here every round but the first compacts the previous round's write away.
//
// As putgetc, Main calls only what the proofs specify (examples/common: StartCompactingServer,
// Serve, NewClient; the client's Put, Compact and Get, each in a context with the examples'
// request timeout); an error from a Put or a Get ends Main without a check.
package compactkv

import (
	"context"

	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/common"
)

// The client address: the string net.Listen is given is the client's endpoint, verbatim (a plain
// host:port, no scheme: clientv3.New's premise plainEndpoint).
const clientAddr = "127.0.0.1:23794"

// The compactor's retention, in revisions.
const retention = 1

// The key every round writes, and the values the rounds write, in order.
const key = "k"

var values = []string{"v1", "v2", "v3", "v4", "v5"}

// Main starts one member of a new cluster with the auto-compactor on and, for each value v of
// values: puts key with value v, compacts at the revision before the Put's, gets key and panics if
// the value is not v.
func Main() {
	lg := zap.NewNop()
	s, err := common.StartCompactingServer("compactkv", "127.0.0.1:23804", clientAddr, retention, lg)
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
	for _, v := range values {
		// each call in a context with the request timeout, cancelled after the call
		pctx, pcancel := context.WithTimeout(context.Background(), common.RequestTimeout)
		presp, err := cli.Put(pctx, key, v)
		pcancel()
		if err != nil {
			return
		}
		// The compaction's error is ignored: the auto-compactor may already have compacted at or
		// past this revision (ErrCompacted), and the round's check does not depend on it.
		cctx, ccancel := context.WithTimeout(context.Background(), common.RequestTimeout)
		_, _ = cli.Compact(cctx, presp.Header.Revision-1)
		ccancel()
		gctx, gcancel := context.WithTimeout(context.Background(), common.RequestTimeout)
		resp, err := cli.Get(gctx, key)
		gcancel()
		if err != nil {
			return
		}
		if len(resp.Kvs) == 0 || string(resp.Kvs[0].Value) != v {
			panic("compactkv: Get did not return the round's value")
		}
	}
}
