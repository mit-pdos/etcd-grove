// Package compactkv is putgetc (examples/putgetc) under compaction pressure: one etcd member
// started in-process with the auto-compactor in revision mode keeping one revision, a client
// connected to it, and rounds of a Put of the round's key, an explicit compaction through the
// client at the revision before the Put's, and a Get of the round's key, checking that the Get
// returns the value; then (from the second round) a Get of the previous round's key at the previous
// round's Put revision, the revision the round compacted at, checking that, if it succeeds, it
// returns that Put's value. Main panics if a check fails; the theorem to prove is that it does not,
// whatever the compactions (the client's and the auto-compactor's, racing) did meanwhile: a latest
// read is never compacted, and a read at an old revision returns the store at that revision or fails
// (ErrCompacted, once a compaction passed it), never another value. After the rounds, a watch of
// the last round's key from revision 2 (compacted) ends with ErrCompacted or sees only the rounds'
// values.
//
// The explicit compactions are what a test sees: the revision compactor polls every five minutes
// (v3compactor's revInterval), so in a run of Main it never fires, and putgetc's test compacts
// nothing. Here every round but the first compacts the previous round's write away.
//
// As putgetc, Main calls only what the proofs specify (examples/common: StartCompactingServer,
// Serve, NewClient; the client's Put, Compact and Get, each in a context with the examples'
// request timeout); an error from a Put or a latest Get ends Main without a check, an error from the
// Get at an old revision skips its check.
package compactkv

import (
	"context"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/common"
)

// The client address: the string net.Listen is given is the client's endpoint, verbatim (a plain
// host:port, no scheme: clientv3.New's premise plainEndpoint).
const clientAddr = "127.0.0.1:23794"

// The compactor's retention, in revisions.
const retention = 1

// The value every round writes, each round at its own key.
const value = "v"

// The number of rounds.
const rounds = 5

// Main starts one member of a new cluster with the auto-compactor on and, for each of the rounds'
// keys k: puts k with value, compacts at the revision before the Put's, gets k and panics if the
// value is not value; then gets the previous round's key at the previous round's Put revision and
// panics if the Get succeeds with another value.
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
	// the rounds' keys, in order
	keys := []string{"k1", "k2", "k3", "k4", "k5"}
	// the previous round's key and its Put's revision (0 before the second round)
	prevKey := ""
	var prevRev int64
	for _, k := range keys {
		// each call in a context with the request timeout, cancelled after the call
		pctx, pcancel := context.WithTimeout(context.Background(), common.RequestTimeout)
		presp, err := cli.Put(pctx, k, value)
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
		resp, err := cli.Get(gctx, k)
		gcancel()
		if err != nil {
			return
		}
		if len(resp.Kvs) == 0 || string(resp.Kvs[0].Value) != value {
			panic("compactkv: Get did not return the round's Put")
		}
		// The previous round's Put revision is the one this round compacted at (each round writes
		// one revision), which the compaction keeps: in a run this Get returns the previous Put's
		// value. A compaction past it (the auto-compactor's) fails it with ErrCompacted, which
		// skips the check.
		if prevRev != 0 {
			octx, ocancel := context.WithTimeout(context.Background(), common.RequestTimeout)
			oresp, err := cli.Get(octx, prevKey, clientv3.WithRev(prevRev))
			ocancel()
			if err == nil {
				if len(oresp.Kvs) == 0 || string(oresp.Kvs[0].Value) != value {
					panic("compactkv: Get at the previous round's revision did not return its Put")
				}
			}
		}
		prevKey = k
		prevRev = presp.Header.Revision
	}
	// A watch of the last round's key from revision 2, below the rounds' compactions: in a run its
	// first response is the compaction's (ErrCompacted), which ends it without a check; a watch
	// that sees events (no compaction passed revision 2: every compaction failed) sees only the
	// rounds' Puts, each of value.
	if prevRev == 0 {
		return
	}
	wctx, wcancel := context.WithCancel(context.Background())
	wch := cli.Watcher.Watch(wctx, prevKey, clientv3.WithRev(2))
	evs, ok := common.Collect(wch, prevRev)
	wcancel()
	if ok {
		for _, e := range evs {
			if e.Val != value {
				panic("compactkv: the watch saw another value")
			}
		}
	}
}
