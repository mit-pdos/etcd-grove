package client

import (
	"context"
	"strconv"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// The compact workload's and the putget workload's rounds, and the compact workload's value and
// assumed retention (compactwatch's).
const (
	compactRounds = 20
	putgetRounds  = 50
	compactValue  = "v"
	// the retention checkCompactRev assumes: every compaction is at least one revision behind a
	// revision the cluster has reached, as the client's (each at its Put's revision minus one) and
	// the revision auto-compactor's (at any retention r >= 1) are; not the periodic compactor's
	// (Lean: WellFormed excludes compact under it, review F5)
	compactRetention = 1
)

// RunCompact is the compact workload (compactwatch.Main minus its start, copied, with its
// checkCompactRev; Lean: Workload.compact): rounds of a Put of the round's key (under
// compactPrefix) with compactValue, an explicit compaction at the revision before the Put's, a
// latest Get of the key, which must return the value at a revision at least the Put's; and, from
// the second round, a Get of the previous successful round's key at its Put's revision, which, if
// it succeeds, must return that Put's value. Then a watch of the last key from revision 2, which
// ends with ErrCompacted or sees only compactValue; and checkCompactRev. Unlike compactwatch, a
// failed Put or latest Get skips its round instead of ending the workload (the faults make errors
// common); a later round compares with the last round whose Put returned, at that Put's revision,
// which no later write of another key changes. Other workloads' writes (putget, durable) are
// allowed beside it: every check is about this workload's own keys or about compaction revisions.
func RunCompact(eps []string) Result {
	cli, err := newClient(eps)
	if err != nil {
		return ended("compact: the client failed to connect")
	}
	defer cli.Close()
	prevKey := ""
	var prevRev int64
	for i := 0; i < compactRounds; i++ {
		k := compactPrefix + "k" + strconv.Itoa(i)
		pctx, pcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
		presp, err := cli.Put(pctx, k, compactValue)
		pcancel()
		if err != nil {
			continue
		}
		// the compaction's error is ignored: another compaction may already be at or past it
		cctx, ccancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
		_, _ = cli.Compact(cctx, presp.Header.Revision-1)
		ccancel()
		gctx, gcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
		resp, err := cli.Get(gctx, k)
		gcancel()
		if err == nil {
			if len(resp.Kvs) == 0 || string(resp.Kvs[0].Value) != compactValue {
				panic("dist compact: Get did not return the round's Put")
			}
			if resp.Header.Revision < presp.Header.Revision {
				panic("dist compact: Get read below the round's Put's revision")
			}
		}
		if prevRev != 0 {
			octx, ocancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
			oresp, err := cli.Get(octx, prevKey, clientv3.WithRev(prevRev))
			ocancel()
			if err == nil {
				if len(oresp.Kvs) == 0 || string(oresp.Kvs[0].Value) != compactValue {
					panic("dist compact: Get at the previous round's revision did not return its Put")
				}
			}
		}
		prevKey = k
		prevRev = presp.Header.Revision
	}
	if prevRev == 0 {
		return ended("compact: no Put returned")
	}
	wctx, wcancel := context.WithCancel(context.Background())
	t := time.AfterFunc(readTimeout, wcancel)
	wch := cli.Watcher.Watch(wctx, prevKey, clientv3.WithRev(2))
	evs, ok := etcdstart.Collect(wch, prevRev)
	t.Stop()
	wcancel()
	if ok {
		for _, e := range evs {
			if e.Val != compactValue {
				panic("dist compact: the watch saw another value")
			}
		}
	}
	checkCompactRev(cli, prevKey)
	return checked()
}

// checkCompactRev (compactwatch's, copied): a watch of key from revision 2, whose first response
// is, if a compaction passed revision 2, the compaction's; its compaction revision is at least
// the retention behind a revision the cluster has reached, so a latest Get after it reads at a
// revision at least the compaction revision plus the retention. Panics if not. A watch that ends
// first (a closed channel) or whose first response is another checks nothing.
func checkCompactRev(cli *clientv3.Client, key string) {
	cctx, ccancel := context.WithTimeout(context.Background(), readTimeout)
	cch := cli.Watcher.Watch(cctx, key, clientv3.WithRev(2))
	crev, cok := etcdstart.CompactRev(cch)
	ccancel()
	if !cok {
		return
	}
	lctx, lcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	lresp, err := cli.Get(lctx, key)
	lcancel()
	if err == nil && lresp.Header.Revision < crev+compactRetention {
		panic("dist compact: a compaction revision within the retention of the latest revision")
	}
}

// RunPutGet is the putget workload (compacted.Main minus its start, copied, in rounds; Lean:
// Workload.putget): each round puts its own key (under putgetPrefix) with its own value and gets
// it; a Get that returns must return the value. A round whose Put failed (an unknown outcome) is
// skipped: no other round writes its key.
func RunPutGet(eps []string) Result {
	cli, err := newClient(eps)
	if err != nil {
		return ended("putget: the client failed to connect")
	}
	defer cli.Close()
	ran := false
	for i := 0; i < putgetRounds; i++ {
		k := putgetPrefix + "k" + strconv.Itoa(i)
		v := "v" + strconv.Itoa(i)
		pctx, pcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
		_, err := cli.Put(pctx, k, v)
		pcancel()
		if err != nil {
			continue
		}
		gctx, gcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
		resp, err := cli.Get(gctx, k)
		gcancel()
		if err != nil {
			continue
		}
		if len(resp.Kvs) == 0 || string(resp.Kvs[0].Value) != v {
			panic("dist putget: Get did not return the Put's value")
		}
		ran = true
	}
	if !ran {
		return ended("putget: no round's Put and Get both returned")
	}
	return checked()
}
