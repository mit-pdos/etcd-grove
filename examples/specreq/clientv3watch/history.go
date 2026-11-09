// Package clientv3watch holds the requirement snippets of etcd's Go client watch API (batch 1b,
// Spec/go_etcd_io/etcd/client/v3/ApiWatch.lean): minimal uses of the patterns the watch's users
// rely on (client/v3/concurrency, leasing, recipes, mirror, naming, the cache, grpcproxy,
// Kubernetes' etcd3 watcher and compactor, this repository's examples), each reliance an explicit
// panic.
//
// Common assumptions (the proofs' setting, as clientv3kv's): cli is a client of a cluster
// (isClient), the caller owns the cluster's state etcdState in an invariant of its own (the
// "owner's invariant"), and a prefix or key a snippet names as "owned" is written by no other
// principal and attached to no lease. Contexts are any contexts that name no other principal in
// their outgoing metadata (W0's ctxPrin: Background, TODO, Perennial's contexts and their
// children, WithRequireLeader's). Errors a watch's users handle
// (an error response, the channel closing) are handled as they do: return.
package clientv3watch

import (
	"context"

	"go.etcd.io/etcd/api/v3/mvccpb"
	clientv3 "go.etcd.io/etcd/client/v3"
)

// REQ clientv3watch/from-get: a watch from a Get's revision + 1 delivers the next write of the
// range, first: no gap, nothing before its start revision.
// Users: naming/endpoints/endpoints_impl.go:131, mirror/syncer.go:119, v3discovery/discovery.go:370,
// leasing/kv.go:174 (monitorLease), the cache (cache.go:392 after its Get), Kubernetes' etcd3
// watcher (watcher.go:493: WithRev(list revision + 1)).
// Assumes: pfx is owned (see the package comment).
// Specs: Client.Get.spec, Client.Put.spec, Client.Watch.spec (Watcher.WatchTriple), WithPrefix.spec,
// WithRev.spec; laws: watchChAt_recv (watchStep's event case at WatchPos.init), watchRespAt_fields,
// eventOwn_unfold, keyValueOwn_unfold, WatchResponse.Err.spec; etcdLb_reach (the history only grows).
func ReqWatchFromGet(ctx context.Context, cli *clientv3.Client, pfx string) {
	g, err := cli.Get(ctx, pfx, clientv3.WithPrefix())
	if err != nil {
		return
	}
	p, err := cli.Put(ctx, pfx+"a", "1")
	if err != nil {
		return
	}
	wch := cli.Watch(ctx, pfx, clientv3.WithPrefix(), clientv3.WithRev(g.Header.Revision+1))
	for wr := range wch {
		if wr.Err() != nil {
			return
		}
		if len(wr.Events) == 0 {
			continue
		}
		ev := wr.Events[0]
		if ev.Type != mvccpb.PUT || ev.Kv.ModRevision != p.Header.Revision ||
			string(ev.Kv.Key) != pfx+"a" || string(ev.Kv.Value) != "1" {
			panic("from-get: the first event is the write after the Get")
		}
		return
	}
}

// REQ clientv3watch/wait-delete: a watch from a key's revision + 1 sees its deletion, at the
// deletion's revision, as the first event if nothing else wrote the key.
// Users: concurrency/key.go:30 waitDelete (Mutex.Lock, Election.Campaign), leasing/kv.go:210
// waitRescind, experimental/recipes/watch.go:28,38 WaitEvents.
// Assumes: k is owned.
// Specs: Client.Put.spec, Client.Delete.spec, Client.Watch.spec, WithRev.spec; watchChAt_recv.
func ReqWatchWaitDelete(ctx context.Context, cli *clientv3.Client, k string) {
	p, err := cli.Put(ctx, k, "v")
	if err != nil {
		return
	}
	d, err := cli.Delete(ctx, k)
	if err != nil {
		return
	}
	for wr := range cli.Watch(ctx, k, clientv3.WithRev(p.Header.Revision+1)) {
		if wr.Err() != nil {
			return
		}
		for _, ev := range wr.Events {
			if ev.Type != mvccpb.DELETE || ev.Kv.ModRevision != d.Header.Revision {
				panic("wait-delete: the deletion, at its revision")
			}
			return
		}
	}
}

// REQ clientv3watch/revision-whole: every event of a revision comes in one response (the cache
// rejects a revision split across responses: store.go validateRevisions, demux.go
// updateStoreLocked).
// Users: the cache (cache.go:392, demux.Broadcast, store.Apply), grpcproxy's broadcast
// (watch_broadcast.go: events below nextrev dropped), Kubernetes' watch cache.
// Assumes: pfx is owned.
// Specs: Client.Txn.spec (one revision for both puts), Client.Watch.spec; watchStep's event case
// (the events of every revision from the first to the last, all of them).
func ReqWatchRevisionWhole(ctx context.Context, cli *clientv3.Client, pfx string) {
	g, err := cli.Get(ctx, pfx, clientv3.WithPrefix())
	if err != nil {
		return
	}
	t, err := cli.Txn(ctx).Then(clientv3.OpPut(pfx+"a", "1"), clientv3.OpPut(pfx+"b", "2")).Commit()
	if err != nil {
		return
	}
	for wr := range cli.Watch(ctx, pfx, clientv3.WithPrefix(), clientv3.WithRev(g.Header.Revision+1)) {
		if wr.Err() != nil {
			return
		}
		n := 0
		for _, ev := range wr.Events {
			if ev.Kv.ModRevision == t.Header.Revision {
				n++
			}
		}
		if n == 1 {
			panic("revision-whole: a revision split across responses")
		}
		if n == 2 {
			return
		}
	}
}

// REQ clientv3watch/order: whatever else writes the range, a watch's events come in revision
// order, never repeated, and a progress notification is never below the last event's revision.
// Users: the cache (validateRevisions: increasing revisions, a progress at least the latest),
// Kubernetes' etcd3 watcher (resource versions from ModRevision and progress bookmarks),
// grpcproxy (drops events below nextrev), the examples' Check (examples/lib/etcdstart/watch.go:144:
// strictly increasing revisions).
// Assumes: none (any writers, compaction, leases); a start revision (every user passes one).
// Specs: Client.Watch.spec, WithProgressNotify.spec, WatchResponse.IsProgressNotify.spec;
// watchChAt_recv (watchStep: events of the revisions after the position, progress not below it).
func ReqWatchOrder(ctx context.Context, cli *clientv3.Client, key string, rev int64) {
	if rev <= 0 {
		return // a watch from the current revision: complete only from its first event
	}
	last := rev - 1
	for wr := range cli.Watch(ctx, key, clientv3.WithPrefix(), clientv3.WithRev(rev),
		clientv3.WithProgressNotify()) {
		if wr.Err() != nil {
			return
		}
		if wr.IsProgressNotify() {
			if wr.Header.Revision < last {
				panic("order: a progress notification below the last event")
			}
			last = wr.Header.Revision
			continue
		}
		prev := last
		for _, ev := range wr.Events {
			if ev.Kv.ModRevision <= prev {
				panic("order: an event repeated or out of order")
			}
			if ev.Kv.ModRevision < last {
				panic("order: events out of order within a response")
			}
			last = ev.Kv.ModRevision
		}
	}
}

// REQ clientv3watch/filter: a watch filtering puts out delivers no put.
// Users: none today (WithFilterPut/WithFilterDelete are verified features: PRINCIPLES, "A smaller
// API is not a narrower scope"); grpcproxy forwards the filters.
// Assumes: none.
// Specs: Client.Watch.spec, WithFilterPut.spec; watchStep (WatchReq.keeps).
func ReqWatchFilter(ctx context.Context, cli *clientv3.Client, key string) {
	for wr := range cli.Watch(ctx, key, clientv3.WithPrefix(), clientv3.WithFilterPut()) {
		for _, ev := range wr.Events {
			if ev.Type == mvccpb.PUT {
				panic("filter: a put")
			}
		}
	}
}

// REQ clientv3watch/history: from revision 2, the events of an owned prefix are exactly the
// writes acknowledged under it, at their revisions (a full-history check).
// Users: examples/etcd/watch/watchkv.go:79, examples/etcd/partition/linkv3p.go:193,
// examples/etcd/auth/authkv.go:434,445, examples/etcd/compactwatch/compactkv.go:122 (Collect and
// Check: every successful Put appears at its revision).
// Assumes: pfx is owned; the owner's invariant records each acknowledged put of this function
// (its revision, key and value): here, one put.
// Specs: Client.Put.spec, Client.Watch.spec, WithRev.spec; watchStep's event case read against
// the reached history (etcdLb_reach, the history only grows).
func ReqWatchHistory(ctx context.Context, cli *clientv3.Client, pfx string) {
	p, err := cli.Put(ctx, pfx+"x", "v")
	if err != nil {
		return
	}
	for wr := range cli.Watch(ctx, pfx, clientv3.WithPrefix(), clientv3.WithRev(2)) {
		if wr.Err() != nil {
			return
		}
		for _, ev := range wr.Events {
			if ev.Kv.ModRevision > p.Header.Revision {
				panic("history: an event after the only write")
			}
			if ev.Kv.ModRevision == p.Header.Revision {
				if string(ev.Kv.Key) != pfx+"x" || string(ev.Kv.Value) != "v" {
					panic("history: the write, as acknowledged")
				}
				return
			}
			panic("history: an event no one wrote")
		}
	}
}
