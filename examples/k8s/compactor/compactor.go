// Package compactor runs Kubernetes' etcd compactor (k8s.io/apiserver/pkg/storage/etcd3,
// compact.go) the way a cluster of API servers runs it, against one etcd member in compaction mode
// with etcd's own compactor off (retention 0: every compaction is a client's). Each simulated API
// server has its own client; servers of them start their own compactor (NewCompactor, a real
// clock, a short interval), sharedServers more share one, the process's compactor of the cluster
// (StartCompactorPerEndpoint, which registers a compactor per endpoint: the first to call it
// starts it, the others find it). The compactors coordinate through the key compact_rev_key,
// which only they write, while a writer puts other keys. Each API server samples its compactor's
// CompactRevision every interval, stops it (a shared compactor's second Stop does nothing), and
// checks:
//
//   - CompactRevision never decreases (across the samples and after Stop);
//   - after Stop it is at most the revision of a later latest Get (a revision the cluster reached);
//   - compact_rev_key, if present, holds a decimal revision, at most a later latest Get's revision.
//
// Main panics if a check fails; the theorem to prove (notes/k8s-compactor-plan.md, K4) is that it
// does not, and that no compactor panics (Compact reads the key's value only when it exists:
// nothing deletes it). The checks Main cannot state in terms of the specs (every compaction at a
// recorded revision, the key's values increasing, one interval between reaching a revision and
// compacting it) are compactor_test.go's.
//
// The API servers run Kubernetes' default configuration: ListFromCacheSnapshot (beta, on by default
// since 1.34) makes NewCompactor also start its watch loop, which follows compact_rev_key through a
// watch (the plan's Q1 (b)).
package compactor

import (
	"context"
	"strconv"
	"sync"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.uber.org/zap"
	"k8s.io/apiserver/pkg/storage/etcd3"
	"k8s.io/utils/clock"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// The client address: the string net.Listen is given is the client's endpoint, verbatim.
const clientAddr = "127.0.0.1:23976"

// The member's peer address (not served: the cluster has no other member).
const peerAddr = "127.0.0.1:23986"

// The key the compactors coordinate through (etcd3's compactRevKey).
const compactRevKey = "compact_rev_key"

// The key the writer puts, outside the compactors' key.
const writeKey = "/registry/objs/w"

// The number of API servers with a compactor of their own.
const servers = 3

// The number of API servers sharing the process's compactor.
const sharedServers = 2

// The compactors' interval.
const interval = 20 * time.Millisecond

// The number of CompactRevision samples each API server takes, one per interval.
const samples = 10

// The number of the writer's Puts.
const writes = 400

// writer puts writeKey writes times, each Put in a context with the request timeout; a failed Put
// is skipped.
func writer(cli *clientv3.Client) {
	for i := 0; i < writes; i++ {
		ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
		_, _ = cli.Put(ctx, writeKey, strconv.Itoa(i))
		cancel()
	}
}

// ready reports whether a latest Get through cli succeeds within the request timeout.
func ready(cli *clientv3.Client) bool {
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	_, err := cli.Get(ctx, compactRevKey)
	cancel()
	return err == nil
}

// compactorAPI is what an API server uses of its compactor (etcd3's *compactor, which both
// constructors return and which the package does not export).
type compactorAPI interface {
	CompactRevision() int64
	Stop()
}

// apiserver runs one API server's compactor on cli: its own (NewCompactor) or, if shared, the
// process's (StartCompactorPerEndpoint), then check.
func apiserver(cli *clientv3.Client, shared bool) {
	if shared {
		check(cli, etcd3.StartCompactorPerEndpoint(cli, interval))
	} else {
		check(cli, etcd3.NewCompactor(cli, interval, clock.RealClock{}, nil))
	}
}

// check samples the compactor's CompactRevision every interval, stops it and checks the package's
// guarantees, panicking if one fails. An error from a final Get skips the checks against it. The
// key's value is checked against a second Get, issued after the first returned it: a revision the
// cluster reached is at most the revision of a read that starts after it is known (the read-side
// law the proof uses).
func check(cli *clientv3.Client, c compactorAPI) {
	var last int64
	for i := 0; i < samples; i++ {
		time.Sleep(interval)
		r := c.CompactRevision()
		if r < last {
			panic("k8scompactor: CompactRevision decreased")
		}
		last = r
	}
	c.Stop()
	r := c.CompactRevision()
	if r < last {
		panic("k8scompactor: CompactRevision decreased after Stop")
	}

	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	resp, err := cli.Get(ctx, compactRevKey)
	cancel()
	if err != nil {
		return
	}
	if r > resp.Header.Revision {
		panic("k8scompactor: CompactRevision ahead of the cluster")
	}
	if len(resp.Kvs) != 0 {
		v, err := strconv.ParseInt(string(resp.Kvs[0].Value), 10, 64)
		if err != nil {
			panic("k8scompactor: compact_rev_key does not hold a revision")
		}
		// v is a revision the cluster reached: at most a later latest Get's revision.
		ctx2, cancel2 := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
		resp2, err := cli.Get(ctx2, compactRevKey)
		cancel2()
		if err != nil {
			return
		}
		if v > resp2.Header.Revision {
			panic("k8scompactor: compact_rev_key ahead of the cluster")
		}
	}
}

// Main starts one member of a new cluster in compaction mode with etcd's compactor off, waits for
// the member to serve, and runs the writer and the API servers (servers with their own compactor,
// then sharedServers sharing one), each on its own client, until
// every API server has stopped its compactor and made its checks. An error before the API servers
// start (the member not serving within the request timeout) ends Main without a check.
func Main() {
	lg := zap.NewNop()
	s, err := etcdstart.StartCompactingServer("k8scompactor", peerAddr, clientAddr, 0, lg)
	if err != nil {
		return
	}
	if err := etcdstart.Serve(s, clientAddr); err != nil {
		return
	}
	wcli, err := etcdstart.NewClient(clientAddr, lg)
	if err != nil {
		return
	}
	// Wait for the member to serve (elect itself leader) before starting the API servers: a
	// latest Get, which waits for a leader (an API server's storage start waits likewise).
	if !ready(wcli) {
		return
	}
	go writer(wcli)

	var wg sync.WaitGroup
	for i := 0; i < servers+sharedServers; i++ {
		cli, err := etcdstart.NewClient(clientAddr, lg)
		if err != nil {
			break
		}
		shared := i >= servers
		wg.Add(1)
		go func() {
			apiserver(cli, shared)
			wg.Done()
		}()
	}
	wg.Wait()
}
