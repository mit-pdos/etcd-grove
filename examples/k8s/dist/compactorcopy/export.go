package compactor

// This directory is a copy of examples/k8s/compactor's package (compactor.go, byte for byte:
// TestVerbatim in examples/k8s/dist checks it), so that examples/k8s/dist can run its API servers
// and its writer on machines of their own: writer, apiserver, check and the constants are
// unexported there, and the driver itself must stay as k8s_safe's proof has it. This file is the
// only addition (notes/k8s-dist.md, "Copies"): check split in two, its sampling and reads on the
// API server's machine (Sample) and its comparisons on the orchestrator (CheckLog), the same
// comparisons on the same values.

import (
	"context"
	"strconv"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"
	"k8s.io/apiserver/pkg/storage/etcd3"
	"k8s.io/utils/clock"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// A Log is what one API server saw (check's values): its compactor's CompactRevision samples,
// the revision after Stop, and the two latest Gets of compact_rev_key that follow (each: whether it
// returned, its header's revision, whether the key was present and its value).
type Log struct {
	Samples   []int64
	Stopped   int64
	Get1      bool
	Rev1      int64
	HasKey    bool
	Value     string
	Get2      bool
	Rev2      int64
}

// Writer is writer: WriteKey written Writes times through cli, a failed Put skipped.
func Writer(cli *clientv3.Client) {
	writer(cli)
}

// The driver's constants the distributed workload names.
const (
	Servers       = servers
	SharedServers = sharedServers
	Writes        = writes
)

// NewOwn is an API server's own compactor on cli (apiserver's NewCompactor).
func NewOwn(cli *clientv3.Client) compactorAPI {
	return etcd3.NewCompactor(cli, interval, clock.RealClock{}, nil)
}

// NewShared is the process's compactor of cli's endpoints (apiserver's StartCompactorPerEndpoint).
func NewShared(cli *clientv3.Client) compactorAPI {
	return etcd3.StartCompactorPerEndpoint(cli, interval)
}

// Sample is check's first half on the API server's machine: samples CompactRevision samples one
// interval apart, stops the compactor, reads CompactRevision again, then the latest Get of
// compact_rev_key and, if it returned the key, a second one issued after it returned; it records
// every value check compares and compares none.
func Sample(cli *clientv3.Client, c compactorAPI) Log {
	var l Log
	for i := 0; i < samples; i++ {
		time.Sleep(interval)
		l.Samples = append(l.Samples, c.CompactRevision())
	}
	c.Stop()
	l.Stopped = c.CompactRevision()

	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	resp, err := cli.Get(ctx, compactRevKey)
	cancel()
	if err != nil {
		return l
	}
	l.Get1, l.Rev1 = true, resp.Header.Revision
	if len(resp.Kvs) != 0 {
		l.HasKey, l.Value = true, string(resp.Kvs[0].Value)
		ctx2, cancel2 := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
		resp2, err := cli.Get(ctx2, compactRevKey)
		cancel2()
		if err == nil {
			l.Get2, l.Rev2 = true, resp2.Header.Revision
		}
	}
	return l
}

// CheckLog is check's second half, on the orchestrator: check's comparisons, in its order, on the
// values Sample recorded; it panics with check's message if one fails.
func CheckLog(l Log) {
	var last int64
	for _, r := range l.Samples {
		if r < last {
			panic("k8scompactor: CompactRevision decreased")
		}
		last = r
	}
	r := l.Stopped
	if r < last {
		panic("k8scompactor: CompactRevision decreased after Stop")
	}
	if !l.Get1 {
		return
	}
	if r > l.Rev1 {
		panic("k8scompactor: CompactRevision ahead of the cluster")
	}
	if l.HasKey {
		v, err := strconv.ParseInt(l.Value, 10, 64)
		if err != nil {
			panic("k8scompactor: compact_rev_key does not hold a revision")
		}
		if !l.Get2 {
			return
		}
		if v > l.Rev2 {
			panic("k8scompactor: compact_rev_key ahead of the cluster")
		}
	}
}
