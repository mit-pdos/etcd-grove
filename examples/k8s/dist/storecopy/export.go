package etcd3

// This directory is a copy of examples/k8s/etcd3's package (k8setcd3.go, watch.go and realcheck.go,
// byte for byte: TestVerbatim in examples/k8s/dist checks it), so that examples/k8s/dist can split
// the driver's Check between machines: its model, its seeds, its generator and the per-client cache
// are unexported there, and the driver itself must stay as k8s_safe's proof has it. This file is
// the only addition: what the distributed workload needs of the copy, each a thin wrapper of the
// driver's own functions (notes/k8s-dist.md, "Copies").

import (
	"time"

	"github.com/anishathalye/porcupine"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/kubernetes"

	"k8s.io/apimachinery/pkg/runtime/schema"
	"k8s.io/apiserver/pkg/storage"
	"k8s.io/apiserver/pkg/storage/etcd3"
)

// Seeded is the model's store after the seeds, with its history (seed's results).
type Seeded struct {
	st0 mstore
	h0  []mstore
}

// Seed writes the seed keys through cli (the driver's seed: revisions 2 and 3 of a fresh
// cluster), or returns false.
func Seed(cli *clientv3.Client) (Seeded, bool) {
	st0, h0, ok := seed(cli)
	return Seeded{st0: st0, h0: h0}, ok
}

// Model is the driver's Model from the seeded store.
func (s Seeded) Model() porcupine.Model {
	return Model(s.st0, s.h0)
}

// NewCache is Check's per-client cache (newWCache): clients unary clients of ops operations each,
// the rest watchers, the drawn resource versions floored at the seeded store's revision.
func (s Seeded) NewCache(clients int, ops int) *cache {
	return newWCache(clients, int64(clients)*int64(ops), s.st0.rv)
}

// RealCheck is the maintainers' checker (realCheck) on a failure-free history ordered by the
// driver's linearization.
func (s Seeded) RealCheck(ops []porcupine.Operation, timeout time.Duration) porcupine.CheckResult {
	return realCheck(s.st0, ops, timeout)
}

// FailureFree is failureFree.
func FailureFree(ops []porcupine.Operation) bool {
	return failureFree(ops)
}

// NewStoreOnly is newStore without the seeds (an API server's store, made on its own machine;
// the seeds are the orchestrator's): the features set (no streaming lists, WatchList on), then the
// store over kc with the driver's codec, versioner, decoder and transformer; false if a step
// failed.
func NewStoreOnly(kc *kubernetes.Client) (storage.Interface, bool) {
	if !noStreaming() || !watchList() {
		return nil, false
	}
	s, err := etcd3.New(kc, noCompactor{}, codec{}, newObj, nil, nil, Prefix, ResourcePrefix,
		schema.GroupResource{Resource: "objs"}, identity{}, etcd3.NewDefaultLeaseManagerConfig(),
		decoder{}, versioner{})
	if err != nil {
		return nil, false
	}
	return s, true
}

// Serve is Apply's half on the API server's machine: the operation in through the store s (a
// watch: runWatch's output; otherwise call's), without the prophecy and without the cache, which
// stay with the orchestrator (Record).
func Serve(s storage.Interface, in Input) Output {
	if in.Kind == KWatch {
		out, _, _ := runWatch(s, in)
		return out
	}
	return call(s, in)
}

// Record is Apply's other half, on the orchestrator: what Apply puts in the cache tbl for the
// operation in and its output out (a watch's last object that is not an error; a unary answer
// with a name; the unary operations' count). An output whose call got no answer (a unary EOther,
// a failed watch) records nothing but the count, as Apply's output of a failed call.
func Record(tbl *cache, in Input, out Output) {
	if in.Kind == KWatch {
		if out.WFailed {
			return
		}
		evs, ok := decodeWEvents(out.WEvents)
		if !ok {
			return
		}
		if last, ok := lastObj(evs); ok {
			tbl.putW(in.Client, last)
		}
		return
	}
	if out.Err == ENone && out.Name != "" {
		tbl.put(in.Client, objOf(out))
	}
	tbl.done.Add(1)
}

// IsWrite is isWrite.
func IsWrite(in Input) bool {
	return isWrite(in)
}

// Rejections are the callbacks' own errors (errDeleteRejected, errUpdateRejected), which a Raw's
// encoding names.
func Rejections() (error, error) {
	return errDeleteRejected, errUpdateRejected
}

// SetFeatures sets the features newStore sets (no streaming lists, WatchList on), or returns
// false: the orchestrator's process has the API servers' features, as the driver's one process.
func SetFeatures() bool {
	return noStreaming() && watchList()
}
