package etcd3

import (
	"os"
	"runtime"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/kubernetes"
	"go.uber.org/zap"
	"k8s.io/apimachinery/pkg/runtime/schema"
	"k8s.io/apiserver/pkg/storage/etcd3"

	"github.com/mit-pdos/etcd-grove/examples/lib/cluster3"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/lintest"
)

// failCounts counts a run's calls by outcome: writes and reads that failed with a client error
// (EOther: the call may or may not have taken effect), and all calls.
type failCounts struct {
	writes, writeFails, reads, readFails atomic.Int64
	// each member's leader changes observed (to another nonzero leader), and the distinct
	// leaders
	mu      sync.Mutex
	last    [3]uint64
	changes int
	leaders map[uint64]bool
	// the model's work during porcupine's check: Step and Equal calls, the time in them, and the
	// largest state (configurations) a Step returned
	steps     atomic.Int64
	equals    atomic.Int64
	modelNs   atomic.Int64
	maxStates atomic.Int64
	checkNs   int64
	lists     atomic.Int64
}

// timedModel is m with its Step and Equal timed and counted in fc.
func timedModel(m porcupine.Model, fc *failCounts) porcupine.Model {
	step, equal := m.Step, m.Equal
	m.Step = func(st, in, out any) (bool, any) {
		t0 := time.Now()
		ok, next := step(st, in, out)
		fc.modelNs.Add(int64(time.Since(t0)))
		fc.steps.Add(1)
		if n := int64(len(next.(state))); n > fc.maxStates.Load() {
			fc.maxStates.Store(n)
		}
		return ok, next
	}
	m.Equal = func(a, b any) bool {
		t0 := time.Now()
		r := equal(a, b)
		fc.modelNs.Add(int64(time.Since(t0)))
		fc.equals.Add(1)
		return r
	}
	return m
}

// mainPartitionCounted is MainPartition (diagnostics only: not the theorem's program) with Check's
// apply wrapped to count the calls' outcomes in fc.
func mainPartitionCounted(clients int, ops int, sched []cluster3.Step, fc *failCounts) porcupine.CheckResult {
	lg := zap.NewNop()
	cfg := clusterConfig()
	srvs, brs, ok := cluster3.StartCluster(cfg, lg)
	if !ok {
		return porcupine.Unknown
	}
	kc, err := kubernetes.New(clientv3.Config{
		Endpoints:            []string{cfg.Bridge1, cfg.Bridge2, cfg.Bridge3},
		DialTimeout:          etcdstart.DialTimeout,
		DialKeepAliveTime:    etcdstart.KeepAliveTime,
		DialKeepAliveTimeout: etcdstart.KeepAliveTimeout,
		Logger:               lg,
	})
	if err != nil {
		return porcupine.Unknown
	}
	st0, h0, ok := seed(kc.Client)
	if !ok || !noStreaming() {
		return porcupine.Unknown
	}
	s, err := etcd3.New(kc, noCompactor{}, codec{}, newObj, nil, nil, Prefix, ResourcePrefix,
		schema.GroupResource{Resource: "objs"}, identity{}, etcd3.NewDefaultLeaseManagerConfig(),
		decoder{}, versioner{})
	if err != nil {
		return porcupine.Unknown
	}
	go cluster3.Partitioner(srvs, brs, sched)
	// the leaders the members report, every 20ms, until the check ends
	done := make(chan struct{})
	defer close(done)
	go func() {
		for {
			select {
			case <-done:
				return
			case <-time.After(20 * time.Millisecond):
			}
			for i, s := range srvs {
				if l := uint64(s.Leader()); l != 0 {
					fc.mu.Lock()
					if fc.last[i] != 0 && fc.last[i] != l {
						fc.changes++
					}
					fc.last[i] = l
					fc.leaders[l] = true
					fc.mu.Unlock()
				}
			}
		}
	}()
	tbl := newCache()
	apply := func(input any) any {
		out := Apply(s, tbl, input)
		read := !isWrite(input.(Input))
		failed := out.(Output).Err == EOther
		if input.(Input).Kind == KList {
			fc.lists.Add(1)
		}
		if read {
			fc.reads.Add(1)
			if failed {
				fc.readFails.Add(1)
			}
		} else {
			fc.writes.Add(1)
			if failed {
				fc.writeFails.Add(1)
			}
		}
		return out
	}
	gen := func(id int) any { return Gen(tbl, id) }
	t0 := time.Now()
	r := lintest.Run(timedModel(Model(st0, h0), fc), apply, gen, lintest.CounterClock(), clients, ops, 0)
	fc.checkNs = int64(time.Since(t0))
	return r
}

// TestPartitionFailures runs mainPartitionCounted on the schedule K8SETCD3_SCHED names (all by
// default), each in a process of its own (inChild), and reports how many calls failed (whether
// the schedules exercise the model's pending writes) and the leaders observed.
func TestPartitionFailures(t *testing.T) {
	only := os.Getenv("K8SETCD3_SCHED")
	for name, sched := range partitionSchedules() {
		if only != "" && name != only {
			continue
		}
		t.Run(name, func(t *testing.T) {
			inChild(t, "TestPartitionFailures", name, func(t *testing.T) {
				fc := failCounts{leaders: map[uint64]bool{}}
				start := time.Now()
				r := mainPartitionCounted(4, 60, sched, &fc)
				fc.mu.Lock()
				t.Logf("%s: %v in %v; writes %d (failed %d), reads %d (failed %d; lists %d); "+
					"leaders %d distinct, %d member-observed changes; the model during the check: "+
					"%d steps, %d equals, %v in Step/Equal, at most %d configurations; "+
					"traffic and check %v", name, r, time.Since(start),
					fc.writes.Load(), fc.writeFails.Load(), fc.reads.Load(), fc.readFails.Load(),
					fc.lists.Load(), len(fc.leaders), fc.changes, fc.steps.Load(), fc.equals.Load(),
					time.Duration(fc.modelNs.Load()), fc.maxStates.Load(), time.Duration(fc.checkNs))
				fc.mu.Unlock()
				if r != porcupine.Ok {
					t.Fatalf("%s: %v, want Ok", name, r)
				}
			})
		})
	}
}

// TestPartitionScale (only with K8SETCD3_SCALE set; diagnostics) runs mainPartitionCounted at the
// correctness test's scale (8 clients of 1250 operations) under the mixed schedule, in a process
// of its own, and reports the model's work during porcupine's check.
func TestPartitionScale(t *testing.T) {
	if os.Getenv("K8SETCD3_SCALE") == "" {
		t.Skip("set K8SETCD3_SCALE to run")
	}
	sched := partitionSchedules()["election"]
	inChild(t, "TestPartitionScale", "", func(t *testing.T) {
		fc := failCounts{leaders: map[uint64]bool{}}
		start := time.Now()
		r := mainPartitionCounted(8, 1250, sched, &fc)
		var ms runtime.MemStats
		runtime.ReadMemStats(&ms)
		t.Logf("scale: heap in use %d MiB, obtained from the OS %d MiB", ms.HeapInuse>>20, ms.Sys>>20)
		t.Logf("scale: %v in %v; writes %d (failed %d), reads %d (lists %d); the model during the check: "+
			"%d steps, %d equals, %v in Step/Equal, at most %d configurations; traffic and check %v",
			r, time.Since(start), fc.writes.Load(), fc.writeFails.Load(), fc.reads.Load(), fc.lists.Load(),
			fc.steps.Load(), fc.equals.Load(), time.Duration(fc.modelNs.Load()), fc.maxStates.Load(),
			time.Duration(fc.checkNs))
		if r != porcupine.Ok {
			t.Fatalf("scale: %v, want Ok", r)
		}
	})
}
