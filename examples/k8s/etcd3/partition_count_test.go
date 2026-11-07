package etcd3

import (
	"os"
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
	st0, ok := seed(kc.Client)
	if !ok {
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
		read := input.(Input).Kind == KGet
		failed := out.(Output).Err == EOther
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
	return lintest.Run(Model(st0), apply, gen, lintest.CounterClock(), clients, ops, 0)
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
				t.Logf("%s: %v in %v; writes %d (failed %d), reads %d (failed %d); "+
					"leaders %d distinct, %d member-observed changes", name, r, time.Since(start),
					fc.writes.Load(), fc.writeFails.Load(), fc.reads.Load(), fc.readFails.Load(),
					len(fc.leaders), fc.changes)
				fc.mu.Unlock()
				if r != porcupine.Ok {
					t.Fatalf("%s: %v, want Ok", name, r)
				}
			})
		})
	}
}
