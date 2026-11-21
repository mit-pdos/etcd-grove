// Package k8sall is the program of the one closed Kubernetes theorem, k8s_safe
// (notes/k8s-unified-scope.md, notes/k8s-compactor-n-plan.md): the Kubernetes etcd3 store's
// partitioned workload on k1 members (examples/k8s/etcd3's MainPartition) and Kubernetes' compactor
// under partitions on k2 more members (examples/k8s/compactor's MainPartition), at once, in one
// process. The two drivers are called unchanged: their clusters' addresses, member names, data
// directories and tokens are disjoint, and the member ids of all k1+k2 members have distinct 16 low
// bits for every k1 <= 1000 and k2 <= 600 (TestMemberIDs), which etcd's request-id generators need of
// the process's members.
// Each driver panics if its check fails; the theorem is that no thread panics or is stuck.
package k8sall

import (
	"sync"
	"time"

	"github.com/mit-pdos/etcd-grove/examples/k8s/compactor"
	k8setcd3 "github.com/mit-pdos/etcd-grove/examples/k8s/etcd3"
	"github.com/mit-pdos/etcd-grove/examples/lib/cluster3"
)

// holdToken sleeps forever: Main runs it on a goroutine of its own, which touches nothing; the
// proof keeps that goroutine's thread token for the store's goroutine to exit with (as
// examples/k8s/etcd3's holdToken).
func holdToken() {
	for {
		time.Sleep(time.Hour)
	}
}

// Main runs k8setcd3.MainPartition(k1, clients, ops, watchers, wops, sched1) on a goroutine and
// compactor.MainPartition(k2, sched2) on its own, and returns when both have (a process ends when its
// main returns).
func Main(k1 uint64, clients int, ops int, watchers int, wops int, sched1 []cluster3.Step,
	k2 uint64, sched2 []cluster3.Step) {
	go holdToken()
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		k8setcd3.MainPartition(k1, clients, ops, watchers, wops, sched1)
		wg.Done()
	}()
	compactor.MainPartition(k2, sched2)
	wg.Wait()
}
