// Package etcdall is the program of the one closed etcd theorem, etcd_safe
// (notes/etcd-unified-scope.md, after notes/k8s-unified-scope.md): eleven etcd examples, each on a
// cluster of its own, at once, in one process -- the KV part (txnlinfaultsN's partitioned
// linearizability workload on k1 members, partition's watch workload under partitions on three,
// compactwatch's revision compactor, compacted's periodic compactor under a Put and a Get, and cache's
// watch cache, on one member each), the auth part (authN on k2 members, authlease on k3), the lease
// part (leaseN on k4, leasecatchup's snapshot catch-up on three) and the restart part (restartN on k5,
// restart1 on one). (leaseexpiryN is not among them: its leases expire, which authlease's and
// leasecatchup's premise lease.leasesNoExpiry, a claim about every lessor of the process, excludes;
// notes/etcd-unified-scope.md §2.2 C.)
// The drivers are called unchanged. Their clusters' member names, data directories and tokens are
// disjoint; their addresses must be too (TestAddrs), and the member ids of all their members must
// have distinct 16 low bits (TestMemberIDs), which etcd's request-id generators need of the
// process's members (TrustedCode/go_etcd_io/etcd/pkg/v3/idutil.lean).
// Main runs the four parts (KV, Auth, Lease, Restart), each running its drivers at once; each part
// has its own triple, so that the parts are proved (and land) one at a time. Each driver panics if
// its check fails; the theorem is that no thread panics or is stuck.
package etcdall

import (
	"sync"
	"time"

	"github.com/mit-pdos/etcd-grove/examples/etcd/authN"
	"github.com/mit-pdos/etcd-grove/examples/etcd/authlease"
	"github.com/mit-pdos/etcd-grove/examples/etcd/cache"
	"github.com/mit-pdos/etcd-grove/examples/etcd/compacted"
	"github.com/mit-pdos/etcd-grove/examples/etcd/compactwatch"
	"github.com/mit-pdos/etcd-grove/examples/etcd/leaseN"
	"github.com/mit-pdos/etcd-grove/examples/etcd/leasecatchup"
	"github.com/mit-pdos/etcd-grove/examples/etcd/partition"
	"github.com/mit-pdos/etcd-grove/examples/etcd/restart1"
	"github.com/mit-pdos/etcd-grove/examples/etcd/restartN"
	"github.com/mit-pdos/etcd-grove/examples/etcd/txnlinfaultsN"
	"github.com/mit-pdos/etcd-grove/examples/lib/cluster3"
)

// holdToken sleeps forever: spawn runs it on a goroutine of its own, which touches nothing; the
// proof keeps that goroutine's thread token for the part's goroutine to exit with (as
// examples/k8s/all's holdToken).
func holdToken() {
	for {
		time.Sleep(time.Hour)
	}
}

// spawn runs f on a goroutine of its own, which calls wg.Done when f returns, beside a holdToken
// goroutine (whose thread token the f goroutine exits with: each driver's triple consumes the token
// it is given).
func spawn(wg *sync.WaitGroup, f func()) {
	go holdToken()
	go func() {
		f()
		wg.Done()
	}()
}

// KV is the KV part: txnlinfaultsN.Main(k1, clients, ops, sched1) (k1 members under partitions,
// porcupine's check of the history), partition.MainWatch(nw, nops, sched2) (three members under
// partitions, watches), compactwatch.Main() (one member, the revision auto-compactor, compacted
// watches), compacted.Main() (one member, the periodic auto-compactor, a Put then a Get of its key)
// and cache.Main(cnw, cnops) (one member, the periodic auto-compactor, etcd's watch cache), at once;
// it returns when all have. Their results are dropped: a failed check is a panic.
func KV(k1 uint64, clients int, ops int, sched1 []cluster3.Step, nw int, nops int,
	sched2 []cluster3.Step, cnw int, cnops int) {
	var wg sync.WaitGroup
	wg.Add(4)
	spawn(&wg, func() { txnlinfaultsN.Main(k1, clients, ops, sched1) })
	spawn(&wg, func() { partition.MainWatch(nw, nops, sched2) })
	spawn(&wg, func() { compactwatch.Main() })
	spawn(&wg, func() { compacted.Main() })
	cache.Main(cnw, cnops)
	wg.Wait()
}

// Auth is the auth part: authN.Main(k2) and authlease.Main(k3) (k2 and k3 members with auth on), at
// once; it returns when both have.
func Auth(k2 uint64, k3 uint64) {
	var wg sync.WaitGroup
	wg.Add(1)
	spawn(&wg, func() { authN.Main(k2) })
	authlease.Main(k3)
	wg.Wait()
}

// Lease is the lease part: leaseN.Main(k4) (k4 members, lease reads) and leasecatchup.Main() (three
// members, a lessor recovered from a snapshot), at once; it returns when both have.
func Lease(k4 uint64) {
	var wg sync.WaitGroup
	wg.Add(1)
	spawn(&wg, func() { leaseN.Main(k4) })
	leasecatchup.Main()
	wg.Wait()
}

// Restart is the restart part: restartN.Main(k5) (a member of k5 stopped and restarted) and
// restart1.Main() (the one member stopped and restarted), at once; it returns when both have.
func Restart(k5 uint64) {
	var wg sync.WaitGroup
	wg.Add(1)
	spawn(&wg, func() { restartN.Main(k5) })
	restart1.Main()
	wg.Wait()
}

// Main runs the four parts at once, three on goroutines of their own (spawn) and Restart on its own
// thread, and returns when all have (a process ends when its main returns).
func Main(k1 uint64, clients int, ops int, sched1 []cluster3.Step, nw int, nops int,
	sched2 []cluster3.Step, cnw int, cnops int, k2 uint64, k3 uint64, k4 uint64, k5 uint64) {
	var wg sync.WaitGroup
	wg.Add(3)
	spawn(&wg, func() { KV(k1, clients, ops, sched1, nw, nops, sched2, cnw, cnops) })
	spawn(&wg, func() { Auth(k2, k3) })
	spawn(&wg, func() { Lease(k4) })
	Restart(k5)
	wg.Wait()
}
