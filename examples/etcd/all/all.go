// Package etcdall is the program of the single-process etcd theorem, etcd_robust_single_process
// (notes/etcd-unified-scope.md, after notes/k8s-unified-scope.md): the restart part, two etcd examples,
// each on a cluster of its own, at once, in one process -- restartN on k5 members (a follower stopped
// and restarted, no acknowledged write lost) and restart1 on one (the one member stopped and
// restarted). (Until 2026-11-27 it also ran the KV, Auth and Lease parts, nine more drivers; they
// went because etcd_safe_nocrash's multi-machine deployments run their workloads: notes/STATUS.md,
// 2026-11-27.)
// The drivers are called unchanged. Their clusters' member names, data directories and tokens are
// disjoint; their addresses must be too (TestAddrs), and the member ids of all their members must
// have distinct 16 low bits (TestMemberIDs), which etcd's request-id generators need of the
// process's members (TrustedCode/go_etcd_io/etcd/pkg/v3/idutil.lean).
// Each driver panics if its check fails; the theorem is that no thread panics or is stuck.
package etcdall

import (
	"sync"
	"time"

	"github.com/mit-pdos/etcd-grove/examples/etcd/restart1"
	"github.com/mit-pdos/etcd-grove/examples/etcd/restartN"
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

// Restart is the restart part: restartN.Main(k5) (a member of k5 stopped and restarted) and
// restart1.Main() (the one member stopped and restarted), at once; it returns when both have.
func Restart(k5 uint64) {
	var wg sync.WaitGroup
	wg.Add(1)
	spawn(&wg, func() { restartN.Main(k5) })
	restart1.Main()
	wg.Wait()
}

// Main runs the restart part, and returns when it has (a process ends when its main returns).
func Main(k5 uint64) {
	Restart(k5)
}
