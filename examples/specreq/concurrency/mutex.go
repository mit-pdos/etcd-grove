package concurrency

import (
	"context"
	"strings"
	"sync"
	"sync/atomic"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/concurrency"
)

// REQ concurrency/fenced-write: a write guarded by the mutex's IsOwner() takes effect only in a
// state where the mutex's key is the oldest under the prefix: the transaction's own reads (after
// the write) see the mutex's key as the first-created one. Exclusion of revisions: two holders'
// fenced writes never take effect in one state.
// Users: etcd's tests (mutex_test.go: IsOwner in a Txn), v3lock's clients (fence on the key and
// its revision), notes/specs-only/top.md (the top-level story).
// Assumes: counter is not under pfx+"/".
// Specs: NewSession.spec, NewMutex.spec, Mutex.Lock.spec, Mutex.IsOwner.spec, Mutex.Key.spec,
// Client.Txn.spec and the Txn contract; laws: fence.spec, etcdLb_reach, etcdLb_init.
func ReqFencedWrite(ctx context.Context, cli *clientv3.Client, pfx, counter string) {
	s, err := concurrency.NewSession(cli)
	if err != nil {
		return
	}
	defer s.Close()
	m := concurrency.NewMutex(s, pfx)
	if err := m.Lock(ctx); err != nil {
		return
	}
	if !strings.HasPrefix(m.Key(), pfx+"/") {
		panic("mutex: key not under the prefix")
	}
	resp, err := cli.Txn(ctx).If(m.IsOwner()).
		Then(clientv3.OpPut(counter, "v"),
			clientv3.OpGet(pfx+"/", clientv3.WithFirstCreate()...),
			clientv3.OpGet(m.Key())).
		Commit()
	if err != nil || !resp.Succeeded {
		return
	}
	owner := resp.Responses[1].GetResponseRange().Kvs
	mine := resp.Responses[2].GetResponseRange().Kvs
	if len(mine) != 1 || len(owner) != 1 {
		panic("mutex: fenced write but the key is absent")
	}
	if owner[0].CreateRevision != mine[0].CreateRevision {
		panic("mutex: fenced write while an older key held the lock")
	}
	_ = m.Unlock(ctx)
}

// REQ concurrency/v3lock: v3lock's server returns the key and header of a successful Lock; the
// header's revision is positive (a revision the cluster reached, at least the key's creation).
// Users: server/etcdserver/api/v3lock/lock.go:34-50.
// Assumes: none.
// Specs: NewSession.spec (WithLease, WithContext), Session.Orphan.spec, NewMutex.spec,
// Mutex.Lock.spec, Mutex.Key.spec, Mutex.Header.spec; Wire's respHeaderOwn_unfold.
func ReqV3LockPattern(ctx context.Context, cli *clientv3.Client, lease clientv3.LeaseID, name string) {
	s, err := concurrency.NewSession(cli, concurrency.WithLease(lease), concurrency.WithContext(ctx))
	if err != nil {
		return
	}
	s.Orphan()
	m := concurrency.NewMutex(s, name)
	if err := m.Lock(ctx); err != nil {
		return
	}
	hdr, key := m.Header(), m.Key()
	if hdr == nil || hdr.Revision <= 0 || key == "" {
		panic("v3lock: no header or key")
	}
	// The remote client unlocks by deleting the key (v3lock's Unlock).
	_, _ = cli.Delete(ctx, key)
}

// REQ concurrency/trylock: TryLock either holds the lock (a header kept) or returns ErrLocked,
// the mutex released (a following Unlock is ErrLockReleased).
// Users: etcd's tests (mutex_test.go: TestMutexTryLock*), example_mutex_test.go.
// Assumes: none.
// Specs: NewMutex.spec, Mutex.TryLock.spec (ErrLocked: the value of its variable; any other
// error notConcErr), Mutex.Unlock.spec (on the released mutex only ErrLockReleased); law: init.spec
// (the variables' values, concErrsOk).
func ReqTryLock(ctx context.Context, s *concurrency.Session, pfx string) {
	m := concurrency.NewMutex(s, pfx)
	err := m.TryLock(ctx)
	switch {
	case err == nil:
		if m.Header() == nil {
			panic("trylock: held without a header")
		}
		_ = m.Unlock(ctx)
	case err == concurrency.ErrLocked:
		if m.Unlock(ctx) != concurrency.ErrLockReleased {
			panic("trylock: ErrLocked but not released")
		}
	}
}

// REQ concurrency/lock-unlock: Unlock after Lock deletes the key; a second Unlock is
// ErrLockReleased.
// Users: etcd's tests (mutex_test.go), v3lock's clients.
// Assumes: none.
// Specs: Mutex.Lock.spec, Mutex.Unlock.spec (nil releases; on the released mutex only
// ErrLockReleased); law: init.spec.
func ReqLockUnlock(ctx context.Context, s *concurrency.Session, pfx string) {
	m := concurrency.NewMutex(s, pfx)
	if err := m.Lock(ctx); err != nil {
		return
	}
	if err := m.Unlock(ctx); err != nil {
		return
	}
	if m.Unlock(ctx) != concurrency.ErrLockReleased {
		panic("unlock: second unlock not ErrLockReleased")
	}
}

// REQ concurrency/locker: NewLocker's Lock/Unlock as a sync.Locker: they return, or panic with
// the client's (non-nil) error, as documented; the caller recovers.
// Users: etcd's tests (mutex_test.go: NewLocker).
// Assumes: none.
// Specs: NewLocker.spec, lockerMutex.Lock.spec, lockerMutex.Unlock.spec.
func ReqLocker(s *concurrency.Session, pfx string) {
	defer func() {
		_ = recover()
	}()
	var l sync.Locker = concurrency.NewLocker(s, pfx)
	l.Lock()
	l.Unlock()
}

// REQ concurrency/lock-after-unlock: a lock taken after another was released has a later header
// revision (the result is a state reached after what the caller knew).
// Users: tests/integration/v3lock_grpc_test.go:49 (l1.Header.Revision < l2.Header.Revision), v3lock's
// remote clients ordering their critical sections.
// Assumes: no other principal writes under pfx+"/".
// Specs: Mutex.Lock.spec (Reach σ0 σ), Mutex.Unlock.spec, Mutex.Header.spec; Reach monotone (a
// pure fact: the revision does not decrease).
func ReqLockAfterUnlock(ctx context.Context, s1, s2 *concurrency.Session, pfx string) {
	m1 := concurrency.NewMutex(s1, pfx)
	if err := m1.Lock(ctx); err != nil {
		return
	}
	r1 := m1.Header().Revision
	if err := m1.Unlock(ctx); err != nil {
		return
	}
	m2 := concurrency.NewMutex(s2, pfx)
	if err := m2.Lock(ctx); err != nil {
		return
	}
	if m2.Header().Revision <= r1 {
		panic("lock: a later lock's header is not later")
	}
}

// REQ concurrency/mutex-no-two-holders: with no lease expiry, a second locker does not return
// from Lock while the first holds the lock (time exclusion, not only revision fencing).
// Users: tests/integration/clientv3/experimental/recipes/v3_lock_test.go:57-99 (testMutexLock:
// "lock %d followers did not wait"), :194-284 (TestMutexWaitsOnCurrentHolder: "new owner obtained
// lock before first owner unlocked"); etcdctl lock (lockUntilSignal runs the command holding it).
// Assumes: no lease expiry (W0's EnvCfg.leaseExpiry = false); pfx+"/" owned, empty at the start;
// no other client revokes the two sessions' leases.
// Specs: NewSession.spec (the grant's pre-state sigma_g, after the first session's grant, has no
// lease id2 while id1 is still live there: id1 != id2), NewMutex.spec, Mutex.Lock.spec (the key
// k = sessKey pfx id, lockedSince, cr above sigma0's revision for a key created after it),
// Mutex.Unlock.spec; mutexEff (each mutex writes only its session's key, so "k1 present while
// released is false" is stable under m2's permission); laws: etcdLb_reach, etcdLb_init.
// Proof idea: m1's key k1 is present, created at r1 <= sigma1's revision, until m1.Unlock; m2's
// key k2 is absent at sigma1 (fresh lease), so m2's cr is above sigma1's revision; m2's lockedSince
// (noOlder pfx cr) at its state sigma2 excludes k1 there, so released was set before sigma2.
func ReqMutexNoTwoHolders(ctx context.Context, cli *clientv3.Client, pfx string) {
	s1, err := concurrency.NewSession(cli)
	if err != nil {
		return
	}
	defer s1.Close()
	s2, err := concurrency.NewSession(cli)
	if err != nil {
		return
	}
	defer s2.Close()
	m1 := concurrency.NewMutex(s1, pfx)
	if err := m1.Lock(ctx); err != nil {
		return
	}
	var released atomic.Bool
	done := make(chan struct{})
	go func() {
		defer close(done)
		m2 := concurrency.NewMutex(s2, pfx)
		if err := m2.Lock(ctx); err != nil {
			return
		}
		if !released.Load() {
			panic("mutex: two holders at once")
		}
		_ = m2.Unlock(ctx)
	}()
	released.Store(true)
	_ = m1.Unlock(ctx)
	<-done
}
