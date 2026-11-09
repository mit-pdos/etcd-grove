package concurrency

import (
	"context"
	"strings"
	"sync"

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
// Assumes: no client call returns one of concurrency's own error values (true: gRPC's, rpctypes'
// and the context's errors are other values; not yet a law: open question, batch-1d.md).
// Specs: NewMutex.spec, Mutex.TryLock.spec, Mutex.Unlock.spec, Mutex.Header.spec; laws:
// concErrVal_ok, init.spec.
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
// Specs: Mutex.Lock.spec, Mutex.Unlock.spec; law: init.spec.
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
// the client's (non-nil) error, as documented.
// Users: etcd's tests (mutex_test.go: NewLocker).
// Assumes: none.
// Specs: NewLocker.spec, lockerMutex.Lock.spec, lockerMutex.Unlock.spec.
func ReqLocker(s *concurrency.Session, pfx string) {
	defer func() {
		if r := recover(); r != nil {
			if _, ok := r.(error); !ok {
				panic("locker: panicked with a non-error")
			}
		}
	}()
	var l sync.Locker = concurrency.NewLocker(s, pfx)
	l.Lock()
	l.Unlock()
}
