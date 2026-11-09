package recipes

import (
	"context"
	"sync/atomic"

	"go.etcd.io/etcd/client/v3/concurrency"
	recipe "go.etcd.io/etcd/client/v3/experimental/recipes"

	clientv3 "go.etcd.io/etcd/client/v3"
)

// REQ recipes/rwmutex-writers-exclude: a writer acquires only once every older lock key under the
// prefix is gone: after the second writer's Lock returns nil, the first writer's key (older) is no
// longer there. (Exclusion in time, which the test checks, would need the first session's lease to
// outlive the second Lock: not modelled; this is the revision fencing the code provides.)
// Users: T/v3_lock_test.go:314-360 (testRWMutex: no reader or writer acquires while a writer
// holds).
// Assumes: the prefix pfx+"/" owned by m1 and m2 (no other key under it); s1, s2 sessions of c.
// Specs: NewRWMutex.spec, RWMutex.Lock.spec (rwHeld over pfx/ at a state after its key's
// creation), Client.Get.spec; laws: etcdLb_reach (the key, never recreated, stays gone).
func ReqWritersExclude(ctx context.Context, c *clientv3.Client, s1, s2 *concurrency.Session, pfx string) {
	m1 := recipe.NewRWMutex(s1, pfx)
	if err := m1.Lock(); err != nil {
		return
	}
	g, err := c.Get(ctx, pfx+"/", clientv3.WithPrefix())
	if err != nil || len(g.Kvs) != 1 {
		return // m1's key may already be gone (its lease)
	}
	k1, r1 := string(g.Kvs[0].Key), g.Kvs[0].CreateRevision
	m2 := recipe.NewRWMutex(s2, pfx)
	if err := m2.Lock(); err != nil {
		return
	}
	g, err = c.Get(ctx, k1)
	if err != nil {
		return
	}
	if len(g.Kvs) == 1 && g.Kvs[0].CreateRevision == r1 {
		panic("rwmutex-writers-exclude: a writer acquired while an older writer's key existed")
	}
}

// REQ recipes/rwmutex-reader-after-writer: a reader acquires only once every older writer's key
// is gone; Unlock and RUnlock delete the held key.
// Users: T/v3_lock_test.go:326-357 (RLock, Lock, Unlock, RUnlock).
// Assumes: the prefix pfx+"/" owned by m1 and m2; s1, s2 sessions of c.
// Specs: RWMutex.Lock.spec, RWMutex.RLock.spec (rwHeld over pfx/write), RWMutex.Unlock.spec,
// RWMutex.RUnlock.spec, Client.Get.spec.
func ReqReaderAfterWriter(ctx context.Context, c *clientv3.Client, s1, s2 *concurrency.Session, pfx string) {
	m1 := recipe.NewRWMutex(s1, pfx)
	if err := m1.Lock(); err != nil {
		return
	}
	g, err := c.Get(ctx, pfx+"/write", clientv3.WithPrefix())
	if err != nil || len(g.Kvs) != 1 {
		return
	}
	k1, r1 := string(g.Kvs[0].Key), g.Kvs[0].CreateRevision
	done := make(chan struct{})
	go func() {
		defer close(done)
		m2 := recipe.NewRWMutex(s2, pfx)
		if err := m2.RLock(); err != nil {
			return
		}
		g, err := c.Get(ctx, k1)
		if err != nil {
			return
		}
		if len(g.Kvs) == 1 && g.Kvs[0].CreateRevision == r1 {
			panic("rwmutex-reader-after-writer: a reader acquired while an older writer's key existed")
		}
		_ = m2.RUnlock()
	}()
	_ = m1.Unlock()
	<-done
}

// REQ recipes/rwmutex-no-two-holders: with no lease expiry, a writer and a reader never hold the
// mutex at once (each handle is unlocked by another goroutine, as the test does).
// Users: T/v3_lock_test.go:314-360 (the non-blocking checks: no reader or writer acquires while a
// writer holds).
// Assumes: no lease expiry (EnvCfg.leaseExpiry = false); pfx+"/" owned by these two mutexes.
// Specs: RWMutex.Lock.spec, RWMutex.RLock.spec (rwHeld: the older key gone, deleted only by its
// owner's Unlock or RUnlock), RWMutex.Unlock.spec, RWMutex.RUnlock.spec.
func ReqNoTwoHolders(s1, s2 *concurrency.Session, pfx string) {
	var holders atomic.Int32
	type held struct {
		m      *recipe.RWMutex
		reader bool
	}
	done := make(chan held, 2)
	go func() {
		m := recipe.NewRWMutex(s1, pfx)
		if err := m.Lock(); err != nil {
			done <- held{}
			return
		}
		if holders.Add(1) != 1 {
			panic("rwmutex-no-two-holders: a writer acquired while another held")
		}
		done <- held{m, false}
	}()
	go func() {
		m := recipe.NewRWMutex(s2, pfx)
		if err := m.RLock(); err != nil {
			done <- held{}
			return
		}
		if holders.Add(1) != 1 {
			panic("rwmutex-no-two-holders: a reader acquired while a writer held")
		}
		done <- held{m, true}
	}()
	for i := 0; i < 2; i++ {
		h := <-done
		if h.m == nil {
			continue
		}
		holders.Add(-1)
		if h.reader {
			_ = h.m.RUnlock()
		} else {
			_ = h.m.Unlock()
		}
	}
}
