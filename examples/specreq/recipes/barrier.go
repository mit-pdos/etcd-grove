// Package recipes holds the requirement snippets of etcd's client recipes
// (go.etcd.io/etcd/client/v3/experimental/recipes, batch 1f): what their users (etcd's
// integration tests, tests/integration/clientv3/experimental/recipes) rely on, each violation a
// panic.
//
// "Owned" below: no other client (and no lease) writes or deletes the keys the snippet names; the
// snippet's program keeps that in its invariant over etcdState (notes/specs-only/top.md). Time is
// not modelled: a session's lease may expire at any time, unless the cluster runs with W0's
// EnvCfg.leaseExpiry = false (a trusted deployment premise: every lease outlives the run); the
// snippets marked "no lease expiry" assume that, and the others hold either way.
package recipes

import (
	"context"
	"errors"
	"sync/atomic"

	recipe "go.etcd.io/etcd/client/v3/experimental/recipes"

	clientv3 "go.etcd.io/etcd/client/v3"
)

// REQ recipes/hold-twice: holding a held barrier fails (the key exists); the first hold of an
// absent key succeeds unless etcd refuses it.
// Users: T/v3_barrier_test.go:44-45 (NoError, then Error).
// Assumes: key owned, absent at the start.
// Specs: NewBarrier.spec, Barrier.Hold.spec (putNewReq: Version(key) = 0 fails on a present key),
// the model's kvStep (.txn); laws: init.spec (ErrKeyExists), recipeErr_ne.
func ReqHoldTwice(c *clientv3.Client, key string) {
	b := recipe.NewBarrier(c, key)
	if err := b.Hold(); err != nil {
		return
	}
	if err := b.Hold(); err == nil {
		panic("hold-twice: a held barrier held again")
	} else if errors.Is(err, recipe.ErrKeyExists) {
		return
	}
}

// REQ recipes/wait-after-release: a waiter on a held barrier is released (Wait returns nil) only
// after a Release (or another delete of the key) took effect.
// Users: T/v3_barrier_test.go:58-75 (no waiter done before Release; all done after).
// Assumes: key owned, absent at the start; only this snippet's Release deletes it.
// Specs: Barrier.Hold.spec, Barrier.Wait.spec (goneAt at a revision after σ0, σ0 taken after the
// Hold), Barrier.Release.spec (its update sets the flag's ghost); laws: etcdLb_reach, etcdState_lb.
func ReqWaitAfterRelease(c *clientv3.Client, key string) {
	b := recipe.NewBarrier(c, key)
	if err := b.Hold(); err != nil {
		return
	}
	var released atomic.Bool
	done := make(chan struct{})
	go func() {
		defer close(done)
		if err := recipe.NewBarrier(c, key).Wait(); err != nil {
			return
		}
		if !released.Load() {
			panic("wait-after-release: released while held")
		}
	}()
	released.Store(true)
	if err := b.Release(); err != nil {
		return
	}
	<-done
}

// REQ recipes/wait-absent: Wait on a barrier whose key is absent can be called (and returns nil
// or an error; the specs do not promise it returns, a liveness fact).
// Users: T/v3_barrier_test.go:104-105 (another key with the barrier's name as prefix exists:
// Wait reads the single key).
// Assumes: none.
// Specs: Barrier.Wait.spec.
func ReqWaitAbsent(ctx context.Context, c *clientv3.Client, key string) {
	if _, err := c.Put(ctx, key+"-0", ""); err != nil {
		return
	}
	_ = recipe.NewBarrier(c, key).Wait()
}
