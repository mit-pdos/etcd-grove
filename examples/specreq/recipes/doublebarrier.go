package recipes

import (
	"context"
	"errors"
	"sync/atomic"

	"go.etcd.io/etcd/client/v3/concurrency"
	recipe "go.etcd.io/etcd/client/v3/experimental/recipes"

	clientv3 "go.etcd.io/etcd/client/v3"
)

// REQ recipes/dbarrier-enter-ready: Enter returns nil only once the barrier's ready key was put
// after this entrant's own waiter key: never before the count-th entrant arrived, for a key used
// for one round. Observed: a ready key written by no one else must exist once Enter returned nil
// (no Leave was called, so nothing deleted it).
// Users: T/v3_double_barrier_test.go:36-96 (TestDoubleBarrier: no entrant passes before the
// last enters), T/v3_closed_watch_test.go:205-231 (a closed client: an error, not nil).
// Assumes: the keys under key+"/" owned by this snippet's barriers; one round; no Leave.
// Specs: NewDoubleBarrier.spec, DoubleBarrier.Enter.spec (readyPutAt at a revision ≥ its key's
// creation), Client.Get.spec, the caller's dbPerm (only Enter's writes happen: the program's
// invariant counts its own calls).
func ReqEnterReady(ctx context.Context, c *clientv3.Client, s1, s2 *concurrency.Session, key string) {
	errc := make(chan error, 2)
	for _, s := range []*concurrency.Session{s1, s2} {
		go func() { errc <- recipe.NewDoubleBarrier(s, key, 2).Enter() }()
	}
	for i := 0; i < 2; i++ {
		if err := <-errc; err != nil {
			continue
		}
		g, err := c.Get(ctx, key+"/ready")
		if err != nil {
			continue
		}
		if len(g.Kvs) != 1 {
			panic("dbarrier-enter-ready: entered before the ready key was put")
		}
	}
}

// REQ recipes/dbarrier-too-many: an entrant that finds the count reached gets ErrTooManyClients
// (with count waiters observed after it started), never nil; Leave after a successful Enter can
// be called (myKey is set: Leave dereferences it).
// Users: T/v3_double_barrier_test.go:99-163 (TestDoubleBarrierTooManyClients: errors.Is the
// sentinel), :60, :92, :140, :198 (Leave after Enter).
// Assumes: key owned; one round. (The test's "10 waiters present, so the 11th gets
// ErrTooManyClients" needs their leases to stay: not modelled; the snippet checks the converse,
// that nil comes only with fewer than count waiters at the first read.)
// Specs: DoubleBarrier.Enter.spec (nil: fewer than count waiters at a revision after σ0; the
// sentinel from init.spec), DoubleBarrier.Leave.spec (its premise: myKey set), Client.Get.spec.
func ReqEnterThenLeave(ctx context.Context, c *clientv3.Client, s *concurrency.Session, key string) {
	b := recipe.NewDoubleBarrier(s, key, 1)
	if err := b.Enter(); err != nil {
		if errors.Is(err, recipe.ErrTooManyClients) {
			return
		}
		return
	}
	_ = b.Leave()
	// a second entrant after the first entered: nil only if, at its first read, no waiter was
	// there; the first's key was (read here), so nil means it was gone by then
	b1 := recipe.NewDoubleBarrier(s, key+"-full", 1)
	if err := b1.Enter(); err != nil {
		return
	}
	g, err := c.Get(ctx, key+"-full/waiters", clientv3.WithPrefix())
	if err != nil || len(g.Kvs) != 1 {
		return
	}
	k1, r1 := string(g.Kvs[0].Key), g.Kvs[0].CreateRevision
	if err := recipe.NewDoubleBarrier(s, key+"-full", 1).Enter(); err != nil {
		return
	}
	g, err = c.Get(ctx, k1)
	if err != nil {
		return
	}
	if len(g.Kvs) == 1 && g.Kvs[0].CreateRevision == r1 {
		panic("dbarrier-too-many: entered a full barrier while its waiter was there")
	}
}

// REQ recipes/dbarrier-count: with no lease expiry, no Enter returns nil before count entrants
// started entering, and an Enter on a barrier whose count keys are held never returns nil.
// Users: T/v3_double_barrier_test.go:46-100 (no entrant passes before the last enters),
// :116-162 (the 11th gets ErrTooManyClients).
// Assumes: no lease expiry (EnvCfg.leaseExpiry = false); key+"/" owned by these barriers; one
// round; no Leave.
// Specs: DoubleBarrier.Enter.spec (the creation and the own delete are the caller's one-shot
// updates, so the invariant counts the keys created, each after its entrant's counter increment;
// ready is put only after count waiters, dbPerm's guard; nil only with fewer than count waiters at
// the first read).
func ReqEnterCount(s1, s2, s3 *concurrency.Session, key string) {
	var entered atomic.Int32
	errc := make(chan error, 2)
	for _, s := range []*concurrency.Session{s1, s2} {
		go func() {
			b := recipe.NewDoubleBarrier(s, key, 2)
			entered.Add(1)
			errc <- b.Enter()
		}()
	}
	for i := 0; i < 2; i++ {
		if err := <-errc; err == nil && entered.Load() < 2 {
			panic("dbarrier-count: entered before count entrants")
		}
	}
	if err := recipe.NewDoubleBarrier(s3, key, 2).Enter(); err == nil {
		panic("dbarrier-count: entered a full barrier")
	}
}
