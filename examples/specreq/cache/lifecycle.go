package cache

import (
	"context"

	"go.etcd.io/etcd/cache/v3"
	clientv3 "go.etcd.io/etcd/client/v3"
)

// REQ cache/new-default: New with the default options never fails, and a cache can be watched and
// closed (Close after the Watch returned, by the holder of the whole cacheOpen token).
// Users: examples/etcd/cache/cachekv.go (cache.New(cli, prefix)); tests/integration (New, defer
// c.Close()).
// Assumes: nothing beyond the package's common assumptions.
// Specs: New.spec (the default configuration is CfgValid and CfgBounded), Cache.Watch.spec,
// Cache.Close.spec.
func ReqNewDefault(ctx context.Context, cli *clientv3.Client, pfx string) {
	c, err := cache.New(cli, pfx)
	if err != nil {
		panic("new-default: the default configuration rejected")
	}
	_ = c.Watch(ctx, pfx, clientv3.WithPrefix())
	c.Close()
	_ = c.Watch(ctx, pfx, clientv3.WithPrefix())
	c.Close()
}

// REQ cache/new-options: options are applied in order; a valid configuration gives a cache, an
// invalid one (a history window of 0) an error and no cache.
// Users: tests/integration (WithHistoryWindowSize(32), WithHistoryWindowSize(1),
// WithProgressNotifyInterval).
// Assumes: nothing.
// Specs: New.spec, WithHistoryWindowSize.spec, WithProgressNotifyInterval.spec.
func ReqNewOptions(cli *clientv3.Client, pfx string) {
	c, err := cache.New(cli, pfx, cache.WithHistoryWindowSize(0), cache.WithHistoryWindowSize(1))
	if err != nil || c == nil {
		panic("new-options: a later option did not override an earlier one")
	}
	c.Close()
	if c2, err := cache.New(cli, pfx, cache.WithHistoryWindowSize(0)); err == nil || c2 != nil {
		panic("new-options: an invalid configuration accepted")
	}
}

// REQ cache/ready-then-get: once WaitReady (or Ready) says the cache is ready, a serializable Get
// of a key in range does not fail for want of data (it may fail otherwise: the context, a
// compacted window); its header revision is at least 1.
// Users: tests/integration (WaitReady after every New, then Gets).
// Assumes: nothing.
// Specs: Cache.WaitReady.spec, Cache.Ready.spec (cacheRevLb c 1), Cache.Get.spec (r0 = 1).
func ReqReadyThenGet(ctx context.Context, c *cache.Cache, k string) {
	if err := c.WaitReady(ctx); err != nil {
		return
	}
	if !c.Ready() {
		return
	}
	gresp, err := c.Get(ctx, k, clientv3.WithSerializable())
	if err != nil {
		return
	}
	if gresp.Header.Revision < 1 {
		panic("ready-then-get: answered before loading")
	}
}
