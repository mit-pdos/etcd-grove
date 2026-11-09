// Package leasing holds the requirement snippets of etcd's leasing KV (batch 1e,
// Spec/go_etcd_io/etcd/client/v3/leasing/): minimal uses of the patterns its users rely on (the
// gRPC proxy with --experimental-leasing-prefix, the integration tests), each reliance an explicit
// panic. The files lifecycle.go, reads.go, writes.go and txn.go hold what the leasing contract
// (LKV.*Triple) gives; unmet.go what the KV contract's users rely on and the pinned code violates
// (each with its issue): no spec can give those.
//
// Common assumptions (the proofs' setting): cli is a client of a cluster as principal who
// (isClient), the caller owns the cluster's state etcdState in an invariant of its own, gave
// NewKV the permission for the protocol's steps under the prefix (protoUpd) and keeps its
// invariant stable under them (its keys outside the prefix, attached to none of who's leases);
// keys named "owned" are written by no other principal and by no call of this program still in
// flight. Contexts carry the client's principal (ctxPrin). A key written through a leasing KV
// is marked first (lkvClean_mark: the program gives up its lkvClean for it); a key never marked
// is read through the cache as W0's serializable read. Each call's principal is its context's
// (ctxPrin who ctx p, W0's round 3), so the proxy's requests may carry each requester's token; a
// cached answer is then W0's serializable read for that principal (CachedSer), which may skip the
// permission check (nonissues/grpcproxy-leasing-auth-cached-read.md).
package leasing

import (
	"context"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/concurrency"
	"go.etcd.io/etcd/client/v3/leasing"
)

// REQ leasing/newkv-proxy: NewKV with no session options returns a KV that serves the client's
// KV API; its close function and error may be ignored.
// Users: server/etcdmain/grpc_proxy.go:488.
// Assumes: the common assumptions, the client's interface fields writable (clientMut, as the
// proxy's); pfx is the program's lease prefix, non-empty.
// Specs: clientMut_split (W0: the KV field kept writable, clientRest for good), NewKV.spec (its KV
// field read and given back; no options: sessOptsAt of nil), lkvAt_methods (LKV.GetTriple).
func ReqNewKVProxy(ctx context.Context, cli *clientv3.Client, pfx, k string) {
	kv, _, _ := leasing.NewKV(cli, pfx)
	cli.KV = kv // the proxy serves this KV from now on
	if _, err := kv.Get(ctx, k); err != nil {
		return
	}
}

// REQ leasing/newkv-close: the close function returns once no call is running or to come.
// Users: tests/integration/clientv3/lease/leasing_test.go (defer closeLKV()).
// Assumes: the common assumptions.
// Specs: NewKV.spec (isClient_KV, isClient_rest), closeFnAt_call (with lkvOpen γL 1), lkvOpen_split.
func ReqNewKVClose(ctx context.Context, cli *clientv3.Client, pfx, k string) {
	lkv, closeLKV, err := leasing.NewKV(cli, pfx)
	if err != nil {
		return
	}
	_, _ = lkv.Get(ctx, k)
	closeLKV()
}

// REQ leasing/newkv-options: NewKV with session options (a TTL).
// Users: tests/integration/clientv3/lease/leasing_test.go:1677, :1749 (WithTTL(1)).
// Assumes: the common assumptions; pfx non-empty.
// Specs: concurrency.WithTTL.spec (1d: sessOptsAt), NewKV.spec, closeFnAt_call.
func ReqNewKVWithTTL(ctx context.Context, cli *clientv3.Client, pfx, k string) {
	lkv, closeLKV, err := leasing.NewKV(cli, pfx, concurrency.WithTTL(1))
	if err != nil {
		return
	}
	_, _ = lkv.Get(ctx, k)
	closeLKV()
}
