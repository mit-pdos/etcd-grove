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
// flight. Contexts carry the client's principal (ctxPrin).
package leasing

import (
	"context"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/leasing"
)

// REQ leasing/newkv-proxy: NewKV with no session options returns a KV that serves the client's
// KV API; its close function and error may be ignored.
// Users: server/etcdmain/grpc_proxy.go:488.
// Assumes: the common assumptions; pfx is the program's lease prefix.
// Specs: NewKV.spec (sessOptsOk_nil), lkvAt_methods (LKV.GetTriple).
func ReqNewKVProxy(ctx context.Context, cli *clientv3.Client, pfx, k string) {
	kv, _, _ := leasing.NewKV(cli, pfx)
	cli.KV = kv // the proxy serves this KV from now on (a W0 req: clientMut with a weaker KV contract)
	if _, err := kv.Get(ctx, k); err != nil {
		return
	}
}

// REQ leasing/newkv-close: the close function returns once no call is running or to come.
// Users: tests/integration/clientv3/lease/leasing_test.go (defer closeLKV()).
// Assumes: the common assumptions.
// Specs: NewKV.spec, closeFnAt_call (with lkvOpen γL 1), lkvOpen_split.
func ReqNewKVClose(ctx context.Context, cli *clientv3.Client, pfx, k string) {
	lkv, closeLKV, err := leasing.NewKV(cli, pfx)
	if err != nil {
		return
	}
	_, _ = lkv.Get(ctx, k)
	closeLKV()
}
