package clientv3kv

import (
	"context"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.uber.org/zap"
)

// trackedKV wraps a KV as Kubernetes' latency tracker does (storage/etcd3/latency_tracker.go): each
// method forwards to the wrapped one; Txn returns a wrapper whose If, Then, Else are the wrapped
// Txn's (promoted: they return the wrapped value) and whose Commit is its own.
type trackedKV struct{ clientv3.KV }

func (t trackedKV) Get(ctx context.Context, key string, opts ...clientv3.OpOption) (*clientv3.GetResponse, error) {
	return t.KV.Get(ctx, key, opts...)
}

func (t trackedKV) Put(ctx context.Context, key, val string, opts ...clientv3.OpOption) (*clientv3.PutResponse, error) {
	return t.KV.Put(ctx, key, val, opts...)
}

func (t trackedKV) Txn(ctx context.Context) clientv3.Txn {
	return trackedTxn{t.KV.Txn(ctx)}
}

type trackedTxn struct{ clientv3.Txn }

func (t trackedTxn) Commit() (*clientv3.TxnResponse, error) {
	return t.Txn.Commit()
}

// REQ clientv3kv/kv-wrapper: a KV wrapper written into a new client's KV field meets the KV
// contract, so the client's calls through it are linearized as the client's own: a put then a get
// of an owned key reads it back; a transaction through the wrapper's Txn commits.
// Users: Kubernetes' storagebackend/factory/etcd3.go:468 (client.KV =
// etcd3.NewETCDLatencyTracker(client.KV)), latency_tracker.go:30-108 (clientV3TxnTracker).
// Assumes: ep serves the cluster; no other client writes k, which is attached to no lease; auth
// off.
// Specs: New.spec (clientMut), kvAt_intro (the wrapper's seven methods over the wrapped kvAt),
// txnAt_intro (the tracker's state: its own value at TxnSt.empty, then the wrapped txnAt),
// clientMut_KV, clientMut_freeze, Client.Put.spec, Client.Get.spec, Client.Txn.spec.
func ReqKVWrapper(ctx context.Context, ep string, lg *zap.Logger, k string) {
	cli, err := clientv3.New(clientv3.Config{Endpoints: []string{ep}, Logger: lg})
	if err != nil {
		return
	}
	defer cli.Close()
	cli.KV = trackedKV{cli.KV}
	if _, err := cli.Put(ctx, k, "v"); err != nil {
		return
	}
	resp, err := cli.Get(ctx, k)
	if err != nil {
		return
	}
	if len(resp.Kvs) != 1 || string(resp.Kvs[0].Value) != "v" {
		panic("kv-wrapper: a read through the wrapper missed the write")
	}
	tresp, err := cli.Txn(ctx).If(clientv3.Compare(clientv3.Value(k), "=", "v")).
		Then(clientv3.OpPut(k, "w")).Commit()
	if err != nil {
		return
	}
	if !tresp.Succeeded {
		panic("kv-wrapper: the compare on the owned key failed")
	}
}
