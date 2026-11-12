package clientv3kv

import (
	"bytes"
	"context"

	clientv3 "go.etcd.io/etcd/client/v3"
)

// REQ clientv3kv/op-getters: an Op built with options reports them through its getters.
// Users: leasing/kv.go, leasing/txn.go, leasing/util.go (IsGet, IsPut, IsDelete, IsTxn,
// KeyBytes, RangeBytes, IsSerializable, IsKeysOnly, IsCountOnly, Txn), the cache
// (cache/cache.go validateGet: Rev, IsSerializable, Limit, IsCountOnly, IsSortSet, the filters).
// Assumes: none.
// Specs: OpGet.spec, OpPut.spec, OpTxn.spec, WithPrefix.spec, WithRev.spec, WithSerializable.spec,
// WithLimit.spec, Op.IsGet.spec, Op.IsPut.spec, Op.IsTxn.spec, Op.KeyBytes.spec, Op.RangeBytes.spec,
// Op.Rev.spec, Op.IsSerializable.spec, Op.Limit.spec, Op.IsSortSet.spec, Op.Txn.spec,
// Op.ValueBytes.spec; the model's prefixEnd.
func ReqOpGetters(k string, rev int64) {
	op := clientv3.OpGet(k, clientv3.WithPrefix(), clientv3.WithRev(rev), clientv3.WithSerializable(),
		clientv3.WithLimit(5))
	if !op.IsGet() || op.IsPut() || op.IsTxn() {
		panic("op: a get")
	}
	if k != "" && !bytes.Equal(op.KeyBytes(), []byte(k)) {
		panic("op: its key")
	}
	if k != "" && !bytes.Equal(op.RangeBytes(), []byte(clientv3.GetPrefixRangeEnd(k))) {
		panic("op: the prefix's range end")
	}
	if op.Rev() != rev || !op.IsSerializable() || op.Limit() != 5 || op.IsSortSet() {
		panic("op: its options")
	}
	put := clientv3.OpPut(k, "v")
	if !put.IsPut() || !bytes.Equal(put.ValueBytes(), []byte("v")) {
		panic("op: a put and its value")
	}
	txn := clientv3.OpTxn(nil, []clientv3.Op{put}, []clientv3.Op{op})
	cmps, thenOps, elseOps := txn.Txn()
	if !txn.IsTxn() || len(cmps) != 0 || len(thenOps) != 1 || len(elseOps) != 1 || !elseOps[0].IsGet() {
		panic("op: a transaction and its branches")
	}
}

// REQ clientv3kv/do: Do of an Op answers in the field of its kind.
// Users: leasing/kv.go:244 (every operation it forwards), the cache (cache/cache.go,
// cache/watcher.go: Do(OpGet(...))), Kubernetes' compactor (etcd3/compact.go).
// Assumes: none.
// Specs: Client.Do.spec (KV.DoTriple), OpResponse.Get.spec, OpResponse.Put.spec,
// OpResponse.Txn.spec.
func ReqDo(ctx context.Context, cli *clientv3.Client, k string) {
	r, err := cli.Do(ctx, clientv3.OpGet(k))
	if err == nil && (r.Get() == nil || r.Put() != nil) {
		panic("do: a get answers in Get()")
	}
	r, err = cli.Do(ctx, clientv3.OpPut(k, "v"))
	if err == nil && r.Put() == nil {
		panic("do: a put answers in Put()")
	}
	r, err = cli.Do(ctx, clientv3.OpTxn(nil, nil, nil))
	if err == nil && (r.Txn() == nil || !r.Txn().Succeeded) {
		panic("do: an empty transaction succeeds")
	}
}

// REQ clientv3kv/serializable-get: a serializable get is answered at some member's view: a
// revision at least 1, the key-values of that revision; nothing ties it to the caller's writes.
// Users: client/v3/concurrency/stm.go:262 (stmSerializable), the cache (serializable reads of
// its own), etcdctl get --consistency=s.
// Assumes: none.
// Specs: Client.Get.spec (the model's range step at IsView).
func ReqSerializableGet(ctx context.Context, cli *clientv3.Client, k string) {
	resp, err := cli.Get(ctx, k, clientv3.WithSerializable())
	if err != nil {
		return
	}
	if resp.Header.Revision < 1 {
		panic("serializable get: a revision is at least 1")
	}
	for _, kv := range resp.Kvs {
		if kv.ModRevision > resp.Header.Revision || kv.CreateRevision > kv.ModRevision {
			panic("serializable get: a key-value of its revision")
		}
	}
}

// REQ clientv3kv/get-options: count-only and keys-only reads, the first-created key of a prefix.
// Users: the cache (WithCountOnly), Kubernetes' store (WithKeysOnly with WithPrefix),
// client/v3/concurrency (WithFirstCreate: the lock's owner), recipes (WithFirstKey: the queue's
// head).
// Assumes: none.
// Specs: Client.Get.spec, WithCountOnly.spec, WithKeysOnly.spec, WithFirstCreate.spec (withTop);
// the model's RangeReq.answers (keys-only: no value; issues/etcd-range-keys-only-lease.md: lease 0).
func ReqGetOptions(ctx context.Context, cli *clientv3.Client, pfx string) {
	c, err := cli.Get(ctx, pfx, clientv3.WithPrefix(), clientv3.WithCountOnly())
	if err == nil && len(c.Kvs) != 0 {
		panic("count-only: no key-value")
	}
	ko, err := cli.Get(ctx, pfx, clientv3.WithPrefix(), clientv3.WithKeysOnly())
	if err == nil {
		for _, kv := range ko.Kvs {
			if len(kv.Value) != 0 {
				panic("keys-only: no value")
			}
		}
	}
	first, err := cli.Get(ctx, pfx, clientv3.WithFirstCreate()...)
	if err == nil && len(first.Kvs) > 1 {
		panic("first-create: at most one key")
	}
}
