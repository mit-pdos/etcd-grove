package mvcc

import (
	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	smvcc "go.etcd.io/etcd/server/v3/storage/mvcc"
)

// REQ mvcc/put-lease: a put with a live lease attaches the key to it in the lessor, a put with no
// lease detaches it, a delete detaches it; the lessor's item map follows the store's keys.
// Users: server/etcdserver/txn/put.go (a put with a lease, after checkPut found the lease),
// lease/lessor.go:555-598 (Attach, Detach, GetLease), examples/mvccrand/mvccrand.go:545.
// Assumes: the sole writer; id is a lease the lessor has (granted, not revoked); key not empty;
// a reader token per transaction.
// Specs: store.Write.spec, metricsTxnWrite.{Put,DeleteRange,End}.spec (Txn.Put: leaseItems moved
// to the store's item map, `Attach` succeeds for a live lease).
func ReqPutLease(kv smvcc.KV, le lease.Lessor, id lease.LeaseID, key, val []byte) {
	tw := kv.Write(traceutil.TODO())
	tw.Put(key, val, id)
	tw.End()
	if le.GetLease(lease.LeaseItem{Key: string(key)}) != id {
		panic("put-lease: the key is not attached to its lease")
	}
	tw = kv.Write(traceutil.TODO())
	tw.Put(key, val, lease.NoLease)
	tw.End()
	if le.GetLease(lease.LeaseItem{Key: string(key)}) != lease.NoLease {
		panic("put-lease: a put without a lease left the key attached")
	}
	tw = kv.Write(traceutil.TODO())
	tw.Put(key, val, id)
	tw.DeleteRange(key, nil)
	tw.End()
	if le.GetLease(lease.LeaseItem{Key: string(key)}) != lease.NoLease {
		panic("put-lease: a deleted key is still attached")
	}
}

// REQ mvcc/range-deleter: the range deleter mvcc hands the lessor opens a write transaction of the
// store, through which the lessor's Revoke deletes a lease's keys (in key order) and ends it.
// Users: kvstore.go:116 (NewStore's SetRangeDeleter), lease/lessor.go:343-361 (Revoke: rd(),
// DeleteRange of each key, the lease bucket's delete under the same batch lock, End),
// server/etcdserver/server.go:1087 (Recover's deleter).
// Assumes: the sole writer (the apply thread revokes); keys sorted, each attached to the lease; a
// reader token for the transaction.
// Specs: NewStore.spec (mvccDeleter: rd()'s triple is KV.Write's), metricsTxnWrite.{DeleteRange,End}.spec.
func ReqRangeDeleter(rd lease.RangeDeleter, keys []string) {
	if rd == nil {
		panic("range-deleter: no deleter")
	}
	txn := rd()
	for _, k := range keys {
		if n, _ := txn.DeleteRange([]byte(k), nil); n != 1 {
			panic("range-deleter: an attached key was not deleted")
		}
	}
	txn.End()
}
