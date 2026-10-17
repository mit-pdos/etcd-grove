package backend_test

import (
	"testing"
	"time"

	"go.etcd.io/etcd/server/v3/storage/backend"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

func readBoth(t *testing.T, b backend.Backend, key []byte) (string, string) {
	rtx := b.ReadTx()
	rtx.RLock()
	_, rv := rtx.UnsafeRange(schema.Test, key, nil, 0)
	rtx.RUnlock()
	tx := b.BatchTx()
	tx.Lock()
	_, wv := tx.UnsafeRange(schema.Test, key, nil, 0)
	tx.Unlock()
	if len(rv) != 1 || len(wv) != 1 {
		t.Fatalf("missing key: read %q, batch %q", rv, wv)
	}
	return string(rv[0]), string(wv[0])
}

func TestReadTxStaleAfterDuplicatePut(t *testing.T) {
	b, _ := betesting.NewTmpBackend(t, time.Hour, 10000)
	defer betesting.Close(t, b)

	tx := b.BatchTx()
	tx.Lock()
	tx.UnsafeCreateBucket(schema.Test)
	tx.UnsafePut(schema.Test, []byte("foo"), []byte("v1"))
	tx.Unlock()
	tx.Commit()

	tx.Lock()
	tx.UnsafePut(schema.Test, []byte("foo"), []byte("v2"))
	tx.UnsafePut(schema.Test, []byte("foo"), []byte("v3"))
	tx.Unlock()

	r, w := readBoth(t, b, []byte("foo"))
	if r != w {
		t.Errorf("ReadTx reads %q, BatchTx reads %q", r, w)
	}
}
