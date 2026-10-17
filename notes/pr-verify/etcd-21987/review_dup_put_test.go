package backend_test

import (
	"fmt"
	"testing"
	"time"

	"go.etcd.io/etcd/server/v3/storage/backend"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// reads returns what ReadTx and ConcurrentReadTx return for [key, end).
func reviewReads(b backend.Backend, bk backend.Bucket, key, end []byte, limit int64) []string {
	var out []string
	rt := b.ReadTx()
	rt.RLock()
	ks, vs := rt.UnsafeRange(bk, key, end, limit)
	rt.RUnlock()
	out = append(out, fmt.Sprint("ReadTx:", pairs(ks, vs)))
	ct := b.ConcurrentReadTx()
	ct.RLock()
	ks, vs = ct.UnsafeRange(bk, key, end, limit)
	ct.RUnlock()
	out = append(out, fmt.Sprint("ConcurrentReadTx:", pairs(ks, vs)))
	return out
}

func pairs(ks, vs [][]byte) string {
	s := ""
	for i := range ks {
		s += fmt.Sprintf(" %s=%s", ks[i], vs[i])
	}
	return s
}

func reviewCheck(t *testing.T, name string, got []string, want string) {
	for _, g := range got {
		// strip the "ReadTx:"/"ConcurrentReadTx:" prefix
		i := 0
		for g[i] != ':' {
			i++
		}
		if g[i+1:] != want {
			t.Errorf("%s: %s, want%s", name, g, want)
		}
	}
}

// TestReviewDupPut: interleavings around writeback's dedupe (etcd#22298).
func TestReviewDupPut(t *testing.T) {
	b, _ := betesting.NewTmpBackend(t, time.Hour, 10000)
	defer betesting.Close(t, b)
	tx := b.BatchTx()
	tx.Lock()
	tx.UnsafeCreateBucket(schema.Test)
	tx.UnsafeCreateBucket(schema.Key)
	tx.Unlock()
	b.ForceCommit()

	// 1. The bug: the read buffer has an emptied bucket (after a commit); a session
	// puts one key twice.
	tx.Lock()
	tx.UnsafePut(schema.Test, []byte("k"), []byte("v0"))
	tx.Unlock()
	b.ForceCommit()
	tx.Lock()
	tx.UnsafePut(schema.Test, []byte("k"), []byte("v1"))
	tx.UnsafePut(schema.Test, []byte("k"), []byte("v2"))
	tx.Unlock()
	reviewCheck(t, "dup put, emptied read bucket", reviewReads(b, schema.Test, []byte("k"), nil, 0), " k=v2")

	// 2. Same key again in a later session (overlap with a non-empty read bucket).
	tx.Lock()
	tx.UnsafePut(schema.Test, []byte("k"), []byte("v3"))
	tx.UnsafePut(schema.Test, []byte("k"), []byte("v4"))
	tx.Unlock()
	reviewCheck(t, "dup put, non-empty read bucket", reviewReads(b, schema.Test, []byte("k"), nil, 0), " k=v4")

	// 3. Mixed UnsafeSeqPut and UnsafePut on one bucket in one session, the seq flag
	// `true` after the previous write-back's reset.
	tx.Lock()
	tx.UnsafeSeqPut(schema.Test, []byte("m"), []byte("s1"))
	tx.UnsafePut(schema.Test, []byte("m"), []byte("p1"))
	tx.UnsafeSeqPut(schema.Test, []byte("z"), []byte("s2"))
	tx.UnsafePut(schema.Test, []byte("m"), []byte("p2"))
	tx.Unlock()
	reviewCheck(t, "mixed seq/put", reviewReads(b, schema.Test, []byte("m"), nil, 0), " m=p2")
	reviewCheck(t, "mixed seq/put z", reviewReads(b, schema.Test, []byte("z"), nil, 0), " z=s2")

	// 4. A safe-range bucket: a range over committed and buffered keys, a buffered key
	// put twice above everything committed.
	tx.Lock()
	tx.UnsafePut(schema.Key, []byte("a"), []byte("1"))
	tx.Unlock()
	b.ForceCommit()
	tx.Lock()
	tx.UnsafePut(schema.Key, []byte("b"), []byte("1"))
	tx.UnsafePut(schema.Key, []byte("c"), []byte("1"))
	tx.UnsafePut(schema.Key, []byte("b"), []byte("2"))
	tx.Unlock()
	reviewCheck(t, "safe range", reviewReads(b, schema.Key, []byte("a"), []byte("z"), 100), " a=1 b=2 c=1")
	// and again in the next session (read bucket non-empty, overlapping)
	tx.Lock()
	tx.UnsafePut(schema.Key, []byte("c"), []byte("2"))
	tx.UnsafePut(schema.Key, []byte("c"), []byte("3"))
	tx.Unlock()
	reviewCheck(t, "safe range 2", reviewReads(b, schema.Key, []byte("a"), []byte("z"), 100), " a=1 b=2 c=3")

	// 5. After a commit the buffer is empty and bbolt has the newest values.
	b.ForceCommit()
	reviewCheck(t, "after commit", reviewReads(b, schema.Test, []byte("k"), nil, 0), " k=v4")
	reviewCheck(t, "after commit m", reviewReads(b, schema.Test, []byte("m"), nil, 0), " m=p2")
	reviewCheck(t, "after commit range", reviewReads(b, schema.Key, []byte("a"), []byte("z"), 100), " a=1 b=2 c=3")
}
