package backend

import (
	"fmt"
	"testing"
)

type rvBucket struct {
	id   BucketID
	name []byte
}

func (b rvBucket) ID() BucketID            { return b.id }
func (b rvBucket) Name() []byte            { return b.name }
func (b rvBucket) String() string          { return string(b.name) }
func (b rvBucket) IsSafeRangeBucket() bool { return false }

func newTxw() *txWriteBuffer {
	return &txWriteBuffer{
		txBuffer:   txBuffer{buckets: make(map[BucketID]*bucketBuffer)},
		bucket2seq: make(map[BucketID]bool),
	}
}

func newTxr(id BucketID, keys ...string) *txReadBuffer {
	rb := &bucketBuffer{buf: make([]kv, 10), used: 0}
	for _, k := range keys {
		rb.add([]byte(k), []byte("r"+k))
	}
	return &txReadBuffer{txBuffer: txBuffer{buckets: map[BucketID]*bucketBuffer{id: rb}}}
}

// checks rb sorted strictly, and that newest value of each key wins.
func checkCanon(t *testing.T, txr *txReadBuffer, id BucketID, want map[string]string) {
	t.Helper()
	b := txr.buckets[id]
	for i := 1; i < b.used; i++ {
		if string(b.buf[i-1].key) >= string(b.buf[i].key) {
			t.Fatalf("not strictly sorted at %d: %q %q", i, b.buf[i-1].key, b.buf[i].key)
		}
	}
	for k, v := range want {
		_, vals := txr.Range(rvBucket{id: id}, []byte(k), nil, 1)
		if len(vals) != 1 || string(vals[0]) != v {
			t.Fatalf("key %q: got %q want %q", k, vals, v)
		}
	}
}

// Overlap path (merge falls back to dedupe), with >12 entries so sort.Sort uses pdqsort
// (unstable): the old code could keep a stale value even here.
func TestReviewOverlapManyDups(t *testing.T) {
	bk := rvBucket{id: 1, name: []byte("t")}
	for n := 13; n < 200; n++ {
		txw := newTxw()
		want := map[string]string{"zz": "rzz"}
		for i := 0; i < n; i++ {
			k := fmt.Sprintf("k%02d", (i*7)%5)
			v := fmt.Sprintf("v%d", i)
			txw.put(bk, []byte(k), []byte(v))
			want[k] = v
		}
		txr := newTxr(1, "a", "zz")
		txw.writeback(txr)
		checkCanon(t, txr, 1, want)
	}
}

// putSeq-only bucket: no dedupe, merge fast path / overlap path.
func TestReviewSeqBucket(t *testing.T) {
	bk := rvBucket{id: 2, name: []byte("key")}
	txw := newTxw()
	txw.putSeq(bk, []byte("b"), []byte("1"))
	txw.putSeq(bk, []byte("c"), []byte("2"))
	txr := newTxr(2, "a")
	txw.writeback(txr)
	checkCanon(t, txr, 2, map[string]string{"a": "ra", "b": "1", "c": "2"})
	// second batch: the bucket survived reset with flag true; putSeq below rb's max (overlap).
	txw.putSeq(bk, []byte("bb"), []byte("3"))
	txw.writeback(txr)
	checkCanon(t, txr, 2, map[string]string{"a": "ra", "b": "1", "bb": "3", "c": "2"})
}

// Mixed put + putSeq on one bucket in one batch, then a later batch reusing the bucket.
func TestReviewMixedAndReuse(t *testing.T) {
	bk := rvBucket{id: 3, name: []byte("m")}
	txw := newTxw()
	txw.putSeq(bk, []byte("m"), []byte("s1"))
	txw.put(bk, []byte("m"), []byte("p1"))
	txw.put(bk, []byte("b"), []byte("p2"))
	txr := newTxr(3, "a")
	txw.writeback(txr)
	checkCanon(t, txr, 3, map[string]string{"a": "ra", "b": "p2", "m": "p1"})
	if txw.bucket2seq[3] != true {
		t.Fatalf("flag after reset: %v", txw.bucket2seq[3])
	}
	txw.put(bk, []byte("m"), []byte("p3"))
	txw.put(bk, []byte("m"), []byte("p4"))
	txw.put(bk, []byte("n"), []byte("p5"))
	txw.writeback(txr)
	checkCanon(t, txr, 3, map[string]string{"a": "ra", "b": "p2", "m": "p4", "n": "p5"})
	// a key below rb's min (fast path not taken since rb last > wb first) and above max.
	txw.put(bk, []byte("zz"), []byte("q1"))
	txw.put(bk, []byte("zz"), []byte("q2"))
	txw.writeback(txr)
	checkCanon(t, txr, 3, map[string]string{"m": "p4", "zz": "q2"})
}
