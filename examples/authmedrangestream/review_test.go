package authmedrangestream

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"strings"
	"sync"
	"testing"
	"unsafe"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
)

// hookStream calls hook(n) at the n-th Send (1-based), then records the chunk.
type hookStream struct {
	fakeStream
	hook func(n int)
}

func (h *hookStream) Send(r *pb.RangeStreamResponse) error {
	if h.hook != nil {
		h.hook(len(h.sent) + 1)
	}
	return h.fakeStream.Send(r)
}

func fill(t *testing.T, srv *etcdserver.EtcdServer, n int, valLen int) int64 {
	ctx := context.Background()
	var rev int64
	for i := 0; i < n; i++ {
		k := []byte(fmt.Sprintf("k%04d", i))
		resp, err := srv.Put(ctx, &pb.PutRequest{Key: k, Value: bytes.Repeat([]byte{'v'}, valLen)})
		if err != nil {
			t.Fatal(err)
		}
		rev = resp.Header.Revision
	}
	return rev
}

func checkKeys(t *testing.T, chunks []*pb.RangeStreamResponse, key, end []byte) int {
	n := 0
	for _, c := range chunks {
		for _, kv := range c.RangeResponse.Kvs {
			if bytes.Compare(kv.Key, key) < 0 || (len(end) > 0 && !bytes.Equal(end, []byte{0}) && bytes.Compare(kv.Key, end) >= 0) {
				panic(fmt.Sprintf("claim: key %q out of [%q,%q)", kv.Key, key, end))
			}
			n++
		}
	}
	return n
}

// A1: compaction between two pages of a pinned stream: the error must be mvcc.ErrCompacted itself.
func TestCompactMidStream(t *testing.T) {
	srv := startServer(t, 256)
	defer srv.Stop()
	fill(t, srv, 100, 50)
	// overwrite so that the compaction removes something
	last := fill(t, srv, 100, 50)
	ctx := context.Background()
	hs := &hookStream{fakeStream: fakeStream{ctx: ctx}}
	hs.hook = func(n int) {
		if n == 1 {
			if _, err := srv.Compact(ctx, &pb.CompactionRequest{Revision: last, Physical: true}); err != nil {
				t.Errorf("compact: %v", err)
			}
		}
	}
	req := &pb.RangeRequest{Key: []byte("k"), RangeEnd: []byte("l"), Revision: last - 10, Serializable: true}
	err := srv.RangeStream(req, hs)
	t.Logf("sent %d chunks, err %v (is ErrCompacted identity: %v)", len(hs.sent), err, err == mvcc.ErrCompacted)
	if err != nil && err != mvcc.ErrCompacted {
		panic(fmt.Sprintf("claim: store error is ErrCompacted/ErrFutureRev/rangeKeys: %v", err))
	}
	checkKeys(t, hs.sent, []byte("k"), []byte("l"))
}

// A2: the context cancelled between pages: the error is rangeKeys' wrap of the context's error.
func TestCancelMidStream(t *testing.T) {
	srv := startServer(t, 256)
	defer srv.Stop()
	fill(t, srv, 200, 50)
	for _, keysOnly := range []bool{false, true} {
		ctx, cancel := context.WithCancel(context.Background())
		hs := &hookStream{fakeStream: fakeStream{ctx: ctx}}
		hs.hook = func(n int) {
			if n == 2 {
				cancel()
			}
		}
		req := &pb.RangeRequest{Key: []byte("k"), RangeEnd: []byte{0}, Serializable: true, KeysOnly: keysOnly}
		err := srv.RangeStream(req, hs)
		t.Logf("keysOnly=%v: sent %d chunks, err %v", keysOnly, len(hs.sent), err)
		if err != nil {
			if !strings.HasPrefix(err.Error(), "rangeKeys: context cancelled: ") || !errors.Is(err, context.Canceled) {
				panic(fmt.Sprintf("claim: cancellation error is rangeKeys': %v", err))
			}
		}
		checkKeys(t, hs.sent, []byte("k"), req.RangeEnd)
	}
}

// A3: keys-only (FastKeysOnly): the chunk's keys alias the index; the request's last Key aliases
// the index key's array (append(lastKey, 0) into its capacity). Check nothing visible changes,
// including after later puts and later streams.
func TestKeysOnlyAliasing(t *testing.T) {
	srv := startServer(t, 128)
	defer srv.Stop()
	fill(t, srv, 60, 10)
	ctx := context.Background()
	hs := &hookStream{fakeStream: fakeStream{ctx: ctx}}
	req := &pb.RangeRequest{Key: []byte("k"), RangeEnd: []byte("l"), KeysOnly: true, Serializable: true}
	if err := srv.RangeStream(req, hs); err != nil {
		t.Fatal(err)
	}
	aliased := 0
	for _, c := range hs.sent {
		for _, kv := range c.RangeResponse.Kvs {
			if cap(kv.Key) > len(kv.Key) && unsafe.SliceData(kv.Key) == unsafe.SliceData(req.Key) {
				aliased++
			}
		}
	}
	t.Logf("%d chunks; final req.Key %q len %d; chunk keys sharing its array: %d", len(hs.sent), req.Key, len(req.Key), aliased)
	// second stream over the same range, and puts of the same keys
	hs2 := &hookStream{fakeStream: fakeStream{ctx: ctx}}
	req2 := &pb.RangeRequest{Key: []byte("k"), RangeEnd: []byte("l"), KeysOnly: true, Serializable: true}
	if err := srv.RangeStream(req2, hs2); err != nil {
		t.Fatal(err)
	}
	fill(t, srv, 60, 10)
	shared := 0
	for i, c := range hs.sent {
		for j, kv := range c.RangeResponse.Kvs {
			if !bytes.Equal(kv.Key, hs.copies[i].RangeResponse.Kvs[j].Key) {
				panic("claim: chunk key bytes unchanged")
			}
			if j < len(hs2.sent[i].RangeResponse.Kvs) && unsafe.SliceData(kv.Key) == unsafe.SliceData(hs2.sent[i].RangeResponse.Kvs[j].Key) {
				shared++
			}
		}
	}
	t.Logf("key slices shared between the two streams' chunks (the index's): %d", shared)
	if req.Key[len(req.Key)-1] != 0 {
		panic("claim: request key's last byte stays 0")
	}
}

// A4: concurrent keys-only streams over the same range (run with -race): both append into the
// capacity of the same index key slices, and each reads its nextKey while the other writes.
// TestConcurrentKeysOnly: four concurrent keys-only streams. It passes without -race; with -race it
// reports the data race at v3_server.go:246 (the append into mvcc's index key), fixed upstream by
// etcd-io/etcd@9acc0ebe37 (nonissues/etcd-rangestream-keysonly-index-key-race.md).
func TestConcurrentKeysOnly(t *testing.T) {
	srv := startServer(t, 128)
	defer srv.Stop()
	fill(t, srv, 200, 10)
	var wg sync.WaitGroup
	for g := 0; g < 4; g++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for it := 0; it < 20; it++ {
				hs := &hookStream{fakeStream: fakeStream{ctx: context.Background()}}
				req := &pb.RangeRequest{Key: []byte("k"), RangeEnd: []byte("l"), KeysOnly: true, Serializable: true}
				if err := srv.RangeStream(req, hs); err != nil {
					t.Error(err)
					return
				}
				if n := checkKeys(t, hs.sent, []byte("k"), []byte("l")); n != 200 {
					panic(fmt.Sprintf("got %d keys", n))
				}
			}
		}()
	}
	wg.Wait()
}

// A5: puts and deletes inside the range during a stream (revision pinned by rangeStream).
func TestWritesMidStream(t *testing.T) {
	srv := startServer(t, 256)
	defer srv.Stop()
	fill(t, srv, 100, 30)
	ctx := context.Background()
	hs := &hookStream{fakeStream: fakeStream{ctx: ctx}}
	hs.hook = func(n int) {
		srv.Put(ctx, &pb.PutRequest{Key: []byte(fmt.Sprintf("k%04d\x00", 10*n)), Value: []byte("x")})
		srv.DeleteRange(ctx, &pb.DeleteRangeRequest{Key: []byte(fmt.Sprintf("k%04d", 10*n+5))})
	}
	req := &pb.RangeRequest{Key: []byte("k0003"), RangeEnd: []byte("k0090"), Serializable: true}
	if err := srv.RangeStream(req, hs); err != nil {
		t.Fatal(err)
	}
	n := checkKeys(t, hs.sent, []byte("k0003"), []byte("k0090"))
	t.Logf("%d chunks, %d keys", len(hs.sent), n)
}

// A6: count-only and future revisions: errors are ErrFutureRev itself.
func TestFutureRev(t *testing.T) {
	srv := startServer(t, 256)
	defer srv.Stop()
	last := fill(t, srv, 5, 3)
	for _, co := range []bool{false, true} {
		hs := &hookStream{fakeStream: fakeStream{ctx: context.Background()}}
		err := srv.RangeStream(&pb.RangeRequest{Key: []byte("k"), RangeEnd: []byte{0}, Revision: last + 5, CountOnly: co, Serializable: true}, hs)
		if err != mvcc.ErrFutureRev || len(hs.sent) != 0 {
			panic(fmt.Sprintf("countOnly=%v: %v, %d sent", co, err, len(hs.sent)))
		}
	}
}
