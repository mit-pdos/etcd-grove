package kubernetes

import (
	"context"
	"errors"
	"reflect"
	"testing"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/mvccpb"
	clientv3 "go.etcd.io/etcd/client/v3"
)

type recordingKV struct {
	clientv3.KV
	lastOp  clientv3.Op
	resp    *clientv3.GetResponse
	err     error
}

func (r *recordingKV) Put(ctx context.Context, key, val string, opts ...clientv3.OpOption) (*clientv3.PutResponse, error) {
	panic("not implemented")
}

func (r *recordingKV) Get(ctx context.Context, key string, opts ...clientv3.OpOption) (*clientv3.GetResponse, error) {
	r.lastOp = clientv3.OpGet(key, opts...)
	if r.err != nil {
		return nil, r.err
	}
	return r.resp, nil
}

func (r *recordingKV) Delete(ctx context.Context, key string, opts ...clientv3.OpOption) (*clientv3.DeleteResponse, error) {
	panic("not implemented")
}

func (r *recordingKV) Compact(ctx context.Context, rev int64, opts ...clientv3.CompactOption) (*clientv3.CompactResponse, error) {
	panic("not implemented")
}

func (r *recordingKV) Do(ctx context.Context, op clientv3.Op) (clientv3.OpResponse, error) {
	panic("not implemented")
}

func (r *recordingKV) Txn(ctx context.Context) clientv3.Txn {
	panic("not implemented")
}

// TestPR21209_KeysBasicAndRevision verifies that Client.Keys sends a keys-only prefix range
// request at the requested revision and populates KeysResponse.{Keys, Count, Revision}.
func TestPR21209_KeysBasicAndRevision(t *testing.T) {
	mock := &recordingKV{
		resp: &clientv3.GetResponse{
			Header: &pb.ResponseHeader{Revision: 105},
			Kvs: []*mvccpb.KeyValue{
				{Key: []byte("/registry/pods/default/a"), Value: nil, ModRevision: 100},
				{Key: []byte("/registry/pods/default/b"), Value: nil, ModRevision: 105},
			},
			Count: 2,
		},
	}
	kc := Client{Client: &clientv3.Client{KV: mock}}

	resp, err := kc.Keys(context.Background(), "/registry/pods/", KeysOptions{Revision: 105})
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if got, want := string(mock.lastOp.KeyBytes()), "/registry/pods/"; got != want {
		t.Fatalf("op key = %q, want %q", got, want)
	}
	if got, want := string(mock.lastOp.RangeBytes()), "/registry/pods0"; got != want {
		t.Fatalf("op rangeEnd = %q, want %q", got, want)
	}
	if !mock.lastOp.IsKeysOnly() {
		t.Fatalf("expected IsKeysOnly() == true")
	}
	if mock.lastOp.IsCountOnly() {
		t.Fatalf("expected IsCountOnly() == false")
	}
	if got, want := mock.lastOp.Rev(), int64(105); got != want {
		t.Fatalf("op rev = %d, want %d", got, want)
	}
	wantKeys := [][]byte{
		[]byte("/registry/pods/default/a"),
		[]byte("/registry/pods/default/b"),
	}
	if !reflect.DeepEqual(resp.Keys, wantKeys) {
		t.Fatalf("resp.Keys = %q, want %q", resp.Keys, wantKeys)
	}
	if resp.Count != 2 || resp.Revision != 105 {
		t.Fatalf("resp.Count=%d resp.Revision=%d, want Count=2 Revision=105", resp.Count, resp.Revision)
	}

	// Verify error propagation
	wantErr := errors.New("rpc failed")
	mock.err = wantErr
	errResp, err := kc.Keys(context.Background(), "/registry/pods/", KeysOptions{})
	if !errors.Is(err, wantErr) {
		t.Fatalf("expected error %v, got %v", wantErr, err)
	}
	if errResp.Keys != nil || errResp.Count != 0 || errResp.Revision != 0 {
		t.Fatalf("expected zero KeysResponse on error, got %+v", errResp)
	}
}

// TestPR21209_EmptyPrefixKeysVsCount demonstrates that Client.Count("", ...) uses
// clientv3.WithPrefix() (which translates an empty prefix "" to Key="\x00", RangeEnd="\x00"),
// whereas Client.Keys("", ...) uses clientv3.WithRange(clientv3.GetPrefixRangeEnd(""))
// (which leaves Key="" empty and sets RangeEnd="\x00", causing etcdserver's checkRangeRequest
// to reject the request with ErrEmptyKey).
func TestPR21209_EmptyPrefixKeysVsCount(t *testing.T) {
	mock := &recordingKV{
		resp: &clientv3.GetResponse{
			Header: &pb.ResponseHeader{Revision: 10},
			Count:  3,
		},
	}
	kc := Client{Client: &clientv3.Client{KV: mock}}

	if _, err := kc.Count(context.Background(), "", CountOptions{}); err != nil {
		t.Fatalf("Count failed: %v", err)
	}
	countKey := mock.lastOp.KeyBytes()
	countEnd := mock.lastOp.RangeBytes()

	if _, err := kc.Keys(context.Background(), "", KeysOptions{}); err != nil {
		t.Fatalf("Keys failed: %v", err)
	}
	keysKey := mock.lastOp.KeyBytes()
	keysEnd := mock.lastOp.RangeBytes()

	t.Logf("Count(\"\") -> KeyBytes=%q (len=%d), RangeBytes=%q", countKey, len(countKey), countEnd)
	t.Logf("Keys(\"\")  -> KeyBytes=%q (len=%d), RangeBytes=%q", keysKey, len(keysKey), keysEnd)

	if string(countKey) != "\x00" || string(countEnd) != "\x00" {
		t.Fatalf("expected Count(\"\") to rewrite key/end to \"\\x00\", got key=%q end=%q", countKey, countEnd)
	}
	if len(keysKey) != 0 || string(keysEnd) != "\x00" {
		t.Fatalf("expected Keys(\"\") to leave key empty and set end=\"\\x00\", got key=%q end=%q", keysKey, keysEnd)
	}
}

// robustnessRecordingClientAdapter mirrors tests/robustness/client.RecordingClient.Get + Range
// (tests/robustness/client/client.go:94-120) to demonstrate how RecordingClient strips WithCountOnly().
type robustnessRecordingClientAdapter struct {
	clientv3.KV
	forwarded *recordingKV
}

func (c *robustnessRecordingClientAdapter) Put(ctx context.Context, key, val string, opts ...clientv3.OpOption) (*clientv3.PutResponse, error) {
	panic("not implemented")
}

func (c *robustnessRecordingClientAdapter) Get(ctx context.Context, key string, opts ...clientv3.OpOption) (*clientv3.GetResponse, error) {
	op := clientv3.OpGet(key, opts...)
	return c.Range(ctx, key, string(op.RangeBytes()), op.Rev(), op.Limit(), op.IsKeysOnly())
}

func (c *robustnessRecordingClientAdapter) Range(ctx context.Context, start, end string, revision, limit int64, keyOnly bool) (*clientv3.GetResponse, error) {
	ops := []clientv3.OpOption{}
	if end != "" {
		ops = append(ops, clientv3.WithRange(end))
	}
	if revision != 0 {
		ops = append(ops, clientv3.WithRev(revision))
	}
	if limit != 0 {
		ops = append(ops, clientv3.WithLimit(limit))
	}
	if keyOnly {
		ops = append(ops, clientv3.WithKeysOnly())
	}
	return c.forwarded.Get(ctx, start, ops...)
}

func (c *robustnessRecordingClientAdapter) Delete(ctx context.Context, key string, opts ...clientv3.OpOption) (*clientv3.DeleteResponse, error) {
	panic("not implemented")
}

func (c *robustnessRecordingClientAdapter) Compact(ctx context.Context, rev int64, opts ...clientv3.CompactOption) (*clientv3.CompactResponse, error) {
	panic("not implemented")
}

func (c *robustnessRecordingClientAdapter) Do(ctx context.Context, op clientv3.Op) (clientv3.OpResponse, error) {
	panic("not implemented")
}

func (c *robustnessRecordingClientAdapter) Txn(ctx context.Context) clientv3.Txn {
	panic("not implemented")
}

// TestPR21209_RecordingClientStripsWithCountOnly demonstrates that when kubernetesTraffic.Count
// calls kc.Count(ctx, keyPrefix, CountOptions{}) through tests/robustness/client.RecordingClient,
// RecordingClient.Get drops op.IsCountOnly() and sends a full Range request (IsCountOnly()==false,
// IsKeysOnly()==false) to the underlying etcd client.
func TestPR21209_RecordingClientStripsWithCountOnly(t *testing.T) {
	underlying := &recordingKV{
		resp: &clientv3.GetResponse{
			Header: &pb.ResponseHeader{Revision: 50},
			Count:  7,
		},
	}
	rec := &robustnessRecordingClientAdapter{forwarded: underlying}
	kc := Client{Client: &clientv3.Client{KV: rec}}

	cnt, err := kc.Count(context.Background(), "/registry/pods/", CountOptions{})
	if err != nil {
		t.Fatalf("Count failed: %v", err)
	}
	if cnt != 7 {
		t.Fatalf("cnt = %d, want 7", cnt)
	}
	t.Logf("Underlying client received Op from kc.Count: IsCountOnly=%v, IsKeysOnly=%v, Key=%q, RangeEnd=%q",
		underlying.lastOp.IsCountOnly(), underlying.lastOp.IsKeysOnly(),
		underlying.lastOp.KeyBytes(), underlying.lastOp.RangeBytes())
	if underlying.lastOp.IsCountOnly() {
		t.Fatalf("expected RecordingClient.Get to have stripped IsCountOnly, but IsCountOnly was true")
	}
}
