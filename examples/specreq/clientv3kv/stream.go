package clientv3kv

import (
	"bytes"
	"context"

	clientv3 "go.etcd.io/etcd/client/v3"
)

// REQ clientv3kv/get-stream: a streamed list delivers the keys of the range in key order, chunk
// by chunk, the last chunk with the header's revision; a chunk with an error ends the stream.
// Users: Kubernetes' store (etcd3/store.go:951 GetList: GetStream(ctx, startKey, WithRange,
// WithRev, WithLimit...), then `for r := range stream { if r.Err() != nil ...; r.Kvs ... }`) and
// watcher (etcd3/watcher.go:391, the initial list).
// Assumes: to is neither empty nor "\x00" (a half-open range); the caller has a thread token for the client's reading goroutine.
// Specs: Client.GetStream.spec (KV.GetStreamTriple), streamAt_recv, RangeStreamResponse.Err.spec;
// the model's streamMatches (default ordering: the chunks are the range's answer).
func ReqGetStream(ctx context.Context, cli *clientv3.Client, from, to string, rev int64) {
	ch, err := cli.GetStream(ctx, from, clientv3.WithRange(to), clientv3.WithRev(rev))
	if err != nil {
		return
	}
	var keys [][]byte
	var hdr int64
	for r := range ch {
		if r.Err() != nil {
			return
		}
		if r.RangeResponse == nil {
			panic("get-stream: a chunk without an error has a reply")
		}
		for _, kv := range r.Kvs {
			keys = append(keys, kv.Key)
		}
		if r.Header != nil {
			hdr = r.Header.Revision
		}
	}
	// the stream ended without an error: its chunks make the range's answer
	for i, k := range keys {
		if i > 0 && bytes.Compare(keys[i-1], k) >= 0 {
			panic("get-stream: keys in order across chunks")
		}
		if bytes.Compare(k, []byte(from)) < 0 || bytes.Compare(k, []byte(to)) >= 0 {
			panic("get-stream: a key outside the range")
		}
	}
	if rev > 0 && hdr != 0 && hdr < rev {
		panic("get-stream: the stream's revision is at least the one asked")
	}
}
