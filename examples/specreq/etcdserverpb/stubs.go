package etcdserverpb

import (
	"context"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"google.golang.org/grpc"
	"google.golang.org/protobuf/proto"
)

// REQ etcdserverpb/kv-stub: the KV stub over a client's connection performs the put on the
// cluster and returns its reply (or an error the client classifies), never a nil reply with a nil
// error.
// Users: client/v3/retry.go (RetryKVClient: pb.NewKVClient(c.conn)), every KV call of the client.
// Assumes: conn is an etcd client's connection (W0's connOk); the request fits (grpc's msgsFit).
// Specs: NewKVClient.spec (remoteKVAt), kVClient.Put.spec; W0's remoteKVAt_methods.
func ReqKVStub(ctx context.Context, conn *grpc.ClientConn, key, val []byte) *pb.PutResponse {
	kc := pb.NewKVClient(conn)
	resp, err := kc.Put(ctx, &pb.PutRequest{Key: key, Value: val})
	if err != nil {
		return nil
	}
	if resp == nil || resp.Header == nil {
		panic("put reply without a header")
	}
	return resp
}

// REQ etcdserverpb/watch-stub: the watch stub opens a stream (or fails), never a nil stream with a
// nil error; a create request sent on it is read, not kept.
// Users: client/v3/watch.go (openWatchClient: w.remote.Watch(w.ctx, w.callOpts...)).
// Assumes: conn is an etcd client's connection (connOk).
// Specs: NewWatchClient.spec (remoteWatchAt), watchClient.Watch.spec; 1b's remoteWatchAt_watch.
func ReqWatchStub(ctx context.Context, conn *grpc.ClientConn, key []byte) {
	wc := pb.NewWatchClient(conn)
	ws, err := wc.Watch(ctx)
	if err != nil {
		return
	}
	if ws == nil {
		panic("nil stream without an error")
	}
	cr := &pb.WatchCreateRequest{Key: key}
	req := &pb.WatchRequest{RequestUnion: &pb.WatchRequest_CreateRequest{CreateRequest: cr}}
	_ = ws.Send(req)
	if string(cr.Key) != string(key) {
		panic("send wrote the request")
	}
}

// REQ etcdserverpb/merge-range: the chunks of a streamed range merged into one reply hold every
// chunk's key-values in order and the last header (the client's GetStreamToGetResponse).
// Users: client/v3/kv.go (GetStreamToGetResponse: proto.Merge of each chunk).
// Assumes: each chunk is a RangeResponse a RangeStream delivered (rangeRespOwn).
// Specs: rangeRespDst_fresh.spec, rangeRespDst_msgAt.spec, proto's Merge.spec (2a's restated, with
// mergeDstOk), rangeResp_merge.spec, rangeRespDst_own.spec, RangeResponse.GetKvs.spec.
func ReqMergeRange(chunks []*pb.RangeResponse) *pb.RangeResponse {
	out := &pb.RangeResponse{}
	n := 0
	for _, c := range chunks {
		n += len(c.GetKvs())
		proto.Merge(out, c)
	}
	if len(out.GetKvs()) != n {
		panic("merge lost key-values")
	}
	return out
}
