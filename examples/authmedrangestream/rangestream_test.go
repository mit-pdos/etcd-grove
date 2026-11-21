package authmedrangestream

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"math/rand"
	"net"
	"testing"

	"google.golang.org/grpc/metadata"
	"google.golang.org/protobuf/proto"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/mvccpb"
	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/features"
	"go.uber.org/zap"
)

func freeAddr(t *testing.T) string {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer l.Close()
	return l.Addr().String()
}

// startServer starts the one member of a new cluster (as examples/lib/etcdstart's StartServer),
// with a small MaxRequestBytes so that streams take many pages of changing sizes.
func startServer(t *testing.T, maxReq uint) *etcdserver.EtcdServer {
	lg := zap.NewNop()
	peer := types.URLs{{Scheme: "http", Host: freeAddr(t)}}
	cfg := config.ServerConfig{
		Name: "rs", DataDir: t.TempDir() + "/rs.etcd",
		InitialPeerURLsMap: types.URLsMap{"rs": peer}, PeerURLs: peer,
		ClientURLs:          types.URLs{{Scheme: "http", Host: freeAddr(t)}},
		InitialClusterToken: "rs", NewCluster: true,
		TickMs: 10, ElectionTicks: 10, SnapshotCount: 1 << 30, SnapshotCatchUpEntries: 1 << 20,
		MaxTxnOps: 128, MaxRequestBytes: maxReq,
		Logger: lg, ServerFeatureGate: features.NewDefaultServerFeatureGate("rs", lg),
	}
	s, err := etcdserver.NewServer(cfg)
	if err != nil {
		t.Fatal(err)
	}
	s.Start()
	<-s.ReadyNotify()
	return s
}

// fakeStream records each chunk (the pointer and a deep copy at Send time) and can fail the
// n-th Send.
type fakeStream struct {
	ctx     context.Context
	sent    []*pb.RangeStreamResponse
	copies  []*pb.RangeStreamResponse
	failAt  int // 1-based; 0: never
	failErr error
}

func (f *fakeStream) Send(r *pb.RangeStreamResponse) error {
	f.sent = append(f.sent, r)
	f.copies = append(f.copies, proto.Clone(r).(*pb.RangeStreamResponse))
	if f.failAt != 0 && len(f.sent) == f.failAt {
		return f.failErr
	}
	return nil
}
func (f *fakeStream) Context() context.Context       { return f.ctx }
func (f *fakeStream) SetHeader(metadata.MD) error    { return nil }
func (f *fakeStream) SendHeader(metadata.MD) error   { return nil }
func (f *fakeStream) SetTrailer(metadata.MD)         {}
func (f *fakeStream) SendMsg(any) error              { panic("SendMsg called") }
func (f *fakeStream) RecvMsg(any) error              { panic("RecvMsg called") }

// inRange is auth.inRange on the model's range end (txn.rangeEndOf): nil -> the key alone;
// non-nil empty -> "\x00"; otherwise the contents.
func inRange(key, end []byte, endNil bool, k []byte) bool {
	if endNil {
		return bytes.Equal(k, key)
	}
	if len(end) == 0 {
		end = []byte{0}
	}
	if bytes.Compare(k, key) < 0 {
		return false
	}
	return bytes.Equal(end, []byte{0}) || bytes.Compare(k, end) < 0
}

func randKey(r *rand.Rand) []byte {
	alpha := []byte{0, 1, 'a', 'b', 0x7f, 0xfe, 0xff}
	n := 1 + r.Intn(4)
	b := make([]byte, n)
	for i := range b {
		b[i] = alpha[r.Intn(len(alpha))]
	}
	return b
}

func TestRangeStreamChunks(t *testing.T) {
	srv := startServer(t, 4096)
	defer srv.Stop()
	ctx := t.Context()
	r := rand.New(rand.NewSource(7))

	// Keys over a small alphabet (prefixes, 0x00 and 0xff bytes), values of varied sizes, some
	// overwritten and deleted, so that pages shrink and grow (adjustChunkLimit) and revisions vary.
	for i := 0; i < 600; i++ {
		k := randKey(r)
		v := bytes.Repeat([]byte{'v'}, r.Intn(3)*r.Intn(900))
		if r.Intn(10) == 0 {
			if _, err := srv.DeleteRange(ctx, &pb.DeleteRangeRequest{Key: k}); err != nil {
				t.Fatal(err)
			}
			continue
		}
		if _, err := srv.Put(ctx, &pb.PutRequest{Key: k, Value: v}); err != nil {
			t.Fatal(err)
		}
	}
	cur, err := srv.Range(ctx, &pb.RangeRequest{Key: []byte{0}, RangeEnd: []byte{0}, CountOnly: true})
	if err != nil {
		t.Fatal(err)
	}
	head := cur.Header.Revision

	chunks, multi := 0, 0
	for i := 0; i < 3000; i++ {
		key := randKey(r)
		var end []byte
		endNil := false
		switch r.Intn(5) {
		case 0:
			end, endNil = nil, true
		case 1:
			end = []byte{}
		case 2:
			end = []byte{0}
		default:
			end = randKey(r)
		}
		limits := []int64{0, 0, -1, 1, 2, 3, 7, 10, 11, 25, 1000}
		req := &pb.RangeRequest{
			Key: append([]byte(nil), key...), RangeEnd: end,
			Limit:        limits[r.Intn(len(limits))],
			Serializable: r.Intn(2) == 0,
			KeysOnly:     r.Intn(3) == 0,
			CountOnly:    r.Intn(8) == 0,
		}
		if r.Intn(4) == 0 {
			req.Revision = head - int64(r.Intn(100))
		}
		orig := proto.Clone(req).(*pb.RangeRequest)
		fs := &fakeStream{ctx: ctx}
		if r.Intn(10) == 0 {
			fs.failAt = 1 + r.Intn(3)
			fs.failErr = fmt.Errorf("send failure %d", i)
		}
		err := srv.RangeStream(req, fs)

		// The error a Send returned is the error returned.
		if fs.failAt != 0 && len(fs.sent) == fs.failAt {
			if !errors.Is(err, fs.failErr) || err != fs.failErr {
				panic(fmt.Sprintf("claim: Send's error returned: got %v want %v", err, fs.failErr))
			}
			if len(fs.sent) != fs.failAt {
				panic("claim: no Send after a failed one")
			}
		} else if err != nil {
			t.Logf("request %d: error %v (sent %d)", i, err, len(fs.sent))
		}
		chunks += len(fs.sent)
		if len(fs.sent) > 1 {
			multi++
		}
		for j, c := range fs.sent {
			rr := c.RangeResponse
			if rr == nil {
				panic("claim: RangeResponse not nil")
			}
			last := j == len(fs.sent)-1
			if rr.Header != nil && !(last && (err == nil || fs.failAt == len(fs.sent))) {
				panic(fmt.Sprintf("claim: only the last chunk has a header (chunk %d of %d)", j, len(fs.sent)))
			}
			if rr.Header != nil && (rr.Header.ClusterId != 0 || rr.Header.MemberId != 0 || rr.Header.RaftTerm != 0) {
				panic("claim: a fresh header")
			}
			for _, kv := range rr.Kvs {
				if !inRange(orig.Key, orig.RangeEnd, endNil, kv.Key) {
					panic(fmt.Sprintf("claim: key %q not in [%q, %q) (nil end %v)", kv.Key, orig.Key, orig.RangeEnd, endNil))
				}
			}
			// Not written after it was sent.
			if !proto.Equal(c, fs.copies[j]) {
				panic(fmt.Sprintf("claim: chunk %d written after Send", j))
			}
			for k, kv := range rr.Kvs {
				if !bytes.Equal(kv.Key, fs.copies[j].RangeResponse.Kvs[k].Key) {
					panic("claim: key bytes changed")
				}
			}
		}
		// The fields but Key, Limit and Revision unchanged.
		got := proto.Clone(req).(*pb.RangeRequest)
		got.Key, got.Limit, got.Revision = orig.Key, orig.Limit, orig.Revision
		if !proto.Equal(got, orig) || endNil != (req.RangeEnd == nil) || !bytes.Equal(req.RangeEnd, end) {
			panic("claim: only Key, Limit and Revision rewritten")
		}
		_ = mvccpb.PUT
	}
	t.Logf("%d chunks, %d multi-chunk streams", chunks, multi)
}
