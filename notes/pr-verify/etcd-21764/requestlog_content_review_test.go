package v3rpc

import (
	"bytes"
	"strings"
	"testing"
	"time"

	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
)

func rvLogger(buf *bytes.Buffer) *zap.Logger {
	return zap.New(zapcore.NewCore(
		zapcore.NewJSONEncoder(zap.NewProductionEncoderConfig()), zapcore.AddSync(buf), zap.InfoLevel))
}

func rvEntry(req any) string {
	var buf bytes.Buffer
	logLightweightRequestInfo(rvLogger(&buf), "/m", "r", 0, req)
	s := buf.String()
	// drop the timestamp field
	if i := strings.Index(s, `"msg"`); i >= 0 {
		s = s[i:]
	}
	return s
}

// etcd keys are arbitrary bytes; zap.ByteString / zap.Strings replace invalid UTF-8
// with U+FFFD, so different binary keys give the same entry.
func TestReviewBinaryKeysCollide(t *testing.T) {
	a := rvEntry(&pb.PutRequest{Key: []byte{0xff, 0x01}, Value: []byte("v")})
	b := rvEntry(&pb.PutRequest{Key: []byte{0xfe, 0x01}, Value: []byte("v")})
	t.Logf("put 0xff01: %s", a)
	t.Logf("put 0xfe01: %s", b)
	if a != b {
		t.Fatalf("entries differ; finding does not hold")
	}
	c := rvEntry(&pb.TxnRequest{Compare: []*pb.Compare{{Key: []byte{0x80}}}})
	d := rvEntry(&pb.TxnRequest{Compare: []*pb.Compare{{Key: []byte{0x81}}}})
	t.Logf("txn cmp 0x80: %s", c)
	if c != d {
		t.Fatalf("txn entries differ; finding does not hold")
	}
}

// The entry's size (and the work to build it) grows with the key: a 1 MiB key is
// written to the request log in full, and a Txn's 10 logged compare keys are each
// copied (string(r.Compare[i].Key)) and logged in full.
func TestReviewEntrySizeUnboundedInKeySize(t *testing.T) {
	key := bytes.Repeat([]byte("k"), 1<<20)
	e := rvEntry(&pb.PutRequest{Key: key})
	t.Logf("put with 1 MiB key: entry %d bytes", len(e))
	if len(e) < 1<<20 {
		t.Fatalf("entry is small; finding does not hold")
	}
	cmps := make([]*pb.Compare, 10)
	for i := range cmps {
		cmps[i] = &pb.Compare{Key: bytes.Repeat([]byte{'a' + byte(i)}, 140<<10)}
	}
	start := time.Now()
	e = rvEntry(&pb.TxnRequest{Compare: cmps})
	t.Logf("txn with 10 x 140 KiB compare keys: entry %d bytes, %v", len(e), time.Since(start))
	if len(e) < 10*140<<10 {
		t.Fatalf("entry is small; finding does not hold")
	}
}
