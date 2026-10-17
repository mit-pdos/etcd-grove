// Copyright 2026 The etcd Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package v3rpc

import (
	"bytes"
	"strings"
	"sync"
	"testing"
	"time"

	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
)

// jsonRequestLogger builds the request logger the way NewServer does, over ws.
func jsonRequestLogger(ws zapcore.WriteSyncer) *zap.Logger {
	return zap.New(zapcore.NewCore(
		zapcore.NewJSONEncoder(zap.NewProductionEncoderConfig()), ws, zap.InfoLevel))
}

type memSink struct {
	mu    sync.Mutex
	buf   bytes.Buffer
	delay time.Duration
}

func (m *memSink) Write(p []byte) (int, error) {
	time.Sleep(m.delay)
	m.mu.Lock()
	defer m.mu.Unlock()
	return m.buf.Write(p)
}
func (m *memSink) Sync() error { return nil }
func (m *memSink) String() string {
	m.mu.Lock()
	defer m.mu.Unlock()
	return m.buf.String()
}

// A transaction's operations are not logged: a Txn that deletes a key with no
// comparison (clientv3's Txn().Then(OpDelete(k)), etcdctl txn) logs no key at
// all, so the request log cannot answer "who deleted this key" for it.
func TestRequestLogTxnOpKeysNotLogged(t *testing.T) {
	sink := &memSink{}
	lg := jsonRequestLogger(zapcore.AddSync(sink))
	req := &pb.TxnRequest{Success: []*pb.RequestOp{{Request: &pb.RequestOp_RequestDeleteRange{
		RequestDeleteRange: &pb.DeleteRangeRequest{Key: []byte("victim-key")}}}}}
	logLightweightRequestInfo(lg, "/etcdserverpb.KV/Txn", "10.0.0.1:1", time.Millisecond, req)
	out := sink.String()
	t.Logf("entry: %s", out)
	if strings.Contains(out, "victim-key") {
		t.Fatalf("the deleted key is logged")
	}
}

// compare_range_ends is not aligned with compare_keys: two different
// transactions produce the same entry.
func TestRequestLogCompareRangeEndsAmbiguous(t *testing.T) {
	entry := func(cmps []*pb.Compare) string {
		sink := &memSink{}
		lg := jsonRequestLogger(zapcore.AddSync(sink))
		logLightweightRequestInfo(lg, "/etcdserverpb.KV/Txn", "r", 0, &pb.TxnRequest{Compare: cmps})
		s := sink.String()
		return s[strings.Index(s, `"msg"`):] // drop the timestamp
	}
	a := entry([]*pb.Compare{{Key: []byte("a"), RangeEnd: []byte("z")}, {Key: []byte("b")}})
	b := entry([]*pb.Compare{{Key: []byte("a")}, {Key: []byte("b"), RangeEnd: []byte("z")}})
	t.Logf("a: %s", a)
	t.Logf("b: %s", b)
	if a != b {
		t.Fatalf("entries differ")
	}
}

// The request logger can block the request path on the sink: when the 256 KB
// buffer is full, BufferedWriteSyncer.Write flushes synchronously, under the
// lock every other request's Write and the 1 s flush loop take.
func TestRequestLogBlocksOnSlowSink(t *testing.T) {
	sink := &memSink{delay: 300 * time.Millisecond}
	ws := &zapcore.BufferedWriteSyncer{WS: zapcore.AddSync(sink), Size: 256 * 1024, FlushInterval: time.Second}
	defer ws.Stop()
	lg := jsonRequestLogger(ws)
	key := bytes.Repeat([]byte("k"), 1024)
	var worst time.Duration
	for i := 0; i < 400; i++ { // ~400 KB of entries
		start := time.Now()
		logLightweightRequestInfo(lg, "/etcdserverpb.KV/Put", "10.0.0.1:1", time.Millisecond, &pb.PutRequest{Key: key})
		if d := time.Since(start); d > worst {
			worst = d
		}
	}
	t.Logf("slowest logLightweightRequestInfo call: %v", worst)
	if worst < 250*time.Millisecond {
		t.Fatalf("no call waited for the sink")
	}
}

// After Cleanup stops the BufferedWriteSyncer, entries still logged (requests the
// gRPC server serves after the EtcdServer's run loop has ended) stay in the buffer
// and never reach the file.
func TestRequestLogLostAfterStop(t *testing.T) {
	sink := &memSink{}
	ws := &zapcore.BufferedWriteSyncer{WS: zapcore.AddSync(sink), Size: 256 * 1024, FlushInterval: 100 * time.Millisecond}
	lg := jsonRequestLogger(ws)
	logLightweightRequestInfo(lg, "/etcdserverpb.KV/Range", "r", 0, &pb.RangeRequest{Key: []byte("before-stop")})
	ws.Stop()
	logLightweightRequestInfo(lg, "/etcdserverpb.KV/Range", "r", 0, &pb.RangeRequest{Key: []byte("after-stop")})
	time.Sleep(500 * time.Millisecond)
	out := sink.String()
	if !strings.Contains(out, "before-stop") {
		t.Fatalf("entry before Stop lost")
	}
	if strings.Contains(out, "after-stop") {
		t.Fatalf("entry after Stop was written")
	}
	t.Logf("the entry logged after Stop is never written")
}
