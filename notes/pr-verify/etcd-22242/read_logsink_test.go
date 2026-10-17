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

package read

import (
	"encoding/binary"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"

	"go.etcd.io/raft/v3"
)

// stallingSink stays inside Write until released, like a write(2) to a stalled log file.
type stallingSink struct {
	writing chan struct{}
	release chan struct{}
}

func (b *stallingSink) Write(p []byte) (int, error) {
	select {
	case b.writing <- struct{}{}:
	default:
	}
	<-b.release
	return len(p), nil
}

func (b *stallingSink) Sync() error { return nil }

func stallingLogger(t *testing.T) (*zap.Logger, *stallingSink) {
	sink := &stallingSink{writing: make(chan struct{}, 1), release: make(chan struct{})}
	t.Cleanup(func() { close(sink.release) })
	lg := zap.New(zapcore.NewCore(
		zapcore.NewJSONEncoder(zap.NewProductionEncoderConfig()),
		zapcore.Lock(zapcore.AddSync(sink)),
		zap.NewAtomicLevelAt(zap.InfoLevel),
	))
	return lg, sink
}

func readOnce(t *testing.T, r *Read, mockRaft *testRaftNode, i int, beforeAnswer func()) {
	readDone := make(chan error, 1)
	go func() { readDone <- r.LinearizableReadNotify(t.Context()) }()
	require.Eventuallyf(t, func() bool { return len(mockRaft.getRequests()) > 0 }, time.Second,
		5*time.Millisecond, "read %d: no ReadIndex request", i)
	beforeAnswer()
	reqs := mockRaft.getRequests()
	ctx := make([]byte, 8)
	binary.BigEndian.PutUint64(ctx, reqs[len(reqs)-1])
	mockRaft.readStateC <- raft.ReadState{Index: 100, RequestCtx: ctx}
	select {
	case err := <-readDone:
		require.NoError(t, err)
	case <-time.After(3 * time.Second):
		t.Fatalf("read %d: linearizable read hung on a stalled log sink", i)
	}
	mockRaft.mu.Lock()
	mockRaft.readIndexRequests = nil
	mockRaft.mu.Unlock()
}

// TestReadLoopStalledSink_SlowIteration: an iteration slower than 100ms logs its trace; with the
// sink stalled, the next linearizable read must still complete (etcd-io/etcd#22214's goroutine
// dump: the loop parked in trace.LogAllStepsIfLong).
func TestReadLoopStalledSink_SlowIteration(t *testing.T) {
	s, mockRaft := setupTestRequestCurrentIndex(t)
	lg, sink := stallingLogger(t)
	s.logger = lg
	s.appliedIndex = 100
	r := NewRead(s, mockRaft)
	go r.LinearizableReadLoop()
	t.Cleanup(func() { close(s.stopping) })

	readOnce(t, r, mockRaft, 0, func() { time.Sleep(250 * time.Millisecond) })
	select {
	case <-sink.writing:
	case <-time.After(time.Second):
		t.Fatal("the slow iteration's trace never reached the sink")
	}
	readOnce(t, r, mockRaft, 1, func() {})
}

// TestReadLoopStalledSink_ReadIndexRetry: a ReadIndex response slower than readIndexRetryTime makes
// requestCurrentIndex log "waiting for ReadIndex response took too long, retrying" on the read loop's
// goroutine; with the sink stalled the loop parks there and the read never completes.
func TestReadLoopStalledSink_ReadIndexRetry(t *testing.T) {
	old := readIndexRetryTime
	readIndexRetryTime = 50 * time.Millisecond
	t.Cleanup(func() { readIndexRetryTime = old })

	s, mockRaft := setupTestRequestCurrentIndex(t)
	lg, sink := stallingLogger(t)
	s.logger = lg
	s.appliedIndex = 100
	r := NewRead(s, mockRaft)
	go r.LinearizableReadLoop()
	t.Cleanup(func() { close(s.stopping) })

	readOnce(t, r, mockRaft, 0, func() {
		select {
		case <-sink.writing: // the retry warning reached the stalled sink
		case <-time.After(time.Second):
			t.Fatal("no retry warning")
		}
	})
}
