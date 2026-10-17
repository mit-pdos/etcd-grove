package read

import (
	"encoding/binary"
	"encoding/json"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/prometheus/client_golang/prometheus/testutil"
	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"

	"go.etcd.io/raft/v3"
)

// slowSink takes `delay` per Write and records what it got (and when).
type slowSink struct {
	delay time.Duration
	mu    sync.Mutex
	lines []string
	times []time.Time
}

func (s *slowSink) Write(p []byte) (int, error) {
	time.Sleep(s.delay)
	s.mu.Lock()
	s.lines = append(s.lines, string(p))
	s.times = append(s.times, time.Now())
	s.mu.Unlock()
	return len(p), nil
}
func (s *slowSink) Sync() error { return nil }

func answerOne(t *testing.T, r *Read, m *testRaftNode, before time.Duration) {
	done := make(chan error, 1)
	go func() { done <- r.LinearizableReadNotify(t.Context()) }()
	deadline := time.Now().Add(2 * time.Second)
	for len(m.getRequests()) == 0 {
		if time.Now().After(deadline) {
			t.Fatal("no ReadIndex request")
		}
		time.Sleep(time.Millisecond)
	}
	time.Sleep(before)
	reqs := m.getRequests()
	ctx := make([]byte, 8)
	binary.BigEndian.PutUint64(ctx, reqs[len(reqs)-1])
	m.readStateC <- raft.ReadState{Index: 100, RequestCtx: ctx}
	select {
	case err := <-done:
		if err != nil {
			t.Fatal(err)
		}
	case <-time.After(3 * time.Second):
		t.Fatal("read hung")
	}
	m.mu.Lock()
	m.readIndexRequests = nil
	m.mu.Unlock()
}

// Slow (not stalled) sink: several back-to-back slow iterations; checks drops, the logged
// "duration" against the iteration's real length, and logging after the loop returned.
func TestReviewSlowSink(t *testing.T) {
	s, m := setupTestRequestCurrentIndex(t)
	sink := &slowSink{delay: 400 * time.Millisecond}
	s.logger = zap.New(zapcore.NewCore(zapcore.NewJSONEncoder(zap.NewProductionEncoderConfig()),
		zapcore.Lock(zapcore.AddSync(sink)), zap.NewAtomicLevelAt(zap.InfoLevel)))
	s.appliedIndex = 100
	r := NewRead(s, m)
	before := testutil.ToFloat64(droppedReadLoopTraces)
	loopDone := make(chan struct{})
	go func() { r.LinearizableReadLoop(); close(loopDone) }()
	for i := 0; i < 4; i++ {
		answerOne(t, r, m, 120*time.Millisecond) // each iteration ~120ms
	}
	close(s.stopping)
	<-loopDone
	returned := time.Now()
	time.Sleep(1500 * time.Millisecond)
	sink.mu.Lock()
	defer sink.mu.Unlock()
	t.Logf("dropped: %v", testutil.ToFloat64(droppedReadLoopTraces)-before)
	for i, l := range sink.lines {
		var e map[string]any
		_ = json.Unmarshal([]byte(strings.TrimSpace(l)), &e)
		t.Logf("trace %d: duration=%v (written %v after loop returned)", i, e["duration"], sink.times[i].Sub(returned))
	}
}
