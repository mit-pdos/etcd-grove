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

package schedule

import (
	"context"
	"runtime"
	"testing"
	"time"

	"go.uber.org/zap"
)

// scheduleBig schedules a job whose closure holds a large object, and returns a
// channel closed when that object is garbage collected.
func scheduleBig(s Scheduler) <-chan struct{} {
	collected := make(chan struct{})
	big := new([1 << 20]byte)
	runtime.SetFinalizer(big, func(*[1 << 20]byte) { close(collected) })
	s.Schedule(NewJob("big", func(context.Context) { big[0] = 1 }))
	return collected
}

// TestFIFOFinishedJobCollected checks that a finished job is not kept reachable by
// the scheduler while later jobs are still pending (etcd-io/etcd#22496).
func TestFIFOFinishedJobCollected(t *testing.T) {
	s := NewFIFOScheduler(zap.NewNop())
	block := make(chan struct{})
	collected := scheduleBig(s)
	s.Schedule(NewJob("block", func(context.Context) { <-block }))
	defer func() {
		close(block)
		s.Stop()
	}()

	deadline := time.Now().Add(5 * time.Second)
	for s.Finished() < 1 {
		if time.Now().After(deadline) {
			t.Fatal("first job did not finish")
		}
		time.Sleep(time.Millisecond)
	}
	if p := s.Pending(); p != 1 {
		t.Errorf("Pending() = %d while the second job runs, want 1 (the running job counts)", p)
	}
	for i := 0; i < 50; i++ {
		runtime.GC()
		select {
		case <-collected:
			return
		case <-time.After(10 * time.Millisecond):
		}
	}
	t.Fatal("the finished job is still reachable while the next job is pending")
}
