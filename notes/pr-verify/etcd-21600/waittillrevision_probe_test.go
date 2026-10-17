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

package cache

import (
	"context"
	"sync"
	"testing"
	"time"
)

// cancelDuringErrCtx is a context that is canceled while its first Err() call
// is running: that call returns nil (the cancellation comes after it), closes
// Done, and returns only a little later -- the schedule of a cancel that races
// with the waiter's ctx.Err() check.
type cancelDuringErrCtx struct {
	context.Context
	done chan struct{}
	once sync.Once
	mu   sync.Mutex
	err  error
}

func newCancelDuringErrCtx() *cancelDuringErrCtx {
	return &cancelDuringErrCtx{Context: context.Background(), done: make(chan struct{})}
}

func (c *cancelDuringErrCtx) Done() <-chan struct{} { return c.done }

func (c *cancelDuringErrCtx) Err() error {
	c.mu.Lock()
	err := c.err
	c.mu.Unlock()
	if err != nil {
		return err
	}
	c.once.Do(func() {
		c.mu.Lock()
		c.err = context.Canceled
		c.mu.Unlock()
		close(c.done)
		time.Sleep(50 * time.Millisecond) // the canceler's Broadcast runs now
	})
	return nil
}

// waitTillRevision wakes up on cancellation by a Broadcast on revCond from a
// goroutine that does not hold the store's lock. A cancel that lands between
// the waiter's ctx.Err() check and its revCond.Wait() is lost: the goroutine
// has exited (so the WaitTimeout wakeup is gone too), and the waiter sleeps
// until the store's revision next changes.
func TestWaitTillRevisionLostCancelWakeup(t *testing.T) {
	c := &Cache{
		cfg:               defaultConfig(), // WaitTimeout 3s
		store:             newStore(32, 8),
		progressRequestor: newConditionalProgressRequestor(nil, realClock{}, time.Hour),
	}
	c.store.Restore(nil, 5)
	done := make(chan error, 1)
	go func() { done <- c.waitTillRevision(newCancelDuringErrCtx(), 10) }()
	select {
	case err := <-done:
		t.Logf("returned %v", err)
	case <-time.After(5 * time.Second):
		c.store.mu.Lock()
		c.store.revCond.Broadcast()
		c.store.mu.Unlock()
		err := <-done
		t.Fatalf("waitTillRevision returned only when the store's revCond was broadcast again, after 5s (canceled context, 3s WaitTimeout): %v", err)
	}
}
