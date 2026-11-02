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

package clientv3

import (
	"context"
	"testing"
	"time"
)

// closeRequireLeader keeps each surviving keep-alive channel with its own context.
func TestCloseRequireLeaderKeepsContextsAligned(t *testing.T) {
	l := &lessor{donec: make(chan struct{}), keepAlives: make(map[LeaseID]*keepAlive)}
	ctxA := WithRequireLeader(context.Background()) // closed by closeRequireLeader
	ctxB, cancelB := context.WithCancel(context.Background())
	ctxB = context.WithValue(ctxB, keepAliveCtxKey{}, &ctxB) // as KeepAlive wraps it
	chA := make(chan *LeaseKeepAliveResponse, 1)
	chB := make(chan *LeaseKeepAliveResponse, 1)
	ka := &keepAlive{
		chs:   []chan<- *LeaseKeepAliveResponse{chA, chB},
		ctxs:  []context.Context{ctxA, ctxB},
		donec: make(chan struct{}),
	}
	l.keepAlives[1] = ka

	l.closeRequireLeader()

	cancelB()
	done := make(chan struct{})
	go func() { l.keepAliveCtxCloser(ctxB, 1, ka.donec); close(done) }()
	select {
	case <-done:
	case <-time.After(time.Second):
		t.Fatal("keepAliveCtxCloser did not return")
	}
	select {
	case _, ok := <-chB:
		if ok {
			t.Fatal("unexpected value on B's channel")
		}
	default:
		t.Fatalf("B's channel not closed after B's context was canceled; ka.ctxs[0] is A's context: %v",
			ka.ctxs[0] == ctxA)
	}
}
