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
)

func isClosed(ch chan *LeaseKeepAliveResponse) bool {
	select {
	case _, ok := <-ch:
		return !ok
	default:
		return false
	}
}

// TestLessorCloseRequireLeaderKeepsPairing: a keepAlive with a require-leader
// subscription A (first) and a plain subscription B. After one leader loss only A
// is closed and B keeps its own context; a second leader loss must not close B,
// which never asked for a leader.
func TestLessorCloseRequireLeaderKeepsPairing(t *testing.T) {
	l := &lessor{keepAlives: make(map[LeaseID]*keepAlive)}
	chA := make(chan *LeaseKeepAliveResponse, 1)
	chB := make(chan *LeaseKeepAliveResponse, 1)
	ctxA := WithRequireLeader(context.Background())
	ctxB := context.Background()
	l.keepAlives[1] = &keepAlive{
		chs:  []chan<- *LeaseKeepAliveResponse{chA, chB},
		ctxs: []context.Context{ctxA, ctxB},
	}

	l.closeRequireLeader()
	if !isClosed(chA) || isClosed(chB) {
		t.Fatalf("first leader loss: want A closed and B open, got A closed=%v B closed=%v", isClosed(chA), isClosed(chB))
	}
	ka := l.keepAlives[1]
	if ka == nil || len(ka.chs) != 1 || ka.ctxs[0] != ctxB {
		t.Errorf("after the first leader loss B's channel is paired with the wrong context (ctxs[0]==ctxA: %v)", ka != nil && len(ka.ctxs) == 1 && ka.ctxs[0] == ctxA)
	}

	l.closeRequireLeader()
	if isClosed(chB) {
		t.Fatalf("second leader loss closed B's channel, whose context does not require a leader (remaining entry: %v)", l.keepAlives[1])
	}
}
