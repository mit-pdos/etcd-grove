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

package mvcc

import (
	"context"
	"fmt"
	"testing"
	"time"

	"go.uber.org/zap"

	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// TestWatchNegativeStartRev checks WatchStream.Watch's documentation: "If
// "startRev" <=0, watch observes events after currentRev". A watch from a
// negative revision should receive nothing before the next write, as one from 0.
func TestWatchNegativeStartRev(t *testing.T) {
	for _, start := range []int64{0, -1, -2} {
		t.Run(fmt.Sprintf("startRev=%d", start), func(t *testing.T) {
			b, _ := betesting.NewDefaultTmpBackend(t)
			s := New(zap.NewNop(), b, &lease.FakeLessor{}, StoreConfig{})
			defer cleanup(s, b)
			s.Put([]byte("a"), []byte("1"), lease.NoLease) // revision 2, before the watch

			ws := s.NewWatchStream()
			defer ws.Close()
			if _, err := ws.Watch(context.TODO(), 0, []byte("a"), nil, start); err != nil {
				t.Fatal(err)
			}
			select {
			case r := <-ws.Chan():
				t.Errorf("before any later write: %d events, revision %d, compact revision %d; want nothing",
					len(r.Events), r.Revision, r.CompactRevision)
			case <-time.After(500 * time.Millisecond):
			}
		})
	}
}
