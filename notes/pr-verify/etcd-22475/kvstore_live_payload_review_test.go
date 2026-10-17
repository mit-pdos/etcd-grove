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
	"testing"
	"time"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// Two stores in one process share the package-level gauge (as keysGauge does): the gauge is
// the sum of both, and restarting one resets it to that store's payload alone.
func TestLiveKVPayloadTwoStoresShareGauge(t *testing.T) {
	b1, _ := betesting.NewDefaultTmpBackend(t)
	b2, _ := betesting.NewDefaultTmpBackend(t)
	s1 := NewStore(zaptest.NewLogger(t), b1, &lease.FakeLessor{}, StoreConfig{})
	s2 := NewStore(zaptest.NewLogger(t), b2, &lease.FakeLessor{}, StoreConfig{})
	s1.Put([]byte("a"), []byte("123"), lease.NoLease)     // 4
	s2.Put([]byte("b"), []byte("1234567"), lease.NoLease) // 8
	t.Logf("after puts: gauge=%d, s1=%d, s2=%d", readGaugeInt(liveKVPayloadGauge), livePayloadOf(t, s1), livePayloadOf(t, s2))
	s1.Close()
	s1 = NewStore(zaptest.NewLogger(t), b1, &lease.FakeLessor{}, StoreConfig{})
	t.Logf("after restarting s1: gauge=%d, s1=%d, s2=%d", readGaugeInt(liveKVPayloadGauge), livePayloadOf(t, s1), livePayloadOf(t, s2))
	s2.DeleteRange([]byte("b"), nil)
	t.Logf("after deleting s2's key: gauge=%d, s1=%d, s2=%d", readGaugeInt(liveKVPayloadGauge), livePayloadOf(t, s1), livePayloadOf(t, s2))
	cleanup(s1, b1)
	cleanup(s2, b2)
}

// A crash in the middle of a scheduled compaction leaves a prefix of the revisions to remove
// deleted; restore (and the resumed compaction) still gives the right gauge.
func TestLiveKVPayloadPartialCompactionResume(t *testing.T) {
	for _, cut := range []int64{0, 2, 3, 4, 5, 6} {
		b, _ := betesting.NewDefaultTmpBackend(t)
		s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
		s.Put([]byte("k1"), []byte("v1"), lease.NoLease)     // rev 2
		s.DeleteRange([]byte("k1"), nil)                     // rev 3
		s.Put([]byte("k2"), []byte("v22"), lease.NoLease)    // rev 4
		s.Put([]byte("k1"), []byte("longer"), lease.NoLease) // rev 5
		s.DeleteRange([]byte("k2"), nil)                     // rev 6
		s.Put([]byte("k3"), []byte("x"), lease.NoLease)      // rev 7
		want := livePayloadOf(t, s)
		tx := s.b.BatchTx()
		tx.Lock()
		UnsafeSetScheduledCompact(tx, 6)
		// simulate the compaction having removed the revisions up to cut (none is kept: k1's
		// rev 2,3 are a dead generation, rev 4 and 6 are k2's dead generation; rev 5 is k1's
		// latest and is kept, so skip it)
		for r := int64(2); r <= cut; r++ {
			if r == 5 {
				continue
			}
			rb := RevToBytes(Revision{Main: r}, NewRevBytes())
			tx.UnsafeDelete(schema.Key, rb)
			tb := RevToBytes(Revision{Main: r}, NewRevBytes())
			tb = append(tb, markTombstone)
			tx.UnsafeDelete(schema.Key, tb)
		}
		tx.Unlock()
		s.Commit()
		s.Close()
		ns := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
		if got := readGaugeInt(liveKVPayloadGauge); got != want {
			t.Errorf("cut %d: after restore gauge = %d, want %d", cut, got, want)
		}
		time.Sleep(100 * time.Millisecond)
		if got := readGaugeInt(liveKVPayloadGauge); got != want || livePayloadOf(t, ns) != want {
			t.Errorf("cut %d: after resumed compaction gauge = %d, range = %d, want %d", cut, got, livePayloadOf(t, ns), want)
		}
		ns.Put([]byte("k2"), []byte("z"), lease.NoLease)
		if got, w := readGaugeInt(liveKVPayloadGauge), livePayloadOf(t, ns); got != w {
			t.Errorf("cut %d: after put gauge = %d, want %d", cut, got, w)
		}
		cleanup(ns, b)
	}
}
