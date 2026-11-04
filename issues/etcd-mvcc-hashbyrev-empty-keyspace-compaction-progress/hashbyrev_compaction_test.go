// Copy into server/storage/mvcc of etcd-io/etcd.

package mvcc

import (
	"context"
	"fmt"
	"testing"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/schedule"
	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// TestHashByRevDuringCompaction computes HashByRev(0) twice, as the periodic
// corruption check does (corruptionChecker.PeriodicCheck), once before the
// compaction job deletes the compacted revisions from the backend and once
// after, with no write in between. Both report the same Revision and
// CompactRevision, so the check expects the same Hash and raises a CORRUPT
// alarm if they differ.
//
// The compaction job is held back by a job queued ahead of it on the store's
// FIFO scheduler, so the first hash is taken before it runs, deterministically.
func TestHashByRevDuringCompaction(t *testing.T) {
	for _, tc := range []struct {
		name string
		live bool // whether a key is live at the compaction revision
	}{
		{name: "no key live", live: false},
		{name: "one key live", live: true},
	} {
		t.Run(tc.name, func(t *testing.T) {
			b, _ := betesting.NewDefaultTmpBackend(t)
			s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
			defer cleanup(s, b)

			for i := 0; i < 10; i++ {
				s.Put([]byte(fmt.Sprintf("k%d", i)), []byte("v"), lease.NoLease)
			}
			if tc.live {
				s.Put([]byte("live"), []byte("v"), lease.NoLease)
			}
			for i := 0; i < 10; i++ {
				s.DeleteRange([]byte(fmt.Sprintf("k%d", i)), nil)
			}
			rev := s.Rev()

			// Hold the scheduler so that the compaction job waits.
			release := make(chan struct{})
			s.fifoSched.Schedule(schedule.NewJob("block", func(context.Context) { <-release }))

			done, err := s.Compact(traceutil.TODO(), rev)
			if err != nil {
				t.Fatal(err)
			}

			h1, _, err := s.hashes.HashByRev(0)
			if err != nil {
				t.Fatal(err)
			}
			close(release)
			<-done
			h2, _, err := s.hashes.HashByRev(0)
			if err != nil {
				t.Fatal(err)
			}

			if h1.Revision != h2.Revision || h1.CompactRevision != h2.CompactRevision {
				t.Fatalf("revisions differ: before %+v, after %+v", h1, h2)
			}
			if h1.Hash != h2.Hash {
				t.Fatalf("HashByRev(0) at revision %d, compact revision %d: hash %d before the compaction job, %d after",
					h1.Revision, h1.CompactRevision, h1.Hash, h2.Hash)
			}
		})
	}
}
