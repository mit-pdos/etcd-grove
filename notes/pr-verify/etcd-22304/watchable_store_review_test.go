package mvcc

import (
	"testing"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"

	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

func reviewStore(t *testing.T) (*watchableStore, func()) {
	b, _ := betesting.NewDefaultTmpBackend(t)
	s := &watchableStore{
		store:    NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{}),
		unsynced: newWatcherGroup(),
		synced:   newWatcherGroup(),
		victimc:  make(chan struct{}, 1),
		stopc:    make(chan struct{}),
	}
	s.store.ReadView = &readView{s}
	s.store.WriteView = &writeView{s}
	return s, func() { cleanup(s, b) }
}

// A watcher on a rarely written key, 5000 revisions behind (writes to other keys). On the base
// one syncWatchers pass delivers its single event and syncs it (watchBatchMaxRevs bounds the
// revisions *with events for the watcher*); on the PR it takes ceil(5000/1001) passes.
func TestReviewSparseWatcherPasses(t *testing.T) {
	s, done := reviewStore(t)
	defer done()
	s.Put([]byte("foo"), []byte("v"), lease.NoLease) // rev 2
	for i := 0; i < 5000; i++ {
		s.Put([]byte("other"), []byte("v"), lease.NoLease)
	}
	ch := make(chan WatchResponse, 16)
	w, _ := s.watch([]byte("foo"), nil, 1, 1, ch)
	passes := 0
	for {
		passes++
		s.syncWatchers()
		if _, ok := s.synced.watchers[w]; ok {
			break
		}
		if passes > 100 {
			t.Fatalf("not synced after 100 passes")
		}
	}
	t.Logf("synced after %d passes", passes)
	if passes != 1 {
		t.Errorf("sparse watcher needed %d syncWatchers passes (base: 1)", passes)
	}
}

// The writer keeps writing 1500 revisions (to other keys) between syncWatchers passes (as at
// ~15k writes/s with the 100ms watchResyncPeriod: a pass that does not reduce the unsynced count
// waits 100ms). A watcher on a quiet key never becomes synced on the PR; on the base it syncs in
// the first pass.
func TestReviewSparseWatcherStarves(t *testing.T) {
	s, done := reviewStore(t)
	defer done()
	s.Put([]byte("foo"), []byte("v"), lease.NoLease)
	for i := 0; i < 1500; i++ {
		s.Put([]byte("other"), []byte("v"), lease.NoLease)
	}
	ch := make(chan WatchResponse, 16)
	w, _ := s.watch([]byte("foo"), nil, 1, 1, ch)
	for pass := 1; pass <= 50; pass++ {
		s.syncWatchers()
		if _, ok := s.synced.watchers[w]; ok {
			t.Logf("synced after %d passes", pass)
			return
		}
		for i := 0; i < 1500; i++ {
			s.Put([]byte("other"), []byte("v"), lease.NoLease)
		}
	}
	t.Errorf("watcher on a quiet key still unsynced after 50 passes; rev=%d minRev=%d", s.Rev(), w.minRev)
}

// Compaction: a watcher below the compaction revision gets the compacted response and is
// removed, as on the base.
func TestReviewCompactedWatcher(t *testing.T) {
	s, done := reviewStore(t)
	defer done()
	for i := 0; i < 3000; i++ {
		s.Put([]byte("foo"), []byte("v"), lease.NoLease)
	}
	chC := make(chan WatchResponse, 16)
	wc, _ := s.watch([]byte("foo"), nil, 2, 1, chC)
	chD := make(chan WatchResponse, 16)
	wd, _ := s.watch([]byte("foo"), nil, 2500, 2, chD)
	fut, err := s.Compact(traceutil.TODO(), 2000)
	if err != nil {
		t.Fatal(err)
	}
	<-fut
	s.syncWatchers()
	select {
	case wr := <-chC:
		if wr.CompactRevision != 2000 {
			t.Fatalf("want compacted response, got %+v", wr.CompactRevision)
		}
	default:
		t.Fatalf("no compacted response")
	}
	if !wc.compacted {
		t.Fatalf("not marked compacted")
	}
	if _, ok := s.unsynced.watchers[wc]; ok {
		t.Fatalf("compacted watcher still unsynced")
	}
	n := 0
	for pass := 0; pass < 5; pass++ {
		for {
			select {
			case wr := <-chD:
				n += len(wr.Events)
				continue
			default:
			}
			break
		}
		s.syncWatchers()
	}
	for {
		select {
		case wr := <-chD:
			n += len(wr.Events)
			continue
		default:
		}
		break
	}
	if n != 3001-2500+1 {
		t.Fatalf("deep watcher got %d events, want %d", n, 3001-2500+1)
	}
	if _, ok := s.synced.watchers[wd]; !ok {
		t.Fatalf("not synced")
	}
}

// A future-revision watcher (after Restore, minRev near MaxInt64) next to a deep one: the
// future one is synced in the first pass, no overflow; the deep one gets all its events.
// A victim from a not-reached window is resent with Revision = window end - 1.
func TestReviewFutureAndVictim(t *testing.T) {
	s, done := reviewStore(t)
	defer done()
	for i := 0; i < 2500; i++ {
		s.Put([]byte("foo"), []byte("v"), lease.NoLease)
	}
	chF := make(chan WatchResponse, 16)
	wf := &watcher{key: []byte("foo"), minRev: 1<<63 - 1 - 2, restore: true, ch: chF, id: 1}
	s.unsynced.add(wf)
	chV := make(chan WatchResponse) // unbuffered: send fails, victim
	wv, _ := s.watch([]byte("foo"), nil, 2, 2, chV)
	s.syncWatchers()
	if _, ok := s.synced.watchers[wf]; !ok {
		t.Fatalf("future watcher not synced")
	}
	if !wv.victim || len(s.victims) != 1 {
		t.Fatalf("expected victim")
	}
	got := make(chan WatchResponse, 1)
	go func() { got <- <-chV }()
	for s.moveVictims() == 0 {
	}
	wr := <-got
	last := wr.Events[len(wr.Events)-1].Kv.ModRevision
	t.Logf("victim resend: %d events, last %d, Revision %d, minRev now %d", len(wr.Events), last, wr.Revision, wv.minRev)
	if wr.Revision < last || wr.Revision != wv.minRev-1 {
		t.Fatalf("bad victim revision")
	}
	if _, ok := s.unsynced.watchers[wv]; !ok {
		t.Fatalf("victim not back in unsynced")
	}
}
