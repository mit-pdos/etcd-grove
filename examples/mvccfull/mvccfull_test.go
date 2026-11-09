package mvccfull

import (
	"path/filepath"
	"testing"
	"time"
)

// The tester's checks hold for every Config (mvccfull.go); the Configs here only make some
// executions likely, each a class of bugs': they are engineering, not part of what is verified.

// small is a base for the engineered Configs: small sizes, fast compactions, a paced registrar.
func small(t *testing.T) Config {
	return Config{Prefix: filepath.Join(t.TempDir(), "m"), Ops: 1500, Depth: 2, MaxVal: 20,
		Readers: 2, Reads: 300, Streams: 2, Watchers: 16,
		CompactionSleep: time.Microsecond,
		Mix: Mix{
			Step:     []int{80, 16, 1, 1, 1, 1},
			Op:       []int{25, 12, 25, 5, 5, 10, 4, 10, 4},
			RangeRev: []int{1, 1, 2, 0},
			Act:      []int{4, 1, 1, 1, 1, 1},
			Start:    []int{1, 3, 0},
			Pause:    100 * time.Microsecond,
		}}
}

// compactionEdge: compactions at the current revision, reads and watches from exactly the
// compaction revision, compactions in batches of one (what is kept at the compaction revision,
// and the ErrCompacted boundary).
func compactionEdge(t *testing.T) Config {
	c := small(t)
	c.CompactionBatchLimit = 1
	c.Mix.Op = []int{25, 15, 20, 3, 3, 20, 2, 10, 2}
	c.Mix.CompactAt = []int{1, 2, 4}
	c.Mix.RangeRev = []int{1, 0, 1, 3}
	c.Mix.Start = []int{1, 1, 4}
	return c
}

// slowReceiver: a receiver slower than the writer, so that the streams' channels fill and
// watchers become victims (moveVictims, the victims' batches, unsynced catch-up).
func slowReceiver(t *testing.T) Config {
	c := small(t)
	c.Depth = 1
	c.Watchers = 100
	c.Mix.RecvPause = 5 * time.Millisecond
	c.Mix.Act = []int{8, 1, 1, 1, 1, 0}
	c.Mix.Start = []int{1, 8, 1}
	return c
}

// churn: restarts and snapshot installs often, the follower far behind (restored watchers,
// resumed compactions, the index and the leases restored from files).
func churn(t *testing.T) Config {
	c := small(t)
	c.BatchLimit = 1
	c.Mix.Step = []int{60, 5, 2, 6, 6, 3}
	c.Mix.Op = []int{25, 10, 20, 8, 6, 15, 4, 8, 4}
	return c
}

// fewKeys: three keys, so the store is often empty (hashes of an empty keyspace) and every change
// reaches many watchers.
func fewKeys(t *testing.T) Config {
	c := small(t)
	c.Depth = 1
	c.MaxVal = 5
	return c
}

func runConfigs(t *testing.T, name string, mk func(*testing.T) Config, n int) {
	t.Run(name, func(t *testing.T) {
		for i := 0; i < n; i++ {
			t.Logf("%+v", Run(mk(t)))
		}
	})
}

func TestRun(t *testing.T) {
	runConfigs(t, "small", small, 4)
	runConfigs(t, "compactionEdge", compactionEdge, 4)
	runConfigs(t, "slowReceiver", slowReceiver, 2)
	runConfigs(t, "churn", churn, 4)
	runConfigs(t, "fewKeys", fewKeys, 4)
}

// TestMain_ runs Main's configuration (the closed theorem's program's) in a fresh directory, and
// logs what it exercised.
func TestMain_(t *testing.T) {
	if testing.Short() {
		t.Skip("Main's sizes")
	}
	t.Logf("%+v", Run(MainConfig(filepath.Join(t.TempDir(), "mvccfull"))))
}
