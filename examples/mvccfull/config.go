package mvccfull

import (
	"time"

	"github.com/goose-lang/primitive"
)

// A Config is a run's: its sizes, mvcc's own settings, and the mix of its choices. Every Config
// is valid (out-of-range values are clamped, normalize), and the tester's checks hold for every
// one: what a Config changes is how large the executions are and how likely each one is, never
// what is checked. Engineered Configs (mvccfull_test.go) make the executions behind a class of
// bugs likely; Main's reaches past mvcc's internal thresholds.
//
//   - Prefix: the files are Prefix-0.db and Prefix-1.db (the members') and Prefix-b<n>.db (the
//     n-th snapshot's), FilePaths(cfg), absent at the start.
//   - Ops: the operations in the log. Depth: the keys are the strings over a, b, c of length 1 to
//     Depth. MaxVal: values have up to MaxVal bytes (beyond the counter that makes them unique).
//   - Readers, Reads: readers on each member, and reads each. Streams: watch streams on each
//     member at a time; Watchers: watchers registered on a member's streams between two
//     restarts (fewer than 512: a restriction, mvccfull.go).
//   - BatchLimit, BatchInterval: the backend's (0: etcd's defaults). CompactionBatchLimit,
//     CompactionSleep: the store's (0, or a negative limit: etcd's defaults).
//   - Mix: the weights of the choices, and pauses.
type Config struct {
	Prefix   string
	Ops      int
	Depth    int
	MaxVal   int
	Readers  int
	Reads    int
	Streams  int
	Watchers int

	BatchLimit           int
	BatchInterval        time.Duration
	CompactionBatchLimit int
	CompactionSleep      time.Duration

	Mix Mix
}

// A Mix weighs the tester's choices. In each field, the i-th entry is the weight of the i-th
// alternative listed with the field; every alternative is possible whatever the weights (an entry
// that is missing, zero or negative counts as 0, and a field whose weights are all 0 chooses
// uniformly), so a Mix only makes some executions more likely than others. Several alternatives
// pick from a subset of another's values (a revision equal to the compaction revision is also
// "any revision"): they exist only to be weighed.
//
// Pause and RecvPause are sleeps (in the proof's model, steps that do nothing): the registering
// goroutine's after each action (with no pause, it registers its watchers at once and then spins
// on progress requests), and the receiving goroutine's after each response (a slow receiver fills
// the stream's channel, making watchers victims).
type Mix struct {
	// the writer's steps: the leader applies a new operation, the follower applies some of the
	// log, the follower installs a snapshot of the leader's, the leader restarts, the follower
	// restarts, the lessors are checked
	Step []int
	// the log's operations: put, range delete, txn, lease grant, lease revoke, compact, commit,
	// read, lessor check
	Op []int
	// a compaction's revision: any from 1 to one past the current revision, one above the
	// compaction revision, the current revision
	CompactAt []int
	// a range read's revision: 0, -1 (both: the current one), any from 0 to one past the
	// current one, the compaction revision
	RangeRev []int
	// a reader's read: Rev, FirstRev, a read transaction, a read-only transaction, the store's
	// own Range, the corruption checker's hashes
	Read []int
	// the registering goroutine's action: register a watcher, cancel one, ask one's progress, ask
	// the stream's progress, check the stream's revision, watch an empty range
	Act []int
	// a watcher's start revision: 0 (from now), any from 1 to two past the current revision, the
	// compaction revision
	Start []int

	Pause     time.Duration
	RecvPause time.Duration
}

// MainConfig is Main's Config, with the files' prefix prefix: sizes
// past mvcc's internal thresholds (mvccfull.go, "Auditing"), batch limits small enough that
// commits and compactions go by count, and a mix weighed toward the log's operations.
func MainConfig(prefix string) Config {
	return Config{Prefix: prefix, Ops: 12000, Depth: 4, MaxVal: 5000, Readers: 2, Reads: 4000,
		Streams: 2, Watchers: 64,
		BatchLimit: 3, CompactionBatchLimit: 2, CompactionSleep: time.Microsecond,
		Mix: Mix{
			Step:      []int{800, 160, 6, 3, 3, 28},
			Op:        []int{25, 12, 25, 5, 5, 10, 4, 10, 4},
			CompactAt: []int{1, 1, 0},
			RangeRev:  []int{1, 1, 2, 0},
			Read:      []int{1, 1, 2, 1, 1, 2},
			Act:       []int{4, 1, 1, 1, 1, 1},
			Start:     []int{1, 3, 0},
			Pause:     100 * time.Microsecond,
		}}
}

// normalize clamps cfg into the range the tester runs in.
func normalize(cfg Config) Config {
	if cfg.Depth < 1 {
		cfg.Depth = 1
	}
	if cfg.MaxVal < 0 {
		cfg.MaxVal = 0
	}
	if cfg.Watchers > 511 {
		cfg.Watchers = 511
	}
	return cfg
}

// choose returns any number in [0, n) (0 if n ≤ 0).
func choose(n int) int {
	if n <= 0 {
		return 0
	}
	return int(primitive.RandomUint64() % uint64(n))
}

// pick returns any alternative in [0, n), weighed by w (above).
func pick(w []int, n int) int {
	total := 0
	for i := 0; i < n && i < len(w); i++ {
		if w[i] > 0 {
			total += w[i]
		}
	}
	if total <= 0 {
		return choose(n)
	}
	r := choose(total)
	for i := 0; i < n && i < len(w); i++ {
		if w[i] > 0 {
			if r < w[i] {
				return i
			}
			r -= w[i]
		}
	}
	return n - 1
}
