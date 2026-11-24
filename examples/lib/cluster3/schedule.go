package cluster3

import (
	"time"

	"github.com/goose-lang/primitive"
)

// below is a random number in [0, n) (n > 0).
func below(n uint64) uint64 { return primitive.RandomUint64() % n }

// RandomSchedule is a schedule of n random steps (none if n <= 0): each after a delay below a
// second, of a random kind on random members among the three (an out-of-range or equal pair does
// nothing, as Step says). The program draws its own fault schedule, so the theorem about it is
// about every schedule this can produce, with no premise on a schedule it is given.
func RandomSchedule(n int) []Step {
	var sched []Step
	for i := 0; i < n; i++ {
		sched = append(sched, Step{Delay: time.Duration(below(uint64(time.Second))),
			Kind: int(below(5)), A: int(below(3)), B: int(below(3))})
	}
	return sched
}
