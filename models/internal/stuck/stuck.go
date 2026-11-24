// Package stuck is the tests' detector of the models' not-modelled convention (models/README.md,
// "Not modelled: stuck"): where a model does not model its library, it blocks forever in an empty
// `select {}`, which Go's runtime reports as the goroutine state "select (no cases)". Run tells
// that apart from a return and from a panic without a timeout: it runs f in a goroutine of its
// own, labelled, and counts the labelled goroutines parked in an empty select (the runtime's
// runtime.block) in the goroutine profile.
//
// A blocked goroutine is never released (nothing can wake an empty select): each stuck call
// leaks one, for the rest of the test binary's life. The tests that use Run make a few thousand
// such calls at most.
package stuck

import (
	"bytes"
	"context"
	"fmt"
	"runtime"
	"runtime/pprof"
	"strconv"
	"strings"
	"sync"
	"time"
)

// Outcome is how f ended.
type Outcome int

const (
	Returned Outcome = iota // f returned
	Panicked                // f panicked (the value is Run's second result)
	Stuck                   // f blocked forever in an empty select (the models' not-modelled points)
)

func (o Outcome) String() string {
	return [...]string{"returned", "panicked", "stuck"}[o]
}

// Limit bounds how long Run waits for f to return, panic or block in an empty select: a goroutine
// blocked anywhere else (a channel, a lock) past it is a test failure, which Run reports by
// panicking.
var Limit = 60 * time.Second

// blocked counts the goroutines Run started (labelled) that are parked in runtime.block (an empty
// select), from the goroutine profile (debug=1: the goroutines grouped by stack and labels, so its
// size is the number of distinct places, not of goroutines; each group's program counters, the
// runtime's frames included, follow its count).
func blocked() int {
	var b bytes.Buffer
	if err := pprof.Lookup("goroutine").WriteTo(&b, 1); err != nil {
		panic(err)
	}
	total := 0
	for _, rec := range strings.Split(b.String(), "\n\n") {
		if !strings.Contains(rec, `"models-stuck-run":"1"`) {
			continue
		}
		head := rec
		if i := strings.Index(head, " @ "); i >= 0 {
			// the group's first line (the profile's own header line may precede it)
			if j := strings.LastIndexByte(head[:i], '\n'); j >= 0 {
				head = head[j+1:]
			}
		}
		head, _, _ = strings.Cut(head, "\n")
		cnt, pcs, ok := strings.Cut(head, " @ ")
		if !ok {
			continue
		}
		n, err := strconv.Atoi(cnt)
		if err != nil {
			continue
		}
		for _, a := range strings.Fields(pcs) {
			pc, err := strconv.ParseUint(a, 0, 64)
			if err != nil {
				break
			}
			if fn := runtime.FuncForPC(uintptr(pc) - 1); fn != nil && fn.Name() == "runtime.block" {
				total += n
				break
			}
		}
	}
	return total
}

var (
	mu     sync.Mutex
	leaked int // the goroutines of Run's stuck calls, parked for good
)

// Run runs f and reports how it ended: Returned, Panicked with the panic's value, or Stuck. Calls
// of Run are serialized (the count of parked goroutines is the detector).
func Run(f func()) (Outcome, any) {
	mu.Lock()
	defer mu.Unlock()
	type end struct {
		o Outcome
		v any
	}
	done := make(chan end, 1)
	go pprof.Do(context.Background(), pprof.Labels("models-stuck-run", "1"), func(context.Context) {
		panicking := true
		defer func() {
			if panicking {
				done <- end{Panicked, recover()}
			}
		}()
		f()
		panicking = false
		done <- end{Returned, nil}
	})
	start := time.Now()
	wait := 20 * time.Microsecond
	for {
		select {
		case e := <-done:
			return e.o, e.v
		case <-time.After(wait):
		}
		if blocked() > leaked {
			leaked++
			return Stuck, nil
		}
		if time.Since(start) > Limit {
			panic(fmt.Sprintf("stuck: f neither returned, panicked nor blocked in an empty select within %v", Limit))
		}
		if wait < 10*time.Millisecond {
			wait *= 2
		}
	}
}

// IsStuck reports whether f blocked forever in an empty select; a panic of f is re-raised.
func IsStuck(f func()) bool {
	o, v := Run(f)
	if o == Panicked {
		panic(v)
	}
	return o == Stuck
}
