// A copy of models/internal/stuck/stuck.go (the tests' detector of a model's not-modelled point,
// an empty select), its names prefixed with stuck: this module does not require models.lab.

package tpdifftest_test

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

// stuckOutcome is how f ended.
type stuckOutcome int

const (
	stuckReturned stuckOutcome = iota // f returned
	stuckPanicked                // f panicked (the value is Run's second result)
	stuckStuck                   // f blocked forever in an empty select (the models' not-modelled points)
)

func (o stuckOutcome) String() string {
	return [...]string{"returned", "panicked", "stuck"}[o]
}

// stuckLimit bounds how long Run waits for f to return, panic or block in an empty select: a goroutine
// blocked anywhere else (a channel, a lock) past it is a test failure, which Run reports by
// panicking.
var stuckLimit = 60 * time.Second

// blocked counts the goroutines Run started (labelled) that are parked in runtime.block (an empty
// select), from the goroutine profile (debug=1: the goroutines grouped by stack and labels, so its
// size is the number of distinct places, not of goroutines; each group's program counters, the
// runtime's frames included, follow its count).
func stuckBlocked() int {
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
	stuckMu     sync.Mutex
	stuckLeaked int // the goroutines of Run's stuck calls, parked for good
)

// Run runs f and reports how it ended: stuckReturned, stuckPanicked with the panic's value, or Stuck. Calls
// of Run are serialized (the count of parked goroutines is the detector).
func stuckRun(f func()) (stuckOutcome, any) {
	stuckMu.Lock()
	defer stuckMu.Unlock()
	type end struct {
		o stuckOutcome
		v any
	}
	done := make(chan end, 1)
	go pprof.Do(context.Background(), pprof.Labels("models-stuck-run", "1"), func(context.Context) {
		panicking := true
		defer func() {
			if panicking {
				done <- end{stuckPanicked, recover()}
			}
		}()
		f()
		panicking = false
		done <- end{stuckReturned, nil}
	})
	start := time.Now()
	wait := 20 * time.Microsecond
	for {
		select {
		case e := <-done:
			return e.o, e.v
		case <-time.After(wait):
		}
		if stuckBlocked() > stuckLeaked {
			stuckLeaked++
			return stuckStuck, nil
		}
		if time.Since(start) > stuckLimit {
			panic(fmt.Sprintf("stuck: f neither returned, panicked nor blocked in an empty select within %v", stuckLimit))
		}
		if wait < 10*time.Millisecond {
			wait *= 2
		}
	}
}

// stuckIsStuck reports whether f blocked forever in an empty select; a panic of f is re-raised.
func stuckIsStuck(f func()) bool {
	o, v := stuckRun(f)
	if o == stuckPanicked {
		panic(v)
	}
	return o == stuckStuck
}
