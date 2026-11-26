package zlrem

import (
	"math"
	"strings"
	"sync"
	"testing"

	"github.com/rs/zerolog"
)

// Rabia's shape: New(nil), a level method, field methods, Msg.
func levels(l *zerolog.Logger) []func() *zerolog.Event {
	return []func() *zerolog.Event{l.Trace, l.Debug, l.Info, l.Warn, l.Error}
}

func fields(e *zerolog.Event) *zerolog.Event {
	return e.Str("s", "\xff\x00\"").
		Int("i", math.MinInt64).Int("i2", math.MaxInt64).
		Int64("j", math.MinInt64).
		Uint32("u", math.MaxUint32).
		Bool("b", true).Bool("b2", false).
		Float64("nan", math.NaN()).Float64("pinf", math.Inf(1)).Float64("ninf", math.Inf(-1)).
		Float64("negz", math.Copysign(0, -1)).Float64("max", math.MaxFloat64).
		Float64("den", math.SmallestNonzeroFloat64).
		Float64("nanbits", math.Float64frombits(0xfff8000000000001)).
		Ints("nil", nil).Ints("empty", []int{}).Ints("one", []int{math.MinInt64}).Ints("many", []int{1, -2, 3})
}

// Every global level (int8 range: Level is int8), every level method, every field method, Msg.
func TestAllLevelsAllFields(t *testing.T) {
	l := zerolog.New(nil)
	enabled, disabled := 0, 0
	for g := -128; g <= 127; g++ {
		zerolog.SetGlobalLevel(zerolog.Level(g))
		for _, m := range levels(&l) {
			e := m()
			if e == nil {
				disabled++
			} else {
				enabled++
			}
			fields(e).Msg("msg")
			e2 := m()
			fields(e2).Msg("") // empty msg: no message key
		}
	}
	zerolog.SetGlobalLevel(zerolog.TraceLevel)
	t.Logf("no panic; enabled events %d, nil (disabled) events %d", enabled, disabled)
}

// A buffer over the pool's 64 KiB cap: Msg does not return it to the pool; nothing panics.
func TestBigBuffer(t *testing.T) {
	zerolog.SetGlobalLevel(zerolog.TraceLevel)
	l := zerolog.New(nil)
	big := strings.Repeat("x", 70000)
	ints := make([]int, 20000)
	for i := range ints {
		ints[i] = -i
	}
	for k := 0; k < 100; k++ {
		l.Info().Str("big", big).Ints("ints", ints).Float64("f", math.NaN()).Msg(big)
		l.Debug().Int("k", k).Msg("small after big")
	}
	t.Log("no panic with >64KiB buffers")
}

// Concurrent events on one logger (each event used by one goroutine), under -race.
func TestConcurrent(t *testing.T) {
	zerolog.SetGlobalLevel(zerolog.TraceLevel)
	l := zerolog.New(nil)
	var wg sync.WaitGroup
	for g := 0; g < 16; g++ {
		wg.Add(1)
		go func(g int) {
			defer wg.Done()
			for k := 0; k < 2000; k++ {
				fields(l.Warn().Int("g", g)).Msg("c")
				if k%100 == 0 {
					zerolog.SetGlobalLevel(zerolog.Level(int8(k/100%7 - 1)))
				}
			}
		}(g)
	}
	wg.Wait()
	zerolog.SetGlobalLevel(zerolog.TraceLevel)
	t.Log("no panic, concurrent")
}

// Reuse after Msg (outside the axioms: Msg consumes the token). What Go does.
func TestReuseAfterMsg(t *testing.T) {
	zerolog.SetGlobalLevel(zerolog.TraceLevel)
	l := zerolog.New(nil)
	defer func() {
		if r := recover(); r != nil {
			t.Logf("reuse after Msg panicked: %v", r)
		}
	}()
	e := l.Info().Int("a", 1)
	e.Msg("first")
	e.Int("b", 2).Float64("c", math.Inf(1)).Ints("d", nil).Msg("second") // double Msg: double putEvent
	e1 := l.Info()
	e2 := l.Info()
	t.Logf("reuse after Msg: no panic; double Put gave aliased events from the pool: %v", e1 == e2)
	e1.Int("x", 1)
	e2.Int("y", 2)
	e1.Msg("")
	e2.Msg("")
}

// Ints reads its slice with no permission in the axiom: a concurrent writer is a data race in Go,
// but []int elements are single words, so no crash (the race detector reports it; run without -race).
func TestIntsRacingWriter(t *testing.T) {
	zerolog.SetGlobalLevel(zerolog.TraceLevel)
	l := zerolog.New(nil)
	xs := make([]int, 1000)
	stop := make(chan struct{})
	done := make(chan struct{})
	go func() {
		defer close(done)
		for k := 0; ; k++ {
			select {
			case <-stop:
				return
			default:
			}
			for i := range xs {
				xs[i] = k * i
			}
		}
	}()
	for k := 0; k < 20000; k++ {
		l.Info().Ints("xs", xs).Msg("")
	}
	close(stop)
	<-done
	t.Log("no panic with a racing writer on Ints' slice")
}
