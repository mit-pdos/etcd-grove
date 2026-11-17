// Package timeformat checks the trust-boundary axiom time.Time.Format (Spec/time/Time__Format.lean,
// Proof/time/Time__Format.lean): t.Format(layout) returns, for every Time t and every layout,
// some string, never panicking. The WAL's cleanupWAL calls
// time.Now().Format("20060102.150405.999999") (wal.go:299).
//
// Decision (the axiom's docstring): outcome allowed, any string; excluded, a panic or no return.
// Evidence: documented (time/format.go: appendFormat handles every layout element and every Time;
// an unknown element is copied) and measured here (go1.27.3 linux/amd64): the WAL's layout and
// 200,000 random layouts (layout elements, literal text, partial elements) on times with random
// wall clocks, monotonic readings, extreme years (Unix seconds near the int64 bounds) and
// locations (UTC, Local, fixed zones of any offset, a loaded zone).
package timeformat

import (
	"math"
	"math/rand"
	"strings"
	"testing"
	"time"
)

func noPanic(t *testing.T, tm time.Time, layout string) {
	t.Helper()
	defer func() {
		if r := recover(); r != nil {
			t.Fatalf("Format(%q) of %#v panicked: %v", layout, tm, r)
		}
	}()
	_ = tm.Format(layout)
}

func TestTimeFormat(t *testing.T) {
	r := rand.New(rand.NewSource(3))
	locs := []*time.Location{time.UTC, time.Local, time.FixedZone("X", 0),
		time.FixedZone("Y", -12*3600-1), time.FixedZone("Z", 14*3600+59), time.FixedZone("", 1<<30)}
	if ny, err := time.LoadLocation("America/New_York"); err == nil {
		locs = append(locs, ny)
	}
	times := []time.Time{{}, time.Now(), time.Unix(0, 0), time.Unix(math.MaxInt64, 999999999),
		time.Unix(math.MinInt64, 0), time.Date(-1, 1, 1, 0, 0, 0, 0, time.UTC),
		time.Date(1<<40, 12, 31, 23, 59, 59, 999999999, time.UTC)}
	elems := []string{"2006", "06", "01", "1", "Jan", "January", "02", "2", "_2", "002", "__2",
		"15", "3", "03", "4", "04", "5", "05", "PM", "pm", "MST", "Z0700", "Z07:00", "-0700",
		"-07:00", "-07", "Z07", "Z070000", "-070000", "Z07:00:00", "-07:00:00", "Mon", "Monday",
		".000", ".999", ",000", ",999", ".000000000", ".999999999", ".0", ".9", ".", ",", "0",
		"9", "_", "-", ":", " ", "x", "é", "\xff", "20060102.150405.999999"}
	for _, tm := range times {
		for _, l := range locs {
			noPanic(t, tm.In(l), "20060102.150405.999999")
		}
	}
	for k := 0; k < 200000; k++ {
		var sb strings.Builder
		for n := r.Intn(10); n >= 0; n-- {
			sb.WriteString(elems[r.Intn(len(elems))])
		}
		var tm time.Time
		switch r.Intn(4) {
		case 0:
			tm = times[r.Intn(len(times))]
		case 1:
			tm = time.Unix(r.Int63()-r.Int63(), r.Int63n(1e9))
		case 2:
			tm = time.Now().Add(time.Duration(r.Int63() - r.Int63()))
		default:
			tm = time.Unix(int64(r.Uint64()), int64(r.Uint64()))
		}
		noPanic(t, tm.In(locs[r.Intn(len(locs))]), sb.String())
	}
}
