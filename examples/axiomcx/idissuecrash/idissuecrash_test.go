package idissuecrash

import (
	"path/filepath"
	"testing"
	"time"
)

var t0 = time.Date(2026, 11, 24, 12, 0, 0, 0, time.UTC)

func panics(f func()) (p bool) {
	defer func() { p = recover() != nil }()
	f()
	return false
}

func TestTwicePanics(t *testing.T) {
	if !panics(func() { Twice(t0) }) {
		t.Fatal("expected a panic")
	}
}

func TestRestartPanicsWhenClockSame(t *testing.T) {
	p := filepath.Join(t.TempDir(), "id")
	Restart(p, t0) // first run
	// crash and reboot; the clock reads the same millisecond (RTC behind)
	if !panics(func() { Restart(p, t0) }) {
		t.Fatal("expected a panic")
	}
}

func TestRestartFineWhenClockForward(t *testing.T) {
	p := filepath.Join(t.TempDir(), "id")
	Restart(p, t0)
	if panics(func() { Restart(p, t0.Add(time.Second)) }) {
		t.Fatal("unexpected panic")
	}
}
