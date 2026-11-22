// Package concatlen checks that slices.Concat panics when the slices' total length reaches 2^63
// (claim #26, 2026-11-22). The trust-boundary axiom slices.Concat.wp_proof (Proof/slices/Concat.lean)
// took no premise, arguing that strings' 16 bytes each bound the total by the address space; but
// Concat sums len(s) over its arguments and panics with "len out of range" once the sum is negative
// (go1.27.3 slices/slices.go:491-498), before allocating anything (Grow(nil, size) comes after),
// and the arguments may alias one another, so the total is not bounded by memory. The fix: the
// premise (xss.map List.length).sum < 2 ^ 63, Perennial's slices.Concat.spec (mit-pdos/perennial#670),
// discharged in collectReasonsAndErrors through the decisions' nesting depth (Dec.depth).
//
// The total is the exact boundary: 2^63-1 returns, 2^63 panics (zero-size elements, aliased, no
// memory). For strings the same check is reached without unsafe given ~2^37 bytes of slice
// headers aliasing one slice (make([]string, 1<<31) passed 1<<32 times), more than this machine
// has; TestStringsOverflow reaches it with string slices whose length unsafe.Slice sets, as the
// model's points-tos may have, and TestStrings32 on a 32-bit int (GOARCH=386) with plain aliasing.
package concatlen

import (
	"strings"
	"testing"
)

func expectLenPanic(t *testing.T, f func()) {
	t.Helper()
	defer func() {
		r := recover()
		if r == nil {
			t.Fatal("slices.Concat did not panic")
		}
		if s, ok := r.(string); !ok || !strings.Contains(s, "len out of range") {
			t.Fatalf("unexpected panic: %v", r)
		}
	}()
	f()
}
