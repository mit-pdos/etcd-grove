package semantics

import (
	"time"

	"go.etcd.io/etcd/pkg/v3/idutil"
)

// issue runs n Nexts of g and returns the ids.
func issue(g *idutil.Generator, n int) []uint64 {
	ids := make([]uint64, n)
	for i := range ids {
		ids[i] = g.Next()
	}
	return ids
}

// common returns the ids of a that b has too.
func common(a, b []uint64) []uint64 {
	in := map[uint64]bool{}
	for _, x := range b {
		in[x] = true
	}
	var c []uint64
	for _, x := range a {
		if in[x] {
			c = append(c, x)
		}
	}
	return c
}

// t0 is a fixed wall-clock time (the tests choose the clock).
var t0 = time.Date(2026, 11, 24, 12, 0, 0, 0, time.UTC)
