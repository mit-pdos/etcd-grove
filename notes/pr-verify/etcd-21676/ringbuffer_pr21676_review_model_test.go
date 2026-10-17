package cache

import (
	"math/rand"
	"testing"
)

// TestReviewRingBufferModel drives the PR's methods (and Append) randomly against a
// list model, with callers respecting the verified premises (Append/ReplaceLatest
// revisions above the newest / second-newest). It checks the logical contents, Len,
// PeekOldest/PeekLatest and the physical invariants after every step.
func TestReviewRingBufferModel(t *testing.T) {
	rnd := rand.New(rand.NewSource(1))
	for iter := 0; iter < 2000; iter++ {
		capacity := 1 + rnd.Intn(6)
		rb := newRingBuffer(capacity, func(x int64) int64 { return x })
		var model []int64
		cp := capacity
		next := int64(1)
		for step := 0; step < 60; step++ {
			switch rnd.Intn(5) {
			case 0, 1:
				next += int64(1 + rnd.Intn(3))
				rb.Append(next)
				if len(model) == cp {
					model = model[1:]
				}
				model = append(model, next)
			case 2:
				if len(model) == 0 {
					continue
				}
				lo := int64(-1 << 62)
				if len(model) >= 2 {
					lo = model[len(model)-2]
				}
				v := lo + 1 + int64(rnd.Intn(3))
				if v > next {
					next = v
				}
				rb.ReplaceLatest(v)
				model[len(model)-1] = v
				if v < next { // keep Append's premise: above the newest
					next = model[len(model)-1]
				}
			case 3:
				rv := next - int64(rnd.Intn(8)) + 2
				rb.RemoveLess(rv)
				var m2 []int64
				for _, x := range model {
					if x >= rv {
						m2 = append(m2, x)
					}
				}
				model = m2
			case 4:
				mc := rnd.Intn(20) - 3
				rb.ensureCapacity(mc)
				for cp < mc {
					cp *= 2
				}
			}
			if len(rb.buffer) != cp {
				t.Fatalf("iter %d step %d: cap %d want %d", iter, step, len(rb.buffer), cp)
			}
			if rb.Len() != len(model) {
				t.Fatalf("iter %d step %d: Len %d want %d", iter, step, rb.Len(), len(model))
			}
			if rb.head != (rb.tail+rb.size)%len(rb.buffer) || rb.tail < 0 || rb.tail >= len(rb.buffer) {
				t.Fatalf("iter %d step %d: bad head/tail/size %d/%d/%d cap %d", iter, step, rb.head, rb.tail, rb.size, len(rb.buffer))
			}
			var got []int64
			rb.AscendGreaterOrEqual(-1<<62, func(rev int64, x int64) bool { got = append(got, x); return true })
			if len(got) != len(model) {
				t.Fatalf("iter %d step %d: got %v want %v", iter, step, got, model)
			}
			for i := range got {
				if got[i] != model[i] {
					t.Fatalf("iter %d step %d: got %v want %v", iter, step, got, model)
				}
			}
			var wo, wl int64
			if len(model) > 0 {
				wo, wl = model[0], model[len(model)-1]
			}
			if rb.PeekOldest() != wo || rb.PeekLatest() != wl {
				t.Fatalf("iter %d step %d: peek %d/%d want %d/%d", iter, step, rb.PeekOldest(), rb.PeekLatest(), wo, wl)
			}
		}
	}
}
