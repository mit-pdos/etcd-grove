package wait

import (
	"math/rand"
	"sync"
	"testing"
)

// Random model check: compare timeList against a reference model, including
// Trigger with deadlines that go down, duplicate Waits, and Pending.
func TestReviewModel(t *testing.T) {
	for seed := int64(0); seed < 2000; seed++ {
		r := rand.New(rand.NewSource(seed))
		tl := NewTimeList()
		last := uint64(0)
		pending := map[uint64]<-chan struct{}{}
		released := []<-chan struct{}{}
		for step := 0; step < 300; step++ {
			switch r.Intn(3) {
			case 0, 1:
				d := uint64(r.Intn(60))
				ch := tl.Wait(d)
				if d <= last {
					select {
					case <-ch:
					default:
						t.Fatalf("seed %d: Wait(%d) <= last %d not closed", seed, d, last)
					}
					continue
				}
				if old, ok := pending[d]; ok && old != ch {
					t.Fatalf("seed %d: duplicate deadline got new chan", seed)
				}
				pending[d] = ch
			case 2:
				d := uint64(r.Intn(60))
				tl.Trigger(d)
				last = d
				for k, ch := range pending {
					if k <= d {
						released = append(released, ch)
						delete(pending, k)
					}
				}
			}
			for _, ch := range released {
				select {
				case <-ch:
				default:
					t.Fatalf("seed %d: released chan not closed", seed)
				}
			}
			for k, ch := range pending {
				select {
				case <-ch:
					t.Fatalf("seed %d: pending %d closed early", seed, k)
				default:
				}
			}
			if tl.Pending() != len(pending) || len(tl.h) != len(tl.m) {
				t.Fatalf("seed %d: Pending %d heap %d map %d model %d", seed, tl.Pending(), len(tl.h), len(tl.m), len(pending))
			}
		}
	}
}

func TestReviewConcurrent(t *testing.T) {
	tl := NewTimeList()
	var wg sync.WaitGroup
	for g := 0; g < 8; g++ {
		wg.Add(1)
		go func(g int) {
			defer wg.Done()
			r := rand.New(rand.NewSource(int64(g)))
			for i := 0; i < 20000; i++ {
				switch r.Intn(3) {
				case 0:
					tl.Trigger(uint64(r.Intn(5000)))
				case 1:
					_ = tl.Pending()
				default:
					tl.Wait(uint64(r.Intn(5000)))
				}
			}
		}(g)
	}
	wg.Wait()
	tl.Trigger(^uint64(0))
	if tl.Pending() != 0 || len(tl.h) != 0 {
		t.Fatalf("leftover %d %d", tl.Pending(), len(tl.h))
	}
	// Wait(max uint64) after Trigger(max) must be closed
	select {
	case <-tl.Wait(^uint64(0)):
	default:
		t.Fatal("not closed")
	}
}
