package swift

import (
	"sync"
	"testing"
)

// SWB-4: with the descriptor pool on, a retired descriptor is reused by newDesc while a commit
// handler of a dependent command may still append to its successors under successorsL (it read
// the descriptor from cmdDescs before the retirement): newDesc's reset of successors must take
// the same lock. Run with -race: before the fix the reset races with the append.
func TestIssueSWB4_SuccessorsResetUnderLock(t *testing.T) {
	if !raceOn {
		t.Skip("needs -race")
	}
	r := newTestReplica(t, 3, 1, 0, true)
	d := &commandDesc{}
	r.poolLevel = 1
	r.descPool.New = func() interface{} { return d }
	var wg sync.WaitGroup
	wg.Add(1)
	go func() { // a dependent command's commit handler
		defer wg.Done()
		for i := 0; i < 100; i++ {
			d.successorsL.Lock()
			d.successors = append(d.successors, CommandId{ClientId: 1, SeqNum: int32(i)})
			d.successorsL.Unlock()
		}
	}()
	for i := 0; i < 100; i++ {
		r.newDesc() // the pool hands out d again
	}
	wg.Wait()
}
