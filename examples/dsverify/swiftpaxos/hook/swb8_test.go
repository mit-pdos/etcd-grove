package hook

import "testing"

// SWB-8: with two stored functions, the first may retire the object that holds the OptCondF
// (SwiftPaxos's descriptor, returned to its sync.Pool) and another goroutine may reuse it and
// store its own functions in the same array (`cf.funs[cf.funs_num] = f`) while Call or Recall
// still reads the old functions (`funs[i]`): a data race, and the old loop may run the new
// owner's function. Run with -race: before the fix the store races with the read of funs[1].
func TestIssueSWB8_StoredFunctionsCopied(t *testing.T) {
	for _, recall := range []bool{false, true} {
		cond := false
		cf := (*OptCondF)(nil).ReinitCondF(func() bool { return cond })
		start, done := make(chan bool), make(chan bool)
		go func() { // the goroutine that reuses the retired object
			<-start
			cf.ReinitCondF(func() bool { return false })
			cf.Call(func() {})
			cf.Call(func() {})
			done <- true
		}()
		ranSecond := false
		cf.Call(func() { start <- true }) // retires the object: no further synchronization
		cf.Call(func() { ranSecond = true })
		cond = true
		if recall {
			cf.Recall()
		} else {
			cf.Call(func() {})
		}
		<-done
		if !ranSecond {
			t.Fatalf("recall=%v: the second stored function did not run", recall)
		}
	}
}
