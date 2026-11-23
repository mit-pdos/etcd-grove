package hook

import "testing"

// SWB-6: a function run by OptCondF.Call or Recall may retire the object that holds the OptCondF
// (SwiftPaxos's descriptor, returned to its sync.Pool and reinitialized by another goroutine);
// Call and Recall must not write the OptCondF after running the functions. Run with -race: before
// the fix, the final `funs_num = 0` races with the other goroutine's ReinitCondF.
func TestIssueSWB6_NoWriteAfterFunctions(t *testing.T) {
	for _, recall := range []bool{false, true} {
		cf := (*OptCondF)(nil).ReinitCondF(func() bool { return true })
		start, done := make(chan bool), make(chan bool)
		go func() { // the goroutine that reuses the retired object
			<-start
			cf.ReinitCondF(func() bool { return false })
			done <- true
		}()
		retire := func() { start <- true } // handed over: no further synchronization
		if recall {
			cf.funs = append(cf.funs, retire)
			cf.funs_num = 1
			cf.Recall()
		} else {
			cf.Call(retire)
		}
		<-done
	}
}
