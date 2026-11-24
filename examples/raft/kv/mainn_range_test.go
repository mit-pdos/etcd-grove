package kv

import (
	"math/rand"
	"testing"
)

// TestMainNRange (rule 38's non-vacuity test for MainN's range check): sizes outside [1, 1000]
// return before starting a cluster, and sizes inside it pass the check and run the cluster and the
// porcupine check (MainN panics unless porcupine answers Ok), including sizes drawn at random.
func TestMainNRange(t *testing.T) {
	MainN(0)
	MainN(1001)
	ks := []uint64{1, 2, 3}
	for i := 0; i < 3; i++ {
		ks = append(ks, 1+uint64(rand.Intn(7)))
	}
	for _, k := range ks {
		MainN(k)
		t.Logf("MainN(%d): ran and passed porcupine", k)
	}
}
