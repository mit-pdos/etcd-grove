package kvreconf

import (
	"fmt"
	"sync"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/goose-lang/primitive"
	"github.com/mit-pdos/etcd-grove/examples/lintest"
)

// Input is one operation of the store as the linearizability test runs and traces it: its
// kind (opPut, opGet or opRead), key and value (unused but for a Put). Its output is a string:
// a read's value, "" for a Put.
type Input struct {
	Kind byte
	Key  string
	Val  string
}

// copyMap is a fresh map with m's contents.
func copyMap(m map[string]string) map[string]string {
	c := make(map[string]string)
	for k, v := range m {
		c[k] = v
	}
	return c
}

// within says whether every key of a has the same value in b (a key b lacks has the value "").
func within(a, b map[string]string) bool {
	for k, v := range a {
		if b[k] != v {
			return false
		}
	}
	return true
}

// hashString is the FNV-1a hash of s.
func hashString(s string) uint64 {
	h := uint64(14695981039346656037)
	for i := 0; i < len(s); i++ {
		h = (h ^ uint64(s[i])) * 1099511628211
	}
	return h
}

// hashMap is an order-independent hash of m; an entry of value "" counts for nothing, so that
// the maps Equal says are equal hash alike.
func hashMap(m map[string]string) uint64 {
	h := uint64(0)
	for k, v := range m {
		if v != "" {
			h = h ^ (hashString(k)*31 + hashString(v))
		}
	}
	return h
}

// Model is the store's sequential specification, as a porcupine model: the state is a
// map[string]string (never changed once made), a key it lacks having the value "". A Put sets
// its key's value, with output ""; a Get or a Read outputs its key's value.
func Model() porcupine.Model {
	return porcupine.Model{
		Init: func() any { return make(map[string]string) },
		Step: func(state, input, output any) (bool, any) {
			s := state.(map[string]string)
			in := input.(Input)
			out := output.(string)
			if in.Kind != opPut {
				return out == s[in.Key], s
			}
			t := copyMap(s)
			t[in.Key] = in.Val
			return out == "", t
		},
		Equal: func(a, b any) bool {
			s := a.(map[string]string)
			t := b.(map[string]string)
			return within(s, t) && within(t, s)
		},
		Hash: func(state any) uint64 {
			return hashMap(state.(map[string]string))
		},
	}
}

// Gen is the test's random traffic: a Put (one in two), a Get through the log or a Read by a
// read index (one in four each), of one of the keys "a", "b", "c", with one of the values
// "000".."999".
func Gen(id int) any {
	n := primitive.RandomUint64()
	kind := byte(opPut)
	if n%4 == 2 {
		kind = opGet
	} else if n%4 == 3 {
		kind = opRead
	}
	key := string([]byte{byte('a' + (n/4)%3)})
	v := (n / 12) % 1000
	val := string([]byte{byte('0' + v/100), byte('0' + (v/10)%10), byte('0' + v%10)})
	return Input{Kind: kind, Key: key, Val: val}
}

// Config is a test run's size and pace.
type Config struct {
	Options
	Clients     int
	Ops         int           // per client
	Reconfigs   int           // at most; the reconfigurer stops when the clients are done
	ReconfPause time.Duration // between two configuration changes
	FaultPause  time.Duration // between two faults (0: no partitions or transfers)
}

// DefaultConfig is Main's.
func DefaultConfig() Config {
	return Config{
		Options:     Options{DropOneIn: 50, PreVote: true, CheckQuorum: true},
		Clients:     4,
		Ops:         100,
		Reconfigs:   1 << 30,
		ReconfPause: 20 * time.Millisecond,
		FaultPause:  40 * time.Millisecond,
	}
}

// Run starts a cluster and runs cfg.Clients clients of cfg.Ops operations of Gen's traffic on it
// while the cluster reconfigures itself (Reconfigure) and faults are injected (Faults), traced
// with the given clock. Once the clients are done and the reconfigurer and the faults have
// stopped (the network healed), it checks the trace against Model with porcupine and that the
// members converge; it returns porcupine's answer, the error of convergence, and the cluster
// (stopped) for its statistics.
func Run(cfg Config, clock lintest.Clock) (porcupine.CheckResult, error, *Cluster) {
	c := StartCluster(cfg.Options)
	stop := make(chan struct{})
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		c.Reconfigure(cfg.Reconfigs, cfg.ReconfPause, stop)
		wg.Done()
	}()
	if cfg.FaultPause != 0 {
		wg.Add(1)
		go func() {
			c.Faults(cfg.FaultPause, stop)
			wg.Done()
		}()
	}
	apply := func(input any) any {
		in := input.(Input)
		if in.Kind == opPut {
			c.Put(in.Key, in.Val)
			return ""
		}
		if in.Kind == opGet {
			return c.Get(in.Key)
		}
		return c.Read(in.Key)
	}
	res := lintest.Run(Model(), apply, Gen, clock, cfg.Clients, cfg.Ops, 0)
	close(stop)
	wg.Wait()
	err := c.Converged(10 * time.Second)
	c.Stop()
	return res, err, c
}

// Main runs DefaultConfig's test with a counter clock; it panics unless porcupine answers Ok
// and the members converge, and unless the run took and installed snapshots, installed one at
// a configuration other than the bootstrap's, and made joint changes.
func Main() {
	res, err, c := Run(DefaultConfig(), lintest.CounterClock())
	if res != porcupine.Ok {
		panic("kvreconf: porcupine rejected the store's trace")
	}
	if err != nil {
		panic(err)
	}
	if c.Stats.SnapshotsInstalled.Load() == 0 || c.Stats.SnapshotsReconfigured.Load() == 0 || c.Stats.JointChanges.Load() == 0 {
		panic(fmt.Sprintf("kvreconf: the run did not exercise snapshots at a changed configuration: %v", &c.Stats))
	}
}
