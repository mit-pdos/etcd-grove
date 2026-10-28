package durablekv

import (
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/goose-lang/primitive"
	"github.com/mit-pdos/etcd-grove/examples/lintest"
)

// Input is one operation of the store as the linearizability test runs and traces it: its
// kind (opPut, opGet, or else an Append), key and value (a Get's is unused), and the replica
// that runs it (an index into the cluster's voters, modulo their number). Its output is a
// string: a Get's value, "" for a Put or an Append.
type Input struct {
	Kind    byte
	Key     string
	Val     string
	Replica uint64
}

// copyMap is a fresh map with m's contents.
func copyMap(m map[string]string) map[string]string {
	c := make(map[string]string)
	for k, v := range m {
		c[k] = v
	}
	return c
}

// within says whether every key of a has the same value in b (a key b lacks has the value
// "", as for Get).
func within(a, b map[string]string) bool {
	ok := true
	for k, v := range a {
		if b[k] != v {
			ok = false
		}
	}
	return ok
}

// hashString is the FNV-1a hash of s.
func hashString(s string) uint64 {
	h := uint64(14695981039346656037)
	for i := 0; i < len(s); i++ {
		h = (h ^ uint64(s[i])) * 1099511628211
	}
	return h
}

// hashMap is an order-independent hash of m (the XOR of its entries' hashes); an entry of
// value "" counts for nothing, so that the maps Equal says are equal hash alike.
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
// map[string]string (never changed once made: a step that changes it makes a copy), a key
// it lacks having the value "". A Put sets its key's value, an Append appends to it, both
// with output ""; a Get outputs its key's value. It is that of a new cluster: the check runs
// on an empty directory.
func Model() porcupine.Model {
	return porcupine.Model{
		Init: func() any { return make(map[string]string) },
		Step: func(state, input, output any) (bool, any) {
			s := state.(map[string]string)
			in := input.(Input)
			out := output.(string)
			if in.Kind == opGet {
				return out == s[in.Key], s
			}
			t := copyMap(s)
			if in.Kind == opPut {
				t[in.Key] = in.Val
			} else {
				t[in.Key] = s[in.Key] + in.Val
			}
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

// Gen is the test's random traffic: each operation a Put, a Get or an Append (one in three
// each) of one of the keys "a", "b", "c", with one of the values "000".."999", on a random
// replica.
func Gen(id int) any {
	n := primitive.RandomUint64()
	kind := byte(opAppend)
	if n%3 == 0 {
		kind = opPut
	} else if n%3 == 1 {
		kind = opGet
	}
	key := string([]byte{byte('a' + (n/3)%3)})
	v := (n / 9) % 1000
	val := string([]byte{byte('0' + v/100), byte('0' + (v/10)%10), byte('0' + v%10)})
	return Input{Kind: kind, Key: key, Val: val, Replica: n / 9000}
}

// crasher restarts a random replica of c every period (none if period is 0) until stop is
// closed, then closes done.
func crasher(c *Cluster, period time.Duration, stop chan struct{}, done chan struct{}) {
	for period != 0 {
		select {
		case <-stop:
			close(done)
			return
		case <-time.After(period):
			c.Restart(c.voters[primitive.RandomUint64()%uint64(len(c.voters))])
		}
	}
	<-stop
	close(done)
}

// Check runs clients clients of the cluster c, each running ops operations of Gen's random
// traffic on it, traced with the given clock, while a random replica crashes and restarts every
// period (never if period is 0), and checks the trace against Model with porcupine (no
// timeout). The cluster must be new (an empty directory).
func Check(c *Cluster, clock lintest.Clock, clients int, ops int, period time.Duration) porcupine.CheckResult {
	apply := func(input any) any {
		in := input.(Input)
		id := c.voters[in.Replica%uint64(len(c.voters))]
		if in.Kind == opGet {
			return c.Get(id, in.Key)
		}
		if in.Kind == opPut {
			c.Put(id, in.Key, in.Val)
		} else {
			c.Append(id, in.Key, in.Val)
		}
		return ""
	}
	stop := make(chan struct{})
	done := make(chan struct{})
	go crasher(c, period, stop, done)
	r := lintest.Run(Model(), apply, Gen, clock, clients, ops, 0)
	close(stop)
	<-done
	return r
}

// Main starts a cluster of three replicas on the directory dir, which must exist and be
// empty, and runs a randomized linearizability test of the store on it: 4 clients of 25
// operations each, on random replicas, while a random replica crashes and restarts every 50ms,
// traced with a counter clock and checked by porcupine; it panics unless porcupine answers Ok.
func Main(dir string) {
	c := StartCluster(dir, []uint64{1, 2, 3})
	if Check(c, lintest.CounterClock(), 4, 25, 50*time.Millisecond) != porcupine.Ok {
		panic("durablekv: porcupine rejected the store's trace")
	}
	c.Stop()
}
