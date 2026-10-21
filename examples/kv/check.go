package kv

import (
	"github.com/anishathalye/porcupine"
	"github.com/goose-lang/primitive"
	"github.com/mit-pdos/etcd-grove/examples/lintest"
)

// Input is one operation of the store as the linearizability test runs and traces it: its
// kind (opPut, opGet, or else an Append), key and value (a Get's is unused), and the
// replica that runs it (an index into the cluster's replicas, modulo their number). Its
// output is a string: a Get's value, "" for a Put or an Append.
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
// with output ""; a Get outputs its key's value.
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
// each) of one of the keys "a", "b", "c", with one of the values "000".."999" (few
// repeated values: porcupine's search slows down when a read could have seen several
// writes), on a random replica.
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

// Check runs clients clients of the replicas kvs, each running ops operations of Gen's
// random traffic on them, traced with the given clock, and checks the trace against Model
// with porcupine (no timeout).
func Check(kvs []*KV, clock lintest.Clock, clients int, ops int) porcupine.CheckResult {
	apply := func(input any) any {
		in := input.(Input)
		r := kvs[in.Replica%uint64(len(kvs))]
		if in.Kind == opGet {
			return r.Get(in.Key)
		}
		if in.Kind == opPut {
			r.Put(in.Key, in.Val)
		} else {
			r.Append(in.Key, in.Val)
		}
		return ""
	}
	return lintest.Run(Model(), apply, Gen, clock, clients, ops, 0)
}

// Main starts a cluster of three replicas connected in process and runs a randomized
// linearizability test of the store on it: 4 clients of 25 operations each, on random
// replicas, traced with a counter clock and checked by porcupine; it panics unless
// porcupine answers Ok.
func Main() {
	kvs := StartCluster([]uint64{1, 2, 3})
	if Check(kvs, lintest.CounterClock(), 4, 25) != porcupine.Ok {
		panic("kv: porcupine rejected the store's trace")
	}
}

// MainWitness is Main on a cluster of two regular voters and a witness (StartClusterWitness:
// voters 1 and 2, the witness 3, which runs no replica): 4 clients of 25 operations each, on
// random replicas, traced with a counter clock and checked by porcupine; it panics unless
// porcupine answers Ok. Nothing changes the cluster's configuration.
func MainWitness() {
	kvs := StartClusterWitness([]uint64{1, 2}, 3)
	if Check(kvs, lintest.CounterClock(), 4, 25) != porcupine.Ok {
		panic("kv: porcupine rejected the store's trace")
	}
}
