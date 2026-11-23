package epaxosnet

import (
	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lib/remote"
)

// The kinds of operations.
const (
	OpPut  byte = 0
	OpGet  byte = 1
	OpScan byte = 2
)

// In is an operation: a put of V at K, a get of K, or a scan of the keys K..K+N (both ends
// included, as SwiftPaxos's SCAN).
type In struct {
	Op byte
	K  uint64
	N  uint64
	V  string
}

// Out is an operation's output: Unknown (its outcome is unknown: it may have taken effect, may
// take effect later, or never), or V: a get's value, a scan's values of the keys in its range in
// key order, concatenated ("" for a put). A key never written, or written "", has the value "".
type Out struct {
	Unknown bool
	V       string
}

// Entry is a key and its value.
type Entry struct {
	K uint64
	V string
}

// Config is one configuration the history may have reached: the store (Kv: one entry per key of
// non-empty value, in no particular order) and the puts of unknown outcome that may still take
// effect (Pend, each at most once, at any later point, or never).
type Config struct {
	Kv   []Entry
	Pend []In
}

// State is the model's state: the configurations the history may have reached (a set: no two
// equal). The model is the key-value store with scans whose puts of unknown outcome are pending
// writes; a state stands for the union of its configurations' futures.
type State []Config

// get is k's value in kv ("" if it has none).
func get(kv []Entry, k uint64) string {
	for i := 0; i < len(kv); i++ {
		if kv[i].K == k {
			return kv[i].V
		}
	}
	return ""
}

// set is kv with k's value v, in a new slice.
func set(kv []Entry, k uint64, v string) []Entry {
	r := make([]Entry, 0, len(kv)+1)
	for i := 0; i < len(kv); i++ {
		if kv[i].K != k {
			r = append(r, kv[i])
		}
	}
	if v != "" {
		r = append(r, Entry{K: k, V: v})
	}
	return r
}

// without is p without its i-th element, in a new slice.
func without(p []In, i int) []In {
	r := make([]In, 0, len(p))
	for j := 0; j < len(p); j++ {
		if j != i {
			r = append(r, p[j])
		}
	}
	return r
}

// pushIn is p with x added, in a new slice.
func pushIn(p []In, x In) []In {
	r := make([]In, len(p)+1)
	copy(r, p)
	r[len(p)] = x
	return r
}

// hasPrefix reports whether s begins with p.
func hasPrefix(s string, p string) bool {
	return len(p) <= len(s) && s[:len(p)] == p
}

// reads is every configuration reachable from c by letting pending puts on the keys k..last take
// effect (each key at most one, chosen in the order of the keys) such that the keys' values,
// concatenated, are out.
func reads(c Config, k uint64, last uint64, out string) []Config {
	if k > last {
		if out == "" {
			return []Config{c}
		}
		return nil
	}
	var r []Config
	v := get(c.Kv, k)
	if hasPrefix(out, v) {
		r = append(r, reads(c, k+1, last, out[len(v):])...)
	}
	for i := 0; i < len(c.Pend); i++ {
		p := c.Pend[i]
		if p.K == k && hasPrefix(out, p.V) {
			d := Config{Kv: set(c.Kv, k, p.V), Pend: without(c.Pend, i)}
			r = append(r, reads(d, k+1, last, out[len(p.V):])...)
		}
	}
	return r
}

// sameEntries reports whether a and b hold the same entries (as sets: keys are distinct).
func sameEntries(a []Entry, b []Entry) bool {
	if len(a) != len(b) {
		return false
	}
	for i := 0; i < len(a); i++ {
		if get(b, a[i].K) != a[i].V {
			return false
		}
	}
	return true
}

// countIn is how many times x is in p.
func countIn(p []In, x In) int {
	n := 0
	for i := 0; i < len(p); i++ {
		if p[i] == x {
			n++
		}
	}
	return n
}

// samePend reports whether a and b are the same multiset.
func samePend(a []In, b []In) bool {
	if len(a) != len(b) {
		return false
	}
	for i := 0; i < len(a); i++ {
		if countIn(a, a[i]) != countIn(b, a[i]) {
			return false
		}
	}
	return true
}

// sameConfig reports whether a and b are the same configuration.
func sameConfig(a Config, b Config) bool {
	return sameEntries(a.Kv, b.Kv) && samePend(a.Pend, b.Pend)
}

// member reports whether c is in s.
func member(s State, c Config) bool {
	for i := 0; i < len(s); i++ {
		if sameConfig(s[i], c) {
			return true
		}
	}
	return false
}

// addAll is s with the configurations of cs it lacks.
func addAll(s State, cs []Config) State {
	for i := 0; i < len(cs); i++ {
		if !member(s, cs[i]) {
			s = append(s, cs[i])
		}
	}
	return s
}

// stepConfig is the configurations c may reach by the operation in with output o.
func stepConfig(c Config, in In, o Out) []Config {
	if o.Unknown {
		if in.Op == OpPut {
			return []Config{{Kv: c.Kv, Pend: pushIn(c.Pend, in)}}
		}
		return []Config{c}
	}
	if in.Op == OpPut {
		if o.V != "" {
			return nil
		}
		return []Config{{Kv: set(c.Kv, in.K, in.V), Pend: c.Pend}}
	}
	if in.Op == OpGet {
		return reads(c, in.K, in.K, o.V)
	}
	if in.K+in.N < in.K {
		return nil
	}
	return reads(c, in.K, in.K+in.N, o.V)
}

// step is the model's step on a state: every configuration's successors; false if there are none.
func step(s State, in In, o Out) (bool, State) {
	var r State
	for i := 0; i < len(s); i++ {
		r = addAll(r, stepConfig(s[i], in, o))
	}
	return len(r) > 0, r
}

// Model is the key-value store with scans and pending writes, as a porcupine model. Inputs are
// Ins, outputs Outs.
func Model() porcupine.Model {
	return porcupine.Model{
		Init: func() any { return State{Config{}} },
		Step: func(state, input, output any) (bool, any) {
			ok, s := step(state.(State), input.(In), output.(Out))
			return ok, s
		},
		// Equal is always false (porcupine then only caches fewer states): two histories can
		// reach the same State whose exact sets of configurations differ (put a unknown, put b
		// ok vs. put b ok, put a unknown: only the first allows "a took effect before b"), so
		// the verification relates a State to its set only up to pending puts that never take
		// effect (notes/dsv-epaxos.md, the model), and equal States need not be equal sets.
		Equal: func(a, b any) bool { return false },
	}
}

func putU64(b []byte, x uint64) {
	for i := uint64(0); i < 8; i++ {
		b[i] = byte(x >> (8 * i))
	}
}

func getU64(b []byte) uint64 {
	x := uint64(0)
	for i := uint64(0); i < 8; i++ {
		x = x | uint64(b[i])<<(8*i)
	}
	return x
}

// Codec is the store's codec: an input as its kind (one byte), K and N (8 bytes little-endian
// each) and V's bytes; an output as one byte (1: unknown) and V's bytes. A get and a scan are
// reads (remote may retry them).
func Codec() remote.Codec {
	return remote.Codec{
		EncIn: func(in any) []byte {
			x := in.(In)
			b := make([]byte, 17, 17+len(x.V))
			b[0] = x.Op
			putU64(b[1:9], x.K)
			putU64(b[9:17], x.N)
			return append(b, []byte(x.V)...)
		},
		DecIn: func(b []byte) (any, bool) {
			if len(b) < 17 || b[0] > OpScan {
				return nil, false
			}
			return In{Op: b[0], K: getU64(b[1:9]), N: getU64(b[9:17]), V: string(b[17:])}, true
		},
		EncOut: func(out any) []byte {
			o := out.(Out)
			b := make([]byte, 1, 1+len(o.V))
			if o.Unknown {
				b[0] = 1
			}
			return append(b, []byte(o.V)...)
		},
		DecOut: func(b []byte) (any, bool) {
			if len(b) < 1 || b[0] > 1 {
				return nil, false
			}
			return Out{Unknown: b[0] == 1, V: string(b[1:])}, true
		},
		IsRead:    func(in any) bool { return in.(In).Op != OpPut },
		Unknown:   func(in any) any { return Out{Unknown: true} },
		IsUnknown: func(out any) bool { return out.(Out).Unknown },
	}
}
