package quepaxanet

import (
	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lib/remote"
)

// In is a key-value operation: Get(K) (Put false) or Put(K, V).
type In struct {
	Put bool
	K   string
	V   string
}

// Out is an operation's output: Unknown (its outcome is unknown), or a get's {Found, V} (V is ""
// when not found), or a put's zero Out.
type Out struct {
	Unknown bool
	Found   bool
	V       string
}

// Entry is one key's state in the model: the key's known state (Found, V: the last answered put's
// value, or the value an answered get saw; nothing known yet: Found false, V ""), and the values of
// the puts of unknown outcome on the key, Old (made pending before the known state was learned) and
// New (made pending after). Each pending put may still take effect, once, or never. It stands for
// the configurations in which either the key's state is the known one, every New put still pending
// and any of the Old ones taken effect before (which the known state then overwrote); or some
// pending put x took effect last (the key's value is x's) and any of the others before it.
type Entry struct {
	K     string
	Found bool
	V     string
	Old   []string
	New   []string
}

// State is the model's state: an entry per key touched (in the order first touched; a key without
// an entry is not found, nothing pending).
type State []Entry

// push is p with v added, in a new slice (states are never written).
func push(p []string, v string) []string {
	q := make([]string, len(p)+1)
	copy(q, p)
	q[len(p)] = v
	return q
}

// has reports whether v is in p.
func has(p []string, v string) bool {
	for i := 0; i < len(p); i++ {
		if p[i] == v {
			return true
		}
	}
	return false
}

// cat is p followed by q, in a new slice.
func cat(p []string, q []string) []string {
	r := make([]string, len(p)+len(q))
	copy(r, p)
	copy(r[len(p):], q)
	return r
}

// erase is p without its first v, in a new slice.
func erase(p []string, v string) []string {
	q := make([]string, 0, len(p))
	found := false
	for i := 0; i < len(p); i++ {
		if !found && p[i] == v {
			found = true
		} else {
			q = append(q, p[i])
		}
	}
	return q
}

// lookup is key k's entry in s (its index, or len(s) and the empty entry).
func lookup(s State, k string) (int, Entry) {
	for i := 0; i < len(s); i++ {
		if s[i].K == k {
			return i, s[i]
		}
	}
	return len(s), Entry{K: k}
}

// set is s with key e.K's entry at index i (len(s): a new one) e, in a new slice.
func set(s State, i int, e Entry) State {
	n := len(s)
	if i == n {
		n++
	}
	t := make(State, n)
	copy(t, s)
	t[i] = e
	return t
}

// stepE is the model's step on one key's entry: a put of unknown outcome is pending (New), a get of
// unknown outcome changes nothing; an answered put makes its value the key's known state, every
// pending put Old; an answered get that saw the known state changes nothing, one that saw a pending
// put's value V makes it the known state (that put took effect last), the other pending puts Old.
func stepE(e Entry, in In, o Out) (bool, Entry) {
	if o.Unknown {
		if in.Put {
			return true, Entry{K: e.K, Found: e.Found, V: e.V, Old: e.Old, New: push(e.New, in.V)}
		}
		return true, e
	}
	if in.Put {
		if o.Found || o.V != "" {
			return false, e
		}
		return true, Entry{K: e.K, Found: true, V: in.V, Old: cat(e.Old, e.New), New: nil}
	}
	if o.Found == e.Found && o.V == e.V {
		return true, e
	}
	all := cat(e.Old, e.New)
	if o.Found && has(all, o.V) {
		return true, Entry{K: e.K, Found: true, V: o.V, Old: erase(all, o.V), New: nil}
	}
	return false, e
}

// step is the model's step: stepE on the input's key.
func step(s State, in In, o Out) (bool, State) {
	i, e := lookup(s, in.K)
	ok, e2 := stepE(e, in, o)
	if !ok {
		return false, s
	}
	return true, set(s, i, e2)
}

// equalS reports whether two lists of values are the same.
func equalS(a []string, b []string) bool {
	if len(a) != len(b) {
		return false
	}
	for i := 0; i < len(a); i++ {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

// equalE reports whether two entries are the same (as values: the same pending lists).
func equalE(a Entry, b Entry) bool {
	return a.K == b.K && a.Found == b.Found && a.V == b.V && equalS(a.Old, b.Old) &&
		equalS(a.New, b.New)
}

// equal reports whether a and b are the same state (as values).
func equal(a State, b State) bool {
	if len(a) != len(b) {
		return false
	}
	for i := 0; i < len(a); i++ {
		if !equalE(a[i], b[i]) {
			return false
		}
	}
	return true
}

// Model is the key-value map with pending puts (linkv's pending-writes model of the map: a put is
// a write, a get a read), as a porcupine model (no partition: the verified porcupine checks the
// history whole). Inputs are Ins, outputs Outs.
func Model() porcupine.Model {
	return porcupine.Model{
		Init: func() any { return State{} },
		Step: func(state, input, output any) (bool, any) {
			ok, s := step(state.(State), input.(In), output.(Out))
			return ok, s
		},
		Equal: func(a, b any) bool { return equal(a.(State), b.(State)) },
	}
}

// appendStr is b with s appended: its length (8 bytes, little-endian), then its bytes.
func appendStr(b []byte, s string) []byte {
	for i := uint64(0); i < 8; i++ {
		b = append(b, byte(uint64(len(s))>>(8*i)))
	}
	return append(b, []byte(s)...)
}

// takeStr is the string at the front of b (appendStr's encoding) and the rest of b.
func takeStr(b []byte) (string, []byte, bool) {
	if len(b) < 8 {
		return "", nil, false
	}
	n := uint64(0)
	for i := uint64(0); i < 8; i++ {
		n = n | (uint64(b[i]) << (8 * i))
	}
	if n > uint64(len(b)-8) {
		return "", nil, false
	}
	return string(b[8 : 8+n]), b[8+n:], true
}

// flag is a boolean's byte.
func flag(x bool) byte {
	if x {
		return 1
	}
	return 0
}

// EncIn is in's encoding: Put (one byte), then K and V (appendStr).
func EncIn(in In) []byte {
	b := []byte{flag(in.Put)}
	b = appendStr(b, in.K)
	return appendStr(b, in.V)
}

// DecIn decodes EncIn's encoding.
func DecIn(b []byte) (In, bool) {
	if len(b) < 1 || b[0] > 1 {
		return In{}, false
	}
	k, r, ok := takeStr(b[1:])
	if !ok {
		return In{}, false
	}
	v, r2, ok2 := takeStr(r)
	if !ok2 || len(r2) != 0 {
		return In{}, false
	}
	return In{Put: b[0] == 1, K: k, V: v}, true
}

// EncOut is o's encoding: Unknown and Found (a byte each), then V's bytes.
func EncOut(o Out) []byte {
	b := []byte{flag(o.Unknown), flag(o.Found)}
	return append(b, []byte(o.V)...)
}

// DecOut decodes EncOut's encoding.
func DecOut(b []byte) (Out, bool) {
	if len(b) < 2 || b[0] > 1 || b[1] > 1 {
		return Out{}, false
	}
	return Out{Unknown: b[0] == 1, Found: b[1] == 1, V: string(b[2:])}, true
}

// Codec is the map's codec (EncIn/DecIn, EncOut/DecOut); a get is a read; the unknown output is
// Out{Unknown: true}.
func Codec() remote.Codec {
	return remote.Codec{
		EncIn: func(in any) []byte { return EncIn(in.(In)) },
		DecIn: func(b []byte) (any, bool) {
			in, ok := DecIn(b)
			return in, ok
		},
		EncOut: func(out any) []byte { return EncOut(out.(Out)) },
		DecOut: func(b []byte) (any, bool) {
			o, ok := DecOut(b)
			return o, ok
		},
		IsRead:    func(in any) bool { return !in.(In).Put },
		Unknown:   func(in any) any { return Out{Unknown: true} },
		IsUnknown: func(out any) bool { return out.(Out).Unknown },
	}
}
