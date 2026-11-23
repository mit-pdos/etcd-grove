package state

import (
	"encoding/hex"
	"math/rand"
	"testing"
)

// hexEncodeToString (hex.go) is hex.EncodeToString.
func TestFixHexEncodeToString(t *testing.T) {
	ins := [][]byte{nil, {}, {0}, {0xff}, {0x0f, 0xf0}, []byte("v19")}
	all := make([]byte, 256)
	for i := range all {
		all[i] = byte(i)
	}
	ins = append(ins, all)
	rng := rand.New(rand.NewSource(5))
	for n := 0; n < 20000; n++ {
		b := make([]byte, rng.Intn(40))
		rng.Read(b)
		ins = append(ins, b)
	}
	for _, b := range ins {
		if got, want := hexEncodeToString(b), hex.EncodeToString(b); got != want {
			t.Fatalf("hexEncodeToString(%v) = %q, hex.EncodeToString = %q", b, got, want)
		}
	}
	// Value.String, its caller (empty values print "(void)" before the call)
	for _, v := range []Value{Value("v19"), Value(all)} {
		if got, want := v.String(), hex.EncodeToString(v); got != want {
			t.Fatalf("Value(%v).String() = %q, want %q", []byte(v), got, want)
		}
	}
}
