package state

import (
	"bytes"
	"testing"
)

// Verification workaround: Value.Unmarshal converts the uint16 length to int
// explicitly for make; values of every length class round-trip.
func TestValueRoundTrip(t *testing.T) {
	for _, n := range []int{0, 1, 255, 256, 300, 65535} {
		v := Value(bytes.Repeat([]byte{'x'}, n))
		var buf bytes.Buffer
		v.Marshal(&buf)
		var w Value
		if err := w.Unmarshal(&buf); err != nil || !bytes.Equal(w, v) || buf.Len() != 0 {
			t.Fatalf("length %d: got %d bytes, err %v, %d left", n, len(w), err, buf.Len())
		}
	}
}
