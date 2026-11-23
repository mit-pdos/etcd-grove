package swift

import (
	"bytes"
	"encoding/binary"
	"math/rand"
	"testing"
)

// readVarint is encoding/binary.ReadVarint (the T1-style verification workaround): same values
// and same nil/non-nil errors on every prefix of encoded values and on overlong inputs.
func TestVarintCopyMatchesStdlib(t *testing.T) {
	vals := []int64{0, 1, -1, 63, -64, 64, 1 << 20, -(1 << 40), 1<<62 + 5, -1 << 63, 1<<63 - 1}
	for _, v := range vals {
		buf := binary.AppendVarint(nil, v)
		for n := 0; n <= len(buf); n++ {
			a, ea := binary.ReadVarint(bytes.NewReader(buf[:n]))
			b, eb := readVarint(bytes.NewReader(buf[:n]))
			if a != b || (ea == nil) != (eb == nil) || (ea != nil && ea.Error() != eb.Error()) {
				t.Fatalf("%d[:%d]: stdlib (%d, %v), copy (%d, %v)", v, n, a, ea, b, eb)
			}
		}
	}
	over := bytes.Repeat([]byte{0xff}, 11)
	_, ea := binary.ReadVarint(bytes.NewReader(over))
	_, eb := readVarint(bytes.NewReader(over))
	if (ea == nil) != (eb == nil) || ea.Error() != eb.Error() {
		t.Fatalf("overflow: %v vs %v", ea, eb)
	}
}

// putVarint is encoding/binary.PutVarint (verification workaround P1): same bytes and same
// length on boundary and random values.
func TestPutVarintCopy(t *testing.T) {
	vals := []int64{0, 1, -1, 63, -63, 64, -64, 1 << 62, -1 << 63, 1<<63 - 1}
	rng := rand.New(rand.NewSource(1))
	for i := 0; i < 100000; i++ {
		v := int64(rng.Uint64())
		vals = append(vals, v, v>>uint(rng.Intn(64)))
	}
	for _, v := range vals {
		a := make([]byte, binary.MaxVarintLen64)
		b := make([]byte, binary.MaxVarintLen64)
		na := binary.PutVarint(a, v)
		nb := putVarint(b, v)
		if na != nb || !bytes.Equal(a, b) {
			t.Fatalf("%d: stdlib %d %x, copy %d %x", v, na, a, nb, b)
		}
		ua := make([]byte, binary.MaxVarintLen64)
		ub := make([]byte, binary.MaxVarintLen64)
		na = binary.PutUvarint(ua, uint64(v))
		nb = putUvarint(ub, uint64(v))
		if na != nb || !bytes.Equal(ua, ub) {
			t.Fatalf("u%d: stdlib %d %x, copy %d %x", uint64(v), na, ua, nb, ub)
		}
	}
}
