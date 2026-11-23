package epaxos

import (
	"bytes"
	"encoding/binary"
	"errors"
	"io"
	"math"
	"math/rand"
	"testing"
)

// The local putVarint/readVarint (varint.go) agree with encoding/binary's PutVarint/ReadVarint.

func varintInputs(rng *rand.Rand) []int64 {
	xs := []int64{0, 1, -1, 2, -2, 63, -64, 64, -65, 127, 128, -128, -129, 255, 256,
		math.MaxInt32, math.MinInt32, math.MaxInt64, math.MinInt64, math.MaxInt64 - 1, math.MinInt64 + 1}
	// every power of two and its neighbours: every encoded length 1..10
	for s := 0; s < 63; s++ {
		p := int64(1) << s
		xs = append(xs, p, p-1, p+1, -p, -p-1, -p+1)
	}
	for i := 0; i < 20000; i++ {
		xs = append(xs, rng.Int63()>>uint(rng.Intn(63))*int64(1-2*rng.Intn(2)))
		xs = append(xs, int64(rng.Uint64()))
	}
	return xs
}

func TestFixVarintPut(t *testing.T) {
	rng := rand.New(rand.NewSource(1))
	lens := map[int]bool{}
	for _, x := range varintInputs(rng) {
		var a, b [binary.MaxVarintLen64]byte
		na := putVarint(a[:], x)
		nb := binary.PutVarint(b[:], x)
		if na != nb || a != b {
			t.Fatalf("putVarint(%d) = %d %x, binary.PutVarint = %d %x", x, na, a[:na], nb, b[:nb])
		}
		lens[na] = true
	}
	for l := 1; l <= 10; l++ {
		if !lens[l] {
			t.Fatalf("no input of encoded length %d", l)
		}
	}
	// a buffer exactly as long as the encoding is enough; one byte shorter panics in both
	for _, x := range []int64{0, 300, math.MinInt64} {
		n := binary.PutVarint(make([]byte, 10), x)
		if putVarint(make([]byte, n), x) != n {
			t.Fatalf("exact buffer")
		}
		pa, pb := panics(func() { putVarint(make([]byte, n-1), x) }), panics(func() { binary.PutVarint(make([]byte, n-1), x) })
		if !pa || !pb {
			t.Fatalf("short buffer for %d: local panics %v, binary panics %v", x, pa, pb)
		}
	}
}

func panics(f func()) (p bool) {
	defer func() { p = recover() != nil }()
	f()
	return
}

type errByteReader struct {
	r   *bytes.Reader
	err error
}

func (e *errByteReader) ReadByte() (byte, error) {
	if e.r.Len() == 0 {
		return 0, e.err
	}
	return e.r.ReadByte()
}

func sameErr(a, b error) bool {
	if a == nil || b == nil {
		return a == b
	}
	if errors.Is(a, io.EOF) || errors.Is(b, io.EOF) || errors.Is(a, io.ErrUnexpectedEOF) || errors.Is(b, io.ErrUnexpectedEOF) {
		return a == b
	}
	return a.Error() == b.Error()
}

func checkRead(t *testing.T, in []byte, tail error) {
	t.Helper()
	ra := &errByteReader{bytes.NewReader(in), tail}
	rb := &errByteReader{bytes.NewReader(in), tail}
	xa, ea := readVarint(ra)
	xb, eb := binary.ReadVarint(rb)
	if xa != xb || !sameErr(ea, eb) || ra.r.Len() != rb.r.Len() {
		t.Fatalf("readVarint(%x) = %d, %v (%d left); binary.ReadVarint = %d, %v (%d left)",
			in, xa, ea, ra.r.Len(), xb, eb, rb.r.Len())
	}
}

func TestFixVarintRead(t *testing.T) {
	rng := rand.New(rand.NewSource(2))
	other := errors.New("other read error")
	for _, tail := range []error{io.EOF, other} {
		// canonical encodings, each followed by junk that must stay unread, and every truncation
		for _, x := range varintInputs(rng)[:3000] {
			var b [binary.MaxVarintLen64]byte
			n := binary.PutVarint(b[:], x)
			checkRead(t, append(b[:n:n], 0x55, 0xff), tail)
			for k := 0; k < n; k++ {
				checkRead(t, b[:k], tail) // EOF (or the other error) in the middle
			}
		}
		// non-canonical encodings (trailing zero groups) of every length 1..10
		for l := 1; l <= 10; l++ {
			in := bytes.Repeat([]byte{0x80}, l-1)
			checkRead(t, append(in, 0x00), tail)
			if l > 1 {
				checkRead(t, append(append([]byte{0x81}, in[1:]...), 0x00), tail)
			}
		}
		// overflow: the 10th byte > 1, or 10 continuation bytes; the 10th byte 0 and 1
		for last := 0; last < 256; last++ {
			checkRead(t, append(bytes.Repeat([]byte{0xff}, 9), byte(last)), tail)
			checkRead(t, append(bytes.Repeat([]byte{0x80}, 9), byte(last)), tail)
		}
		checkRead(t, bytes.Repeat([]byte{0x80}, 11), tail)
		checkRead(t, bytes.Repeat([]byte{0xff}, 20), tail)
		checkRead(t, nil, tail)
		// random byte strings, biased towards continuation bytes
		for i := 0; i < 50000; i++ {
			in := make([]byte, rng.Intn(13))
			for j := range in {
				in[j] = byte(rng.Intn(256))
				if rng.Intn(4) != 0 {
					in[j] |= 0x80
				}
			}
			checkRead(t, in, tail)
		}
	}
}

func TestFixVarintRoundTrip(t *testing.T) {
	rng := rand.New(rand.NewSource(3))
	for _, x := range varintInputs(rng) {
		var b [binary.MaxVarintLen64]byte
		n := putVarint(b[:], x)
		y, err := readVarint(bytes.NewReader(b[:n]))
		if err != nil || y != x {
			t.Fatalf("round trip %d: %d, %v", x, y, err)
		}
	}
}
