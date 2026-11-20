package pbcodec

import (
	"math/rand"
	"testing"
	"unicode/utf8"
)

// The tests against unicode/utf8 (the harness module's own build). The tests against the real
// google.golang.org/protobuf/encoding/protowire are in protowire_test.go (build tag protowire),
// which needs the real module: run them from a module that requires it,
//
//	cd harness/rpcmodel/grpcdifftest && go test -tags protowire dsverify.lab/harness/pbcodec

// TestValidUTF8Exhaustive: every byte string of length up to 3 over all bytes, and of length 4
// over a set of interesting bytes.
func TestValidUTF8Exhaustive(t *testing.T) {
	b := make([]byte, 0, 4)
	if ValidUTF8(b) != utf8.Valid(b) {
		t.Fatalf("ValidUTF8(%q)", b)
	}
	for x := 0; x < 256; x++ {
		b1 := append(b[:0], byte(x))
		if ValidUTF8(b1) != utf8.Valid(b1) {
			t.Fatalf("ValidUTF8(%q)", b1)
		}
		for y := 0; y < 256; y++ {
			b2 := append(b1[:1], byte(y))
			if ValidUTF8(b2) != utf8.Valid(b2) {
				t.Fatalf("ValidUTF8(%q)", b2)
			}
			for z := 0; z < 256; z++ {
				b3 := append(b2[:2], byte(z))
				if ValidUTF8(b3) != utf8.Valid(b3) {
					t.Fatalf("ValidUTF8(%q)", b3)
				}
			}
		}
	}
	interesting := []byte{0x00, 0x41, 0x7f, 0x80, 0x8f, 0x90, 0x9f, 0xa0, 0xbf, 0xc0, 0xc1, 0xc2,
		0xdf, 0xe0, 0xe1, 0xec, 0xed, 0xee, 0xef, 0xf0, 0xf1, 0xf3, 0xf4, 0xf5, 0xf7, 0xf8, 0xff}
	for _, x := range interesting {
		for _, y := range interesting {
			for _, z := range interesting {
				for _, w := range interesting {
					s := []byte{x, y, z, w}
					if ValidUTF8(s) != utf8.Valid(s) || ValidString(string(s)) != utf8.ValidString(string(s)) {
						t.Fatalf("ValidUTF8(%q)", s)
					}
				}
			}
		}
	}
}

// TestValidUTF8Random: random strings of encoded runes (valid and not), cut and spliced.
func TestValidUTF8Random(t *testing.T) {
	r := rand.New(rand.NewSource(1))
	for it := 0; it < 300000; it++ {
		var b []byte
		for k := r.Intn(6); k > 0; k-- {
			switch r.Intn(4) {
			case 0:
				b = append(b, byte(r.Intn(256)))
			case 1:
				b = utf8.AppendRune(b, rune(r.Intn(0x110000)))
			case 2:
				b = utf8.AppendRune(b, rune(r.Intn(0x800)))
			default:
				var c [4]byte
				n := utf8.EncodeRune(c[:], rune(0xd000+r.Intn(0x1000)))
				b = append(b, c[:r.Intn(n+1)]...)
			}
		}
		if ValidUTF8(b) != utf8.Valid(b) {
			t.Fatalf("ValidUTF8(%q) = %v", b, ValidUTF8(b))
		}
	}
}

// TestVarintRoundTrip: AppendVarint and ConsumeVarint agree, SizeVarint is the length.
func TestVarintRoundTrip(t *testing.T) {
	r := rand.New(rand.NewSource(2))
	for it := 0; it < 100000; it++ {
		v := r.Uint64() >> uint(r.Intn(64))
		b := AppendVarint(nil, v)
		if uint64(len(b)) != SizeVarint(v) {
			t.Fatalf("SizeVarint(%d)", v)
		}
		w, n, ok := ConsumeVarint(b)
		if !ok || n != uint64(len(b)) || w != v {
			t.Fatalf("ConsumeVarint(AppendVarint(%d))", v)
		}
		z := EncodeZigZag(int64(v))
		if DecodeZigZag(z) != int64(v) {
			t.Fatalf("zigzag %d", int64(v))
		}
	}
}
