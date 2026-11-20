//go:build protowire

package pbcodec

// The tests against the real google.golang.org/protobuf/encoding/protowire (v1.36.12). The
// harness module does not require the real module, so these run from one that does:
//
//	cd harness/rpcmodel/grpcdifftest && go test -tags protowire dsverify.lab/harness/pbcodec

import (
	"bytes"
	"math"
	"math/rand"
	"testing"

	"google.golang.org/protobuf/encoding/protowire"
)

// rndWire: random bytes biased toward the wire format's structure: tags of every wire type,
// varints with continuation bits, lengths, overlong and maximal varints.
func rndWire(r *rand.Rand, n int) []byte {
	var b []byte
	for len(b) < n {
		switch r.Intn(9) {
		case 0:
			b = append(b, byte(r.Intn(256)))
		case 1:
			b = append(b, 0x80|byte(r.Intn(128)))
		case 2:
			b = protowire.AppendTag(b, protowire.Number(1+r.Intn(20)), protowire.Type(r.Intn(8)))
		case 3:
			b = protowire.AppendVarint(b, uint64(r.Intn(12)))
		case 4:
			b = protowire.AppendVarint(b, r.Uint64()>>uint(r.Intn(64)))
		case 5:
			b = append(b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, byte(r.Intn(4)))
		case 6:
			b = protowire.AppendTag(b, protowire.Number(r.Intn(3)), protowire.StartGroupType)
		case 7:
			b = protowire.AppendTag(b, protowire.Number(r.Intn(3)), protowire.EndGroupType)
		default:
			b = protowire.AppendVarint(b, uint64(r.Intn(1<<31))<<3|uint64(r.Intn(8)))
		}
	}
	return b[:n]
}

// someInputs: all byte strings of length up to 2, the varint-shaped strings up to 11 bytes,
// and random wire-like strings.
func someInputs(r *rand.Rand) [][]byte {
	var out [][]byte
	out = append(out, nil, []byte{})
	for x := 0; x < 256; x++ {
		out = append(out, []byte{byte(x)})
		for y := 0; y < 256; y++ {
			out = append(out, []byte{byte(x), byte(y)})
		}
	}
	for n := 1; n <= 11; n++ {
		for _, last := range []byte{0, 1, 2, 0x7f, 0x80, 0xff} {
			b := bytes.Repeat([]byte{0xff}, n)
			b[n-1] = last
			out = append(out, b, append(append([]byte{}, b...), 0x05))
			c := bytes.Repeat([]byte{0x80}, n)
			c[n-1] = last
			out = append(out, c)
		}
	}
	for it := 0; it < 200000; it++ {
		out = append(out, rndWire(r, r.Intn(24)))
	}
	return out
}

func TestAppend(t *testing.T) {
	r := rand.New(rand.NewSource(1))
	vals := []uint64{0, 1, 127, 128, 255, 16383, 16384, math.MaxUint32, math.MaxInt64, math.MaxUint64}
	for it := 0; it < 100000; it++ {
		vals = append(vals, r.Uint64()>>uint(r.Intn(64)))
	}
	for _, v := range vals {
		pre := []byte{9}
		if got, want := AppendVarint(pre, v), protowire.AppendVarint(pre, v); !bytes.Equal(got, want) {
			t.Fatalf("AppendVarint(%d) = %x, want %x", v, got, want)
		}
		if got, want := SizeVarint(v), protowire.SizeVarint(v); got != uint64(want) {
			t.Fatalf("SizeVarint(%d) = %d, want %d", v, got, want)
		}
		if got, want := AppendFixed64(pre, v), protowire.AppendFixed64(pre, v); !bytes.Equal(got, want) {
			t.Fatalf("AppendFixed64(%d)", v)
		}
		if got, want := AppendFixed32(pre, uint32(v)), protowire.AppendFixed32(pre, uint32(v)); !bytes.Equal(got, want) {
			t.Fatalf("AppendFixed32(%d)", v)
		}
		if got, want := EncodeZigZag(int64(v)), protowire.EncodeZigZag(int64(v)); got != want {
			t.Fatalf("EncodeZigZag(%d)", int64(v))
		}
		if got, want := DecodeZigZag(v), protowire.DecodeZigZag(v); got != want {
			t.Fatalf("DecodeZigZag(%d)", v)
		}
		num := 1 + v%uint64(MaxValidNumber)
		typ := v % 8
		if got, want := AppendTag(pre, num, typ), protowire.AppendTag(pre, protowire.Number(num), protowire.Type(typ)); !bytes.Equal(got, want) {
			t.Fatalf("AppendTag(%d, %d)", num, typ)
		}
		s := make([]byte, v%300)
		r.Read(s)
		if got, want := AppendBytes(pre, s), protowire.AppendBytes(pre, s); !bytes.Equal(got, want) {
			t.Fatalf("AppendBytes(len %d)", len(s))
		}
		if got, want := AppendString(pre, string(s)), protowire.AppendString(pre, string(s)); !bytes.Equal(got, want) {
			t.Fatalf("AppendString(len %d)", len(s))
		}
	}
}

func TestConsume(t *testing.T) {
	r := rand.New(rand.NewSource(2))
	for _, b := range someInputs(r) {
		v, n, ok := ConsumeVarint(b)
		wv, wn := protowire.ConsumeVarint(b)
		if ok != (wn >= 0) || (ok && (v != wv || n != uint64(wn))) {
			t.Fatalf("ConsumeVarint(%x) = %d %d %v, want %d %d", b, v, n, ok, wv, wn)
		}
		num, typ, n, ok := ConsumeTag(b)
		wnum, wtyp, wn := protowire.ConsumeTag(b)
		if ok != (wn >= 0) || (ok && (num != uint64(wnum) || typ != uint64(wtyp) || n != uint64(wn))) {
			t.Fatalf("ConsumeTag(%x) = %d %d %d %v, want %d %d %d", b, num, typ, n, ok, wnum, wtyp, wn)
		}
		// ConsumeFieldTag: protowire's ConsumeTag, then the field number at most MaxValidNumber
		num, typ, n, ok = ConsumeFieldTag(b)
		fv, fn := protowire.ConsumeVarint(b)
		fok := fn >= 0 && fv>>3 >= 1 && fv>>3 <= uint64(protowire.MaxValidNumber)
		if ok != fok || (ok && (num != fv>>3 || typ != fv&7 || n != uint64(fn))) {
			t.Fatalf("ConsumeFieldTag(%x) = %d %d %d %v", b, num, typ, n, ok)
		}
		s, n, ok := ConsumeBytes(b)
		ws, wn := protowire.ConsumeBytes(b)
		if ok != (wn >= 0) || (ok && (!bytes.Equal(s, ws) || n != uint64(wn))) {
			t.Fatalf("ConsumeBytes(%x) = %x %d %v, want %x %d", b, s, n, ok, ws, wn)
		}
		f32, n, ok := ConsumeFixed32(b)
		wf32, wn := protowire.ConsumeFixed32(b)
		if ok != (wn >= 0) || (ok && (f32 != wf32 || n != uint64(wn))) {
			t.Fatalf("ConsumeFixed32(%x)", b)
		}
		f64, n, ok := ConsumeFixed64(b)
		wf64, wn := protowire.ConsumeFixed64(b)
		if ok != (wn >= 0) || (ok && (f64 != wf64 || n != uint64(wn))) {
			t.Fatalf("ConsumeFixed64(%x)", b)
		}
		for typ := uint64(0); typ < 8; typ++ {
			for _, num := range []uint64{1, 2, 5} {
				n, ok := SkipField(num, typ, b)
				wn := protowire.ConsumeFieldValue(protowire.Number(num), protowire.Type(typ), b)
				if ok != (wn >= 0) || (ok && n != uint64(wn)) {
					t.Fatalf("SkipField(%d, %d, %x) = %d %v, want %d", num, typ, b, n, ok, wn)
				}
			}
		}
	}
}

// group returns a group of field num nested depth deep (the outermost's start tag excluded,
// as ConsumeFieldValue's input), with fields of every scalar wire type inside.
func group(num protowire.Number, depth int, inner protowire.Number) []byte {
	var b []byte
	for i := 1; i < depth; i++ {
		b = protowire.AppendTag(b, inner, protowire.StartGroupType)
	}
	b = protowire.AppendTag(b, 7, protowire.VarintType)
	b = protowire.AppendVarint(b, 300)
	b = protowire.AppendTag(b, 8, protowire.BytesType)
	b = protowire.AppendBytes(b, []byte("xy"))
	b = protowire.AppendTag(b, 9, protowire.Fixed32Type)
	b = protowire.AppendFixed32(b, 1)
	b = protowire.AppendTag(b, 10, protowire.Fixed64Type)
	b = protowire.AppendFixed64(b, 1)
	b = protowire.AppendTag(b, 1<<31-1, protowire.VarintType) // above MaxValidNumber: accepted in a group
	b = protowire.AppendVarint(b, 0)
	for i := 1; i < depth; i++ {
		b = protowire.AppendTag(b, inner, protowire.EndGroupType)
	}
	return protowire.AppendTag(b, num, protowire.EndGroupType)
}

// TestSkipGroups: nesting at and past the depth limit, mismatched and missing end tags, and
// every cut of a nested group.
func TestSkipGroups(t *testing.T) {
	check := func(num uint64, b []byte) {
		t.Helper()
		n, ok := SkipField(num, StartGroupType, b)
		wn := protowire.ConsumeFieldValue(protowire.Number(num), protowire.StartGroupType, b)
		if ok != (wn >= 0) || (ok && n != uint64(wn)) {
			t.Fatalf("SkipField(group %d, len %d) = %d %v, want %d", num, len(b), n, ok, wn)
		}
	}
	for _, d := range []int{1, 2, 3, 9999, 10000, 10001, 10002, 10003, 20000} {
		check(3, group(3, d, 4))
		check(3, group(3, d, 3))
		check(3, append(group(3, d, 4), 1, 2, 3))
		check(4, group(3, d, 4))
	}
	g := group(5, 6, 2)
	for k := 0; k <= len(g); k++ {
		check(5, g[:k])
	}
	for i := range g {
		for _, c := range []byte{0x00, 0x08, 0x0b, 0x0c, 0x13, 0x14, 0x1c, 0x1e, 0x1f, 0xff} {
			h := append([]byte{}, g...)
			h[i] = c
			check(5, h)
		}
	}
	check(1, protowire.AppendVarint(nil, uint64(1)<<34|4))
	check(1, protowire.AppendVarint(nil, 4))
	check(1, append(protowire.AppendVarint(nil, uint64(1)<<34), 0, 0x0c))
}
