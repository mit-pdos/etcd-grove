// Package crc32 checks the trusted model of hash/crc32 (TrustedCode/hash/crc32.lean) against Go.
// Since 2026-11-22 (etcd-grove#14) the model is only the Castagnoli fast path's arch hooks; its one
// claim about values is archUpdateCastagnoli(crc, p) = crc32c crc p, the Lean CRC-32C. On amd64 with
// SSE4.2, Go's MakeTable(Castagnoli) and Update take exactly that hook (castagnoliSSE42), so the
// tests below check the claim through the public API. (Until 2026-11-22 the model was MakeTable and
// Update themselves, as Go's portable code.)
//
// The functions below transcribe the Lean definitions (crcBit, crcBits, crcTableEntry, crcUpdByte,
// crcUpdate) one for one; the tests compare them with Go's MakeTable and Update on the whole table,
// on the check vector whose value the Lean file proves (crc32c_check: "123456789" gives
// 0xE3069283, by kernel evaluation of the Lean definitions), and on random inputs and splits
// (Update chains: Update(Update(c, t, p), t, q) = Update(c, t, p++q), crc32c_append).
//
// Decision (the hook's docstring): outcome allowed, archUpdateCastagnoli(c, p) is the table-driven
// CRC-32C; evidence: measured (this test, go1.27.3 linux/amd64), and Go's own TestArchCastagnoli.
package crc32

import (
	"hash/crc32"
	"math/rand"
	"testing"
)

const castagnoliPoly uint32 = 0x82f63b78

// crcBit is the Lean crcBit.
func crcBit(poly, c uint32) uint32 {
	if c&1 == 1 {
		return (c >> 1) ^ poly
	}
	return c >> 1
}

// crcTableEntry is the Lean crcTableEntry (crcBits poly 8).
func crcTableEntry(poly uint32, i int) uint32 {
	c := uint32(i)
	for k := 0; k < 8; k++ {
		c = crcBit(poly, c)
	}
	return c
}

// crcUpdate is the Lean crcUpdate over crcTableOf(poly).
func crcUpdate(poly, c uint32, p []byte) uint32 {
	var tab [256]uint32
	for i := range tab {
		tab[i] = crcTableEntry(poly, i)
	}
	c = ^c
	for _, v := range p {
		c = tab[byte(c)^v] ^ (c >> 8)
	}
	return ^c
}

func TestTable(t *testing.T) {
	if crc32.Castagnoli != castagnoliPoly {
		t.Fatalf("Castagnoli = %#x", crc32.Castagnoli)
	}
	tab := crc32.MakeTable(crc32.Castagnoli)
	for i := 0; i < 256; i++ {
		if tab[i] != crcTableEntry(castagnoliPoly, i) {
			t.Fatalf("entry %d: Go %#x, model %#x", i, tab[i], crcTableEntry(castagnoliPoly, i))
		}
	}
}

func TestCheckVector(t *testing.T) {
	tab := crc32.MakeTable(crc32.Castagnoli)
	if got := crc32.Update(0, tab, []byte("123456789")); got != 0xE3069283 {
		t.Fatalf("Go: %#x", got)
	}
	if got := crcUpdate(castagnoliPoly, 0, []byte("123456789")); got != 0xE3069283 {
		t.Fatalf("model: %#x", got)
	}
	if got := crc32.Update(0x1234, tab, nil); got != 0x1234 {
		t.Fatalf("nil: %#x", got)
	}
}

func TestRandom(t *testing.T) {
	tab := crc32.MakeTable(crc32.Castagnoli)
	r := rand.New(rand.NewSource(1))
	for n := 0; n < 20000; n++ {
		p := make([]byte, r.Intn(3000))
		r.Read(p)
		c := r.Uint32()
		want := crcUpdate(castagnoliPoly, c, p)
		if got := crc32.Update(c, tab, p); got != want {
			t.Fatalf("len %d crc %#x: Go %#x, model %#x", len(p), c, got, want)
		}
		k := 0
		if len(p) > 0 {
			k = r.Intn(len(p) + 1)
		}
		if got := crc32.Update(crc32.Update(c, tab, p[:k]), tab, p[k:]); got != want {
			t.Fatalf("split %d of %d: %#x, want %#x", k, len(p), got, want)
		}
	}
}
