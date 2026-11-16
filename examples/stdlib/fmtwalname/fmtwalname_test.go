// Package fmtwalname checks the trust-boundary axioms fmt.SprintfWalName and fmt.SscanfWalName
// (Spec/fmt/{SprintfWalName,SscanfWalName}.lean, Proof/fmt/{SprintfWalName,SscanfWalName}.lean)
// against Go: the WAL's walName (util.go:117, fmt.Sprintf("%016x-%016x.wal", seq, index)) and
// parseWALName (util.go:112, fmt.Sscanf(str, "%016x-%016x.wal", &seq, &index)).
//
// The functions below transcribe the Lean definitions of Proof/fmt/WalName.lean one for one
// (hexPad, walNameStr, isHexByte, hexDigitVal, hexValue, mayBeSpace, scanHex16, scanWalName).
//
// Decisions (the axioms' docstrings) and evidence, measured here (go1.27.3 linux/amd64):
//   - SprintfWalName: the result is walNameStr(seq, index), each number its lowercase hexadecimal
//     zero-padded to 16 digits (TestSprintfWalName: edge values and 100,000 random pairs).
//   - SscanfWalName: where scanWalName gives ok(a, b), Sscanf returns a nil error and stores a and
//     b; where it gives err, Sscanf returns a non-nil error; where it gives unknown (a byte at which
//     Go skips spaces), nothing is claimed (TestSscanfWalName: the model's own examples, and
//     200,000 random strings over an alphabet of hex digits of both cases, '-', '.', "wal", other
//     letters, spaces and a non-ASCII space; outcome allowed, the model's; excluded, any other).
package fmtwalname

import (
	"fmt"
	"math"
	"math/rand"
	"strings"
	"testing"
)

// hexPad is the Lean fmt.hexPad: n's last w hexadecimal digits, lowercase.
func hexPad(w int, n uint64) string {
	if w == 0 {
		return ""
	}
	return hexPad(w-1, n/16) + string("0123456789abcdef"[n%16])
}

// walNameStr is the Lean fmt.walNameStr.
func walNameStr(s, i uint64) string {
	return hexPad(16, s) + "-" + hexPad(16, i) + ".wal"
}

func TestSprintfWalName(t *testing.T) {
	r := rand.New(rand.NewSource(1))
	vals := []uint64{0, 1, 15, 16, 255, math.MaxUint32, math.MaxUint64 - 1, math.MaxUint64}
	check := func(s, i uint64) {
		got := fmt.Sprintf("%016x-%016x.wal", s, i)
		if want := walNameStr(s, i); got != want {
			t.Fatalf("Sprintf(%d, %d) = %q, model %q", s, i, got, want)
		}
	}
	for _, s := range vals {
		for _, i := range vals {
			check(s, i)
		}
	}
	for k := 0; k < 100000; k++ {
		// Random magnitudes: a random number of significant bits.
		s := r.Uint64() >> uint(r.Intn(65)%64)
		i := r.Uint64() >> uint(r.Intn(65)%64)
		check(s, i)
	}
}

type scanRes int

const (
	resOk scanRes = iota
	resErr
	resUnknown
)

// isHexByte is the Lean fmt.isHexByte.
func isHexByte(b byte) bool {
	return ('0' <= b && b <= '9') || ('A' <= b && b <= 'F') || ('a' <= b && b <= 'f')
}

// hexDigitVal is the Lean fmt.hexDigitVal.
func hexDigitVal(b byte) uint64 {
	if b <= '9' {
		return uint64(b - '0')
	}
	if b <= 'F' {
		return uint64(b - 'A' + 10)
	}
	return uint64(b - 'a' + 10)
}

// mayBeSpace is the Lean fmt.mayBeSpace.
func mayBeSpace(b byte) bool {
	return (9 <= b && b <= 13) || b == 32 || 128 <= b
}

// scanHex16 is the Lean fmt.scanHex16: the value of the run of hex digits at the start of s and
// the rest, or ok = false if the run is empty or longer than 16. (The Lean value is a natural
// number below 16^16, then cut to 64 bits by W64: the same here.)
func scanHex16(s string) (uint64, string, bool) {
	n := 0
	for n < len(s) && isHexByte(s[n]) {
		n++
	}
	if n == 0 || n > 16 {
		return 0, "", false
	}
	var v uint64
	for k := 0; k < n; k++ {
		v = v*16 + hexDigitVal(s[k])
	}
	return v, s[n:], true
}

// scanWalName is the Lean fmt.scanWalName.
func scanWalName(s string) (scanRes, uint64, uint64) {
	if len(s) > 0 && mayBeSpace(s[0]) {
		return resUnknown, 0, 0
	}
	a, s1, ok := scanHex16(s)
	if !ok || len(s1) == 0 || s1[0] != '-' {
		return resErr, 0, 0
	}
	s2 := s1[1:]
	if len(s2) > 0 && mayBeSpace(s2[0]) {
		return resUnknown, 0, 0
	}
	c, s3, ok := scanHex16(s2)
	if !ok {
		return resErr, 0, 0
	}
	if strings.HasPrefix(s3, ".wal") {
		return resOk, a, c
	}
	return resErr, 0, 0
}

func checkScan(t *testing.T, s string) scanRes {
	var seq, index uint64
	_, err := fmt.Sscanf(s, "%016x-%016x.wal", &seq, &index)
	res, a, b := scanWalName(s)
	switch res {
	case resOk:
		if err != nil || seq != a || index != b {
			t.Fatalf("Sscanf(%q) = (%x, %x, %v), model ok(%x, %x)", s, seq, index, err, a, b)
		}
	case resErr:
		if err == nil {
			t.Fatalf("Sscanf(%q) = (%x, %x, nil), model err", s, seq, index)
		}
	}
	return res
}

func TestSscanfWalName(t *testing.T) {
	// The model's examples (Proof/fmt/WalName.lean) and the header's cases.
	for _, c := range []struct {
		s    string
		want scanRes
	}{
		{"1-2.wal", resOk}, {"A-b.wal.tmp", resOk}, {"0-0.tmp", resErr},
		{"00000000000000000-0.wal", resErr}, {" 0-0.wal", resUnknown}, {"0- 0.wal", resUnknown},
		{"0-0.walx", resOk}, {"0-0.wal.wal", resOk}, {"0x1-2.wal", resErr}, {"", resErr},
		{"-1.wal", resErr}, {"1-.wal", resErr}, {"g-0.wal", resErr}, {"1-2.wa", resErr},
		{walNameStr(math.MaxUint64, 0), resOk}, {walNameStr(12345, 678), resOk},
	} {
		if got := checkScan(t, c.s); got != c.want {
			t.Fatalf("scanWalName(%q) = %v, want %v", c.s, got, c.want)
		}
	}
	r := rand.New(rand.NewSource(2))
	pieces := []string{"0", "1", "9", "a", "f", "A", "F", "g", "x", "-", ".", "wal", ".wal", "w",
		"l", " ", "\t", "\n", " ", "ffffffffffffffff", "0000000000000000", "+", "_"}
	counts := map[scanRes]int{}
	for k := 0; k < 200000; k++ {
		var sb strings.Builder
		for n := r.Intn(8); n >= 0; n-- {
			sb.WriteString(pieces[r.Intn(len(pieces))])
		}
		counts[checkScan(t, sb.String())]++
	}
	if counts[resOk] == 0 || counts[resErr] == 0 {
		t.Fatalf("random inputs reach too few outcomes: %v", counts)
	}
}
