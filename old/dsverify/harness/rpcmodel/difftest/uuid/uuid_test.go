package uuiddifftest

// The uuid model's claim (harness/rpcmodel/uuid): for what it implements, it is v1.3.1.
// The same tests build against the real package (go.mod) and the model (go.model.mod), and
// run.sh compares what TestSameBytes writes in each: ID, Time, Version, Variant and String of
// the same bytes, and the Variant constants. TestNew* check, in each, what New, NewRandom,
// NewString and Must guarantee: the version-4 and variant bits, the other 122 bits random (each
// seen both 0 and 1), the string form, a nil error, Must's panic.

import (
	"errors"
	"fmt"
	"math/rand"
	"os"
	"strings"
	"sync"
	"testing"

	"github.com/google/uuid"
)

// cases: edge patterns, every single bit, and seeded pseudo-random bytes.
func cases() []uuid.UUID {
	var cs []uuid.UUID
	var z, ones uuid.UUID
	for i := range ones {
		ones[i] = 0xff
	}
	cs = append(cs, z, ones)
	for b := 0; b < 128; b++ {
		var u uuid.UUID
		u[b/8] = 1 << (b % 8)
		cs = append(cs, u)
		v := ones
		v[b/8] &^= 1 << (b % 8)
		cs = append(cs, v)
	}
	r := rand.New(rand.NewSource(1))
	for i := 0; i < 2000; i++ {
		var u uuid.UUID
		r.Read(u[:])
		cs = append(cs, u)
	}
	return cs
}

// oracle: the canonical form, independently of either package.
func oracle(u uuid.UUID) string {
	return fmt.Sprintf("%x-%x-%x-%x-%x", u[0:4], u[4:6], u[6:8], u[8:10], u[10:16])
}

func TestSameBytes(t *testing.T) {
	var out strings.Builder
	fmt.Fprintf(&out, "variants %d %d %d %d %d\n", uuid.Invalid, uuid.RFC4122, uuid.Reserved,
		uuid.Microsoft, uuid.Future)
	fmt.Fprintf(&out, "nil %x\n", uuid.Nil[:])
	for _, u := range cases() {
		s := u.String()
		if s != oracle(u) {
			t.Fatalf("String(%x) = %q, want %q", u[:], s, oracle(u))
		}
		fmt.Fprintf(&out, "%x id=%d time=%d version=%d variant=%d string=%s\n", u[:], u.ID(),
			int64(u.Time()), u.Version(), u.Variant(), s)
	}
	if f := os.Getenv("UUID_DIFF_OUT"); f != "" {
		if err := os.WriteFile(f, []byte(out.String()), 0o644); err != nil {
			t.Fatal(err)
		}
	}
}

// checkV4 checks the bits New sets and records the others.
func checkV4(t *testing.T, u uuid.UUID, seen0, seen1 *[16]byte) {
	t.Helper()
	if u[6]&0xf0 != 0x40 || u[8]&0xc0 != 0x80 || u.Version() != 4 || u.Variant() != uuid.RFC4122 {
		t.Fatalf("not version 4, RFC 4122: %x", u[:])
	}
	for i := range u {
		seen1[i] |= u[i]
		seen0[i] |= ^u[i]
	}
}

func TestNew(t *testing.T) {
	var seen0, seen1 [16]byte
	for i := 0; i < 4000; i++ {
		var u uuid.UUID
		switch i % 3 {
		case 0:
			u = uuid.New()
		case 1:
			var err error
			u, err = uuid.NewRandom()
			if err != nil {
				t.Fatal(err)
			}
		case 2:
			s := uuid.NewString()
			if len(s) != 36 || s[8] != '-' || s[13] != '-' || s[18] != '-' || s[23] != '-' ||
				s[14] != '4' || !strings.ContainsRune("89ab", rune(s[19])) {
				t.Fatalf("NewString() = %q", s)
			}
			continue
		}
		if u.String() != oracle(u) {
			t.Fatalf("String(%x) = %q", u[:], u.String())
		}
		checkV4(t, u, &seen0, &seen1)
	}
	// every bit but the 6 fixed ones takes both values
	for i := range seen0 {
		fixed := byte(0)
		switch i {
		case 6:
			fixed = 0xf0
		case 8:
			fixed = 0xc0
		}
		if seen0[i]|fixed != 0xff || seen1[i]|fixed != 0xff {
			t.Errorf("byte %d: bits never 0: %08b, never 1: %08b", i, ^seen0[i]&^fixed, ^seen1[i]&^fixed)
		}
	}
}

func TestNewConcurrent(t *testing.T) {
	var wg sync.WaitGroup
	for g := 0; g < 8; g++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			var seen0, seen1 [16]byte
			for i := 0; i < 200; i++ {
				checkV4(t, uuid.New(), &seen0, &seen1)
				_ = int32(uuid.New().ID())   // SwiftPaxos's client id
				_ = int64(uuid.New().Time()) // SwiftPaxos's client buffer key
			}
		}()
	}
	wg.Wait()
}

func TestMust(t *testing.T) {
	u := uuid.UUID{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16}
	if uuid.Must(u, nil) != u {
		t.Fatal("Must(u, nil) != u")
	}
	e := errors.New("boom")
	defer func() {
		if r := recover(); r != e {
			t.Fatalf("Must(u, err) panicked with %v, want err", r)
		}
	}()
	uuid.Must(u, e)
	t.Fatal("Must(u, err) returned")
}
