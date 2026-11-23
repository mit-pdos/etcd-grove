package tpdifftest_test

import (
	"errors"
	"math/rand"
	"testing"

	"github.com/google/uuid"
)

// The uuid model (models/uuid) against uuid v1.3.1.
//
// ID and Time are deterministic: on random and edge UUIDs their results go to the transcript
// (run.sh compares the real library's with the model's) and are checked against the RFC 4122
// layout computed here. New and NewRandom are random (crypto/rand in v1.3.1, goose's
// primitive.RandomUint64 in the model): the claim is that every UUID either returns is any 16
// bytes with the version-4 and variant bits set, so both builds are checked for those bits, a nil
// error, and every other bit taking both values over the samples; the transcript records the
// verdicts.

func uuidEdges() []uuid.UUID {
	var out []uuid.UUID
	var zero, ones uuid.UUID
	for i := range ones {
		ones[i] = 0xff
	}
	out = append(out, zero, ones)
	for b := 0; b < 128; b++ {
		var u, v uuid.UUID
		u[b/8] = 0x80 >> (b % 8)
		v = ones
		v[b/8] &^= 0x80 >> (b % 8)
		out = append(out, u, v)
	}
	return out
}

func TestUUIDIDTime(t *testing.T) {
	tr := newTranscript("uuid-id-time")
	rng := rand.New(rand.NewSource(2))
	us := uuidEdges()
	for i := 0; i < 20000; i++ {
		var u uuid.UUID
		rng.Read(u[:])
		us = append(us, u)
	}
	for _, u := range us {
		id, tm := u.ID(), u.Time()
		tr.printf("%x id %d time %d", u[:], id, int64(tm))
		wantID := uint32(u[0])<<24 | uint32(u[1])<<16 | uint32(u[2])<<8 | uint32(u[3])
		wantTime := int64(wantID) | int64(uint16(u[4])<<8|uint16(u[5]))<<32 |
			int64((uint16(u[6])<<8|uint16(u[7]))&0xfff)<<48
		if id != wantID || int64(tm) != wantTime {
			t.Fatalf("%x: ID %d Time %d; want %d %d", u[:], id, tm, wantID, wantTime)
		}
	}
	t.Logf("uuid: ID and Time on %d UUIDs", len(us))
	tr.save(t)
}

func TestUUIDNew(t *testing.T) {
	tr := newTranscript("uuid-new")
	const n = 20000
	var seen0, seen1 [16]byte // bits seen 0 / seen 1, per byte
	distinct := map[uuid.UUID]bool{}
	bad := 0
	for i := 0; i < n; i++ {
		var u uuid.UUID
		switch i % 3 {
		case 0:
			u = uuid.New()
		case 1:
			var err error
			u, err = uuid.NewRandom()
			if err != nil {
				t.Fatalf("NewRandom: %v", err)
			}
		default:
			u = uuid.Must(uuid.NewRandom())
		}
		if u[6]>>4 != 4 || u[8]&0xc0 != 0x80 {
			bad++
		}
		for j := range u {
			seen1[j] |= u[j]
			seen0[j] |= ^u[j]
		}
		distinct[u] = true
	}
	tr.printf("samples %d, version-4 and variant bits wrong in %d", n, bad)
	if bad != 0 {
		t.Errorf("%d UUIDs without the version-4 and variant bits", bad)
	}
	// every bit but the 6 fixed ones takes both values
	var fixed [16]byte
	fixed[6], fixed[8] = 0xf0, 0xc0
	var stuck []int
	for j := 0; j < 16; j++ {
		for b := 0; b < 8; b++ {
			mask := byte(0x80 >> b)
			if fixed[j]&mask != 0 {
				if seen0[j]&mask != 0 && seen1[j]&mask != 0 {
					t.Errorf("fixed bit %d varies", j*8+b)
				}
				continue
			}
			if seen0[j]&mask == 0 || seen1[j]&mask == 0 {
				stuck = append(stuck, j*8+b)
			}
		}
	}
	tr.printf("free bits that never varied: %v", stuck)
	if len(stuck) != 0 {
		t.Errorf("bits that never varied: %v", stuck)
	}
	// not claimed (no uniqueness), but a check that the randomness is wired
	tr.printf("all distinct: %v", len(distinct) == n)
	tr.save(t)
}

func TestUUIDMust(t *testing.T) {
	tr := newTranscript("uuid-must")
	u := uuid.UUID{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16}
	r := uuid.Must(u, nil)
	tr.printf("must(u, nil) = %x", r[:])
	e := errors.New("boom")
	var got interface{}
	func() {
		defer func() { got = recover() }()
		uuid.Must(u, e)
	}()
	tr.printf("must(u, err) panics with err: %v", got == e)
	if got != e {
		t.Errorf("Must(u, err) panicked with %v", got)
	}
	tr.save(t)
}
