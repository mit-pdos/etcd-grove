package tpdifftest_test

import (
	"bytes"
	"crypto/rand"
	"encoding/gob"
	"encoding/json"
	"errors"
	"fmt"
	mrand "math/rand"
	"testing"

	"github.com/google/uuid"
)

// The methods Go's standard library reaches through an interface (fmt's String, encoding's text and
// binary marshalers, encoding/json, encoding/gob, database/sql's Value and Scan) and what they
// call (Parse, ParseBytes), against v1.3.1: results and errors' texts to the transcript.

// uuidInputs are texts to parse: every accepted form, upper case, each form cut and with a byte
// changed, every length 0..50, and random bytes.
func uuidInputs(rng *mrand.Rand) []string {
	u := uuid.UUID{0x12, 0x3e, 0x45, 0x67, 0xe8, 0x9b, 0x12, 0xd3, 0xa4, 0x56, 0x42, 0x66, 0x14, 0x17, 0x40, 0x00}
	s := u.String()
	hex32 := fmt.Sprintf("%x", u[:])
	forms := []string{s, "urn:uuid:" + s, "URN:UUID:" + s, "{" + s + "}", hex32,
		"123E4567-E89B-12D3-A456-426614174000", "urn:uuix:" + s, "[" + s + "]"}
	var out []string
	for _, f := range forms {
		out = append(out, f, f[:len(f)-1], f+"0")
		for i := 0; i < len(f); i += 3 {
			b := []byte(f)
			b[i] = "g-0{:zZ"[rng.Intn(7)]
			out = append(out, string(b))
		}
	}
	for n := 0; n <= 50; n++ {
		b := make([]byte, n)
		for i := range b {
			b[i] = "0123456789abcdefABCDEF-{}:urnid"[rng.Intn(31)]
		}
		out = append(out, string(b))
	}
	for i := 0; i < 200; i++ {
		b := make([]byte, []int{32, 36, 38, 45}[i%4])
		rng.Read(b)
		out = append(out, string(b))
	}
	return out
}

func errText(err error) string {
	if err == nil {
		return "<nil>"
	}
	return err.Error()
}

func TestUUIDFormats(t *testing.T) {
	tr := newTranscript("uuid-formats")
	rng := mrand.New(mrand.NewSource(4))
	us := uuidEdges()[:40]
	for i := 0; i < 200; i++ {
		var u uuid.UUID
		rng.Read(u[:])
		us = append(us, u)
	}
	for _, u := range us {
		tr.printf("%x: String %s; %%v %v; %%s %s; %%q %q; %%x %x; %%+v %+v", u[:], u.String(), u, u, u, u, u)
		mt, err := u.MarshalText()
		tr.printf("  MarshalText %s %s", mt, errText(err))
		mb, err := u.MarshalBinary()
		tr.printf("  MarshalBinary %x %s", mb, errText(err))
		j, err := json.Marshal(u)
		tr.printf("  json %s %s", j, errText(err))
		j2, err := json.Marshal(struct {
			U  uuid.UUID
			P  *uuid.UUID
			M  map[uuid.UUID]int
			Ar []uuid.UUID
		}{u, &u, map[uuid.UUID]int{u: 1}, []uuid.UUID{u, {}}})
		tr.printf("  json struct %s %s", j2, errText(err))
		var back struct {
			U uuid.UUID
			P *uuid.UUID
			M map[uuid.UUID]int
		}
		tr.printf("  json back %s %v", errText(json.Unmarshal(j2, &back)), back.U == u && *back.P == u && back.M[u] == 1)
		var buf bytes.Buffer
		err = gob.NewEncoder(&buf).Encode(struct{ U uuid.UUID }{u})
		tr.printf("  gob %x %s", buf.Bytes(), errText(err))
		var gb struct{ U uuid.UUID }
		tr.printf("  gob back %s %v", errText(gob.NewDecoder(&buf).Decode(&gb)), gb.U == u)
		v, err := u.Value()
		tr.printf("  Value %v %T %s", v, v, errText(err))
	}
	for _, s := range uuidInputs(rng) {
		u, err := uuid.Parse(s)
		tr.printf("Parse %q: %x %s", s, u[:], errText(err))
		u2, err2 := uuid.ParseBytes([]byte(s))
		tr.printf("  ParseBytes %x %s", u2[:], errText(err2))
		var t1 uuid.UUID
		tr.printf("  UnmarshalText %s %x", errText(t1.UnmarshalText([]byte(s))), t1[:])
		var t2 uuid.UUID
		tr.printf("  json %s %x", errText(json.Unmarshal([]byte(fmt.Sprintf("%q", s)), &t2)), t2[:])
		var t3 uuid.UUID
		tr.printf("  UnmarshalBinary %s %x", errText(t3.UnmarshalBinary([]byte(s))), t3[:])
		var t4, t5 uuid.UUID
		tr.printf("  Scan string %s %x; bytes %s %x", errText(t4.Scan(s)), t4[:], errText(t5.Scan([]byte(s))), t5[:])
	}
	for _, src := range []interface{}{nil, "", []byte{}, 42, 1.5, []byte("0123456789abcdef"), true} {
		var u uuid.UUID
		tr.printf("Scan %T %v: %s %x", src, src, errText(u.Scan(src)), u[:])
	}
	var nilp *uuid.UUID
	tr.printf("nil *UUID: UnmarshalText %s; UnmarshalBinary %s; Scan %s; Sprint %s",
		outcome(func() { nilp.UnmarshalText([]byte("x")) }),
		outcome(func() { nilp.UnmarshalBinary(make([]byte, 16)) }),
		outcome(func() { nilp.Scan(nil) }), fmt.Sprint(nilp))
	tr.save(t)
}

type failReader struct{}

func (failReader) Read([]byte) (int, error) { return 0, errors.New("no randomness") }

// TestUUIDReplacedReader: crypto/rand.Reader assigned after uuid's initialization (outside the
// model's premise, which is that the program never assigns it): v1.3.1 read the reader at its
// initialization, so New still succeeds, as the model's does. (Assigned before, by a package
// initialized earlier, v1.3.1's New panics: run.sh's randprobe, outside the claim.)
func TestUUIDReplacedReader(t *testing.T) {
	tr := newTranscript("uuid-reader")
	old := rand.Reader
	rand.Reader = failReader{}
	defer func() { rand.Reader = old }()
	var u uuid.UUID
	var err error
	tr.printf("New: %s", outcome(func() { u = uuid.New() }))
	tr.printf("NewRandom: %s", outcome(func() { u, err = uuid.NewRandom() }))
	tr.printf("  err %s, version bits %v", errText(err), u[6]>>4 == 4 && u[8]&0xc0 == 0x80)
	tr.save(t)
}
