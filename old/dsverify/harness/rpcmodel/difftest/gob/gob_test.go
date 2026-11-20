// The lab's model of encoding/gob (harness/rpcmodel/src/encoding/gob) against Go's, on what a
// program that sends values over a byte stream sees (SwiftPaxos's MSync: a fresh Encoder per
// value on a bufio.Writer, a fresh Decoder per value on a bufio.Reader): the values decoded, the
// reader left exactly after each value, and the errors of an empty and of a cut stream. run.sh
// runs the tests against both (the model: goroot.sh OUT gob, tag rpcmodel).
package gobdifftest

import (
	"bufio"
	"bytes"
	"encoding/gob"
	"errors"
	"io"
	"math/rand"
	"reflect"
	"testing"
)

// Msg is the test's type: an integer, a byte slice and a map (gob sends a nil map field as
// nothing, an empty one as empty).
type Msg struct {
	X int32
	S []byte
	M map[int32]int64
}

func randMsg(r *rand.Rand) Msg {
	m := Msg{X: int32(r.Uint32())}
	if r.Intn(2) == 0 {
		m.S = make([]byte, 1+r.Intn(5))
		r.Read(m.S)
	}
	switch r.Intn(3) {
	case 0:
	case 1:
		m.M = map[int32]int64{}
	default:
		m.M = map[int32]int64{int32(r.Intn(10)): r.Int63(), int32(10 + r.Intn(10)): -r.Int63()}
	}
	return m
}

// TestStream writes values with a fresh encoder each and a sentinel byte after each, and reads
// them back with a fresh decoder each: every value comes back, and every sentinel follows its
// value.
func TestStream(t *testing.T) {
	register()
	r := rand.New(rand.NewSource(1))
	for round := 0; round < 200; round++ {
		var buf bytes.Buffer
		w := bufio.NewWriter(&buf)
		var sent []Msg
		for i := 0; i < 1+r.Intn(4); i++ {
			m := randMsg(r)
			sent = append(sent, m)
			if err := gob.NewEncoder(w).Encode(&m); err != nil {
				t.Fatal(err)
			}
			w.WriteByte(byte(0xa0 + i))
		}
		w.Flush()
		rd := bufio.NewReader(&buf)
		for i, m := range sent {
			got := new(Msg)
			if err := gob.NewDecoder(rd).Decode(got); err != nil {
				t.Fatalf("round %d value %d: %v", round, i, err)
			}
			if !reflect.DeepEqual(*got, m) {
				t.Fatalf("round %d value %d: sent %#v, got %#v", round, i, m, *got)
			}
			if b, err := rd.ReadByte(); err != nil || b != byte(0xa0+i) {
				t.Fatalf("round %d value %d: the sentinel: %v %v", round, i, b, err)
			}
		}
		if _, err := rd.ReadByte(); err != io.EOF {
			t.Fatalf("round %d: bytes left", round)
		}
	}
}

// TestErrors: decoding an empty stream gives io.EOF; a stream cut inside a value gives
// io.ErrUnexpectedEOF; a write error is Encode's error.
func TestErrors(t *testing.T) {
	register()
	if err := gob.NewDecoder(bufio.NewReader(bytes.NewReader(nil))).Decode(new(Msg)); err != io.EOF {
		t.Fatalf("empty: %v", err)
	}
	var buf bytes.Buffer
	m := Msg{X: 7, S: []byte("abc"), M: map[int32]int64{1: 2}}
	if err := gob.NewEncoder(&buf).Encode(&m); err != nil {
		t.Fatal(err)
	}
	b := buf.Bytes()
	for cut := 1; cut < len(b); cut++ {
		err := gob.NewDecoder(bufio.NewReader(bytes.NewReader(b[:cut]))).Decode(new(Msg))
		if err != io.ErrUnexpectedEOF {
			t.Fatalf("cut at %d of %d: %v", cut, len(b), err)
		}
	}
	if err := gob.NewEncoder(failWriter{}).Encode(&m); err == nil {
		t.Fatal("a failed write: no error")
	}
}

type failWriter struct{}

func (failWriter) Write(p []byte) (int, error) { return 0, errors.New("broken") }
