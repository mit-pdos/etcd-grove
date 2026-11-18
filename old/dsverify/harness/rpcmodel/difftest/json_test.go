package difftest_test

// The encoding/json model's claims (harness/rpcmodel/src/encoding/json), with difftest's codec
// (codec/json_gen.go, for Msg, Body and Item): the same tests pass against real encoding/json and
// the model. Encoder: one Write per Encode of the value's encoding and a newline, and a write
// error is returned (and kept). Decoder: over a reader that returns the stream in pieces of any
// size, the values Encode wrote, then io.EOF; for broken streams, the same sequence of outcomes
// (a value, a decoding error that does not stop the stream, a syntax error, io.EOF,
// io.ErrUnexpectedEOF, the reader's error) as real encoding/json. Marshal, Unmarshal, Valid and
// RawMessage as go-vsr uses them. (Decoder reads ahead of the values it decodes in both, by
// amounts that differ; the model's doc says why every amount Go's may read the model's may.)

import (
	"bytes"
	"encoding/json"
	"errors"
	"io"
	"math/rand"
	"reflect"
	"strings"
	"testing"

	"dsverify.lab/rpcdifftest"
	"dsverify.lab/rpcdifftest/codec"
)

type countWriter struct {
	bytes.Buffer
	writes int
	fail   bool
}

func (w *countWriter) Write(p []byte) (int, error) {
	w.writes++
	if w.fail {
		return 0, errors.New("write failed")
	}
	return w.Buffer.Write(p)
}

// pieces returns the stream in pieces of random sizes, sometimes with io.EOF on the last one;
// then the error end (io.EOF if nil).
type pieces struct {
	r   *rand.Rand
	b   []byte
	end error
}

func (p *pieces) Read(q []byte) (int, error) {
	if len(p.b) == 0 {
		if p.end != nil {
			return 0, p.end
		}
		return 0, io.EOF
	}
	n := 1 + p.r.Intn(40)
	if n > len(p.b) {
		n = len(p.b)
	}
	if n > len(q) {
		n = len(q)
	}
	copy(q, p.b[:n])
	p.b = p.b[n:]
	if len(p.b) == 0 && p.end == nil && p.r.Intn(2) == 0 {
		return n, io.EOF
	}
	return n, nil
}

func rndBody(r *rand.Rand) difftest.Body {
	b := difftest.Body{N: r.Uint64() >> uint(r.Intn(64)), S: strings.Repeat("ab c", r.Intn(4)), Ok: r.Intn(2) == 0, K: uint32(r.Intn(1000))}
	if r.Intn(2) == 0 {
		for i := r.Intn(4); i > 0; i-- {
			b.L = append(b.L, difftest.Item{D: strings.Repeat("x", r.Intn(30))})
		}
	}
	return b
}

func TestJSONStream(t *testing.T) {
	codec.Register()
	r := rand.New(rand.NewSource(5))
	for it := 0; it < 300; it++ {
		var w countWriter
		enc := json.NewEncoder(&w)
		var sent []difftest.Body
		for i := r.Intn(30); i > 0; i-- {
			body := rndBody(r)
			data, err := json.Marshal(body)
			if err != nil {
				t.Fatal(err)
			}
			before, n0 := w.Len(), w.writes
			if err := enc.Encode(&difftest.Msg{Type: uint8(r.Intn(12)), Data: data}); err != nil {
				t.Fatal(err)
			}
			if w.writes != n0+1 || w.Bytes()[w.Len()-1] != '\n' || w.Len() == before {
				t.Fatalf("Encode: %d writes, %q", w.writes-n0, w.Bytes()[before:])
			}
			sent = append(sent, body)
		}
		dec := json.NewDecoder(&pieces{r: r, b: w.Bytes()})
		for i, want := range sent {
			var m difftest.Msg
			if err := dec.Decode(&m); err != nil {
				t.Fatalf("message %d: %v", i, err)
			}
			var got difftest.Body
			if err := json.Unmarshal(m.Data, &got); err != nil || !reflect.DeepEqual(got, want) {
				t.Fatalf("message %d: %#v %v, sent %#v", i, got, err, want)
			}
		}
		var m difftest.Msg
		if err := dec.Decode(&m); err != io.EOF {
			t.Fatalf("after the stream: %v", err)
		}
	}
	// a fixed encoding
	var w countWriter
	json.NewEncoder(&w).Encode(&difftest.Msg{Type: 3, Data: json.RawMessage(` { "n" : "7" , "l":[ ] } `)})
	if want := "{\"@type\":3,\"data\":{\"n\":\"7\",\"l\":[]}}\n"; w.String() != want {
		t.Fatalf("Encode: %q, want %q", w.String(), want)
	}
}

// outcome classes
func class(err error) string {
	var se *json.SyntaxError
	switch {
	case err == nil:
		return "ok"
	case err == io.EOF:
		return "eof"
	case err == io.ErrUnexpectedEOF:
		return "uneof"
	case errors.As(err, &se):
		return "syntax"
	case err.Error() == "read failed":
		return "rerr"
	}
	return "err"
}

func TestJSONStreamErrors(t *testing.T) {
	codec.Register()
	rerr := errors.New("read failed")
	for _, c := range []struct {
		in   string
		end  error
		want string
	}{
		{`{"@type":1,"data":{}}` + "\n", nil, "ok eof eof"},
		{`{"@type":1,"data":{"n":"1"}}{"@type":2}  {"@type":3}`, nil, "ok ok ok eof"},
		{`{"@type":1`, nil, "uneof uneof"},
		{"  \n\t ", nil, "eof eof"},
		{``, nil, "eof eof"},
		{`{"@type":1}x`, nil, "ok syntax syntax"},
		{`12x`, nil, "err syntax syntax"},
		{`12`, nil, "err eof"},
		{`{"@type":"1"}{"@type":2}`, nil, "err ok eof"},
		{`{"@type":1}]`, nil, "ok syntax"},
		{`[]`, nil, "err eof"},
		{`{"@type":300}`, nil, "err eof"},
		{`{"@type":-1}`, nil, "err eof"},
		{`{"@type":1.0}`, nil, "err eof"},
		{`{"@type":null,"data":null}`, nil, "ok eof"},
		{`{"@TYPE":1,"Data":[1, 2]}`, nil, "ok eof"},
		{`nul`, nil, "uneof"},
		{`nulx`, nil, "syntax"},
		{`null`, nil, "ok eof"},
		{`{"@type":1}`, rerr, "ok rerr rerr"},
		{`{"@type":1`, rerr, "rerr rerr"},
		{`{"@type":1,}`, nil, "syntax syntax"},
		{`{"@type":1}` + "\n" + `{"@type"`, rerr, "ok rerr"},
	} {
		for seed := int64(0); seed < 20; seed++ {
			dec := json.NewDecoder(&pieces{r: rand.New(rand.NewSource(seed)), b: []byte(c.in), end: c.end})
			var got []string
			for range strings.Fields(c.want) {
				var m difftest.Msg
				got = append(got, class(dec.Decode(&m)))
			}
			if g := strings.Join(got, " "); g != c.want {
				t.Fatalf("%q (seed %d): %s, want %s", c.in, seed, g, c.want)
			}
		}
	}
}

func TestJSONMarshalUnmarshal(t *testing.T) {
	codec.Register()
	var b difftest.Body
	for _, c := range []struct {
		in   string
		want string
	}{
		{`{"n":"5"}`, "ok"}, {`{"n":"5"} x`, "syntax"}, {``, "syntax"}, {` `, "syntax"},
		{`{"n":5}`, "err"}, {`{"n":"5",}`, "syntax"}, {`{"k":4294967296,"s":"z"}`, "err"},
	} {
		b = difftest.Body{S: "keep"}
		err := json.Unmarshal([]byte(c.in), &b)
		if class(err) != c.want {
			t.Errorf("Unmarshal(%q): %v (%s), want %s", c.in, err, class(err), c.want)
		}
		if c.want == "syntax" && (b.S != "keep" || b.N != 0) {
			t.Errorf("Unmarshal(%q): a syntax error changed the value: %#v", c.in, b)
		}
		if c.in == `{"k":4294967296,"s":"z"}` && b.S != "z" {
			t.Errorf("Unmarshal(%q): decoding goes on after an error: %#v", c.in, b)
		}
	}
	if err := json.Unmarshal([]byte(`{}`), (*difftest.Body)(nil)); err == nil {
		t.Errorf("Unmarshal into a nil pointer: no error")
	}
	if err := json.Unmarshal([]byte(`{}`), difftest.Body{}); err == nil {
		t.Errorf("Unmarshal into a non-pointer: no error")
	}
	if !json.Valid([]byte(` {"a":[1,2,{}]} `)) || json.Valid([]byte(`{"a"}`)) || json.Valid(nil) {
		t.Errorf("Valid")
	}
	var raw json.RawMessage
	if out, err := json.Marshal(&difftest.Msg{Type: 1, Data: raw}); err != nil || string(out) != `{"@type":1,"data":null}` {
		t.Errorf("Marshal with a nil RawMessage: %s %v", out, err)
	}
	if err := json.Unmarshal([]byte(`{"@type":2,"data": [1, 2 ] }`), &difftest.Msg{}); err != nil {
		t.Errorf("Unmarshal: %v", err)
	}
	var m difftest.Msg
	json.Unmarshal([]byte(`{"@type":2,"data": [1, 2 ] }`), &m)
	if string(m.Data) != `[1, 2 ]` {
		t.Errorf("RawMessage: %q", m.Data)
	}
	if out, _ := json.Marshal(&difftest.Msg{Type: 1, Data: m.Data}); string(out) != `{"@type":1,"data":[1,2]}` {
		t.Errorf("Marshal compacts a RawMessage: %s", out)
	}
	if _, err := json.Marshal(&difftest.Msg{Type: 1, Data: json.RawMessage(`{`)}); err == nil {
		t.Errorf("Marshal of an invalid RawMessage: no error")
	}
}

func TestJSONEncoderWriteError(t *testing.T) {
	codec.Register()
	w := &countWriter{fail: true}
	enc := json.NewEncoder(w)
	if err := enc.Encode(&difftest.Msg{Type: 1}); err == nil {
		t.Fatalf("Encode: no write error")
	}
	w.fail = false
	err := enc.Encode(&difftest.Msg{Type: 1})
	t.Logf("Encode after a write error: %v, %d writes", err, w.writes)
	if err == nil || w.writes != 1 {
		t.Fatalf("Encode after a write error: %v, %d writes (want the error kept)", err, w.writes)
	}
}
