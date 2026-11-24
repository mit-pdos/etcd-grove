package jsoncodec

import (
	"bytes"
	"encoding/json"
	"io"
	"math/rand"
	"strings"
	"testing"
	"unicode/utf8"

	"models.lab/internal/stuck"
)

const alpha = "{}[],:\" \n\t0123-.eE+tfrulnasx\\/bAF\xff\x7f\x01"

func rndText(r *rand.Rand, n int) []byte {
	b := make([]byte, r.Intn(n))
	for i := range b {
		b[i] = alpha[r.Intn(len(alpha))]
	}
	return b
}

// TestValid: Valid is real encoding/json's Valid on random texts over JSON's syntax.
func TestValid(t *testing.T) {
	r := rand.New(rand.NewSource(1))
	for it := 0; it < 500000; it++ {
		b := rndText(r, 14)
		if got, want := Valid(b), json.Valid(b); got != want {
			t.Fatalf("Valid(%q) = %v, real %v", b, got, want)
		}
	}
	for _, d := range []int{9999, 10000, 10001, 20000} {
		for _, s := range []string{strings.Repeat("[", d) + strings.Repeat("]", d),
			strings.Repeat(`{"a":`, d) + "1" + strings.Repeat("}", d)} {
			if got, want := Valid([]byte(s)), json.Valid([]byte(s)); got != want {
				t.Fatalf("Valid(depth %d) = %v, real %v", d, got, want)
			}
		}
	}
	for _, s := range []string{`"\u00e9\n\/"`, `"\uD800"`, `"\u12"`, `"\x"`, "\"\xc3\xa9\"", `[1`, `[`, `[[[[1]]]]`, `{"a":{"b":[true,false,null]}}`, `-0.5e+10`, `"x y"`, ` 0 `, `01`, `[1,]`, `{"a"}`, `1.`, `-`, `1e`, `[`} {
		if got, want := Valid([]byte(s)), json.Valid([]byte(s)); got != want {
			t.Fatalf("Valid(%q) = %v, real %v", s, got, want)
		}
	}
}

// TestScanStream: on a stream (then EOF), Scan(b, true) says Done exactly when real Decoder's
// first Decode succeeds, with the value it decodes; More when it reports io.EOF or
// io.ErrUnexpectedEOF; Bad on a syntax error. And Scan(b, false) on every prefix of a value is
// More, unless the prefix is a complete number or literal followed by nothing (Done needs eof
// or a following byte for a number).
func TestScanStream(t *testing.T) {
	r := rand.New(rand.NewSource(2))
	for it := 0; it < 300000; it++ {
		b := rndText(r, 16)
		var raw json.RawMessage
		err := json.NewDecoder(bytes.NewReader(b)).Decode(&raw)
		st, end := Scan(b, true)
		switch {
		case err == nil:
			if st != Done || string(bytes.TrimSpace(b[:end])) != string(raw) {
				t.Fatalf("%q: real %q, Scan %d %d", b, raw, st, end)
			}
		case err == io.EOF || err == io.ErrUnexpectedEOF:
			if st != More {
				t.Fatalf("%q: real %v, Scan %d %d", b, err, st, end)
			}
		default:
			if st != Bad {
				t.Fatalf("%q: real %v, Scan %d %d", b, err, st, end)
			}
		}
		if st == Done {
			// a prefix of a complete value without eof: More, or Done at the same value
			for cut := 0; cut < int(end); cut++ {
				s2, e2 := Scan(b[:cut], false)
				if s2 == Bad || (s2 == Done && e2 > uint64(cut)) {
					t.Fatalf("Scan(%q, false) = %d %d (the whole: %q)", b[:cut], s2, e2, b)
				}
			}
		}
	}
}

// TestEncode: the encoders' bytes are real encoding/json's.
func TestEncode(t *testing.T) {
	r := rand.New(rand.NewSource(3))
	for it := 0; it < 100000; it++ {
		x := r.Uint64() >> uint(r.Intn(64))
		w, _ := json.Marshal(x)
		if g := AppendUint(nil, x); string(g) != string(w) {
			t.Fatalf("AppendUint(%d) = %s, real %s", x, g, w)
		}
		w, _ = json.Marshal(struct {
			X uint64 `json:",string"`
		}{x})
		if g := "{\"X\":" + string(AppendQuotedUint(nil, x)) + "}"; g != string(w) {
			t.Fatalf("AppendQuotedUint(%d) = %s, real %s", x, g, w)
		}
	}
}

// TestAppendString: AppendString is real encoding/json's Marshal of a string, on every string of up
// to two bytes, every three-byte string starting at 0xe0 or above, random strings mixing ASCII,
// control bytes, '<', '>', '&', valid and invalid UTF-8, U+2028/U+2029; and seqLen is
// utf8.DecodeRuneInString's size at every byte of 0x80 or above (every lead byte against every
// second and third byte, the fourth over the bytes around its range's bounds).
func TestAppendString(t *testing.T) {
	check := func(s string) {
		w, err := json.Marshal(s)
		if err != nil {
			t.Fatalf("real Marshal(%q): %v", s, err)
		}
		if g := AppendString([]byte("x"), s); string(g) != "x"+string(w) {
			t.Fatalf("AppendString(%q) = %s, real %s", s, g[1:], w)
		}
	}
	check("")
	for a := 0; a < 256; a++ {
		check(string([]byte{byte(a)}))
		for b := 0; b < 256; b++ {
			check(string([]byte{byte(a), byte(b)}))
		}
	}
	for a := 0xe0; a < 256; a++ {
		for b := 0; b < 256; b++ {
			for c := 0; c < 256; c++ {
				check(string([]byte{byte(a), byte(b), byte(c)}))
			}
		}
	}
	pieces := []string{"a", "Z", "~", " ", "\"", "\\", "/", "<", ">", "&", "\x00", "\x1f", "\x7f", "\b",
		"\f", "\n", "\r", "\t", "\u00e9", "\u20ac", "\U0001f600", "\u2028", "\u2029", "\ufffd",
		"\xff", "\xc3", "\xe2\x80", "\xf0\x9f\x98", "\xed\xa0\x80", "\xc0\x80", "\xf4\x90\x80\x80"}
	r := rand.New(rand.NewSource(7))
	for it := 0; it < 200000; it++ {
		var sb strings.Builder
		for i := r.Intn(12); i > 0; i-- {
			sb.WriteString(pieces[r.Intn(len(pieces))])
		}
		check(sb.String())
	}
	edge := []byte{0x00, 0x7f, 0x80, 0x81, 0x8f, 0x90, 0x9f, 0xa0, 0xbf, 0xc0, 0xff}
	for a := 0x80; a < 256; a++ {
		for b := 0; b < 256; b++ {
			for c := 0; c < 256; c++ {
				for _, d := range edge {
					for _, s := range []string{string([]byte{byte(a), byte(b), byte(c), d}),
						string([]byte{byte(a), byte(b), byte(c)}), string([]byte{byte(a), byte(b)}),
						string([]byte{byte(a)})} {
						_, want := utf8.DecodeRuneInString(s)
						if got := seqLen(s, 0); got != uint64(want) {
							t.Fatalf("seqLen(%q) = %d, utf8 %d", s, got, want)
						}
					}
				}
			}
		}
	}
}

func TestEncodeInt(t *testing.T) {
	r := rand.New(rand.NewSource(4))
	for it := 0; it < 100000; it++ {
		x := int64(r.Uint64() >> uint(r.Intn(64)))
		if r.Intn(2) == 0 {
			x = -x
		}
		if it < 4 {
			x = []int64{-9223372036854775808, 9223372036854775807, 0, -1}[it]
		}
		w, _ := json.Marshal(x)
		if g := AppendInt(nil, x); string(g) != string(w) {
			t.Fatalf("AppendInt(%d) = %s, real %s", x, g, w)
		}
		w, _ = json.Marshal(struct {
			X int64 `json:",string"`
		}{x})
		if g := "{\"X\":" + string(AppendQuotedInt(nil, x)) + "}"; g != string(w) {
			t.Fatalf("AppendQuotedInt(%d) = %s, real %s", x, g, w)
		}
	}
	for _, v := range []bool{true, false} {
		w, _ := json.Marshal(v)
		if g := AppendBool(nil, v); string(g) != string(w) {
			t.Fatalf("AppendBool(%v) = %s", v, g)
		}
	}
}

type raw []byte

func (m raw) MarshalJSON() ([]byte, error) { return m, nil }

// TestCompact: AppendCompact is what real encoding/json makes of a MarshalJSON method's output.
func TestCompact(t *testing.T) {
	r := rand.New(rand.NewSource(4))
	nStuck := 0
	defer func() { t.Logf("AppendCompact: %d stuck (not modelled)", nStuck) }()
	for it := 0; it < 300000; it++ {
		b := rndText(r, 16)
		w, werr := json.Marshal(raw(b))
		var g []byte
		var ok bool
		o, pv := stuck.Run(func() { g, ok = AppendCompact([]byte("x"), b) })
		if o == stuck.Panicked {
			t.Fatalf("AppendCompact(%q) panicked: %v; real %q %v", b, pv, w, werr)
		}
		if o == stuck.Stuck {
			// outside the subset (not modelled: it blocks): a string with an escape or a non-ASCII byte
			if !bytes.ContainsAny(b, "\\\xff\x7f") || werr != nil {
				t.Fatalf("AppendCompact(%q) blocked; real %q %v", b, w, werr)
			}
			nStuck++
			continue
		}
		if (werr == nil) != ok || (ok && string(g) != "x"+string(w)) {
			t.Fatalf("AppendCompact(%q) = %q %v, real %q %v", b, g, ok, w, werr)
		}
	}
}

// TestScalars: Uint, QuotedUint, String and Bool decode as real encoding/json does into a
// struct field (set, kept, or an error that leaves it).
func TestScalars(t *testing.T) {
	vals := []string{"0", "7", "255", "256", "-0", "-1", "1.0", "1e2", "1E0", "4294967295", "4294967296",
		"18446744073709551615", "18446744073709551616", "99999999999999999999", "null", "true", "false",
		`""`, `"x"`, `"12"`, `"012"`, `"null"`, `" 1"`, `"1 "`, `"-1"`, `"256"`, `"1e2"`, `[]`, `{}`, `[1]`,
		`{"a":1}`, `"18446744073709551616"`, `"true"`, `"+1"`, `"+"`, `"-"`, `"-0"`, `"+0"`, `"-128"`, `"-129"`,
		`"127"`, `"128"`, "-128", "-129", "127", "128", `"-9223372036854775808"`, `"-9223372036854775809"`,
		"-9223372036854775808", "-9223372036854775809", "9223372036854775807", "9223372036854775808",
		`"00"`, `"-00"`, `"+-1"`, `"1_0"`, `"0x10"`, `"nul"`, `"nulll"`, `"Null"`, "-0.0", "-1e0", `"\u0037"`,
		`"\u006eull"`, `"1\n"`}
	for _, v := range vals {
		data := []byte(`{"a": ` + v + ` }`)
		pos := uint64(5)
		{
			p := struct{ A uint8 }{A: 42}
			err := json.Unmarshal(data, &p)
			x, st, k := Uint(data, pos, 255)
			check(t, "uint8", v, err, p.A == 42, uint64(p.A) == x, st, k, data)
		}
		{
			p := struct{ A uint64 }{A: 42}
			err := json.Unmarshal(data, &p)
			x, st, k := Uint(data, pos, 18446744073709551615)
			check(t, "uint64", v, err, p.A == 42, p.A == x, st, k, data)
		}
		{
			p := struct {
				A uint32 `json:",string"`
			}{A: 42}
			err := json.Unmarshal(data, &p)
			var x, st, k uint64
			if escaped(t, "uint32,string", v, err, func() { x, st, k = QuotedUint(data, pos, 4294967295) }) {
				check(t, "uint32,string", v, err, p.A == 42, uint64(p.A) == x, st, k, data)
			}
		}
		{
			p := struct {
				A uint64 `json:",string"`
			}{A: 42}
			err := json.Unmarshal(data, &p)
			var x, st, k uint64
			if escaped(t, "uint64,string", v, err, func() { x, st, k = QuotedUint(data, pos, 18446744073709551615) }) {
				check(t, "uint64,string", v, err, p.A == 42, p.A == x, st, k, data)
			}
		}
		{
			p := struct{ A int8 }{A: 42}
			err := json.Unmarshal(data, &p)
			x, st, k := Int(data, pos, 127)
			check(t, "int8", v, err, p.A == 42, int64(p.A) == x, st, k, data)
		}
		{
			p := struct{ A int64 }{A: 42}
			err := json.Unmarshal(data, &p)
			x, st, k := Int(data, pos, 9223372036854775807)
			check(t, "int64", v, err, p.A == 42, p.A == x, st, k, data)
		}
		{
			p := struct {
				A int8 `json:",string"`
			}{A: 42}
			err := json.Unmarshal(data, &p)
			var x int64
			var st, k uint64
			if escaped(t, "int8,string", v, err, func() { x, st, k = QuotedInt(data, pos, 127) }) {
				check(t, "int8,string", v, err, p.A == 42, int64(p.A) == x, st, k, data)
			}
		}
		{
			p := struct {
				A int64 `json:",string"`
			}{A: 42}
			err := json.Unmarshal(data, &p)
			var x int64
			var st, k uint64
			if escaped(t, "int64,string", v, err, func() { x, st, k = QuotedInt(data, pos, 9223372036854775807) }) {
				check(t, "int64,string", v, err, p.A == 42, p.A == x, st, k, data)
			}
		}
		{
			p := struct{ A string }{A: "q"}
			err := json.Unmarshal(data, &p)
			var x string
			var st, k uint64
			if escaped(t, "string", v, err, func() { x, st, k = String(data, pos) }) {
				check(t, "string", v, err, p.A == "q", p.A == x, st, k, data)
			}
		}
		{
			p := struct{ A bool }{A: true}
			err := json.Unmarshal(data, &p)
			x, st, k := Bool(data, pos)
			_ = x
			check(t, "bool", v, err, p.A, p.A == x, st, k, data)
		}
	}
}

// escaped runs f; it reports whether f returned. f may block (not modelled) only for a string
// holding an escape sequence (real encoding/json unescapes it first); a panic fails.
func escaped(t *testing.T, ty, v string, err error, f func()) (returned bool) {
	t.Helper()
	o, x := stuck.Run(f)
	switch {
	case o == stuck.Panicked:
		t.Errorf("%s from %s: panic %v (real: %v)", ty, v, x, err)
	case o == stuck.Stuck && !strings.Contains(v, "\\"):
		t.Errorf("%s from %s: blocked (not modelled) (real: %v)", ty, v, err)
	}
	return o == stuck.Returned
}

func check(t *testing.T, ty, v string, err error, kept, same bool, st, k uint64, data []byte) {
	t.Helper()
	ok := false
	switch {
	case err != nil:
		ok = st == TypeErr && kept
	case kept:
		ok = st == Keep || (st == Set && same)
	default:
		ok = st == Set && same
	}
	if !ok {
		t.Errorf("%s from %s: status %d, real: err %v, field kept %v, same %v", ty, v, st, err, kept, same)
	}
	if SkipSpace(data, k) != uint64(len(data)-1) {
		t.Errorf("%s from %s: end %d", ty, v, k)
	}
}

// TestFold: FoldEq is ASCII case folding (encoding/json's key match within the plain subset).
func TestFold(t *testing.T) {
	type S struct {
		A uint64 `json:"view_num"`
	}
	for _, k := range []string{"view_num", "VIEW_NUM", "View_Num", "viewnum", "view_nu", "view_numx", "vIeW_nUm"} {
		var s S
		json.Unmarshal([]byte(`{"`+k+`":5}`), &s)
		if (s.A == 5) != FoldEq(k, "view_num") {
			t.Errorf("FoldEq(%q): %v, real %v", k, FoldEq(k, "view_num"), s.A == 5)
		}
	}
}

type rawHolder struct{ R json.RawMessage }

// TestNesting: Nesting is the depth real encoding/json's encoder counts for a raw value: a raw
// value of nesting n inside d containers (its holder one of them) is written iff d+n <= MaxDepth
// (random valid texts, each at the limit and one past it).
func TestNesting(t *testing.T) {
	r := rand.New(rand.NewSource(5))
	n := 0
	for it := 0; n < 200 && it < 2000000; it++ {
		b := rndText(r, 16)
		if !Valid(b) {
			continue
		}
		n++
		k := Nesting(b)
		for _, d := range []uint64{MaxDepth - k, MaxDepth - k + 1} {
			var v any = rawHolder{json.RawMessage(b)}
			for i := uint64(1); i < d; i++ {
				v = []any{v}
			}
			_, err := json.Marshal(v)
			if (err == nil) != (d+k <= MaxDepth) {
				t.Fatalf("Nesting(%q) = %d: inside %d containers real Marshal err %v", b, k, d, err)
			}
		}
	}
	if n < 200 {
		t.Fatalf("only %d valid texts", n)
	}
}
