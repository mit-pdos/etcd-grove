package httpdifftest

import (
	"bufio"
	"fmt"
	"math/rand"
	"net/http"
	"net/textproto"
	"strings"
	"testing"
)

// The model's modelReadMIMEHeader (models/net/http/textproto_model.go) quotes string(kv) where
// textproto quotes its []byte kv (MODEL, 2026-11-24, models/README.md): %q gives the same output
// for both.
func TestSprintfQBytesAsString(t *testing.T) {
	cases := [][]byte{nil, {}, []byte(`"`), []byte(`\`), []byte("\x00\x01\r\n\t\x7f"),
		[]byte("\xff\xfe"), []byte("\xc3"), []byte("\xc3\xa9"), []byte("\xe2\x80\xa8"),
		[]byte("\xef\xbf\xbd"), []byte("\xf4\x90\x80\x80"), []byte("\xed\xa0\x80"), []byte("a`b")}
	for b := 0; b < 256; b++ {
		cases = append(cases, []byte{byte(b)}, []byte{'x', byte(b), '"'})
	}
	r := rand.New(rand.NewSource(3))
	alpha := []byte("\x00\x01\x1f \"'\\`:\r\n\t\x7f\x80\xbf\xc3\xa9\xe2\xf0\xffaZ")
	for i := 0; i < 20000; i++ {
		b := make([]byte, r.Intn(12))
		for j := range b {
			if r.Intn(2) == 0 {
				b[j] = byte(r.Intn(256))
			} else {
				b[j] = alpha[r.Intn(len(alpha))]
			}
		}
		cases = append(cases, b)
	}
	for _, b := range cases {
		if q, qs := fmt.Sprintf("%q", b), fmt.Sprintf("%q", string(b)); q != qs {
			t.Fatalf("%%q of %v: []byte gives %s, string gives %s", b, q, qs)
		}
	}
}

// ReadRequest's error on a header line without a colon or with an invalid name is
// textproto's ReadMIMEHeader's (in the model build: modelReadMIMEHeader's message, against Go's
// real net/textproto).
func TestMIMEHeaderErrorMessages(t *testing.T) {
	lines := []string{
		"NoColon", "", "\"q\\uote\"", "bad\xffutf8", "ctl\x01\x7f", "\xc3\xa9", "a`b'c",
		"Na\x01me: v", "N\"m: v", "N\\m: v", "\xff: v", "N\xc3\xa9: v", "(x): v", ": empty name",
	}
	r := rand.New(rand.NewSource(4))
	alpha := []byte("\x00\x01\"'\\`\x7f\x80\xc3\xa9\xffaZ-:")
	for i := 0; i < 2000; i++ {
		b := make([]byte, 1+r.Intn(10))
		for j := range b {
			b[j] = alpha[r.Intn(len(alpha))]
		}
		lines = append(lines, string(b))
	}
	compared := 0
	for _, l := range lines {
		head := "Ok: 1\r\n" + l + "\r\n\r\n"
		_, terr := textproto.NewReader(bufio.NewReader(strings.NewReader(head))).ReadMIMEHeader()
		if terr == nil {
			continue // a valid line: not about the messages
		}
		got := try(func() string {
			_, err := http.ReadRequest(bufio.NewReader(strings.NewReader("GET / HTTP/1.1\r\n" + head)))
			return fmt.Sprint(err)
		})
		if got == "NOT MODELLED" {
			continue
		}
		compared++
		if want := terr.Error(); got != want {
			t.Errorf("line %q: ReadRequest gives %s, textproto %s", l, got, want)
		}
	}
	if compared < 1000 {
		t.Errorf("only %d error messages compared", compared)
	}
	t.Logf("%d error messages compared (model=%v)", compared, model)
}
