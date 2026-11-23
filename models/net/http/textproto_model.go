// MODEL: this file is the model's own (not in Go's net/http).
//
// Package http here is a model of Go 1.27.3's net/http (models/README.md): Go's code, but for the
// parts this file and the places marked MODEL replace. The claim (trusted): every behavior of Go's
// net/http, as the program observes it, is a behavior of this model; where the model does not
// model Go's behavior it panics ("net/http model: ..."), so that a proof that the program does not
// panic shows it never gets there. What is replaced:
//
//   - The HTTP/1.x message head parser (Go's net/textproto Reader: ReadLine and readMIMEHeader, as
//     ReadRequest, the server's request reading and ReadResponse call them) is this file's
//     modelReadLine and modelReadMIMEHeader, which return what textproto's return on the heads they
//     accept, and panic on the others: a header continuation line (obsolete line folding) and a
//     header line whose name holds a space (Go accepts it, uncanonicalized). On a malformed line
//     they return textproto's error (a textproto.ProtocolError with its message).
//   - url.ParseRequestURI, which readRequest calls on a request's URI, is modelParseRequestURI:
//     Go's result computed here on a path of the bytes modelPathByte accepts, Go's function on
//     every other URI (Perennial translates strings.Cut, ToLower and Index, which net/url's parse
//     calls, as names only).
//   - httpguts.HeaderValuesContainsToken, which shouldClose calls on a head's Connection values, is
//     modelHeaderValuesContainsToken: the same code with strings.IndexByte (which Perennial
//     translates as a name only) as modelIndexByte, and tokenEqual's range over a string's runes as
//     one over its bytes.
//   - Chunked message bodies (transfer.go: a request or response with Transfer-Encoding chunked)
//     are not modelled: reading one panics. Content-Length bodies, bodies to the end of the
//     connection, and no body are Go's code.
//   - TLS and HTTP/2 serving (server.go, conn.serve: a connection that is a TLS connection, and
//     unencrypted HTTP/2 when the Server enables it) are not modelled: serving one panics.
//   - The client's Transport (transport.go, roundTrip) is not modelled: a round trip panics. (The
//     Client's own code, redirects and cookies, is Go's.)
//
// Everything else is Go's code: the server's connection loop (conn.serve, the background read that
// cancels a request's context when the client goes, keep-alive, Hijack, the 400/431/501 answers),
// the response writer (buffering, Content-Length or chunked framing, Content-Type sniffing, Date),
// ServeMux and its patterns, the handlers (Error, Redirect, StripPrefix, TimeoutHandler,
// MaxBytesHandler, FileServer), Header, Cookie, Request and Response and their Write methods, the
// Server's Serve, Shutdown and Close.

package http

import (
	"bufio"
	"errors"
	"fmt"
	"io"
	"net/textproto"
	"net/url"

	"golang.org/x/net/http/httpguts"
)

// notModelled is the value the model panics with where it does not model Go's behavior. The
// server's recovery of a handler's panic (conn.serve) panics again with any value that has a
// NotModelled method (this one, net/rpc's model's, the generated codecs'), so that it stops the
// program instead of closing one connection.
type notModelled string

// NotModelled marks the value as the models' panic.
func (notModelled) NotModelled() {}

// modelReadLine is textproto's (*Reader).ReadLine over b: the next line, without its "\n" or
// "\r\n"; at the end of the input, the bytes before it (without error) if there are any, else
// the read error (bufio's ReadLine, which textproto's readLineSlice calls).
func modelReadLine(b *bufio.Reader) (string, error) {
	var line []byte
	for {
		c, err := b.ReadByte()
		if err != nil {
			if len(line) > 0 {
				return string(line), nil
			}
			return "", err
		}
		if c == '\n' {
			if len(line) > 0 && line[len(line)-1] == '\r' {
				line = line[:len(line)-1]
			}
			return string(line), nil
		}
		line = append(line, c)
	}
}

// trimLine is textproto's trim (reader.go): the line without leading and trailing spaces and
// tabs.
func trimLine(s []byte) []byte {
	i := 0
	for i < len(s) && (s[i] == ' ' || s[i] == '	') {
		i++
	}
	n := len(s)
	for n > i && (s[n-1] == ' ' || s[n-1] == '	') {
		n--
	}
	return s[i:n]
}

// errMessageTooLarge is textproto's (its message is what net/http tests for).
var errMessageTooLarge = errors.New("message too large")

// modelReadMIMEHeader is textproto's readMIMEHeader(r, math.MaxInt64, maxHeaders) over b, on the
// heads without continuation lines: header lines up to an empty line, each "Name: value" (the
// name canonicalized, the value without the space around it), at most maxHeaders of them.
func modelReadMIMEHeader(b *bufio.Reader, maxHeaders int64) (textproto.MIMEHeader, error) {
	m := make(textproto.MIMEHeader)
	// The first line cannot start with a leading space (textproto quotes up to 80 bytes of it).
	if buf, err := b.Peek(1); err == nil && (buf[0] == ' ' || buf[0] == '\t') {
		panic(notModelled("net/http model: a header block starting with a space is not modelled"))
	}
	for {
		s, err := modelReadLine(b)
		if err != nil {
			return m, err
		}
		if len(s) == 0 {
			return m, nil
		}
		kv := []byte(s)
		// textproto's mustHaveFieldNameColon, on the line as read
		colon := -1
		for i := 0; i < len(kv); i++ {
			if kv[i] == ':' {
				colon = i
				break
			}
		}
		if colon < 0 {
			return nil, textproto.ProtocolError(fmt.Sprintf("malformed MIME header: missing colon: %q", kv))
		}
		// a continuation line follows (obsolete line folding): not modelled
		if next, err := b.Peek(1); err == nil && (next[0] == ' ' || next[0] == '\t') {
			panic(notModelled("net/http model: a header continuation line is not modelled"))
		}
		kv = trimLine(kv)
		colon = -1
		for i := 0; i < len(kv); i++ {
			if kv[i] == ':' {
				colon = i
				break
			}
		}
		k, v := kv[:colon], kv[colon+1:]
		for _, c := range k {
			if c == ' ' {
				panic(notModelled("net/http model: a header name holding a space is not modelled"))
			}
		}
		if !httpguts.ValidHeaderFieldName(string(k)) {
			return m, textproto.ProtocolError(fmt.Sprintf("malformed MIME header line: %q", kv))
		}
		key := textproto.CanonicalMIMEHeaderKey(string(k))
		if !httpguts.ValidHeaderFieldValue(string(v)) {
			// (textproto canonicalizes the name in the line it quotes)
			return m, textproto.ProtocolError(fmt.Sprintf("malformed MIME header line: %q", key+string(kv[colon:])))
		}
		maxHeaders--
		if maxHeaders < 0 {
			return nil, errMessageTooLarge
		}
		// Skip initial spaces in value.
		i := 0
		for i < len(v) && (v[i] == ' ' || v[i] == '\t') {
			i++
		}
		m[key] = append(m[key], string(v[i:]))
	}
}

// modelCutByte is strings.Cut(s, string(sep)) for a byte sep (the model's ReadResponse and
// parseRequestLine call it in place of strings.Cut, which Perennial translates as a name only:
// notes/perennial-changes.md): the text before and after the first sep, and true; or s, "" and
// false when s holds none. strings.Cut finds the first instance with strings.Index, which for a
// one-byte separator is the first index of that byte.
func modelCutByte(s string, sep byte) (before, after string, found bool) {
	for i := 0; i < len(s); i++ {
		if s[i] == sep {
			return s[:i], s[i+1:], true
		}
	}
	return s, "", false
}

// modelTrimLeftByte is strings.TrimLeft(s, string(c)) for an ASCII byte c (the model's ReadResponse
// calls it in place of strings.TrimLeft, a name only in Perennial's translation): Go's TrimLeft of a
// one-byte ASCII cutset is strings' trimLeftByte, this loop.
func modelTrimLeftByte(s string, c byte) string {
	for len(s) > 0 && s[0] == c {
		s = s[1:]
	}
	return s
}

// modelChunked stands for a chunked body's reader: not modelled.
func modelChunked(r io.Reader) io.Reader {
	panic(notModelled("net/http model: a chunked message body is not modelled"))
}

// modelParseRequestURI is url.ParseRequestURI(rawurl) (Go 1.27.3's net/url). On a URI that is "/"
// followed by bytes modelPathByte accepts, it returns what Go's parse(rawurl, true) returns, the
// URL with that path and nothing else: no scheme (getScheme stops at the first byte, '/'), no
// query (no '?': strings.Cut finds none, RawQuery ""), no authority (a request URI without a
// scheme has none, even after "//"), Path the URI unescaped (no '%': unchanged), RawPath "" (escape
// in encodePath mode changes none of these bytes). On every other URI it is Go's function.
// MODEL: Go's parse calls strings.Cut, ToLower and Index, which Perennial translates as names only.
func modelParseRequestURI(rawurl string) (*url.URL, error) {
	if len(rawurl) > 0 && rawurl[0] == '/' && modelPathBytes(rawurl) {
		return &url.URL{Path: rawurl}, nil
	}
	return url.ParseRequestURI(rawurl)
}

// modelPathBytes reports whether every byte of s is one modelPathByte accepts.
func modelPathBytes(s string) bool {
	for i := 0; i < len(s); i++ {
		if !modelPathByte(s[i]) {
			return false
		}
	}
	return true
}

// modelPathByte reports whether c is a byte net/url leaves alone in a path: RFC 3986's unreserved
// bytes (letters, digits, "-", "_", ".", "~") and the sub-delimiters and separators that
// shouldEscape(c, encodePath) does not escape ("$", "&", "+", ",", "/", ":", ";", "=", "@").
func modelPathByte(c byte) bool {
	if 'a' <= c && c <= 'z' || 'A' <= c && c <= 'Z' || '0' <= c && c <= '9' {
		return true
	}
	return c == '-' || c == '_' || c == '.' || c == '~' || c == '$' || c == '&' || c == '+' ||
		c == ',' || c == '/' || c == ':' || c == ';' || c == '=' || c == '@'
}

// modelHeaderValuesContainsToken is httpguts.HeaderValuesContainsToken(values, token) (Go 1.27.3's
// vendored golang.org/x/net/http/httpguts): whether a comma-separated element of one of values,
// without the optional whitespace around it, is token, ASCII case-insensitively. httpguts' code,
// but for strings.IndexByte(v, ','), which Perennial translates as a name only, as modelIndexByte,
// and tokenEqual's loop (modelTokenEqual). MODEL: shouldClose calls it in place of httpguts'.
func modelHeaderValuesContainsToken(values []string, token string) bool {
	for _, v := range values {
		if modelHeaderValueContainsToken(v, token) {
			return true
		}
	}
	return false
}

// modelHeaderValueContainsToken is httpguts' headerValueContainsToken (strings.IndexByte as
// modelIndexByte).
func modelHeaderValueContainsToken(v string, token string) bool {
	for comma := modelIndexByte(v, ','); comma != -1; comma = modelIndexByte(v, ',') {
		if modelTokenEqual(modelTrimOWS(v[:comma]), token) {
			return true
		}
		v = v[comma+1:]
	}
	return modelTokenEqual(modelTrimOWS(v), token)
}

// modelIndexByte is strings.IndexByte(s, c): the index of the first c in s, or -1.
func modelIndexByte(s string, c byte) int {
	for i := 0; i < len(s); i++ {
		if s[i] == c {
			return i
		}
	}
	return -1
}

// modelTrimOWS is httpguts' trimOWS: x without the spaces and tabs at its ends.
func modelTrimOWS(x string) string {
	for len(x) > 0 && (x[0] == ' ' || x[0] == '\t') {
		x = x[1:]
	}
	for len(x) > 0 && (x[len(x)-1] == ' ' || x[len(x)-1] == '\t') {
		x = x[:len(x)-1]
	}
	return x
}

// modelLowerASCII is httpguts' lowerASCII.
func modelLowerASCII(b byte) byte {
	if 'A' <= b && b <= 'Z' {
		return b + ('a' - 'A')
	}
	return b
}

// modelTokenEqual is httpguts' tokenEqual(t1, t2): t1 and t2 equal, ASCII case-insensitively, t1
// ASCII. httpguts ranges over t1's runes and fails at the first one not ASCII (utf8.RuneSelf or
// above, utf8.RuneError for a byte that starts no valid encoding); before it every rune is one
// byte, at its byte index. This loop over t1's bytes fails at the first byte not ASCII, which
// starts that rune: the same result.
func modelTokenEqual(t1, t2 string) bool {
	if len(t1) != len(t2) {
		return false
	}
	for i := 0; i < len(t1); i++ {
		b := t1[i]
		if b >= 0x80 {
			return false
		}
		if modelLowerASCII(b) != modelLowerASCII(t2[i]) {
			return false
		}
	}
	return true
}
