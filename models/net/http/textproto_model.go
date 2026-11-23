// MODEL: this file is the model's own (not in Go's net/http).
//
// Package http here is a model of Go 1.27.3's net/http (models/README.md): Go's code, but for the
// parts this file and the places marked MODEL replace. The claim (trusted): every behavior of Go's
// net/http, as the program observes it, is a behavior of this model; where the model does not
// model Go's behavior it blocks forever (`select {}`, never a panic, which could be recovered), so
// that a proof of the program says nothing of a run that gets there. What is replaced:
//
//   - The HTTP/1.x message head parser (Go's net/textproto Reader: ReadLine and readMIMEHeader, as
//     ReadRequest, the server's request reading and ReadResponse call them) is this file's
//     modelReadLine and modelReadMIMEHeader, which return what textproto's return on the heads they
//     accept, and block forever on the others: a header continuation line (obsolete line folding) and a
//     header line whose name holds a space (Go accepts it, uncanonicalized). On a malformed line
//     they return textproto's error (a textproto.ProtocolError with its message).
//   - Chunked message bodies (transfer.go: a request or response with Transfer-Encoding chunked)
//     are not modelled: reading one blocks forever. Content-Length bodies, bodies to the end of the
//     connection, and no body are Go's code.
//   - TLS and HTTP/2 serving (server.go, conn.serve: a connection that is a TLS connection, and
//     unencrypted HTTP/2 when the Server enables it) are not modelled: serving one blocks forever.
//   - The client's Transport (transport.go, roundTrip) is not modelled: a round trip blocks forever. (The
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

	"golang.org/x/net/http/httpguts"
)

// Where the model does not model Go's behavior it blocks forever (`select {}`, after a comment `MODEL: not modelled (stuck): ...`), never a panic:
// a panic can be recovered (Go's recover, Perennial's with_defer_recover), so a value panic would add
// behaviors the library does not have; being stuck only removes behaviors (models/README.md).
// (So conn.serve's recovery of a handler's panic is upstream's: no model panic reaches it.)

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
		select {} // MODEL: not modelled (stuck): net/http model: a header block starting with a space is not modelled
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
			select {} // MODEL: not modelled (stuck): net/http model: a header continuation line is not modelled
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
				select {} // MODEL: not modelled (stuck): net/http model: a header name holding a space is not modelled
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

// modelChunked stands for a chunked body's reader: not modelled.
func modelChunked(r io.Reader) io.Reader {
	select {} // MODEL: not modelled (stuck): net/http model: a chunked message body is not modelled
}
