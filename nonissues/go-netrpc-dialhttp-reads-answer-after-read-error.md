---
upstream: none
checked: 2026-11-23
links: []
blocks-proof: no
---
# net/rpc: `DialHTTPPath` reads the CONNECT answer on after a read error

`DialHTTPPath` reads the server's answer to its `CONNECT` request with `http.ReadResponse` over a
`bufio.Reader` of the connection, then hands the connection itself (not the reader) to `NewClient`.
textproto's `ReadLine` returns a line cut by a read error (EOF or another) without the error, and
`bufio.Reader` does not keep an error, so the parser reads on after it. If the connection yielded a
byte after an error, the answer's status line `HTTP/1.0 200 Connected to Go RPC` cut by the error
and then its first `"\n"` would parse as the whole answer, the empty header block included, and the
answer's last `"\n"` would be left on the connection, where the client's codec would take it for
the start of a response.

**Why not an issue:** no test, found by code reading (Go 1.27.3's `net/rpc/client.go`,
`DialHTTPPath`; `net/textproto/reader.go`, `readLineSlice`; `bufio/bufio.go`, `readErr`). It needs a
read that fails and a later read that returns bytes on the same connection: on Linux a read error
comes once the unread bytes are read, then EOF (`examples/net/semantics`' `TestReadEOFAfterFin`,
`TestResetCloseUnreadInput`), except for a read deadline's timeout, and `DialHTTPPath` dials the
connection itself and sets no deadline. Go's `net/rpc` is frozen.

## Proof

no: the net/rpc model reads the answer through `connectReader` (`models/net/rpc/client.go`), which
drops any byte after a read error: Go's behavior over Linux. The net extension's semantics allows
bytes after a read error on a cut direction, which is why the model says it (as for the server
codec's sticky read error, `go-netrpc-server-reads-on-after-body-read-error.md`).
