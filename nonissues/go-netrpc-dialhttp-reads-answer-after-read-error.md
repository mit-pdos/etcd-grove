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

no: handled by the net extension's semantics (2026-11-23, D1 v3.5, `GooseLang/Ext/Net/Impl.lean`):
a `sys` read error comes only once nothing is unread, so after a read error (EOF, `sys`, `closed`)
no read returns a byte (`readDead`, `read_after_dead_au` in `GooseLang/Ext/Net/Proto.lean`), and a
timeout needs a read deadline, which `DialHTTPPath` does not set (the dialer's `rdlTok cn false
false`). The model's `connectReader` wrapper is removed: `DialHTTPPath` reads through
`bufio.NewReader(conn)` as Go's does, and its proof (`Net/Proof/net/rpc/DialHTTPPath.lean`,
`crStream`) gives `http.ReadResponse.spec` the finality law it needs.
