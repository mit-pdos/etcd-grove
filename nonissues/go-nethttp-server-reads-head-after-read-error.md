---
upstream: none
checked: 2026-11-23
links: []
blocks-proof: no
---
# net/http: the server reads a request's head on after a read error

The server (`conn.serve`, `readRequest`) reads a request's head through a `bufio.Reader` of its
`connReader`. textproto's `ReadLine` returns a line cut by a read error (EOF or another) without the
error, `bufio.Reader` does not keep an error, and `connReader.Read` keeps none either (it only
cancels the connection's context, `handleReadErrorLocked`), so the parser reads on after it. If the
connection yielded bytes after an error, a request line cut by the error and the bytes after it would
parse as one head (for net/rpc's `CONNECT` handshake: a dialer's later bytes taken as the head's
rest, and the connection handed to the handler at the wrong position).

**Why not an issue:** no test, found by code reading (Go 1.27.3's `net/http/server.go`,
`connReader.Read`, `backgroundRead`; `net/textproto/reader.go`, `readLineSlice`; `bufio/bufio.go`,
`readErr`). It needs a read that fails and a later read that returns bytes on the same connection: on
Linux a connection's end yields no byte after a read error (`examples/net/semantics`'
`TestReadEOFAfterFin`, `TestResetInNetwork`, `TestKilledWithUnreadInput`, `TestTimeoutOnBreak`),
except for a read deadline's timeout, after which the connection is usable again and Go reads on as
it should (a server's `ReadTimeout`, `ReadHeaderTimeout`, `IdleTimeout` close the connection after
one anyway).

## Proof

no: handled by the net extension's semantics (2026-11-23, D1 v3.5): no read returns a byte after a
read error (`readDead`, `read_after_dead_au`), and a timeout needs a read deadline. The model's
`connReader.failed` is removed (`models/net/http/server.go` is Go's code again); the head reader's
proof (`Net/Proof/net/http/connReader__Read.lean`, `crHead`) holds the end's `rdlTok cn true false`
(no read deadline while the head is read) and records the first error (`crHeadErr`,
`crHeadErr_final`: nothing delivered after it), the law a head parser's spec takes.
