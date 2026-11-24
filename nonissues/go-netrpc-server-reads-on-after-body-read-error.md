---
upstream: none
checked: 2026-11-24
links: []
blocks-proof: no
---
# net/rpc: after a request body's read fails, the server keeps reading the connection from the middle of that request

When a request's header reads but its body's read fails, Go's `net/rpc` server answers the request
with the read's error and goes on reading the connection (`ServeCodec`: `readRequest` returns the
error with `keepReading` true). gob's decoder does not remember the failure: its next `Decode`
reads from wherever the failed read stopped, inside the request that failed, as if a message
started there. If the connection yields bytes after the failure, the server decodes the rest of
that request as new requests, and a byte sequence that happens to decode as a header naming a
registered method runs that method on arguments no client sent.

**Why not an issue:** no test, found by code reading (Go 1.27.3's `net/rpc/server.go`, `ServeCodec`
and `readRequest`; `encoding/gob/decoder.go`, `DecodeValue` resets `dec.err`). It needs a read that
fails and a later read that returns bytes on the same connection: on Linux a read error comes once
the unread bytes are read, then EOF (`examples/net/semantics`' `TestResetInNetwork`,
`TestKilledWithUnreadInput`, `TestTimeoutOnBreak`), except for a read deadline's timeout, which a
program that sets a read deadline on a connection it serves would hit. Go's `net/rpc` is frozen;
neither etcd nor the dsverify-lab kits set read deadlines on served connections.

## Proof

no: the net extension's semantics makes a read error sticky but a read deadline's timeout (D1 v3.5:
no byte after an EOF, a `sys` error or `closed`, `readDead`), which is Linux's behavior
(`examples/net/semantics`' "Sticky read errors"). The net/rpc model's server codec reads on after an
error as Go's does (its `rerr` wrapper is gone, 2026-11-24), and the proof shows the case cannot
arise for the programs proved: a served connection's read deadline is not set (`rdlTok cn true
false`, from `Accept`, or cleared by net/http's hijack), so a body read that fails leaves the end's
reading dead and the next header read fails, ending the loop (`rdrOwn`, `ServerDefs.lean`); and a
body frame longer than the model's `maxFrame`, the other way the loop reads on from the middle of a
request, is excluded by the protocol (a model client's frames fit, its `WriteRequest`'s stuck point
on a longer one, `reqOk`). A program that sets a read deadline on a connection it serves is outside
the proofs (it has no `rdlTok cn true false`), not outside the model.
