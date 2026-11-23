---
upstream: none
checked: 2026-11-23
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

no: the net/rpc model's server codec makes a frame read's error sticky (`serverCodec.rerr`,
`models/net/rpc/codec.go`), which is Go's behavior over Linux without read deadlines; the model's
claim excludes programs that set a read deadline on a served connection, and the net extension's
semantics (which allows bytes after a read error on a cut direction) is not what the model's
faithfulness rests on here.
