---
upstream: none
checked: 2026-10-31
links:
  - grpc/grpc-go#9056 issue closed: the same panic message (makeslice: len out of range) from a message mutated while marshaled; not this bug
blocks-proof: yes
---

# grpc-go: marshaling a message whose encoding is over 2^48 bytes panics instead of failing with ResourceExhausted

grpc's proto codec allocates a message's whole encoded size before any size check, so a message
whose encoding exceeds Go's largest allocation (2^48 bytes on linux/amd64) panics the process with
`makeslice: len out of range`, in a client sending it as a request or a server sending it as a
reply. Such a message is cheap to build when a repeated field holds one submessage many times: one
16 MiB value held 2^24 times takes about 150 MiB of memory.

**Expected:** `Marshal` should return an error, and an RPC sending such a message should fail with
`ResourceExhausted`, as grpc does for any message over 4 GiB (`encode`'s check) and over the send
limits.

**Impact:** low. A process panics only when it sends such a message itself; for a server, when a
handler's reply can be made that large by a client (replies sharing submessages). etcd's client
sends requests through this codec (a `Txn` holding 2^18 + 1 copies of one get of a 1 GiB key
panics the client); etcd's server uses its own codec, whose `proto.Marshal` has the same
allocation (`etcd-txn-keysonly-reply-alloc-panic`).

**Reproduction:** `TestMarshalTooLarge` in
[`issues/grpc-codec-alloc-before-size-check/codec_too_large_test.go`](grpc-codec-alloc-before-size-check/codec_too_large_test.go),
in a scratch module requiring google.golang.org/grpc v1.85.0 (2026-10-27, the latest release;
protobuf v1.36.12), go1.27.3:

```
$ go test . -run TestMarshalTooLarge -count=1
--- FAIL: TestMarshalTooLarge (2.06s)
panic: runtime error: makeslice: len out of range [recovered, repanicked]
google.golang.org/grpc/internal/mem.(*SimpleBufferPool).Get(0x1c5cc298cde0, 0x100000a000000)
	google.golang.org/grpc@v1.85.0/internal/mem/buffer_pool.go:356 +0xf4
google.golang.org/grpc/encoding/proto.(*codecV2).Marshal(...)
	google.golang.org/grpc@v1.85.0/encoding/proto/proto.go:74 +0x118
```

**Cause:** [`codecV2.Marshal`](https://github.com/grpc/grpc-go/blob/c9ab42cdb0a2b3e7b9d5510ebbc999638ee41eb7/encoding/proto/proto.go#L43-L83)
computes `proto.Size(m)` (a submessage held N times counts N times) and gets a buffer of that
size from the pool, which `make`s it; the [4 GiB check in
`encode`](https://github.com/grpc/grpc-go/blob/c9ab42cdb0a2b3e7b9d5510ebbc999638ee41eb7/rpc_util.go#L820-L823)
and the send limits run only after `Marshal` returns.

## Proof

yes: grpc's send side takes the encoded-size premise `Req.wireLen ≤ grpcMsgMax` (2^32) on
`Invoke` and `NewStream` (`Proof/google_golang_org/grpc/InvGrpc.lean`, `notes/invoke-size.md`),
which etcd's client does not check; its callers carry it as bounds on keys, values and operations.

## Fix

The fix branch `fix/grpc-codec-alloc-before-size-check` (2026-10-31, off grpc/grpc-go master
bc90736a6fadc41582f9a23fb955bb66088f1bb8, never pushed) was in a clone that no longer exists. Its
substance: `codecV2.Marshal` returns `status.Errorf(codes.ResourceExhausted, "grpc: message too
large (%d bytes)", size)` when `size > math.MaxUint32`, before allocating, and `encode` returns a
codec's status error unchanged instead of wrapping it as `Internal`; tests `TestMarshalTooLarge`
(`encoding/proto`) and `TestEncodeTooLarge` (`rpc_util_test.go`) on the message above. Capping the
initial allocation is not enough: protobuf-go's `MarshalAppend` then allocates the whole size
itself (`proto/encode.go:190`) and panics the same way.

## Notes

grpc-go asks for crashes to go through its CVE process (`P4-grpc-cve-process.md`) rather than a
public issue: the user decides, together with
[`etcd-txn-keysonly-reply-alloc-panic`](etcd-txn-keysonly-reply-alloc-panic.md), which is on hold.
grpc-go's rules differ from etcd's: CLA (not DCO), PR title starting `encoding/proto:`, `Fixes`
first, a `RELEASE NOTES:` bullet. protobuf-go's `proto.Marshal` panicking on the same message is a
separate, unreported bug.
