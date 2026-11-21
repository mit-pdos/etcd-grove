# `proto.Size` and `proto.SizeMessage`: `0 ≤ n` false for shared sub-messages (prove-protootel, 2026-11-20)

Found while triaging the `proto` trust boundary (extlib group `protootel`), by reading the pinned code
(protobuf-go v1.36.12, raft at the fork's `565c2bd`, etcd at the fork's pin) and checked in Go
(`examples/axiomcx/protosizewrap`, `PROTOSIZEWRAP=1`, go1.27.3; the three tests below, 20-35 s each).
No Lean counterexample was built.

## What protobuf-go does

`proto.Size(m)` (`proto/size.go:19-40`) is the generated fast path's `sizePointer`
(`internal/impl/encode.go:63-117`), which sums each field's size with Go's `int` additions; a repeated
message field adds, for each element, its tag, its length's varint and the element's size, recomputed
every time (`codec_field.go`, `sizeMessageSliceInfo`; the size cache is only read with
`UseCachedSize`). Nothing checks for overflow: a true size of `2^63` or more wraps, and the result can
be negative. `proto.SizePb`'s docstring already says so ("Above, Go's `int` sum wraps silently, without
panicking, so the post says nothing of the result"), and its post is `size c < 2^63 → n = size c`.

A message whose repeated message fields hold the **same pointer** many times has a true size far above
its memory, and its byte slices need not be touched (Size reads only their lengths): a `2^33`-byte
slice made by `make` costs address space only.

## `proto.SizeMessage.wp_proof`: **false as stated, recorded, not fixed**

`Spec/google_golang_org/protobuf/proto/SizeMessage.lean`: for any `msgPtsC l dq dqe cap ms`, returns `n`
with `0 ≤ sint.Z n`. `msgPtsC` (`Proof/go_etcd_io/raft/v3/InvPb.lean`) holds the entries read-only
(`entRO`, persistent: the same pointer may appear many times) and the responses as bare pointers
(`rs ↦*{dq} ms.resps`, nothing about what they point to).

`TestSizeMessageNegative`: one `*Entry` with a `2^33`-byte `Data`, `2^15` times in a response's
`Entries`, that response `2^15` times in the message's `Responses`: `proto.Size(m) =
-9223372023969611776`. With no responses, the entries alone do it at `2^30` copies (an 8 GiB slice of
pointers, as the range response below).

**Why not fixed.** Two callers use the `0 ≤ n`, for `receivedBytes...Add(float64(proto.Size(m)))`
(prometheus' `Counter.Add` panics on a negative value): `streamReader.decodeLoop` and
`snapshotHandler.ServeHTTP`, on a message just decoded (`EtcdServer.Process` and `Transport.Send` drop
the result). A true restatement is `proto.SizePb`'s at the content: `msgPtsCC l dq dqe cap c` with
`c.resps = []`, post `msgSize c < 2^63 → sint.Z n = msgSize c` (plus a no-claim case over `msgPtsC` for
the two callers that drop the result). `ServeHTTP` can discharge `msgSize c < 2^63`: `decodeLimit`
gives `bs.length ≤ numBytes` and `MsgDecC c bs` gives `msgSize c ≤ 2 * bs.length`. `decodeLoop` cannot
today: the stream decoders give a size fact only under the payload's `N.Sz` (`Reader.lean`,
`wp_stream_decode`: `N.Sz → ¬ isHB → msgSizeOk c`), and the msgappv2 decoder's `MsgApp` takes its
entry count and sizes from the stream; Lean's slices are unbounded (Perennial's `make` admits any
length below `2^63`, no `maxAlloc`), so without `N.Sz` a decoded message can be larger than `2^63` in
the model. The fix needs the receiver's size facts unconditional: every sender's `netBundle` is
`msgSizeOk` since 2026-11-10 ("Of bounded size whatever the payload"), but the codec relations
(`V2Frame Sz`, `MsgEncSz Sz`, the codecs' `F`) still carry `Sz`; removing it from the stream path is a
rafthttp refactor beyond this group. Not reachable in etcd: a decoded message is a tree, its size at
most about twice the bytes it was decoded from.

## `proto.Size.wp_proof` at a range response and a transaction's response: **false as stated, fixed**

`Spec/google_golang_org/protobuf/proto/Size.lean`, conjuncts 2 and 3: `0 ≤ sint.Z n` for any
`txn.rangeResponseIs r ...` and any `txn.roTxnRespRd r`. Both hold their key-values (`kvsIs`, a
persistent `□ ∀ i`) and a transaction's responses (`[∗list] p ∈ ps, roOpRd p`, persistent) read-only,
shared pointers allowed.

- `TestSizeRangeResponseNegative`: one `*KeyValue` with a `2^33`-byte value, `2^30` times in `Kvs`:
  `-9223372023969873918`.
- `TestSizeTxnResponseNegative`: that key-value `2^15` times in a range response, the range response
  `2^15` times in the transaction's `Responses`: `-9223372023969284094`.

Fix: the post of both conjuncts drops `0 ≤ sint.Z n` (some `int`, the header's id fields back). No
caller used it (`EtcdServer.Range`'s `rangeResult_warn`, `EtcdServer.Txn`'s `txnResp_warn`: the size
goes to a log field); their patterns changed from `⟨-, Hh⟩` to `Hh`. Conjunct 1 (a put request) is
true and unchanged: two byte slices and scalars, no repeated message field, so memory bounds its size.
The spec plan's `SpecPlan/Spec/google_golang_org/protobuf/proto/Size.lean` already states the
wrapped size (`n = W64 (encSize c)`): the fix converges to it. Ledger: `notes/specs-only/ledger.md`,
2026-11-20.
