# `proto.SizeMessage`: the `0 ≤ n` claim replaced, and the stream receiver's size facts (rafthttpfix, 2026-11-20)

Found by prove-protootel (`notes/axiom-review/proto-size-wrap.md` and its Go test
`examples/axiomcx/protosizewrap`, both on branch `prove-protootel/2026-11-20` when this was written;
ledger 2026-11-20): `proto.SizeMessage.spec` returned `0 ≤ sint.Z n` for any `msgPtsC l dq dqe cap ms`,
but protobuf-go sums sizes with wrapping `int` additions (`internal/impl/encode.go:63-117`), and
`msgPtsC` admits one entry pointer repeated many times (entries are read-only, `entRoC`) and says
nothing of the responses: a message repeating one `2^33`-byte entry `2^30` times (or through `2^15`
responses of `2^15` entries) sizes negative (`TestSizeMessageNegative`). Fixed here.

## The new statement

`Spec/google_golang_org/protobuf/proto/SizeMessage.lean`, a conjunction:

1. over `msgPtsC l dq dqe cap ms`: some `int`, the message back, **nothing said of it** (the old
   statement without `0 ≤ n`);
2. over `msgPtsCC l dq dqe cap c` with `c.resps = []`: `msgSize c < 2^63 → sint.Z n = msgSize c`.

Why 2 is true: with no responses the message's content is all owned or frozen at `c` (scalars,
`entRoC` entries, owned snapshot, `bytesC` context, `pbMsg`'s unknown fields), `msgSize` is
protobuf's formula (as in `proto.SizePb`, the per-type models' size axiom), and the additions are of
non-negative parts, so below `2^63` no partial sum wraps. Above, nothing is claimed (as `SizePb`).
The responses are excluded because `msgPtsCC` holds only their pointers.

## The callers

* `EtcdServer.Process`, `rafthttp.Transport.Send`: drop the result; form 1.
* `rafthttp.snapshotHandler.ServeHTTP` (`receivedBytes.Add(float64(proto.Size(m)))`, prometheus'
  `Counter.Add` panics on a negative value): form 2 on the decoded message, whose content
  `decodeLimit` gives with `bs.length ≤ 64 MiB` and `MsgDecC c bs`, so `msgSize c ≤ 2^27`; the
  message is read through half (`msgPtsCC_read`) for `GetFrom` before `Size`.
* `rafthttp.streamReader.decodeLoop` (the same counter): form 2, given `msgSizeOk c`, so
  `msgSize c < 2^47` (`msgSize_lt_of_ok`). That fact was available only under the payload's `N.Sz`
  and not for link heartbeats; now unconditionally:
  - the stream codec's size parameter is `True` on the whole stream path, writers and reader
    (`StreamTy.codec True`: `streamResp`, `stream_known`, `swLive`, `WriterRun`'s instance,
    `streamWriter.run`, `decodeLoop`), the messages' content facts `msgSzC True` (`peerMsg`, `sendMsg`,
    `swMsg`): every sender's bundle is `msgSizeOk` whatever the payload (`netBundle`, since
    2026-11-10), so the writers' frames are of bounded size whatever `N.Sz`. The pipeline keeps
    `msgSzC N.Sz` (`pipeMsg_of_peerMsg` weakens, `msgSzC_mono`);
  - `msgAppV2Decoder.decode.spec`'s post: `Sz → msgSizeOk c` (was `Sz → ¬ isHB → msgSizeOk c`): a link
    heartbeat is a clone of `linkHeartbeatMessage`, whose content is `msgSizeOk` (`hbMsg_msgRoC`);
  - `wp_stream_decode` takes the codec's `Sz` apart from the payload's, post `Sz → msgSizeOk c`.

  `netRecv`'s `N.Sz → … → msgSizeOk c` is unchanged (discharged unconditionally).

The trust base's count does not change (one axiom's text).
