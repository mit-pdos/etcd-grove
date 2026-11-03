---
upstream: known
checked: 2026-11-01
links:
  - etcd-io/etcd#21874 pr open: same bug and fix (entry count and sizes capped at `readBytesLimit`, `ErrExceedSizeLimit`), by someone else, with an e2e test; no review since the maintainer asked for the reproduction; labeled stale 2026-09-29
  - etcd-io/etcd#5386 issue closed: the same bug in the other codec (`messageDecoder`, `msg_codec.go`)
  - etcd-io/etcd#6349 pr merged: #5386's fix (the `readBytesLimit` check before allocating) that msgappv2 never got
  - etcd-io/etcd#20152 issue closed: related only: an OOM with `msgAppV2Decoder.decode` in the profile, from legitimate traffic
blocks-proof: no
---

# rafthttp: the msgappv2 stream decoder allocates whatever entry count and sizes the stream says

A peer's msgappv2 stream frame can make the receiving member allocate up to `2^63` entry pointers
or bytes (`makeslice: len out of range`, or memory exhaustion), on the stream reader's goroutine,
which ends the process. The other stream codec refuses a message over `readBytesLimit` (512 MiB).

**Why not an issue:** no test; found by code reading (proving the decoder), and only a sender that
is not etcd's encoder (a misbehaving peer, a corrupted stream) reaches it. A test could promote
it: a frame with a huge entry count fed to `msgAppV2Decoder` through a `streamReader`, as
etcd-io/etcd#21874's test does; supporting that open PR is the step if anyone wants it fixed.

## Proof

no: the decoder's spec takes that the bytes read are an etcd encoder's frame (`V2Compat`, the HTTP
boundary's closed world), which etcd's members meet
(`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/msgAppV2Decoder__decode.lean`).

## Notes

`msgAppV2Decoder.decode` (`server/etcdserver/api/rafthttp/msgappv2_codec.go`) allocates
`make([]*raftpb.Entry, int(l))` and `make([]byte, int(size))` unchecked. The same sender can also
panic it with malformed entry bytes (`pbutil.MustUnmarshalMessage`).
