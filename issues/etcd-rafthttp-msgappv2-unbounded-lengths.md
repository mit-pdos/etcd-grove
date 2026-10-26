---
upstream: known
checked: 2026-10-26
links:
  - etcd-io/etcd#21874 pr open: same bug and fix (entry count and sizes capped at `readBytesLimit`, `ErrExceedSizeLimit`), by someone else, with an e2e test; no review since the maintainer asked for the reproduction; labeled stale 2026-09-29
  - etcd-io/etcd#5386 issue closed: the same bug in the other codec (`messageDecoder`, `msg_codec.go`)
  - etcd-io/etcd#6349 pr merged: #5386's fix (the `readBytesLimit` check before allocating) that msgappv2 never got
  - etcd-io/etcd#20152 issue closed: related only: an OOM with `msgAppV2Decoder.decode` in the profile, from legitimate traffic
---

# rafthttp: the msgappv2 decoder allocates whatever lengths the stream says

**Status**: a robustness gap, not reachable between etcd members. A peer that is not etcd's
encoder (a misbehaving or incompatible member, or a corrupted stream) can make a follower allocate
up to `2^63` entries' pointers or bytes from a single frame, which panics (`makeslice: len out of
range`) or exhausts memory. The streams' other codec bounds the same thing:
`messageDecoder.decode` refuses a message over `readBytesLimit` (512 MiB, `ErrExceedSizeLimit`).
Unchanged on upstream `main` `f3221acd1` and release-3.6/3.5 (rechecked 2026-10-26); etcd-io/etcd#21874
(open, by someone else, stalled) has the fix. The same peer can also panic the decoder with
malformed entry or message bytes, bounded lengths or not: `pbutil.MustUnmarshalMessage` (`:225`,
`:243`).

**Where** (etcd `goose-lean` `188113160d`, `server/etcdserver/api/rafthttp/msgappv2_codec.go`):
`msgAppV2Decoder.decode` (line 179) reads an AppEntries frame's entry count `l` and allocates
`make([]*raftpb.Entry, int(l))` (line 206); each entry's size, and allocates `make([]byte,
int(size))` when it is at least `msgAppV2BufSize` (line 219); and an App frame's size, allocating
`make([]byte, int(size))` (line 239). None is checked against a limit, and `int(l)` of a value at
least `2^63` is negative (a panic in `make`).

**What happens**: the decoder runs in `streamReader.decodeLoop`, a goroutine; a panic there takes
down the member. The bytes come from the peer's HTTP response stream (`streamTypeMsgAppV2`),
authenticated only by TLS when configured.

**Expected**: a bound like `messageDecoder`'s: an error (`ErrExceedSizeLimit`), closing the stream,
for a count or size over a limit.

**How the proof handles it**: the decoder's spec (`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/
rafthttp/msgAppV2Decoder__decode.lean`) takes that the bytes read are a prefix of a frame of etcd's
encoder or extend one (`V2Compat`, from the HTTP boundary's closed world: received bytes are those
a member of the program sent), so every count and size it reads is below `2^63` and is the frame's
own (`V2Compat.short_count`, `short_len`, `app_len` in `rafthttp/MsgAppV2.lean`).

**Possible fixes**: check `l` and `size` against `readBytesLimit` (or a limit derived from
`MaxSizePerMsg`) and return `ErrExceedSizeLimit`, as `messageDecoder.decodeLimit` does.

**Found**: 2026-10-22, proving `msgAppV2Decoder.decode` (rafthttp stage 3, D38a): the decoder's
proof needs the closed-world premise to know the lengths are an encoder's.
