# raft-entsize: handoff

Worktree `/shared/etcd-grove-ptm`, branch `per-type-models`. Scope: `/shared/tmp/raft-entsize-scope-r3.md`
(§4 and the dated sections [r3a]-[r3j]).

## Build

```
export TMPDIR=/shared/tmp
timeout 12000 flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G \
  lake build --packages=/shared/tmp/manifest-ddc.json [targets]
```

`LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json` for `etc/*.py` (`etc/lean-check.py`,
`etc/importers.py`). Targeted builds: `etc/importers.py --uses NAME FILE --files`.

## Done (the receive row, part A1: the sender side; 2026-11-10, uncommitted)

- `NetPayload.Sz : Prop` (rafthttp `Net.lean`); the server's `srvNet.Sz := γ.cl.maxData ≠ none`.
- Pure lemmas (`Net.lean`, section `sizePure`): `msgSizeOk_of_size` (`msgSize c ≤ 2^30`, no
  responses → `msgSizeOk c`), `msgSize_lt_of_ok` (`msgSizeOk c → msgSize c < 2^47`), with varint/size
  helpers.
- `msgPtsCC_msgRoC` (and the snapshot-level `*CC_*RoC` chain, `Net.lean`, section `contentRo`): a
  read-only content form without responses is `msgRoC`.
- `netBundle` gains `∃ c, msgRoC m c ∗ ⌜c.model = st ∧ c.csUfNil ∧ (N.Sz → msgSizeOk c)⌝`.
- `msgSzC Sz ml st` (`Net.lean`): one content with `msgSize c < 2^47` and `Sz → msgSizeOk c`;
  `msgSzC_swMsgBound` (`MsgAppV2.lean`). `peerMsg`, `sendMsg`, `pipeMsg`, `swMsg` take
  `msgSzC Rh.γn.N.Sz ml st` in place of `swMsgBound ml st`.
- `sendMsg_of_netBundle`: by cases on `Sz`: the bundle's content (bound by `msgSize_lt_of_ok`), else
  `swMsgBound_phys`'s (unchanged axiom).
- Server: `srvMsgNet` gains the content (`maxData ≠ none → msgSizeOk c`), from `msgOut_netContent`
  (`InvBuild.lean`, via `Cluster.outObj_size`); its producers in `ServerOn.lean`, `BuildGap.lean`.

## Done (part A2: frames and encoders; 2026-11-10, uncommitted)

- `MsgAppV2.lean` (from the draft): `MsgEncSz Sz`, `EntsSz Sz` (+ `EntsSz.of_msg`), `V2Frame Sz`,
  `V2Compat Sz` with every lemma threaded; `msgSzC_mono`, `msgSzC_of_swMsgBound` (a condition that
  does not hold).
- `v2Codec Sz`, `StreamTy.codec Sz` (`Stream.lean`; `streamResp` at `Rh.γn.N.Sz`), `encOwn Sz`,
  `decOwn Sz`, `swLive`, `wp_stream_encode Sz`, `wp_stream_decode` (at `N.Sz`), `stream_perm`,
  `stream_known`, `streamSent_v2Compat` (at `N.Sz`).
- `messageEncoder.encode.spec`: `∀ Sz`, `msgSzC Sz` (was `swMsgBound`), permission and post
  `MsgEncSz Sz`. `msgAppV2Encoder.encode.spec`: `∀ Sz`, `msgSzC (Sz ∧ ¬isHB st.msg)` (a link
  heartbeat's frame carries no encoding, and its clone's size is not known: see below), `V2Frame
  Sz`. `wp_stream_encode` takes `msgSzC (Sz ∧ ¬isHB st.msg)`; the writer's message case weakens
  `msgSzC Rh.γn.N.Sz` (`msgSzC_mono`), the heartbeat case still takes `swMsgBound_phys` and
  `msgSzC_of_swMsgBound`.
- `msgAppV2Decoder.decode.spec`: `∀ Sz`, `V2Compat Sz`/`V2Frame Sz` (post unchanged otherwise).
- `pipeReq` and `pipeline.post.spec`: `MsgEncSz Rh.γn.N.Sz` (was `MsgEnc`); `pipeline.handle` gives
  it from `msgSzC`; `Pipe.lean` imports `MsgAppV2`.
- `createSnapBody`: `messageEncoder` at `Sz := False` (`msgSzC_of_swMsgBound`).
- Targeted build of all 222 rafthttp Spec/Proof modules green (`/shared/tmp/ptm-cp3/entsize/a2-rafthttp.log`).

## Started (part B; 2026-11-10, uncommitted)

- `rafthttp/MsgRead.lean` (new): `msgPtsCC_read l cap c (hcs : c.csUfNil)`: an object at a content,
  `msgPtsCC l 1 1 cap c`, gives `msgPtsC l dqh dqh false c.model` (half, today's form) and the wand
  that rebuilds `msgPtsCC l 1 1 cap c` from that half given back; with `msgPtsCC_split`/`_join` and
  the nested `snapOptCC`/`ownSnapCC`/`smOptCC`/`smPtsCC`/`csOptCC`/`csPtsCC`/`bytesCC` halves (a conf
  state owned whose half comes back frozen is rebuilt frozen: `csPtsCC_join_ro`). Why: every reader of
  a received message (`decodeLoop`: `proto.Size`, `GetFrom`, `isLinkHeartbeatMessage`, `GetType`;
  `pipelineHandler`; `EtcdServer.Process`: `GetFrom`/`GetTo`/`GetType`/`proto.Size`) uses specs over
  `msgPtsC` (raft's getters, the `proto.SizeMessage` axiom) whose posts give back some `msgPtsC`, not
  the content (two contents of one object cannot be shown equal); all are generic in the fractions, so
  the half trick keeps the content that carries the size fact. No spec or axiom changes.
- `pbutil.MustUnmarshalMessagePb.spec`: post strengthened to `decC l c₀` and `∀ c₁` valid with
  `bs = pbEncC T c₁ → c₁ = c₀` (D2, from `proto.UnmarshalPb`); the msgappv2 decoder adjusted (its
  entries are now `entRoC p ec` at the sender's content; the App frame converts `decC` back to
  `msgPtsC` until (c) below).
- Targeted build (pbutil's `MustUnmarshalMessagePb` and all rafthttp Spec/Proof modules, `MsgRead`
  included) green: `/shared/tmp/ptm-cp3/entsize/b1-rafthttp.log` (targets `b1-targets.txt`).
- Forms decided: in `questions.md` (untracked, worktree).

## Next, in order

1. B, the rest: (a) `netRecv` → `∃ st c, msgPtsCC ml 1 1 true c ∗ ⌜c.model = ⟨st.msg, st.ents,
   st.snap, st.ctx, []⟩ ∧ c.csUfNil ∧ st.msg.To' = id ∧ (γn.N.Sz → st.msg.Type' ≠ MsgSnap →
   msgSizeOk c)⌝ ∗ □ P st ∗ O st ∗ netSnapRecv γd st` (replaces `wireEq st st'`, same meaning by
   `msgPtsC_iff_CC`); `stepIn_of_recv` passes the size fact (`srvNet.Sz := maxData ≠ none`);
   `Process` reads through `msgPtsCC_read`. (b) `messageDecoder.decodeLimit`/`decode` posts: the
   decoded content (`msgPtsCC`, D2's `c = c0`, D1's `msgSize c ≤ 2·|bs|`); with
   `|bs| ≤ readBytesLimit = 2^29`, `msgSizeOk_of_size`. (c) `msgAppV2Decoder.decode` post: the content,
   with `Sz → ¬isHB → msgSizeOk c`; App frame: D2 against `MsgEncSz`'s content; AppEntries frame: a
   new `msgPtsCC_of_struct` (as raft's `msgPtsC_of_struct_uf`, entries `entRoC` at the decoded
   contents, header `uf = []`), the loop tracking the decoded contents and
   `MustUnmarshalMessagePb`'s uniqueness, so they are `EntsSz`'s (needs `entFrames` injective to
   match the frame's `ebs` with `pre`); hdrBytes 0. (d) `wp_stream_decode`, `decodeLoop` (reads via
   `msgPtsCC_read`, builds `netRecv`), `pipelineHandler` (D2's `c' = c0` and `MsgEncSz`'s size),
   `snapshotHandler` (a `MsgSnap`: the size fact vacuous).
2. The server switch to `maxData = some 2^30` (drop `srvClusterOk`'s interim `maxData = none`; the
   allocations discharge raft's boot-data premise from `BootCore`'s `bootDataOk`; `raftPropose ≤ 2^27`
   and the read context's 8 bytes).
3. The users of `swMsgBound_phys` (Transport `sendMsg_of_netBundle`; `streamWriter.run`'s heartbeat
   clone; `createSnapBody` per [r3c]), then delete the axiom. At the start, check [r3c]'s snapshot-data
   bound. Note for the heartbeat: the clone is `chb` (`ClonePb`: `c' = c` when it marshals), the
   content of the global `linkHeartbeatMessage`, whose init axiom gives only `msgOwn … hbSt`, so its
   unknown fields' length (hence `msgSize < 2^47`, which the message encoder's `proto.Size` needs) is
   not known from existing facts: likely a STOP (the init axiom would have to state the content).

Old text of item 1 (kept for reference): B: decoder specs give `msgPtsCC` at the content with D1/D2 facts (`decodeLimit`: size ≤ 2·|bs|
   and `∀ c₀, … bs = msgEncC c₀ → c = c₀`); v2 decoder: fresh header plus D2 entries; `netRecv` →
   `∃ st c', msgPtsCC ml 1 1 true c' ∗ ⌜c'.model = ⟨…, []⟩ ∧ c'.csUfNil ∧ (N.Sz → Type' ≠ MsgSnap →
   msgSizeOk c')⌝ ∗ …`; `stepIn_of_recv` feeds `stepIn_intro` (`maxData = some b → Sz`).

## Pitfalls

- Two `msgRoC` contents of one location cannot be shown equal (`pbMsg`'s unknown fields live in an
  invariant): the bundle's size fact must be on the same content the encoder encodes (hence
  `msgSzC`, and content-linked encoder specs in A2).
- `omega` atoms: a `match` restated in a hypothesis is a different matcher than the definition's;
  the enum-varint term of `MsgFC.size`/`entrySize` elaborates differently when restated: use
  `generalize hT : optVarintSize (Option.map _ f.type) = T` and `generalize f.snapshot = sn`.
- `msgOut_netContent` needs `[StorageModel GF]` (callers: `letI := srvStor γ.node`).
