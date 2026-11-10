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

## Next, in order

1. A2: frames and encoders carry the content. Draft of `MsgAppV2.lean` (compiles alone):
   `/shared/tmp/ptm-cp3/entsize/MsgAppV2.a2-partial.lean` (`MsgEncSz`, `EntsSz`, `V2Frame Sz …`,
   `V2Compat Sz …`, all `V2Compat.*` lemmas threaded). Remaining: `v2Codec Sz`, `StreamTy.codec Sz`
   and its ~25 use sites (Writer, WriterRun, Reader, streamReader__decodeLoop, streamWriter__run,
   Stream's `streamResp`); `messageEncoder.encode`/`msgAppV2Encoder.encode` specs take `msgSzC Sz`
   and give `MsgEncSz Sz` / `V2Frame Sz` (their proofs already encode `c.f.entries.map entryEncC` of
   the unpacked content: add `EntsSz` from `msgSizeOk c`); `pipeReq` with `MsgEncSz Rh.γn.N.Sz`
   (`pipeline__post` spec premise); `createSnapBody` uses `Sz := False`.
2. B: decoder specs give `msgPtsCC` at the content with D1/D2 facts (`decodeLimit`: size ≤ 2·|bs|
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
