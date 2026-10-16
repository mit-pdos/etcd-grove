# etcd-io/raft#392: With retries/duplicates, read-only index can be stale (non-linearizable)

- **Bug**: https://github.com/etcd-io/raft/issues/392, closed 2026-03-09 (filed 2026-02-28 by
  upamanyus; the user-visible symptom is etcd-io/etcd#20418).
- **Affected**: raft before v3.7 (`ReadOnlySafe`; every release up to v3.6), with etcd up to v3.6.
- **Fix**: two halves, both in the pins.
  - raft: etcd-io/raft#397 (merge `eed49d45e`, 2026-03-09), "Use unique index as heartbeat ctxes for
    read-only operations": `readOnly` keys pending reads by position (`unconfirmedReads`,
    `confirmedReads`, per-voter `acks`), heartbeats carry the last position (`heartbeatCtx`), and
    `maybeAdvance` confirms the prefix a quorum has acknowledged. Ancestor of the raft pin `509271dac`
    (v3.7.0 `b867cf13` plus the single-voter fix). The release-3.6 branch only got a documentation
    change, etcd-io/raft#398 (`0798d4573`): do not retry `ReadIndex` with the same `rctx`.
  - etcd: etcd-io/etcd#21399 (merge `5944c74e3`, 2026-03-01), "Don't reuse same ReadIndex in
    retries": every resend takes a new id (`NextRequestID()`) and the loop accepts a read state of
    any of its ids. Ancestor of the etcd pin `107edf7e4`.
- **What goes wrong** (pre-#397 `read_only.go`): `readOnly` kept a queue of request contexts (the
  client's `rctx` bytes) and a heartbeat carried the last pending context. A quorum of
  `MsgHeartbeatResp` acks for context `A` made `advance` release every queued request up to `A`. etcd
  (pre-#21399) resent `ReadIndex` with the *same* `rctx` on timeout. At a stale leader: `A` is
  confirmed and dequeued; etcd resends `A`; a fresh request `B` (stale commit index, a new leader has
  committed since) is queued; the resent `A` is queued after it; delayed acks of the *first* `A`'s
  heartbeats arrive, reach a quorum for context `A`, and `advance` releases `[B, A]`: `B`'s
  `ReadState` misses entries committed before `B` was issued.

## Classification

**F (fixed before the verified code); counterfactual F+ for etcd's half (the trigger), F− at the raft
API for raft's half (the raft spec's premise `rdFresh` excludes the trigger).**

Both fixes are ancestors of the pins (`git merge-base --is-ancestor`: `eed49d45e` ⊑ `509271dac`,
`5944c74e3` ⊑ `107edf7e4`). Would the current specs have excluded the old code? etcd's old read loop
could not be verified: each `ReadIndex` call needs the context's exclusive token `rdFresh γ c`, which
the deposit hands to raft's invariant for good, so a resend with the same id has none (F+). The old
raft code would, as far as can be argued without a proof attempt, meet raft's API specs: they take
`rdFresh γ c` too, so they never see a reused context, and with unique contexts (and `MsgReadIndex`
never duplicated, a linear `rdCred`) the old queue-by-context is safe (F−). The gap is the premise. It
is stronger than v3.7 needs: v3.7's `ReadIndex` documentation does not forbid reuse, and the fixed
code handles it.

## The code path and its verification state

Source: direct inspection of the worktree (`verified.txt` was not yet produced). Each listed proof is
a `theorem` with no `sorry`/`axiom` in its file and linked in its `Link.lean`.

| Function (at the pin) | State | Spec |
|---|---|---|
| etcd `read.Read.requestCurrentIndex` (`server/etcdserver/read/read.go:148`) | verified (read `Link.lean:169`) | `Spec/go_etcd_io/etcd/server/v3/etcdserver/read/Read__requestCurrentIndex.lean` |
| etcd `read.Read.sendReadIndex` (`read.go:232`) | verified (read `Link.lean:165`) | `.../read/Read__sendReadIndex.lean` |
| raft `node.ReadIndex` (`node.go:614`) | verified | `Spec/go_etcd_io/raft/v3/node__ReadIndex.lean` |
| raft `RawNode.ReadIndex` | verified | `Spec/go_etcd_io/raft/v3/RawNode__ReadIndex.lean` |
| raft `raft.Step`/`stepLeader` (`MsgReadIndex`, `MsgHeartbeatResp`, `raft.go:1571`) | verified | `Spec/go_etcd_io/raft/v3/raft__Step.lean` |
| raft `sendMsgReadIndexResponse` (`raft.go:2138`), `bcastHeartbeat` (`raft.go:724`) | verified (raft `Link.lean:1159`) | `Spec/.../sendMsgReadIndexResponse.lean` |
| raft `readOnly.{addRequest,recvAck,AckedIndex,maybeAdvance,heartbeatCtx}` (`read_only.go:60-93`) | verified | `Spec/go_etcd_io/raft/v3/readOnly__*.lean` |

The pre-fix functions (`readOnly.advance`, `lastPendingRequestCtx`, `readIndexStatus`) do not exist
at the pin.

## The counterfactual (step 5)

What the specs promise. A `ReadState{Index: i, RequestCtx: c}` handed out by `Ready` carries
`readStateOk γ st` (`Proof/go_etcd_io/raft/v3/Protocol/GhostState.lean:1467`), i.e.
`readOk γ c i` (`:65`): `∃ Lc, readReq γ c Lc ∗ ⌜|Lc| ≤ i⌝`, where `readReq γ c Lc` (`:56`) is the
persistent registry element `c ↪[γ.reReads]□ (γq, Lc)`: `Lc` is the global committed log when the
read with context `c` was deposited. The registry has **one entry per context**, because a deposit
consumes `rdFresh γ c` (`GhostState.lean:889`, `c ↪[γ.reRdFresh] ()`), which the invariant then keeps
(`Protocol/Ghost.lean:264-266`: "a read deposit consumes and the invariant keeps, so no context is
deposited twice"; `read_deposit`, `Protocol/ReadIndex.lean:66`). The client must supply it:
`"Hfr" ∷ rdFresh γ c` (`Spec/go_etcd_io/raft/v3/RawNode__ReadIndex.lean:73`), `rdFresh γ.raft c`
(`Spec/go_etcd_io/raft/v3/node__ReadIndex.lean:58`).

**etcd's half: F+.** `Read.sendReadIndex.spec` requires `srvRdFresh γr.raft (beBytes id) ∗ srvRdCred
γr.raft` (`Spec/.../read/Read__sendReadIndex.lean:36`; `srvRdFresh` is `rdFresh`,
`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvRequest.lean:435`), and the only source of one is
`NextRequestID()` (`isReadServer`, `Proof/.../read/Inv.lean:215`), one per id, minted from the id
generator's fresh ids (`srvRdFreshInv`, `InvRequest.lean:540`). The pre-#21399 loop took one id
before `requestCurrentIndex` and called `sendReadIndex(requestID)` again on the retry timer and on
`firstCommitInTerm` with the same id. The second call needs `rdFresh γ (beBytes requestID)`, which
the first call's deposit gave to raft's invariant. Two copies of a ghost-map element are
contradictory, so the proof of `requestCurrentIndex` breaks at the first resend: the retry branch's
call to `Read.wp_sendReadIndex`. The pinned loop mints a new id per resend (`read.go:197-199`,
`211-213`), as the proof needs.

**raft's half: F− at the API (likely; a proof attempt would settle it).** With `rdFresh` and
`rdCred`, which makes a `MsgReadIndex` linear so the transport cannot duplicate it, a context enters
a leader's `readOnly` at most once in the cluster's lifetime. `addRequest` also deduplicated. Under
those premises the pre-#397 code is safe:
- a heartbeat carrying context `c` is sent only after `c` is queued (`sendMsgReadIndexResponse`, or
  `bcastHeartbeat` with the last pending context);
- an ack for `c` therefore attests leadership after every request queued before `c`;
- `readOnly` is reset at every term change, and responses of another term are filtered by term;
- empty contexts are never acked (`len(m.Context) == 0` returns early, `c078be8df:raft.go:1592`):
  that is a liveness gap, not a safety one.

So the old raft code would plausibly meet `RawNode.ReadIndex.spec`/`node.ReadIndex.spec`/
`raft.Step.spec`. The internal refinement would differ, since today's `HbCtxOk` and `rqRecOk` are
stated over positions (`Protocol/Model.lean:232`). The stale read needs a reused context, which the
premise rules out. That is upstream's own rule on release-3.6 (#398), but **not** v3.7's
documentation: `node.go:218-223` at the pin says only that "it is user's job to ensure read index
retries", and v3.7's code is correct under reuse.

Secondary class for raft's half, as a C analysis of the F− gap: **C-scope**. The read-index
guarantee is proved only for clients that never reuse a context (and a transport that never
duplicates `MsgReadIndex`). The issue's stated property, "the `Index` includes everything committed
when its `RequestCtx` was *first* created", is about clients that do reuse contexts. Not a bug in
this repository's specs: `rdFresh` is a sound premise that the pinned etcd discharges. But it is a
premise the v3.7 API does not state.

## Proposal

**Slug `readindex-ctx-reuse`**: drop `rdFresh` from raft's read-index specs, so that a context may
be deposited any number of times and the guarantee is per first deposit.

Statement sketch:
- `RawNode.ReadIndex.spec`/`node.ReadIndex.spec` without `"Hfr" ∷ rdFresh γ c`;
- `read_deposit` becomes `raftCommitInv γ -∗ readAu γ Qr -∗ isCommitted γ L0 ={⊤}=∗ ∃ Lc,
  readReq γ c Lc ∗ (⌜L0 <+: Lc⌝ ∗ isRead γ c Qr ∨ ⌜Lc <+: Lnow⌝)`: the second branch is for a context
  already registered, returning its existing record (the first deposit's `Lc`, a prefix of the log
  at the resend) and no new update handle;
- `readOk`/`readStateOk` unchanged: still `|Lc_first| ≤ i`.

The old raft code fails this statement in the issue's trace. `B`'s context is fresh, `B`'s
`ReadState` index is below `|Lc_B|`, and `readStateOk` for `B` cannot be established at `advance`:
the acks are for an earlier `A`, sent before `B` was queued.

Optionally, let `rdCred` be duplicable on `MsgReadIndex`, so that the transport may duplicate a read
request. #398 calls that a bug for UDP transports; with #397 it is harmless. The credits bound the
positions, so a position budget would replace them.

Cost: small to medium, in the protocol ghost layer only. That is `read_deposit`'s second case and the
`reReads` registry's agreement on a resent context, plus `isRead`/`read_collect` for a handle per
context. The code-level refinement already keys requests by position. Each request record's "read at
the commit index at arrival" implies `|Lc_first| ≤ i`, because arrival follows the first deposit.
etcd's read loop would keep minting fresh ids, which it still does, and lose nothing. Pays off as a
statement that the v3.7 raft is linearizable for any `ReadIndex` client, including one that retries
as pre-#21399 etcd did.

## Findings

- No `issues/` file: the bug is not in the pinned code (both fixes are ancestors of the pins).
  `issues/raft-readindex-singleton-stale.md` already links etcd-io/raft#392/#397/#398 as related but
  different, which is correct: that one is the `IsSingleton` shortcut, still present in v3.7.0 and
  fixed in the fork.
- No bug in this repository's specs. Remark for `notes/`, for the coordinator: the `rdFresh` premise
  of `RawNode.ReadIndex`/`node.ReadIndex` is stronger than v3.7's documented contract (no rule
  against reusing `rctx` at the pin's `node.go:218-223`); see the proposal.
