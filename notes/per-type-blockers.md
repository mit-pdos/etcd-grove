---
title: grpc.serve's handler pool is the caller's choice; pbEnc is keyed by address, not content
found: 2026-11-07
by: the per-type Scope's review (etcd-grove-82's workflow), compiled by etcd-grove-c9
blocks-proof: yes
status: open; both are fixed in the per-type stage (the user's decision via etcd-grove-82, 2026-11-07)
---
# Two blockers of the per-type stage: `grpc.serve`'s pool and `pbEnc`'s key

Both are bugs in our trust base, not in grpc, protobuf-go or etcd, and both are false at the
**genuine** message models. So the per-type registry alone fixes neither (`notes/pbenc-ok-inconsistent.md`,
`notes/grpc-msg-models.md`). The review is `notes/axiom-review/per-type-blockers.md`.

## (a) `grpc.serve`'s handler pool is the caller's choice

**The claim.** `grpc.serve` (`Proof/google_golang_org/grpc/InvGrpc.lean:961`) and `grpc.serveStream`
(`InvGrpcStream.lean`) take a resource `S` and a copy count `n`, both picked by the caller. The pool
is `[∗list] _ ∈ List.replicate n (), S`, and `S` is in the precondition of each handler's triple
(`grpcMethodOkMd`).

**Why it is false.**

- At `S := ⌜False⌝` and `n := 0`, every handler meets every spec vacuously.
- More generally, any `n` below grpc-go's real concurrency claims that at most `n` handlers run at
  once, which grpc does not ensure.

**The derivation.** Branch `axiom/grpc-serve-pool`, commit `1ad2cc63a0`, at the genuine
`pbCompactionRequest`/`pbCompactionResponse`:

- `anyHandler_ok`: any handler, a panicking one included, meets `grpcMethodOkMd … ⌜False⌝ Spec`.
  It uses no axiom.
- `served_call_fails`: `conn.Invoke` is proved to return a non-nil error, from `grpc.serve … ⌜False⌝ 0`
  and `ClientConn.Invoke.wp_proof`. grpc-go returns success.
- `anyStreamHandler_ok`: the same for streams, at `pbWatchRequest`/`pbWatchResponse`.

**Reach:** 71 linked results, 42 exported, 17 `*_safe`.

**The fix**, in the per-type stage: tie the pool to threadTok and adequacy's thread bound
(`notes/bounds-plan.md`), so that the caller chooses neither `n` nor `S`.

## (b) `pbEnc` is keyed by address, not content

**The claim.** `opaque pbEnc (ty : go.GoType) (l : Loc) : List w8` (`InvProto.lean:73`) is one
global function. `pbEnc_ok` holds in every ghost world.

**Why it is false.** Two worlds holding different frozen entries at the same address `l` force
`pbEnc ty l` to encode both.

**The derivation.** Branch `axiom/pbenc-heaps`, commit `0d40894e13`, at the genuine `pbEntry`:

- `world_decode`: each world is built from Iris's soundness with Perennial's `goose_init`, from an
  empty heap. The fields of `l` are allocated with `na_heap_alloc` and made persistent, and `pbMsg`
  comes from `inv_alloc_open`. That gives `entDecode (pbEnc raftpb.Entry.ty l) = some (entWith d)`.
- `pbEnc_heaps_false`: worlds with `d = []` and `d = [1]` give `False`.
- `#print axioms` is Lean's three plus `pbEnc_ok` only.

The theorem ranges over the ambient semantics instances, as every result here does: Lean has no
concrete `go.Semantics`. It also takes layout hypotheses: `l`'s field addresses distinct and in
range, which Go's real layout satisfies.

**Reach:** as `pbEnc_ok`'s, 40 exported results and all 17 `*_safe` (`notes/pbenc-ok-inconsistent.md`).

**The fix**, in the per-type stage: key the encoding on the frozen wire content (the model plus the
unknown fields), not on the address. Derive `pbEnc_ok` from one `_sat` axiom per registered type.

## `UnmarshalPb` at `pbMessage` claims a decoded `ConfState` has no unknown fields (found 2026-11-07, stage A Draft CP1)

**The false statement.** `proto.UnmarshalPb.spec` (`Spec/google_golang_org/protobuf/proto/UnmarshalPb.lean:30-37`),
at the genuine `pbMessage` (`rafthttp/PbMessage.lean:78`), gives a successful decode the post
`T.dec l m`. That is `msgPtsC l (own 1) (own 1) true m`, and its snapshot's `ConfState` is owned
through `csPts`, which fixes the `ConfState`'s unknown fields to `[]` (`raft/v3/InvPb.lean`).

Go's decoder succeeds on peer bytes whose snapshot `ConfState` carries an unknown field, and it
keeps that field. So the post is false of such bytes. This is the trusted fact behind
`messageDecoder.decodeLimit`, `pipelineHandler.ServeHTTP` and `msgAppV2Decoder.decode`.

**What it allows.** The Go consequence is `nonissues/raft-confstate-unknown-fields-panic.md`:
- `ConfState.Equivalent` compares unknown fields;
- the follower that restores such a snapshot panics;
- `csPts`'s "no unknown fields" is what lets raft's restore proof skip that panic.

That nonissue's "Proof: no" holds for raft's API, whose callers build the `ConfState`. It does not
hold for the receive path's trusted decoder spec, which hands a peer's bytes to raft.

**Reach.** It is subsumed today: every result that reaches these decoders already rests on the
inconsistent `pbEnc_ok` and the refuted generic `*Pb` specs (the sections above), so it adds no new
vacuity. It is recorded so that the per-type stage does not carry it over.

**The fix (stage A Draft, branch `per-type-models`).**
- `pbMessageC`'s content `MsgC` has the `ConfState`'s unknown fields at their level
  (`PerTypeMessage.lean`).
- The bridge to today's ownership, `msgRoC_msgOwn`, takes `c.csUfNil`.
- On the receive path, `csUfNil` comes from the sender's content, not from the decoder. The
  sender is raft, which builds the `ConfState` with `csPts` (no unknown fields), and `D2` (decoding
  `enc c` gives `c` back exactly) carries it to the receiver. This is the same route as
  `resps = []` (raft-entsize r3 [r3b]).
- A message from outside the cluster is not covered, as today: peers are trusted.
- **Corrected at the re-freeze (2026-11-09; the first Freeze package did not fix it).** The
  content-level fix never reached the decoder's post, which handed back `dec` at the model, i.e.
  `msgPtsC` with `csPts`' `uf = []`. Now `PbModelC` has `decOk` (`MsgC.csUfNil` for `Message`),
  `proto.UnmarshalPb`/`ClonePb` give `⌜decOk c⌝ -∗ dec l (modelOf c)`, and the receivers get
  `decOk` from the sender's frame (`MsgEnc` carries `csUfNil`) through `D2`. The same review found
  that `Message`'s D1 `wire` claimed `resps = []` (Go decodes `Responses`, field 14): `wire` is now
  `MsgDecOk` (`msgDecode bs = some (wireOf st)`), and `resps = []` comes from the sender through
  `D2`. Review: `/shared/tmp/pertype-stageA-freeze-review.md`; checked by the D1 harness
  (`72 00` decodes with one response; `4a 08 12 06 0a 04 08 01 30 00` has `decOk` false).
