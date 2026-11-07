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
