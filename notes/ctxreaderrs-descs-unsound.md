---
title: ContextReadErrs.descs (the premise Hctx of 50 closed results) makes them silent past v3rpc's initialization
found: 2026-11-17
by: the ctx-descs review (etcd-grove-03's agent), notes/axiom-review/ctx-descs.md, branch axiom/ctx-descs
blocks-proof: no (every closed etcd theorem takes it; their statements say nothing past v3rpc's initialization until the fix)
status: fixed in incomingof Part B (branch incomingof-scope, 2026-11-18): the `Canceled` half deleted (and later `descDeadline`), users take `Error()`'s message per run (`ctxErrsErr`'s `ctxErrMsg`); notes/axiom-review/incomingof-b.md
---
# `ContextReadErrs.descs` is unsound as a premise

A bug in this repository's specs, not in etcd.

`EtcdGrove.ContextReadErrs.descs` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/read/Init.lean:82`)
is an entailment `isPkgInit context ⊢ (∃ e, Canceled ↦□ e ∗ ⌜errDesc e = "context canceled"⌝) ∗
(∃ d, DeadlineExceeded ↦□ d ∗ ⌜errDesc d = "context deadline exceeded"⌝)`. Its docstring argues per
execution, but an entailment from persistent points-to cells holds in every heap that has those
cells (`crossWorld`, proved on `axiom/ctx-descs`): the `Canceled` half then says that every
`*errors.errorString`, at every location, describes `"context canceled"`. With the trust-base axiom
`v3rpc.toGRPCErrorMap_init`, which gives mvcc's `ErrFutureRev` (also an `*errorString`) its own
description, the call v3rpc's initializer makes has postcondition `False`
(`toGRPCErrorMap_init_diverges`, proved from step 1, which is argued). Not `False` in Lean: the
axiom's post is per execution.

**Reach.** The 50 `Results`/`Adequacy` files that take `Hctx : ∀ hG, ContextReadErrs (heapAt hG
lctx)` (every closed etcd theorem: putget*, auth*, lease*, watch, compacted, compactwatch, cache,
partition, restart*, txnlin*, k8s compactor, k8s etcd3): each initializes v3rpc, so each says nothing
about an execution past that point. The `DeadlineExceeded` half is sound (a location-free value).

**Fix (direction approved, not applied).** Delete the `Canceled` half; state the `DeadlineExceeded`
half as a pure location-free fact; get the facts per run: v3rpc's from `toGRPCErrorMap_init`'s own
conjuncts, the client's by making grpc's `ctxErrsErr` conjunct `errDesc err ∉ handlerDescs` per run
(`errorMsgIs` of a message outside `handlerDescs`, `errDesc` from `FromError`'s wand where the error is
converted). The client side needs trust-model text (`notes/soundness-1117-handoff.md`, B1), hence a
Scope.
