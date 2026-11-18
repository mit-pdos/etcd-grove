---
title: incomingOf_cancelCtx and incomingOf_cancellableContext make metadata.incomingOf constant
found: 2026-11-17
by: the ctx-descs review (etcd-grove-03's agent), notes/axiom-review/ctx-descs.md, branch axiom/ctx-descs
blocks-proof: no (22 collections list incomingOf_cancelCtx; refuted in meaning)
status: open; the incomingof Scope's Part A (per-run guard) was refuted and not linked (2026-11-17, notes/axiom-review/incomingof.md); fix: the per-heap redesign, its own Scope (user, 2026-11-17)
---
# `incomingOf_cancelCtx` is false in meaning

A bug in this repository's trust base, not in grpc.

`EtcdGrove.incomingOf_cancelCtx` (`grpc/metadata/Incoming.lean:61`) is the entailment `ctxField c ↦□
p ⊢ ⌜incomingOf (*cancelCtx c) = incomingOf p⌝`. An entailment from one persistent points-to holds in
every heap: applied in a world with `ctxField c ↦□ p1` and in one with `↦□ p2`, it gives
`incomingOf p1 = incomingOf p2` for every two interfaces (`incomingOf_const`, proved on
`axiom/ctx-descs`, axioms: Lean's three and this one). Not `False` in Lean, but in a run that makes
two contexts with different metadata, `FromIncomingContext.spec`'s post and `incomingOf_const` give
`False`. `v3rpc.incomingOf_cancellableContext` (`v3rpc/WrapperMd.lean:76`) has the same shape (not
formalized).

**Reach.** The 22 collections that list it (auth, putget, lease, watch, txnlin, k8s etcd3 among
them).

**Fix.** State it per execution (a law inside the post of the spec that makes the context, or
`incomingOf` behind a ghost name): the incomingOf Scope. Its Part A (the law as a persistent wand
`incomingKept` delivered by grpc's `srvRawStreamIs`, the v3rpc axiom guarded by it) was refuted on
2026-11-17: a fresh world owning a persistent authoritative heap (`Auth DFrac.discard σ`) satisfies the
wand by its choice of `σ` (`notes/axiom-review/incomingof.md`, Go: `examples/axiomcx/incomingof-attack`
`TestWrappersNotConstant`). The user decided: not linked; the fix is a per-heap relation (`incomingIs` as
an IProp, and the `errDesc` analogue), in its own Scope.
