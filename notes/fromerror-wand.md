---
title: status.FromError.wp_proof's post wand pins errDesc to a message proved after the call (false)
found: 2026-11-18
by: etcd-grove-03's attack on incomingof's T8 (notes/axiom-review/incomingof-b.md, "T8'")
blocks-proof: no (no proof used the wand: every caller dropped the conjunct; the restated spec's callers fix m at the call)
status: fixed in incomingof Part B (branch incomingof-scope): m a parameter, errorMsgIs in the precondition, no wand in the post
---
# `status.FromError.wp_proof`'s last conjunct is false

A bug in this repository's trust base, not in grpc. Since fromerror-stable (2026-11-06) the axiom's
post ended with
```lean
□ (∀ (e : GoInterfaceOk) (m : GoString), ⌜ok = false ∧ err = GoInterface.ok e⌝ →
  errorMsgIs e m -∗ ⌜errDesc err = m⌝)
```
a persistent wand, usable at any later time. `errorMsgIs e m` is a partial-correctness WP ("each call
of `Error()` returns `m` or does not return"): an `Error()` that starts diverging after `FromError`
returned satisfies `errorMsgIs e m` for **every** `m`. Applying the wand to `errorMsgIs e "B"` and
`errorMsgIs e "C"`, both provable after the switch, gives `"B" = "C"`, i.e. `False`, so any code after
the call (a `panic`) is proved unreachable.

Go: `examples/axiomcx/fromerrorflip` (`TestFlip`; grpc v1.84.0, go1.27.3): `flipErr.Error()` returns
`"A"` while a flag is on and loops once it is off; `FromError` returns `ok=false` (message `"A"`), the
flag is switched, and `Main` panics.

**What was true.** At the call, the precondition `statusErrOk err` gives some `m` that `Error()`
stably returns; `FromError` calls `Error()` during the call, so its description is that `m`. What was
wrong is only that the post let the caller choose `m` later.

**Fix (the user's decision, 2026-11-18, via etcd-grove-03).** `status.FromError.spec` takes `m` as a
parameter, with `∀ e, ⌜err = ok e⌝ → errorMsgIs e m` in the precondition and `⌜ok = false → errDesc err
= m⌝` in the post (no wand); likewise `rpctypes.ErrorDesc`, `rpctypes.Error` and `ContextError` take
`m`; no post restates the wand. The `errorMsgIs` docstring now says a partial-correctness WP does not
pin `m` against later divergence.

**Reach.** Every result resting on `status.FromError.wp_proof` (collections listing it: the client's,
k8s's, the examples'); no proof applied the wand (all destructured it as `-`), so no result is known to
depend on the false part.
