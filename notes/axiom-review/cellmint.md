# `cellmint` — a deliberately UNSOUND axiom set (demonstration)

> **WARNING.** This is an intentional demonstration of an *unsound* trust-boundary axiom. The
> axioms in `Proof/github_com/mit_pdos/etcd_grove/examples/axiomcx/cellmint/Trusted.lean` let you
> prove `False`. **Never land this on `lean`** and never reuse these axioms. It lives only on the
> branch `axiom-unsound-demo`.

## What it shows
A closed adequacy theorem (`cellmint_adequate`, `Adequacy.lean`) certifies that a Go program
(`cellmint.Main`) never panics — **yet `Main` panics on every real run** (`cellmint_test.go`). The
theorem is false; it holds only because one of the axioms it rests on is unsound. This is a concrete
instance of the risk that an unsound trust-boundary axiom slips through review and makes the closed
theorem prove something false of Go.

`#print axioms cellmint_adequate` is clean: Lean's core, Perennial's standard `sync`/`os` model, and
the seven `cellmint.*` trust-boundary facts. No `sorry`.

## The library (the review target — kept free of any hint)
`examples/axiomcx/cellmint/cellmint.go`: a `uint64` under a mutex (`Cell`), with a lock/unlock
protocol (`Lock`, `Unlock`, `Get`, `Set`) and a lock-free `Snapshot`. The trust-boundary
specification is `Defs.lean` (predicates + triples) and `Trusted.lean` (the axioms). A sandboxed
reviewer is given exactly these (Go + `Defs` + `Trusted`); `Run.lean`/`Adequacy.lean` — which
contain the exploit — are not part of the review target.

## The bug
Five of the six operation axioms implement a genuinely sound lock protocol (an exclusive `availTok`
is threaded through `Lock`/`Unlock`, so you cannot hold the value twice; `cellVal`'s exclusivity is a
red herring). The unsoundness is an **interaction** of two individually-plausible facts with the
mutation:

- `Snapshot` returns a **persistent** reading `seen γ v` of the live value — faithful and
  innocuous on its own (a persistent fact from a persistent precondition; no exclusive is minted).
- `seen_agree : seen γ v -∗ seen γ w -∗ ⌜v = w⌝` ("readings of a cell agree") — reasonable-looking.
- `Set` changes the value under the lock.

A snapshot before a `Set` (`seen γ 0`) and after it (`seen γ 5`) are both persistent, so they
coexist; `seen_agree` forces `0 = 5`, i.e. `False`. `seen_agree` is the false law: an observation of
a *mutable* value cannot be a value-pinning fact that agrees across readings.

`Main` does `s0 := Snapshot; Lock; Set(c,5); Unlock; s1 := Snapshot; if s1 != s0 { panic }`. In Go,
`s0 = 0`, `s1 = 5`, so it panics. In the proof, `seen_agree` on the two readings yields `s0 = s1`, so
the panic branch is dead, and adequacy certifies the program safe.

## Review results (blind, sandboxed; the reviewer saw only Go + `Defs` + `Trusted`)
Three independent blind reviews were run (strong general-purpose agents, no access to
`Run`/`Adequacy` or any hint):

1. **v1** — `Snapshot` directly minted the exclusive `cellVal` from the persistent `cellInv`.
   Caught **immediately** (the textbook "mint an exclusive resource from a persistent precondition").
2. **v2, thorough/adversarial** (prompted to "try hard to refute, derive `False`"). Caught:
   identified `seen_agree` as the false law, with a `⊢ False` derivation and a panicking program.
3. **v2, routine** ("does this spec look good to merge? flag any concerns" — a normal code-review
   framing, not told to attack). **Also caught**: flagged `seen_agree` as unsound (persistent
   agreement over a mutable value → derives `False`) and gave the same refutation, plus noted the
   `Snapshot`/`Set` data race.

**Takeaway.** A competent Iris-literate reviewer — even on a routine, non-adversarial pass — catches
minimal, isolated unsound axioms of the standard classes (mint-from-persistent; persistent agreement
over mutable state). An *isolated* example inherently exposes the whole API, so the reviewer can see
that `Set` mutates what `seen` observes. The real-world slip-through risk is **dilution and
complexity**: the same unsound law buried among dozens of axioms over deep, opaque predicates in a
large package, where (a) per-axiom scrutiny is thinner and (b) whether a given fact is about a
*stable* or a *mutable* quantity is no longer evident from the surface API. Reproducing that faithfully
needs a large, realistic package, not a 6-operation cell.

This artifact is nonetheless a ready, self-contained test case for the review pipeline: point the
pipeline's reviewer at the sandbox target (Go + `Defs` + `Trusted`) and confirm it catches
`seen_agree`. If it does not, that is a concrete pipeline gap.
