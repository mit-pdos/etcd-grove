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
- A first version where `Snapshot` directly minted the exclusive `cellVal` from the persistent
  `cellInv` was caught **immediately** (the textbook "mint an exclusive resource from a persistent
  precondition").
- This interaction version was also caught by a **thorough, refutation-focused** review (prompted to
  "try hard"): the reviewer identified `seen_agree` as the false law by a clean semantic argument
  (a persistent observation of mutable state cannot entail agreement) and gave both a `⊢ False`
  derivation and a panicking Go program.

**Takeaway.** A route-(b)-capable ("can you derive `False`?") review that follows the axiom-skill
methodology thoroughly catches minimal, isolated unsound axioms of this kind. The practical danger is
*dilution*: the same unsound law buried among dozens of axioms in a large, complex package, where
per-axiom scrutiny is thinner. This example is a ready test case for the review pipeline — run the
pipeline's reviewer against the sandbox target (Go + `Defs` + `Trusted`) and see whether it catches
`seen_agree`.
