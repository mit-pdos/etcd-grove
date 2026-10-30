---
name: progressive-verification
description: Formally specify and verify one Go function of etcd or raft (or a PR's few changed functions) in this repository, over the specs of its callees, with assumed specs at the trust boundary where a callee has none. Use when asked to verify a single function whose callers already have specs; a new slice or stage of work goes through the spec-first plan instead.
---

# Verifying a function progressively

**The idea** (`paper.pdf`, background: verifying chosen etcd functions with concurrent separation
logic, without verifying the whole system): verify one function at a time. Its callees are used
through their specs: proved, unfinished (`sorry`) or assumed (a trust-boundary axiom). The callees
need not be verified first, and the function's spec is useful to its callers before they are.

**When this skill fits.** One function, or the few a PR changes (`etcd-pr-verify` uses this skill),
whose callers already have specs, so that the spec's clients exist. For a new slice, a new package,
or a stage that widens proved code (a new mode, a feature through the server), use the steps of
`notes/spec-first-plan.md` (Scope, Draft, Review, Test, Probe, Freeze, Prove). They draft every spec
of the slice and its callers' glue before any expensive proof. A single function's spec, written from
the function alone, is what most later revisions changed: in the plan's study of 64 spec revisions,
23 were a caller needing more and 20 a case the spec had excluded.

**The steps.**

1. **Understand the function**: its Go code (`Code/` is the translation, `.lake/go-src/<project>`
   the source at the pinned revision), its callers in Go and their proofs, the shared state it
   touches, and its concurrency: locks, channels, goroutines, contexts.
2. **Its callees**: reuse their specs (`Spec/<pkg>/<fn>.lean`) and the package's invariants
   (`Inv*`). For a callee with no spec, write an assumed spec in the existing style (`axiom
   <fn>.wp_proof` in `Proof/<pkg>/<fn>.lean`). It is part of the trust base: true of the callee's Go
   code or documented behavior, including when it panics. A Perennial or standard-library gap
   follows CLAUDE.md, "Changes to Perennial".
3. **The spec**, with the `spec` skill: its `PRINCIPLES.md` (the hard rules: sound, complete for
   every caller, local, faithful to concurrency, no unneeded premise, one spec per function) and its
   examples. Before proving, check the spec against each existing caller: the caller can give the
   precondition and its proof gets what it needs from the postcondition. Prove the callers whose
   bodies only thread state, if they are short: a missing frame or a too-weak postcondition shows
   there first. Mode variants and special cases are instances of the one spec (a mode is part of the
   state), never a second spec beside it; a change that would start such a family, or change a
   trusted statement, goes to the user first (`notes/spec-first-plan.md`, "Who decides").
4. **Review before proving**: a fresh `spec-reviewer` agent on the spec, the assumed specs and the
   invariants, given the Go code and the callers, not your conclusions. It checks soundness (above
   all of the assumed specs, under concurrency) and whether the spec captures the function's
   intended behavior for its callers. After every repair, a new round looking hardest at what the
   repair changed: repairs introduce defects.
5. **Prove** (`Proof/<pkg>/<fn>.lean`, `etc/lean-check.py` for the edit loop; Perennial's
   `docs/PERENNIAL_PROOF_TUTORIAL.md` and `PERENNIAL_PROOF_REFERENCE.md`). A proof left unfinished is
   a `sorry`, reported as such: that is progressive, not a failure. A spec the proof shows wrong goes
   back to step 3 and to the reviewer.
6. **Link and check**: add the function to its link list and regenerate `Link.lean`
   (`etc/gen-link.py`); `lake build`, `etc/tcb-report.py --check`, the interfaces
   (`etc/gen-interface.py`). CLAUDE.md's rules hold throughout: the layout, modules, package APIs,
   `issues/` for a bug found in the Go code, no change to Perennial for one proof.
