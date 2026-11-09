# Brief: a reviewer of a batch

You judge one batch (`notes/specs-only/batches.md`) of the specs-only branch, in the worktree
`/home/ubuntu/etcd-grove/.claude/worktrees/specs-only`. You did not write it, and you judge it
without the author's conclusions: read the specs, the Go code and the users yourself. Read-only,
except your report. Read `notes/specs-only/README.md` (what a spec is here, the snippets, the review)
and `.claude/skills/spec/PRINCIPLES.md` (the hard rules and preferences) first. The batch's files:
`Spec/<its packages>/`, `examples/specreq/<its aliases>/`, its report `notes/specs-only/batch-<id>.md`.
Go sources: `.lake/src/...`; old specs and notes: `/home/ubuntu/etcd-grove/.claude/worktrees/specs-ref`.

Your kind is given in your prompt.

## Provability

1. **Snippets provable.** For each snippet: under its stated assumptions, is it provably panic-free
   from the batch's specs and laws (and the specs of other packages it calls)? Sketch the proof:
   which spec at each call, what the caller would hold (an invariant over the opaque resources, the
   atomic update it passes and how it fires), which law turns the post into the fact the `panic`
   guard needs. A snippet you cannot prove is a finding (the spec is too weak, or the snippet
   assumes something nothing gives).
2. **Specs sound.** For each spec, against the Go code: no panic, hang or out-of-bounds under its
   pre; its post holds on every path, errors included; an atomic update fires exactly once, at a
   point where the abstract state really changes (or is really read); a persistent resource is
   really duplicable; a resource given back is really free. Check every premise is needed and that
   none is false of some input a caller passes.
3. **Sketches plausible.** Each proof sketch: every resource it uses has a source (the pre, a
   callee's post, an invariant whose content is stated), the realization of each opaque predicate in
   the vocabulary's header can satisfy every spec and law at once (find two specs whose realizations
   conflict), and the callees' needs written in `notes/specs-only/req/` (or the callee specs, if they
   exist) suffice.
4. **Not vacuous**: a law family that holds with every predicate read as `True` says nothing; a
   disjunct that always holds; a parameter only in the pre.

## Completeness

1. **Users.** Find every use of the batch's API outside the batch (the pinned etcd and raft sources,
   `examples/`, the Kubernetes code under `/home/ubuntu/go/pkg/mod/k8s.io/` and `Code/k8s_io`), not
   only those the author lists. Group them into patterns: what each relies on (a returned value's
   meaning, an error's meaning, ordering, exclusivity, concurrency, durability, what it may do with
   the result afterwards).
2. **Covered.** Each pattern is covered by a snippet that relies on the same thing (one snippet per
   pattern is enough). List the uncovered patterns, each with a call site.
3. **Establishable, sufficient.** For a sample of real call sites, one per pattern: the caller can
   establish the spec's pre with the values it actually passes (its context, options, its own state),
   and the post gives what it needs next.
4. **Relaxable.** Premises or restrictions that a user's real call violates or that the code does
   not need.

## Locality and abstraction (both kinds, briefly)

Specs over more than their footprint; implementation vocabulary in a client-facing statement; a
predicate a client would have to unfold (a missing law); a spec family where one general spec would
do.

## Report

`notes/specs-only/reviews/<batch>-<provability|completeness>-<round>.md`: findings ranked, first
tier (a hard rule broken: unsound, a user not served, a snippet unprovable) apart from the rest;
each with the file, the Go code or call site that shows it, and a suggested fix. Then a short
verdict. Your final message: the first-tier findings, one line each, and the verdict.
