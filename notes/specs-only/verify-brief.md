# Brief: the verification round (2026-11-09)

The user's acceptance test for the specs-only branch, run once on the final state:

> An agent given a batch of related specs and the Go snippets agrees that the snippets are
> provable (panic-free) from the specs, and can come up with a proof plan for each spec on top of
> the lower-level specs. An agent that scans over the users of that API agrees that the snippets
> capture every aspect the callers rely on, and that the specs are strong enough for them.

You are one of two reviewers of one area (your prompt names it and your kind). You are independent:
you did not write these specs, and you judge them **without the authors' conclusions**: do not read
`notes/specs-only/batch-*.md`, `integration-*.md`, `open-questions.md` or `reviews/` until you have
written your own findings; afterwards you may read them only to check whether a finding is already a
recorded open decision (then mark it so; it still counts). Read-only, except your report.

Read first: `notes/specs-only/README.md` (what a spec is here, the snippets) and
`.claude/skills/spec/PRINCIPLES.md` (the hard rules). Worktree:
`/home/ubuntu/etcd-grove/.claude/worktrees/specs-only`. Go sources: `.lake/src/{client,server,api,pkg,
cache,raft,bbolt}`; examples and Kubernetes users as in `notes/specs-only/review-brief.md`.

## Provability kind

For **every** spec file in your area (not a sample):
1. **Proof plan.** Write a short proof plan from the specs the function's Go body calls, *as they
   are now*: which callee spec at each call, the resources held between calls and where each comes
   from (pre, a callee's post, an invariant whose content the vocabulary's header states), the
   linearization point of an atomic update, what a loop or goroutine carries. A spec passes if
   every step closes; it fails if a premise has no source, a post is too weak for the next step, a
   cited law or name does not exist, or the spec is false of the code (a panic or path its pre
   admits, a post some path violates). For trivial helpers one line suffices; batch them.
2. **Snippets.** For every snippet in your area's `examples/specreq/` packages: is it provably
   panic-free from the specs under its stated assumptions? Sketch the proof.
3. **Laws.** Every law (`... .spec : Prop` that is not a function's triple): plausible from the
   stated realization, and not making the vocabulary vacuous.

## Completeness kind

1. **Users.** Find every use of your area's API outside it (pinned etcd/raft/bbolt sources, the
   examples, Kubernetes), classify into patterns, and for each pattern check: a snippet relies on
   the same thing; at one real call site, the caller can establish the pre with what it holds and
   the post gives what it needs next.
2. **Callers' specs.** Where a caller in this repository has a spec (another area's), check the
   caller's proof sketch's use of your area's spec actually fits (names exist, premises
   establishable, posts sufficient).
3. **Coverage.** Every function with a spec in the old tree
   (`/home/ubuntu/etcd-grove/.claude/worktrees/specs-ref/Spec/<pkg>/`) has one here.

## Report

`notes/specs-only/verify/<area>-<provability|completeness>.md`:
- a **verdict per batch** in your area: PASS (every spec/snippet/user closes), PASS WITH OPEN
  DECISIONS (closes except where a recorded user decision is pending — name it), or FAIL;
- for FAIL, the **first-tier findings**: file, the step that does not close (or the user not
  served), the evidence (Go line, spec line), a suggested fix;
- counts: specs checked, snippets checked, users checked; how many close.

Final message: the verdict per batch and the first-tier findings, one line each.
