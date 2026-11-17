# Trace-check goal (for `/goal`)

**Goal:** complete trace-check's closed theorem against the corrected `etcdraft.tla`
(`etc/tla-fixes/`, twelve patches), per `notes/trace-validation-plan.md` and
`notes/spec-first-plan.md`, on branch `trace-check`:

> `raft_tracecheck_safe`: no execution of the tracecheck package's initialization then `Main()`
> (`RunConcurrent(DefaultCConfig)`, `ConvertEvents`, `NewTrace`, `CheckTrace(tr, true)`, panic
> unless `TLCOK`) panics,

with the corollary that every run's trace satisfies `TraceAccepts` (`CheckTraceRel`, TLC's
deterministic verdict, the invariants of `Traceetcdraft.cfg`).

## Order of work

Each piece committed as it lands:

1. **Q6 in Lean**, every traced-only item gated on `γ.raft.reTrace`: `StartNode`'s
   `isTraceLogger`, the message tokens with both halves (at most once, after the sender's
   `Ready`), the refused calls, `storBnd`, the traced allocation. Each step passes the acceptance
   test below.
2. **S5** (layer B): `simInv`, the hooks' non-nil specs carrying the simulation through raft's
   internals, determinism, the invariants through `R`.
3. **S6** (layer C): every action's spec and proof, `StepLine`/`CheckTrace` against
   `CheckTraceRel`.
4. **S7** (layer D): the harness, `Main`, adequacy, `Results.lean`, a tcb collection.

Draft before proof; fresh `spec-reviewer` rounds until nothing is first-tier; then the freeze
(tag `trace-check-frozen`, under the delegation the plan records); then Prove.

## Acceptance test (after every statement change)

- `lake build` green;
- every existing closed theorem's statement unchanged and still proved;
- `etc/tcb-report.py --check` (and its collections) unchanged, except where an entry says why;
- `interface/` differs only by gated additions and the pure fact `γ.raft.reTrace = none`;
- `etc/goose.py --check` and the tracecheck Go tests (with and without `with_tla`) pass.

## Standing rules

- Never push or post anything.
- Commit on `trace-check` as Joseph Tassarotti <jt4767@nyu.edu>, with the trailer
  `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.
- No new axiom, model assumption or `sorry` in the final result, and no change to the closed
  statement beyond this goal, without the user.
- A question that is the user's: record it in the plan's "Questions for the user" with its options
  and a recommendation, take the recommendation where the plan allows (marked pending the user's
  veto), and keep going on work that does not depend on it.
- A bug found in raft's Go code, in `etcdraft.tla`, or in the transcriptions: write it up
  (`issues/`, `nonissues/` or `notes/`, as `CLAUDE.md` says), work around it within these rules,
  and keep going.
- Keep `notes/STATUS.md` and the plan current.

## Exit criterion

Either:

- **(a) done:** `raft_tracecheck_safe` and the corollary are stated in
  `Proof/github_com/mit_pdos/etcd_grove/examples/raft/tracecheck/Results.lean` and proved;
  `#print axioms` shows only the trust base's existing axioms; the acceptance test passes; the plan
  says "done"; and a summary is reported. Or
- **(b) blocked:** every remaining path to (a) needs something only the user can give (a push, a
  trust-base change, a change to the closed statement, or a decision the plan does not let the
  agent take), each such question is recorded in the plan with its options and a recommendation,
  and they are reported.

Running out of context, a slow build, a failing proof, or a long remaining list is not an exit:
continue.
