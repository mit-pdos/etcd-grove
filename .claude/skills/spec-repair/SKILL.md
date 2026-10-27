---
name: spec-repair
description: Review a Go function's spec in this repository and make it better — or write one where none exists — judging it as its clients and a reader of `interface/` see it; then repair what the review finds and re-prove. Use when asked to review, critique, improve, fix or write a spec (a Hoare triple, or the predicates and laws a package exports). `--review-only` stops after the review.
---

# Reviewing and repairing a spec

**Goal:** the spec of the target (a function, or a predicate and the specs that mention it) is the
best contract its clients can have: true of the Go code, as strong as the code allows and its clients
need, stated in abstract terms, with the laws its clients need, and readable in `interface/`. Start
from whatever exists, including nothing. How to get there is up to you. Read `LESSONS.md` first.

**Review.** Spawn a fresh `spec-reviewer` agent (`.claude/agents/spec-reviewer.md`: the rubric, the
metrics, the failure patterns past reviews found, the report's form; it reads `LESSONS.md` itself).
Give it the targets (the `interface/` files; where the package has none, the spec file and the
definitions it names), the Go source and the clients (call sites and their proofs or contracts), but
not your conclusions. Ask it where the contract is wrong, weak, too strong,
leaky or unusable. Check its findings against the source before acting on them. Look at least for:

- a claim the Go code does not support, or one it supports but the spec omits;
- a premise that is neither a real precondition of the Go code nor a stated, filed scope restriction
  (`issues/`, CLAUDE.md "Issues in the verified code");
- implementation detail in the statement: ghost names, fractions, internal records or fields;
- a client that unfolds the spec's predicates or opens the package's invariants: a missing law;
- a spec that no client uses;
- a statement that `interface/` does not show in full or that hides behind a wrapper.

**Repair.** Fix what the review confirms. Afterwards, spawn a second fresh `spec-reviewer` on the new
`interface/` and iterate until it finds nothing you agree with. **Feed the reviewer:** a later
revision of a reviewed spec that no review criterion caught (or a review finding later reverted) goes
into `LESSONS.md`, and its rule into the reviewer's "Failure patterns" (`notes/spec-first-plan.md`,
"Phase 1b", the feedback loop).

**Constraints:**

- **Ask before changing a trusted statement.** For an exported or linked result (CLAUDE.md, "Trust
  base"), a premise of one, or anything that changes the trust base, stop and present the findings
  and the proposed statement. Intermediate specs may change once their callers are proved again.
- **The trust base does not grow** without that approval: no new axiom, `sorry`, or weaker check.
- **Nothing verified becomes unverified** (`etc/verified-code.py`).
- CLAUDE.md's rules hold: layout, modules, "Package APIs" (seal with `@[no_expose]` and add laws;
  don't unseal), generated files only through their scripts, no Perennial changes for one proof.

**Success:**

| check | must |
|---|---|
| `lake build` | pass |
| `etc/tcb-report.py --check` and every `etc/tcb-collections/*.txt` | pass, or differ only as approved |
| `etc/api-check.py` and `etc/gen-interface.py --check --layout` for the package | pass, with `interface/` regenerated |
| the second reviewer | no finding left that you agree with |

**Deliverable:** a branch off `origin/lean` with the changes and the regenerated `interface/`,
pushed; a note in `notes/decisions.md` for each spec whose design changed (what it was, why); a line
in `notes/STATUS.md`; a report listing each finding, what you did about it (fixed, rejected and why,
or left for the user), and the `interface/` diff of the target. With `--review-only`, the report of
findings is the deliverable and nothing is changed.
