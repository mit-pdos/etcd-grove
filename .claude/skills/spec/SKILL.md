---
name: spec
description: Design a spec in this repository — write one for a Go function or package API that has none, or improve an existing one (a Hoare triple, or the predicates and laws a package exports), including the vocabulary it is written in; or review one without changing it. Use when asked to write, design, improve, review, critique or fix a spec.
---

# Designing specs

**Goal:** the spec of the target is the best contract its clients can have: sound (true of the Go
code), complete (sufficient for every caller), local (about its function's footprint only), as
strong as the code allows, stated in abstract terms, with the laws its clients need. Start from
whatever exists, including nothing. How to get there is up to you.

**Read first**, before writing anything:

- `PRINCIPLES.md`: what makes a good spec here — the judgments the code and the proofs cannot decide
  for you, each pointing to where it was learned.
- `examples/README.md`: the index of specs the user reviewed, each from its first version through the
  user's critiques to the spec after them. They are the ground truth; open the ones whose kind or
  principles match your target (and those the principles you rely on point to), not all of them.

**A second opinion.** The author misses what it wrote (a vacuous disjunct the author had written
itself survived the author's own review). For an outside reading, spawn the `spec-reviewer` agent
(read-only) on the target, its Go code and its callers, without your conclusions. After a repair,
ask it again: repairs introduce defects.

**Iterating with the user:** keep the current candidate, in full (every premise, conjunct and new
definition, with a header listing its changes), in a scratch file outside the repository (never
committed), and point to it: no abbreviated sketch in chat.

**The user's feedback teaches the skill.** A critique of a spec becomes a principle in
`PRINCIPLES.md` (or sharpens one), stated so it reads without this conversation, with a pointer to
where it was learned; and a spec the user approves becomes an example in `examples/` (the first
version, each critique with what it changed, the approved spec; one sitting to read), with a row in
`examples/README.md`. Only specs the user reviewed go in `examples/`.

**Repository policy** (not a sequence; what must hold when you are done):

- **Ask before changing a trusted statement**: an exported or linked result (CLAUDE.md, "Trust
  base"), a premise of one, or anything that changes the trust base. Present the proposed statement
  and why.
- The trust base does not grow without that approval (no new axiom, `sorry`, or weaker check), and
  nothing verified becomes unverified (`etc/verified-code.py`).
- CLAUDE.md's rules hold: layout, modules, "Package APIs" (seal with `@[no_expose]` and add laws;
  don't unseal), generated files only through their scripts, issues found in the Go code go to
  `issues/`, no Perennial changes for one proof.
- A changed spec is done when `lake build`, `etc/tcb-report.py --check` (and the collections),
  `etc/api-check.py` and `etc/gen-interface.py --check --layout` pass, with `interface/` regenerated,
  and a note in `notes/decisions.md` says what the spec was and why it changed.
