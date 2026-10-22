---
name: proof-cleanup
description: Clean up this repository's proofs — delete what no result needs (unused lemmas, dead definitions, leftover experiments) and simplify what remains (invariants with fewer cases, simpler intermediate specs, shorter proofs) — without changing any top-level result or adding to the trust base. Use when asked to clean up, simplify, or shrink proofs.
---

# Cleaning up proofs

**Goal:** less proof for the same results. Remove what nothing needs: lemmas, definitions,
instances and files that no result uses and that no planned proof will use. Before deleting, check
whether an unfinished proof's `sorry` or a plan in `notes/` still needs it. Make what stays
simpler: invariants with fewer cases or conjuncts, intermediate specs that say only what their
callers use, proofs that are shorter or more direct. How to get there is up to you.

**Constraints:**

- **Top-level results do not change.** The exported results keep their exact statements, and so
  does every definition those statements are written in terms of. The exported results are the
  linked results no other proof uses (CLAUDE.md, "Trust base") and the theorems of every
  `Results.lean`, such as adequacy theorems about concrete Go driver programs. Intermediate specs,
  invariants and helper definitions may change, provided everything above them is proved again.
- **The trust base does not grow.** Add no axiom or `sorry`, and nothing that weakens what the
  kernel checks (`native_decide`, `implemented_by`, ...). Removing one is welcome.
- **Nothing verified becomes unverified.** Every function that `etc/verified-code.py` counts as
  verified stays verified.
- **Some files stay as they are.** Do not touch `Code/`, `GeneratedProof/`, `TrustedCode/` or
  Perennial. Change generated files (`Link.lean`, `Init.lean`) only through their scripts. The
  proof rules of CLAUDE.md ("Proof writing", "Modules") still hold.

**Success:**

| check | must |
|---|---|
| `lake build` | pass |
| `.claude/skills/proof-perf/fingerprint.py`, `--diff` against `origin/lean`'s | every differing line is an intermediate spec or a definition only intermediate results reach; none is top-level |
| `etc/tcb-report.py --check`, and `--collection C --check` for each `etc/tcb-collections/*.txt` | pass, or differ only by removals (then `--update`) |
| `etc/verified-code.py` | no function goes from verified to anything else |

The proof must also be measurably smaller or simpler. Report the lines and declarations removed,
and for each simplified invariant or spec, what it was before.

**Deliverable:**

- a branch `cleanup/<YYYY-MM-DD>` off `origin/lean`, with one commit per coherent change, pushed to
  `origin`;
- a line in `notes/STATUS.md`, plus `notes/decisions.md` if the design of a spec or an invariant
  changed;
- a report of what was removed, what was simplified, and what was tried and not kept.

Never merge the branch or push to `lean` or `main`; the user reviews it.
