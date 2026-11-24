# What to record

The point of the method is measurable: fewer re-statements after proofs exist. Record enough to tell.

## Per stage (in the stage's plan file, `notes/<stage>-plan.md`)

- **Scope**: the configuration, the top-level statement, the restrictions with their reasons, what
  admitting the new case breaks.
- **Interface**: statements written (count), invariants written (with their laws).
- **Review**: findings per tier, what each repair changed, what the check of the repairs found.
- **Freeze**: date, the tag, the user's approval (or the logged decision when no user could answer),
  hypotheses attacked and results.
- **Prove**: the change log of the interface, tagged (`SPEC-FIRST.md`); counts of F and R per
  abstraction; per package, the internal statements changed while proving and the unfolds listed;
  whether the top functions were stated first and the riskiest step's proof came next, and what it
  changed; the goal path's `sorry` count per round.
- **Cost**: wall time, agent time and tokens per phase if available, full builds run.
- **Tooling**: the tools built in this stage (`TOOLS.md`), when, and what each cost to build and fix;
  the given scripts that failed you, and how.

## Per project (`notes/STATUS.md`, kept current)

- A dated summary line per landed stage, newest first (keep the ten newest; move older ones to an
  append-only history file).
- What the goal rests on: the goal path's `sorry`s and open hypotheses (from the report, not by
  hand); at the end, `#print axioms` of the goal theorem.
- Verified code per package (from the accounting script).
- Findings in the target: counts, which block the proof; the fixes, separately; findings about the
  challenge (a premise refuted, a model that accepts too much).
- Hub churn: changes per hub statement per stage, before and after slots.
- Where the agent was stuck, and what it asked the user (with the answers).

## At the end of the experiment

- How far the result reaches: whether the goal is proved (`CHALLENGE.md`, "Done"), and if not, what
  is left (the `sorry`s and hypotheses on its path, each with what blocks it); the configuration it
  covers.
- The post-freeze change log summarized: F and R by category and abstraction, against spec size.
- Which phases paid (findings per hour) and which did not.
- Principles added or sharpened in `PRINCIPLES.md`, with the misses that caused them.
