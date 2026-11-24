# dsv-skill: the dsverify skill moves into etcd-grove

Branch `dsv-skill` (off `lean` e7adfa1365). The user decided (2026-11-24) that the dsverify skill
(the method given to agents doing automatic proving) moves from the dsverify-lab repository into
etcd-grove, beside kit generation (branch `dsv-kitgen`, notes/dsv-kitgen.md), and that its
environment parts are rewritten for a challenge exported from etcd-grove. The lab's experiment
harness (`sandbox.sh` and co.) stays in the lab and runs agents on exported challenges.

## Provenance

- Source: dsverify-lab `skill/` at lab commit `3768a53` (2026-11-18, `git -C /shared/dsverify-lab
  log -1 --format=%h -- skill`; tree `89257fd460`), the skill of the lab's recent runs.
- Not copied: `skill/examples/` beyond its README (it held only the README), and nothing else of the
  lab. The lab repository is unchanged.

## Where it is

`.claude/skills/dsverify/` (etcd-grove keeps its skills in `.claude/skills/`; Claude Code's skill
format: `SKILL.md` with `name`/`description` front matter, supporting files beside it). The
challenge's `CLAUDE.md` template is outside it, `etc/dsv/challenge-CLAUDE.md`, because a control arm
gets the same `CLAUDE.md` without the skill.

| file | status | what |
|---|---|---|
| `SKILL.md` | rewritten (structure kept) | the challenge, the file table, the workflow (read the challenge, run the test, scope given, model first, hubs, interface → review → freeze → prove, done), the rules |
| `CHALLENGE.md` | new | what a challenge gives, what is the agent's and what is not, "done" (the goal proved; `#print axioms` = Lean's three; statement and premises byte-identical; non-vacuity builds; the checks pass), the premise rules, prophecy patches |
| `NET.md` | new | the statement's shape (`Robust [] (system σ) g threads (2^63)` under `DistDeploy`, the bridges), the net extension's fault model and specs, `examples/lib/remote` (`Check`/`Run`, `Do`, `ServeClient`, `Serve`, call budgets), the given codecs and models |
| `SETUP.md` | rewritten | the parts (`Dsverify/`, `Net/`, main tree, `Robustness/`) and layout, Link naming, never redeclaring a name, the kit file `etc/dsv/<kit>.py`, the generators (goose, gen-init, kitgen, codec generators), modules, import tiers, package APIs, building and checking, operating rules (no network) |
| `TOOLS.md` | rewritten | the scripts the challenge has (was: the scripts to build), and the few worth building |
| `HUBS.md` | rewritten in part | the challenge's hubs (the start, each machine's share and `main`, the constructors); the slot convention and its rules kept; the program-start bundle becomes the deployment's start boundary |
| `TRUST.md` | rewritten | what the goal may rest on (no axioms, trusted models or `sorry`s of the agent's); hypotheses while working (visible, true of the real code, one canonical spec, discharged before done); attacking a hypothesis (and a declared premise); findings (a bug is what the deployment's test can trigger; fixes recorded separately); bounds |
| `PRINCIPLES.md` | kept | edits: hypotheses instead of axioms; one canonical spec across the tree; real preconditions; no pin table |
| `SPEC-FIRST.md` | kept | edits: Scope is given (records the configuration, the premises, the cases that break the obvious invariant); the interface includes the goal's proof against `sorry`s; hypotheses attacked instead of axioms; "who decides" without trust-base growth (never an option); named runs and kits removed (a go-vsr bug's description, run names); the session registry dropped; landing lock generalized to merging |
| `TESTING.md` | kept | edits: the test is given (the deployment: servers, client machines, the orchestrator); porcupine is verified here (`remote.Check`'s spec), so the porcupine-axiom section becomes what `Check` requires (`isModel`, `codecOk`); the recording-layer sketch dropped (lintest/remote are given); variants are the agent's own tests |
| `LIFECYCLE.md` | kept verbatim | |
| `PROOF-NOTES.md` | kept | edits: `etc/lean-check.py`; large contexts (`iframe` over a large `[∗list]`); initializers through gen-init and `InitHyp`; prophecies through patches |
| `REPORT.md` | kept | edits: hypotheses; what the goal rests on; fixes and findings about the challenge reported apart |
| `examples/README.md` | kept verbatim | empty index |
| `etc/dsv/challenge-CLAUDE.md` | new | the challenge's `CLAUDE.md` template, fields `{{...}}` listed in its header comment |

Dropped versus the lab skill: building the project from scratch (Lake setup, choosing a fork and pins,
writing goose/gen-link/gen-init/tcb-report/gates: the tools exist); the porcupine-completeness
axiom (proved here); `TrustedCode` and trust-boundary axioms as options; scope negotiation with the
user (the goal is fixed); per-run anecdotes naming kits (craq, go-vsr, hraft, ablate-*), one of them
a known bug of a kit; the session registry.

Left out on purpose (from etcd-grove's own rules): the multi-session coordination (GitHub issues,
the land queue, gh-inbox, sessions, tokens, build machines), any kit's proofs, design or known bugs,
and the #8 statement rule.

## Interface with kitgen's export (`etc/dsv/kitgen.py --export-challenge KIT DIR`, dsv-kitgen)

Proposed for the dsv-kitgen agent (not implemented here; that branch owns `kitgen.py`):

1. **Skill**: `--export-challenge KIT DIR` copies `.claude/skills/dsverify/` whole to
   `DIR/.claude/skills/dsverify/` (a project skill: Claude Code finds it in the work tree);
   `--no-skill` leaves it out (the control arm). Nothing else of `.claude/` is copied (the other
   skills and agents are etcd-grove's own, some with etcd material).
2. **CLAUDE.md**: the export fills `etc/dsv/challenge-CLAUDE.md`'s `{{...}}` fields (its header
   lists them; most come from `KITGEN`) and writes `DIR/CLAUDE.md`, with the header comment
   removed, identical with and without the skill. It does not copy etcd-grove's own `CLAUDE.md`
   or `notes/` (they describe other kits and the coordination).
3. **Provenance**: the export writes `DIR/CHALLENGE.txt` (or a JSON equivalent) with
   `source: <etcd-grove commit>` (`git rev-parse HEAD`, refusing a dirty tree or noting it),
   `kit: <kit>`, `skill: <tree hash of .claude/skills/dsverify at that commit, or none>`,
   `claude-md: <hash of the filled CLAUDE.md>`. A run records this file; same skill tree, same
   skill, whatever commit named it (as the lab's `meta.txt` does today with `skill: REV (COMMIT)
   tree TREE`). Keep `CHALLENGE.txt` out of what the agent is told to read (or make it harmless: it
   holds hashes only).
4. **What not to export** (the skill's no-leak rule extends to the tree): the kit's proofs (the
   point), other kits' `Dsverify/` proofs and notes, `old/dsverify/` (the lab's old harness and its
   kits), `issues/` and `nonissues/` entries of dsverify kits, `notes/dsv-*.md`, and the
   `etc/tcb-collections/dsv-*.txt` baselines of other kits.
5. **Offline**: the challenge has no network, so the export (or the lab's image) must provide the Go
   toolchain `etc/goose.py` pins (`GO_TOOLCHAIN`; goose otherwise lets Go fetch it), the kit's Go
   module cache (`examples/dsverify/<kit>` and `models/`), the Lake packages built, and `prophcheck`'s
   module. The skill tells the agent to rerun goose and gen-init after a Go or patch change.
6. **Checks**: the template's `{{CHECKS}}` defaults (goose `--check --project dsv-<kit>`, `proph_patch`,
   gen-init `--check`, kitgen `--check <kit>`, tier-check `--check`); the export keeps the ones its
   tree supports (tier-check's baseline must match the exported tree).
7. **Non-vacuity**: the challenge ships the kit's `NonVacuityLinked.lean` (the NON-VACUITY rule:
   each premise class's built instance) as a fixed file; the template names it.
8. Decisions left to the coordinator (the template has fields for them): whether code changes to
   the system are allowed (`{{CODE_CHANGES}}`; the skill's default: fixes allowed, each with its
   failing test, never the orchestrator, model or codec), and whether the challenge's statement
   ships with the generated top-level proof skeleton and `Start.lean` scaffold or without.

## Ablation arms

An arm is an export option, not a skill revision: `--export-challenge KIT DIR` (with the skill) and
`--export-challenge --no-skill KIT DIR` (without), from the same etcd-grove commit, give two trees
that differ only in `.claude/skills/dsverify/`. An older or variant skill is an etcd-grove commit
(or branch) of `.claude/skills/dsverify/`, exported with `--skill-from REV` (proposed: the tree of
`REV:.claude/skills/dsverify` instead of the working tree's), so the challenge and the skill can
come from different commits and the run records both. The lab's pre-merge arms (`skill-nospec`,
lab-commit skills) stay reproducible through the lab's old path (below).

## What the lab's `sandbox.sh` should change (the coordinator applies this later)

- `sandbox.sh new RUN --challenge DIR` (new): copy the exported challenge `DIR` into the run's home
  as the work tree (a fresh git repository, one initial commit), instead of a kit seed; read
  `DIR/CHALLENGE.txt` into `runs/RUN/meta.txt` (`source`, `kit`, `skill` tree, `claude-md`).
- The skill: if `DIR/.claude/skills/dsverify/` exists, either leave it as a project skill in the work
  tree (simplest; the agent can read and edit it, which the runs' diff then shows), or move it into
  the config dir's `~/.claude/skills/dsverify/` as today (keeps it out of the agent's commits; the
  `additionalDirectories` entry stays). Recommendation: move it, so the work tree holds only the
  challenge, and the skill's place is the same as in past runs.
- `sandbox.sh new RUN SKILL_REV` (`REV:skill`) and `skill-nospec` stay for reruns of old arms; the
  lab's `skill/` is then frozen at `3768a53` with a README line pointing here.
- The lab's README rule "keep anything an agent must not read outside `skill/`" moves with it:
  etcd-grove's `etc/dsv/README.md` now says it for `.claude/skills/dsverify/`.
- `verify.sh`/`goal-check.sh`: "done" is `CHALLENGE.md`'s (the goal builds, `#print axioms` is
  Lean's three, the statement and premise files byte-identical to the export's, the non-vacuity
  module builds, the template's checks pass); the comparator step can compare the goal's statement
  with the exported one directly.
- `check-env.sh`: add a leak check that the run's tree holds no `Dsverify/Proof` file of the kit
  beyond what the export ships, no `old/dsverify/`, and no `notes/dsv-*.md`.

## State

- 2026-11-24: skill moved and rewritten (this branch); the template written; `etc/dsv/README.md`
  points to both. dsv-kitgen has no `--export-challenge` yet (its head 489560bccf); the interface
  above is to be copied into notes/dsv-kitgen.md by that branch's agent (this branch does not edit
  dsv-kitgen).
