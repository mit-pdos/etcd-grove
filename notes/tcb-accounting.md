# What `etc/tcb-report.py` does and does not establish

Audited 2026-09-21, against branch `worktree-election-close-admits` at
`0b3943d1f`, whose commit message claims *"every Hoare triple on the election
path is Qed except `wp_raftLog__slice_at`"*.

The short version: **that claim is true as a statement about the source text,
and `tcb-report.py` reports it accurately — but it was quoted as if it were
evidence that the proofs check, which it is not, and the scoped invocation
omits the axioms that matter most.** Read this before quoting a TCB number at
anyone.

## The audit process

Set 2026-09-22. **An audit is two commands, in this order, and neither
substitutes for the other.**

    make ci                                    # or a narrower .vo target
    etc/tcb-report.py                          # what the build cannot check

**Step 1 — `make` is the ground truth that the proofs check.** `make ci`
builds `new/should_build.vo`, which reaches
`election_proof/election.v` (`should_build.v:52`) and `v3.v`. The generic
`%.vo: %.v` rule means a narrower target works too —
`make new/proof/go_etcd_io/raft/election_proof/election.vo` — though note that
nothing in this tree has `.vo` dependencies, so any `.vo` target starts by
building all of Perennial (`STATUS.md`, "Checking your work"). There is no
single "top-level etcd proof" file today; `should_build.v` and `election.v`
are the two aggregators that exist.

**Step 2 — `tcb-report.py` exists to check what step 1 cannot.** That is the
whole of its remit, and the reason it does not and should not invoke Rocq.
Keeping the two apart is what makes each one's output mean something:

| `make` establishes | `tcb-report.py` establishes |
|---|---|
| every `Qed` is real — proof bodies typecheck | whether the *statements* say what was meant: the definitions the exported triple is written in terms of, which is the larger half of the TCB |
| a functor really discharges its signature's `Parameter`s, so an obligation is not an assumption | whether an axiom set has a non-trivial **model** — Rocq will never tell you that `own_raft_ghost := False` satisfies all twelve axioms |
| with an `assumptions.v`, `Print Assumptions` gives the exact transitive set of axioms and admitted lemmas a named theorem rests on, *through* `Notation`s and typeclass instances | **what is not in the build at all** — `make` silently does not check what nothing requires |
| | whether an `Axiom` is a declared trust-boundary assumption or unfinished work, and whether the scope rule allows it |
| | which Go function a triple is about, and whether that function exists in `new/code/` (this is `check-module-discipline.py`, sharing the parser) |
| | whether an admission is a whole unproven lemma or one side condition, and whether it is known false outside a stated regime |
| | whether `new/golang/defn/` — the operational model — has been modified |
| | a number a human can watch move between sessions |

**The consequence worth stating twice: `make` is necessary and silently
incomplete.** It checks exactly what `should_build.v` reaches, and reports
nothing about what it did not build. A `link_*.v` dropped from `election.v`
takes its collection out of the build with no error anywhere. That makes
**G6 the most load-bearing thing `tcb-report.py` does**, not the tidiness
item it looks like.

## What was independently reproduced

A comment-stripped scan of
`new/proof/go_etcd_io/raft/election_proof/` (330 files), written without
reference to the tool, agrees with it exactly:

| | count |
|---|---|
| `Admitted` | 1 (`wp_raftLog__slice_at`, marked `(* Trusted *)`) |
| `Axiom` | 10 |
| `Qed` | 169 |
| `Parameter` | 78 (all inside `Module Type`s) |
| `Abort` | 0 |

Three further things check out, none of which the tool itself checks:

- **All 330 files are reachable** from `election_proof/election.v` through the
  `Require` graph, and `new/should_build.v:52` requires `election.v`. So
  nothing counted is orphaned from the build. (`election.v`'s own header
  says this is load-bearing and manual — see gap **G6**.)
- **No soundness escape hatches** anywhere under
  `new/proof/go_etcd_io/raft/`: no `Unset Guard/Positivity/Universe
  Checking`, no `bypass_check`, no admitted `Program` obligations, no
  `Local Axiom`.
- `etc/check-module-discipline.py --scope election_proof` exits 0. Its five
  findings are three naming notes and two `F6-unknown-function` warnings on
  `raftpb.Entry.Size` and `big.Int.Int64`, which are exactly two of the ten
  axioms — expected, not a discrepancy.

**What was not reproduced: step 1.** No `make` was run against that branch
here. The tree carries 333 `.vos` files and no `.vo`/`.vok`, and `.vos`
skips proof bodies by construction. The evidence offered was a manual `-vok`
sweep described in a commit message ("99 pass, 0 fail"): not committed, not
tied to a revision, not reproducible from the repository. CI
(`.github/workflows/ci.yml:43`, `make -j4 -k ci`) *is* the real step 1, but
it triggers only on pushes to `main` and PRs targeting `main`, and that
branch is neither.

So the strongest honest statement about it remains: **"the source says 169
`Qed`, no `make` has been run against it here, and someone reported a `-vok`
sweep passing on 2026-09-21."** That is a fact about how the branch was
audited, not a defect in `tcb-report.py` — which is the whole of what the
two-step process clarified.

**Update, 2026-09-22 (evening): step 1 has now been reproduced for that
work**, after it landed on `main` and this branch was rebased onto it. At
`454e0d780`, the `.vos` closure (471 files) and then `.vok` of all 336 raft
files the build reaches — the election work plus `v3.v`, `v3_proof/` and
`readonly.v` — completed with **0 errors**. It is not a `make ci`: `-vok`
skips universe constraints. But it is a build at a named revision that
anyone can re-run from the repository, which is exactly what the
commit-message report was not. The recipe is in `STATUS.md`.

## What the build was not checking

Item 1 of the plan landed on 2026-09-22 and reported, on its first run,
that **`v3_proof/readonly.v` is reached by nothing**: 955 lines, 5
`Admitted`, 7 `Axiom`, requiring `v3_proof/protocol.v` and required by no
file in the repository. `make ci` has therefore never compiled it. Checked
independently of the tool: no `Require` naming `readonly` exists anywhere
under the repository root.

**Resolved the same day**: `readonly.v` still checks at `-vok`, and
`should_build.v:51` now requires it, so `etc/tcb-report.py` reports no file
outside the build (198 files, per `.rocqdeps.d`). It is wired in as a
stopgap pending a clean-up of the old proofs.

Two things worth taking from it. The first is that this is exactly the
failure G6 described, found the moment anything looked for it, in a
development whose `STATUS.md` opened by saying the directory was built. The
second is a calibration: the file had been in `STATUS.md`'s next steps for
days -- item 8 proposed bringing its eleven loose triples into the module
discipline -- while it was not being compiled at all.

**A caveat on the fallback graph, which the finding survives.** Without
`.rocqdeps.d` the closure is computed from `Require` lines by
`rocqscan.requires`, and that function models `From X Require a b` as string
concatenation where Rocq treats `X` as a *prefix filter* on a suffix match.
It also misses a `Require` whose `Import` lands on the next line. Either can
*miss* an edge and so report a false orphan; `should_build.v` has two
requires it cannot resolve for exactly these reasons
(`New.proof.Import`, `New.proof.leasing_proof.protocol`). `readonly.v` is
not one of those cases, since nothing references it under any spelling.
Fixing the parser is worth doing; running `make` once so that `.rocqdeps.d`
exists is worth more, since deferring to the build's own graph is the whole
point of item 1.

## The gaps

**Numbered in the order they were found, which is not their order of
importance.** By importance: **G6, G3, G2, G4, G5, G7, G1**. The labels are
cited in `journal.md` and in commit messages, so they stay put rather than
being renumbered.

**G2 and G6 are two symptoms of one root cause**, found a day apart and
written up separately before that was noticed: `tcb-report.py` decides what
to look at by **globbing a directory**, where `make` decides by **walking a
dependency graph**. Every discrepancy between the two follows — files on
disk that the build never compiles (G6), and files the build compiles that a
scoped report drops (G2). They have **one fix**, plan item 1.

### G1. A report cannot be tied to the build that backs it

**Most of this gap dissolved when the two-step process was written down on
2026-09-22, and what is left is the least severe item in this list.** It is
kept, shrunken, rather than deleted, because the reasoning is worth not
re-deriving.

What it used to say was "the tool never compiles anything" — `tcb-report.py`
and `rocqscan.py` contain no `subprocess`, no `rocq`, no reference to
`.vo`/`.vok`; they strip comments and count sentences, so a `Qed.` in a file
that does not typecheck is counted as a proof. **That is the design, and it
is right.** Step 1 checks proofs; a source scanner that also tried to would
be a worse version of `make`. Criticising it for that was criticising it for
not being a different tool.

The other half of the old G1 — that the election branch's number was not
backed by a build — is a fact about how that branch was audited, and now
lives above under "What was not reproduced".

**What genuinely survives is narrow:** a `tcb-report.py` run carries no
record of *what it looked at*. It prints counts with no revision, so two
halves of an audit cannot be shown to be about the same tree, and a figure
pasted into a commit message or a notes file is unattributable a week later.
The process says "quote step 1 and step 2 together"; nothing in the output
helps anyone do that, or notices when they did not. Plan item 4 is the fix
and it is roughly a header line.

### G2. `--scope` is a path filter, not a dependency cone

`tcb-report.py:515-524` computes the whole report and then keeps the units,
assumptions, results and definitions whose path is under the scope
directory. Anything the scoped files *depend on* from outside simply
vanishes from the output, with no boundary line saying so.

Concretely: every file in `election_proof/` requires
`election_proof/protocol.v` (through `defs.v`), which carries **12
`Axiom`s**. `--scope election_proof` prints `assumed 11`. The true figure for the
election development is 23. The commit message does say the protocol axioms
are "outside this pass by design" — the tool's output does not, and the
number is what gets quoted.

The same filter also silently mixes out-of-scope project definitions into
the "494 distinct names resolve to nothing in this tree" bucket, which the
tool labels *"binders, and Perennial/stdpp/Rocq constants"*. Under
`--scope election_proof` that bucket also swallows `nstate.t`, `step`,
`own_raft_ghost` and `is_message`.

### G3. The one exported spec is vacuous under the trivial ghost model, and nothing says so

The result this development is for is `wp_raft__Step` — a Hoare triple on a
Go function — and `--scope election_proof --view surface` reports
`wp_raft__Step_body` as the sole externally-facing result.
`raft_election_safety` is an internal lemma, not the payoff
([decisions.md](decisions.md), 2026-09-21), so it does not belong among the
results, and an earlier version of this file was wrong to call its absence a
gap.

(That was true by accident at first: `--scope` was a path filter and the
corollary sat outside the directory. Once `--scope` became a dependency cone
it reappeared, through a rule that promoted *any* unused theorem in a file
nothing required. Since 2026-09-23 the surface has two sections — results,
which must be Go-function triples, and *root lemmas*, stated facts nothing
uses yet — and the corollary is in the second, not counted in the TCB.)

The real problem is that the exported triple cannot yet mean anything.
`own_raft_ghost`, `is_message` and `is_leader` are `Axiom`s, and
**`election_proof/protocol.v` contains no allocation or initialisation axiom
producing `own_raft_ghost` from anything.** Instantiating

    own_raft_ghost γ id s := False        is_leader γ id t := False

satisfies all twelve axioms — exclusivity, the step obligation, the outbox
obligation, uniqueness, the timeless and persistent instances. Under that
model `wp_raft__Step`'s precondition is `False`, so the triple holds
trivially; so does `raft_election_safety`, which is why the corollary cannot
do its sanity-check job either.

This is not news — it is next step #4 in `STATUS.md`, "construct
`own_raft_ghost` / `is_message` rather than axiomatizing them". The point
here is narrower: **no output of `tcb-report.py` would lead a reader to
discover it**, and the scoped run reads as though the development were
nearly closed. Gap-closing item 2 below is the cheap fix.

### G4. An `Admitted` is labelled more benignly than it is

`proof_raftLog__slice.v:283` ends `Admitted. (* Trusted *)` and the tool
prints it under *"of those, trusted — deliberate, marked in a comment"*,
alongside the two genuine overflow assumptions at `readonly.v:464,471`.

Two things that hides:

- **Granularity.** The proof script runs to line 280 with a single `admit.`
  at line 233 discharging one arithmetic side condition (`Hfitsx`). But the
  object entering the trust base is the *whole Hoare triple* — that is what
  `Print Assumptions` would name. The tool cannot tell an admitted side
  condition inside an otherwise complete proof from a lemma with no proof at
  all, and the `(* Trusted *)` marker does not record the difference.
- **Soundness of the assumption.** The file's own header states: *"So the
  triple as stated is **false** at a log with ~2^63 unstable entries."* That
  is a documented-false statement sitting in the trust base — a different
  category from "the log fits in memory", and a different category again
  from a deliberate modelling assumption. The tool's vocabulary has one
  bucket for all three.

The standard repair is the one `campaign` got (`notes/false-statements.md`):
make the assumption an explicit named `Axiom` premise and close the lemma
with `Qed`, so the TCB item is the assumption rather than the theorem. The
file argues at length that no premise can carry it *in the caller*; that
argument does not rule out a top-level `Axiom log_fits : …` cited by the
proof, which would be strictly more honest than admitting the triple.

### G5. Changes to the model itself are outside the default root

`DEFAULT_PROOF_ROOT = "new/proof/go_etcd_io/raft"`. Branch
`worktree-election-close-admits` also edits `new/golang/defn/map.v` and
`new/golang/theory/map.v`. A `defn/` change is a change to the **operational
semantics** — TCB in the strictest sense, exactly like the 2026-09-17
`go.len`/`go.cap` array rules — and no invocation of `tcb-report.py` in the
notes covers it. The framework carries two `Admitted`s of its own in
`new/golang/theory/` (`array.v`, `postlifting.v`) and three in
`new/golang/defn/prelang.v`.

### G6. Reachability from the build is not checked — and this is the one that matters most

The tool counts every `.v` file under the root. Nothing verifies that a
counted file is in the `Require` closure of `new/should_build.v`. A
`link_*.v` dropped from `election.v` would take its collection out of the
build while `tcb-report.py` went on counting its `Qed`s.

Numbered sixth because it was found sixth; under the two-step process it is
**first in importance**. Step 1 cannot catch it — `make` does not know that
a file it was never asked to build exists — so this is the single way a
green build and a clean report can both be true of a development that is not
being checked. `election.v`'s own header says the `link_*` list is
load-bearing and maintained by hand. I verified it today (330/330
reachable); it should not be verified by hand again.

### G7. The reference graph is spelling-based

Already documented in the tool's own docstring, and the reason the
definition count is a lower bound: a reference through a `Notation` or an
unnamed typeclass instance is invisible. It is not fixable inside a
syntactic scanner, and it does not need to be: `Print Assumptions` from
step 1 is notation-blind-proof, so plan item 5 retires it by reconciling
against the build's own answer rather than by improving the guess.

## Plan: what would make step 2 complete enough

"Complete enough" means: **given a green step 1, `tcb-report.py` tells a
reader everything about the trust base that the build could not have told
them** — and says plainly which of the two it is speaking for. It is not
trying to become a proof checker; there is one, and it is `make`.

Ordered by importance, matching the list under "The gaps" above. Items 1-4
are pure additions to the existing scanner and need no build; item 5
consumes an artefact the build already almost produces.

**Item 1 landed 2026-09-22**, and found a real defect on its first run --
see "What the build was not checking" above. Items 2-4 are unclaimed.

### Slice 1 — one afternoon, no Rocq required

1. ~~**Scan what `make` builds, not what a directory holds (G6 + G2).**~~
   **Landed 2026-09-22.** The one feature both of those gaps want: **the set of files `tcb-report.py`
   scans should be the set `make` compiles.** Make the scanned set a
   dependency closure rather than a glob, rooted at `new/should_build.v` by
   default and at the scope's aggregator (`election.v`) under `--scope`.
   Everything else falls out:

   - a file under the proof root but outside the closure is **not counted**,
     and is **reported** — *"3 .v files are not in the build closure"*, with
     the list, and a non-zero exit under `--strict`. Not counting it is not
     enough on its own; silently dropping an orphan looks like the numbers
     improving (G6);
   - a scoped report automatically includes what the scope depends on, so
     `--scope election_proof` reaches `election_proof/protocol.v` and prints `assumed
     23` instead of `11`. Keep a presentation line for the boundary — *"of
     the 23, 12 are from outside the scope directory"* — since the reader
     still wants to know which side of it a thing is on (G2);
   - `--scope-dir` survives as the old path filter for anyone who wants it,
     clearly labelled as not being the build's view.

   **Take the graph from `.rocqdeps.d`, not from a fresh `Require` parse.**
   That file is `rocq dep` output and is exactly what `make` expands its
   prerequisites from — `Makefile:47-53` generates and includes it, and
   `Makefile:64` makes every `.vo` depend on it. Rolling a second parser is
   how the two sets drift apart again, which is the whole thing being fixed. It is generated rather than committed, so fall back to
   `rocqscan.requires` when it is absent and **say in the output which
   source was used** — a fallback answer is the tool's guess at the build
   graph, not the build's own.

2. **Flag never-allocated abstract predicates (G3).** For every
   `Axiom P : … → iProp Σ`, search the tree for a statement whose conclusion
   mentions `P` and whose premises do not — an allocation or initialisation
   lemma. If there is none, print `P` as **"never allocated: every statement
   that consumes it may be vacuous"**. On today's tree that flags
   `own_raft_ghost`, `is_leader` and `is_message`. **This is the clearest
   case of the tool doing something the build structurally cannot**: Rocq
   will happily check every proof in the development under the model that
   sends all three to `False`.
3. **Give admissions a machine-readable marker (G4).** Replace free-text
   `(* Trusted *)` with a one-line grammar the tool parses and
   `check-module-discipline.py` gates, distinguishing at least:
   - `(* TCB: <reason> *)` — a deliberate assumption believed to be true;
   - `(* TCB-partial: false when <condition> *)` — known false outside a
     stated regime, which `wp_raftLog__slice_at` is;
   - and error on a trusted admission with no marker.
   Report an admitted lemma as assuming its **whole statement**, in those
   words — `Print Assumptions` names the whole triple, so the report should
   agree with what step 1 would say.
4. **Make a run attributable (G1).** A header line carrying the revision
   scanned and the premise: *"Source-text analysis at `<rev>` (`-dirty` if
   the tree is modified). Assumes `make` is green at this revision; it does
   not check proofs."* Then a pasted figure says which tree it describes.
   Worth adding beside it: if `.vo` files exist under the scope, report the
   oldest against the newest `.v`, so a stale build is visible; if none
   exist, say `no build artifacts present`. **Lowest value of the four** —
   output hygiene, not a TCB check — but also the cheapest, and it is what
   makes the two-command process auditable after the fact. Do it while
   waiting for a build.

### Slice 2 — reconcile with what the build knows

5. **Diff against `Print Assumptions` (G7).** Add
   `election_proof/assumptions.v`
   containing nothing but `Print Assumptions` for each **top-level function
   spec** — today `wp_raft__Step`, and `wp_Node__Propose` from `v3.v` —
   reached from `should_build.v`, so step 1 emits it. Those triples are the
   result ([decisions.md](decisions.md), 2026-09-21), so they are what
   ground truth has to be taken at. Then `tcb-report.py --assumptions <file>`
   reports the two-way difference:

   - a name Rocq lists that the scanner missed → the spelling-based graph
     has a hole, and the printed TCB was too small;
   - an `Axiom` in the tree that Rocq does **not** list → it is dead, or the
     theorem does not depend on what everyone assumes it does.

   Neither direction is visible to either tool alone, which is exactly why
   this belongs in step 2 rather than step 1. It also retires G7, since the
   reconciliation is against an answer that sees through `Notation`s and
   typeclass instances.

   **Deliberately dropped.** An earlier version of this plan proposed
   committing a `-vok` manifest — revision, per-file source hash, exit code
   — for `tcb-report.py` to join against, so it could report which `Qed`s
   had been machine-checked. Under the two-step process that is step 1's job
   and the tool should not restate it. If the *provenance* of a build result
   ever needs recording, it belongs next to the build, as a CI artefact, not
   inside a source scanner.

### Slice 3 — when someone cares about the framework number

6. **Second root for the model (G5).** `--also-root new/golang`, plus a
   section counting this development's *diff* against the upstream
   merge-base in `new/golang/defn/` (hard TCB — the operational semantics)
   separately from `new/golang/theory/` (lemmas, which step 1 checks). A
   green build says nothing about whether the semantics it checked against
   are the right ones, so the `defn/` line is the one that should make a
   reader stop.

## Rule of thumb until the above lands

Quote step 1 and step 2 together, or neither: **"`make` green at `<rev>`;
`tcb-report.py` says …"**. A TCB number with no build behind it describes a
text file.

For step 2, quote **the full-tree run**
(`etc/tcb-report.py` with no `--scope`), which on
`worktree-election-close-admits` says *43 assumed — 8 `Admitted`, 35
`Axiom` — 80 definitions, 953 lines, 6.2% of the development*, and say in the
same breath that the numbers are syntactic and that the exported triple
`wp_raft__Step` rests on an un-constructed ghost state. A `--scope election_proof`
figure quoted on its own is misleading in three independent ways (G2, G3,
G4).
