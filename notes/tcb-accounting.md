# What `etc/tcb-report.py` does and does not establish

Audited 2026-09-21, against branch `worktree-election-close-admits` at
`0b3943d1f`, whose commit message claims *"every Hoare triple on the election
path is Qed except `wp_raftLog__slice_at`"*.

The short version: **that claim is true as a statement about the source text,
and `tcb-report.py` reports it accurately — but the tool cannot demonstrate
it, and the scoped invocation that is quoted as evidence omits the axioms
that matter most.** Read this before quoting a TCB number at anyone.

## What was independently reproduced

A comment-stripped scan of
`new/proof/go_etcd_io/raft/v3_proof/election/` (330 files), written without
reference to the tool, agrees with it exactly:

| | count |
|---|---|
| `Admitted` | 1 (`wp_raftLog__slice_at`, marked `(* Trusted *)`) |
| `Axiom` | 10 |
| `Qed` | 169 |
| `Parameter` | 78 (all inside `Module Type`s) |
| `Abort` | 0 |

Three further things check out, none of which the tool itself checks:

- **All 330 files are reachable** from `v3_proof/election.v` through the
  `Require` graph, and `new/should_build.v:51` requires `election.v`. So
  nothing counted is orphaned from the build. (`election.v`'s own header
  says this is load-bearing and manual — see gap **G6**.)
- **No soundness escape hatches** anywhere under
  `new/proof/go_etcd_io/raft/`: no `Unset Guard/Positivity/Universe
  Checking`, no `bypass_check`, no admitted `Program` obligations, no
  `Local Axiom`.
- `etc/check-module-discipline.py --scope election` exits 0. Its five
  findings are three naming notes and two `F6-unknown-function` warnings on
  `raftpb.Entry.Size` and `big.Int.Int64`, which are exactly two of the ten
  axioms — expected, not a discrepancy.

## The gaps, worst first

### G1. The tool never compiles anything

`tcb-report.py` and `rocqscan.py` contain no `subprocess`, no `rocq`, no
reference to `.vo`/`.vok`. They strip comments and count sentences. **A
`Qed.` in a file that does not typecheck is counted as a proof.**

The tree carries 333 `.vos` files and no `.vo`/`.vok`. `.vos` skips proof
bodies by construction, so their presence certifies nothing about the 169
`Qed`s. The actual evidence is a manual `-vok` sweep described in the commit
message ("99 pass, 0 fail"), which is:

- not committed anywhere — the results lived in a `$CLAUDE_JOB_DIR`;
- not tied to a revision, so nothing can say whether it predates the last
  edit;
- not reproducible from the repository.

CI (`.github/workflows/ci.yml:43`, `make -j4 -k ci`) *is* a full `.vo` build
of `should_build.v` and would be ground truth, but it triggers only on
pushes to `main` and PRs targeting `main`. This branch is neither.

**So the strongest honest statement today is: "the source says 169 `Qed`,
and someone reported that they all checked at some point on 2026-09-21."**

### G2. `--scope` is a path filter, not a dependency cone

`tcb-report.py:515-524` computes the whole report and then keeps the units,
assumptions, results and definitions whose path is under the scope
directory. Anything the scoped files *depend on* from outside simply
vanishes from the output, with no boundary line saying so.

Concretely: every file in `election/` requires
`v3_proof/election_protocol.v` (through `defs.v`), which carries **12
`Axiom`s**. `--scope election` prints `assumed 11`. The true figure for the
election development is 23. The commit message does say the protocol axioms
are "outside this pass by design" — the tool's output does not, and the
number is what gets quoted.

The same filter also silently mixes out-of-scope project definitions into
the "494 distinct names resolve to nothing in this tree" bucket, which the
tool labels *"binders, and Perennial/stdpp/Rocq constants"*. Under
`--scope election` that bucket also swallows `nstate.t`, `step`,
`own_raft_ghost` and `is_message`.

### G3. The theorem the work is for is out of scope, and is currently vacuous

`raft_election_safety` lives in `v3_proof/election.v`, one level above the
scope directory, so `--scope election --view surface` reports exactly one
externally-facing result: `wp_raft__Step_body`. The payoff theorem is not
in the report at all.

Worse, it cannot yet mean anything. Its proof
(`election.v:136-147`) is three lines over `own_raft_ghost_is_leader` and
`is_leader_unique`, both axioms; `own_raft_ghost`, `is_message` and
`is_leader` are themselves `Axiom`s, and **`election_protocol.v` contains no
allocation or initialisation axiom producing `own_raft_ghost` from
anything.** Instantiating

    own_raft_ghost γ id s := False        is_leader γ id t := False

satisfies all twelve axioms — exclusivity, the step obligation, the outbox
obligation, uniqueness, the timeless and persistent instances. Under that
model `raft_election_safety` is trivial, and so is `wp_raft__Step`, whose
precondition owns `own_raft_ghost`.

This is not news — it is next step #4 in `STATUS.md`, "construct
`own_raft_ghost` / `is_message` rather than axiomatizing them". The point
here is narrower: **no output of `tcb-report.py` would lead a reader to
discover it**, and the scoped run reads as though the development were
nearly closed.

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

### G6. Reachability from the build is not checked

The tool counts every `.v` file under the root. Nothing verifies that a
counted file is in the `Require` closure of `new/should_build.v`. A
`link_*.v` dropped from `election.v` would take its collection out of the
build while `tcb-report.py` went on counting its `Qed`s. I checked this by
hand today (330/330 reachable); the check should not be by hand.

### G7. The reference graph is spelling-based

Already documented in the tool's own docstring, and the reason the
definition count is a lower bound: a reference through a `Notation` or an
unnamed typeclass instance is invisible. Lowest priority, because the fix
for G1 (below) subsumes it.

## Plan: what would make it complete enough

"Complete enough" means: **a reader can run one command and get a number
that is machine-backed, covers everything the named theorem rests on, and
distinguishes an assumption with a model from one without.** Ordered by
value per unit of work; the first three are pure additions to the existing
scanner and need no build.

### Slice 1 — one afternoon, no Rocq required

1. **Make `--scope` mean the dependency cone (G2).** Keep the path filter as
   `--scope-dir` if anyone wants it, but make `--scope X` report the
   transitive `Require` closure of the files under `X`. At minimum, always
   print a boundary line: *"this scope requires N files outside it, carrying
   M axioms and K admits"*, with the list. For `election` that turns
   `assumed 11` into `assumed 23` and names `election_protocol.v`.
2. **Flag never-allocated abstract predicates (G3).** For every
   `Axiom P : … → iProp Σ`, search the tree for a statement whose conclusion
   mentions `P` and whose premises do not — an allocation or initialisation
   lemma. If there is none, print `P` as **"never allocated: every statement
   that consumes it may be vacuous"**. This is a syntactic check the
   existing name graph already supports, and on today's tree it would flag
   `own_raft_ghost`, `is_leader` and `is_message` — which is precisely the
   thing the current output hides.
3. **Check build reachability (G6).** `--require-reachable new/should_build.v`:
   warn on any scanned file outside the `Require` closure. Twenty lines,
   using the parser that already exists.
4. **Give admissions a machine-readable marker (G4).** Replace free-text
   `(* Trusted *)` with a one-line grammar the tool parses and the gate
   enforces, distinguishing at least:
   - `(* TCB: <reason> *)` — a deliberate assumption believed to be true;
   - `(* TCB-partial: false when <condition> *)` — known false outside a
     stated regime, which `wp_raftLog__slice_at` is;
   - and error on a trusted admission with no marker.
   Report an admitted lemma as assuming its **whole statement**, in those
   words.

### Slice 2 — needs a build, and is what makes the tool definitive

5. **Join against a checking manifest (G1).** Have whatever runs the `-vok`
   sweep write `etc/vok-status.json`: git rev, rocq version, and one record
   per file with its `.v` **blob hash** and exit code. `tcb-report.py` joins
   on it and annotates each file `checked` / `UNCHECKED` / `STALE (source
   changed since)` — blob hash, not mtime, so a rebase cannot fake it.
   `--require-checked` exits non-zero, which makes it a gate. The sweep
   already exists as an ad-hoc script; committing its output is most of the
   work.
6. **Cross-check against `Print Assumptions` (G1, G7).** Add
   `v3_proof/assumptions.v` containing nothing but
   `Print Assumptions Election.raft_election_safety.` and the same for
   `wp_raft__Step`, reached from `should_build.v`. CI already does a full
   `.vo` build, so archiving that output is nearly free. Then
   `tcb-report.py --compare-print-assumptions <file>` diffs ground truth
   against the syntactic estimate and reports names on one side only. **This
   is the single change that converts the tool from a viewer that is
   believed into one that is checked**, and it retires G7 as a worry.

### Slice 3 — when someone cares about the framework number

7. **Second root for the model (G5).** `--also-root new/golang`, plus a
   section counting this development's *diff* against the upstream
   merge-base in `new/golang/defn/` (hard TCB — the operational semantics)
   separately from `new/golang/theory/` (lemmas, which are checked). The
   `defn/` line is the one that should make a reader stop.

## Rule of thumb until the above lands

When quoting the trust base, quote **the full-tree run**
(`etc/tcb-report.py` with no `--scope`), which on
`worktree-election-close-admits` says *43 assumed — 8 `Admitted`, 35
`Axiom` — 80 definitions, 953 lines, 6.2% of the development*, and say in the
same breath that the numbers are syntactic and that election safety rests on
an un-constructed ghost state. A `--scope election` figure quoted on its own
is misleading in three independent ways (G2, G3, G4).
