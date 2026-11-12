# What the btree proof cost

Measured on the proof of google/btree (`EtcdGrove/Btree/`, 2026-10-08/09), before it
moved onto the cache's fork (the same code, renamed: the proofs carried over unchanged,
so the numbers stand, but for the non-generic API the fork lacks).

## Building it

A clean build of the btree proof and its translation, with Perennial (and Iris)
already built, measured 2026-10-09 with
`etc/build-report.py build --packages=<Perennial override> EtcdGrove.Btree.Results GoogleBtree`
on 24 cores:

| | |
|:--|:--|
| wall time | **1m49s** |
| CPU time | 12m23s (166 modules) |
| longest import chain | 1m38s (bounds the wall time on any number of cores) |
| peak memory | 2.8 GiB (`Proof/node__remove`) |

Two modules dominate: `Proof/node__iterate` (1m03s, on the critical path) and
`Proof/node__remove` (57s); next are `node__insert` (19s) and `BTreeG__ReplaceOrInsert`
(16s). By CPU: proofs 58%, specs 29%, lemmas 6%, the translation 3%.

A build that also rebuilds Perennial (needed once after a change to its pin, e.g. the
`copy-memmove` branch) adds Perennial's own build, not measured here (several minutes
on 24 cores).

## Writing it

2026-10-08, from the first look at google/btree (≈20:40 UTC) to the last commit
(23:11 UTC): **about 2.5 hours of wall time**, by one coordinating agent and up to seven
proof agents working in parallel (one per group of functions: Low, Alloc, Struct, Read,
Insert, Remove, Item).

| | |
|:--|:--|
| proof agents (as reported per run, summed) | ≈ 2.73M tokens, ≈ 4.2 agent-hours |
| coordinator (design, `Defs`/specs, Perennial fixes, integration; approximate, from its context counter) | ≈ 0.6M tokens |
| **total** | **≈ 3.3M tokens** |

Per group (tokens / wall time of each run): Low 220k / 13m; Alloc 261k / 18m; Struct
258k / 23m; Read 554k / 65m; Insert 357k / 38m; Remove 201k / 12m (stopped on two spec
problems, then) 555k / 70m; Item 151k / 12m (stopped on a missing Perennial rule,
then) 177k / 3m.

## Size

| | Lean lines |
|:--|--:|
| `Tree`, `Model`, `Defs`, `Init`, `Item`, `NodeLemmas`, `ListLemmas`, `Fractional`, `Link`, `Results` | 1,428 |
| `Spec/` (74 files) | 2,601 |
| `Lemmas/` (7 files) | 3,130 |
| `Proof/` (73 files) | 6,470 |
| **total** | **13,629** |

for 641 non-blank, non-comment lines of Go (`btree_generic.go`), about 21 lines of Lean
per line of Go. Perennial changes on top (branch `copy-memmove`): about 200 lines.

## Where the effort went (and what could be automated)

From the seven proof agents' transcripts (aggregate counts; the transcripts do not keep
the agents' thinking text, so it is inferred from build counts, errors and output size):

- **392 build-and-check runs, 256 (65%) with errors.** About 130 errors were "unsolved
  goals", partly the trick of ending a proof with `done` to see the goal.
- **Waiting on the compiler: 40–47% of wall time** for four of the seven groups (Low,
  Alloc, Struct, Read; 2–21% for the others). Every check recompiles the whole file
  (about 60s for `Proof/node__iterate`), and the only way to see a goal is to make the
  build fail.
- **About 814k output tokens**, of which roughly 190k is proof text written; the rest is
  almost all thinking, mostly about why a tactic did not match.
- **About 2.4M characters of build output fed back to the agents**: Perennial goals print
  the whole rest of the function as a GooseLang term. Re-reading that context is most
  of the ~2.7M total tokens.

**Hard thinking** (not automatable; a small share of the tokens): the specs and
invariants (keys rather than items; owned vs frozen nodes under copy-on-write; which
shape facts the code needs not to panic), finding modelling problems (Perennial's
unsound `copy`, the missing pointer-conversion rule, two callee specs demanding too much
ownership), and a few invariants (`hit` in descending iteration; the state joining
steal-left, steal-right and merge in `growChildAndRemove`; after a merge the second
`remove` descends into the merged child).

**Easy work that could be automated:**

1. *Pure list facts* (`take`/`drop`/subslice/`set`/length, sortedness, in-order
   contents): most of `Lemmas/` (3,130 lines). The Insert, Read and Remove agents
   re-derived the same lemmas (they collided on names like `sorted_mid`,
   `elemsAux_append`). A decision procedure for list segments and one shared lemma
   library would remove most of it.
2. *Perennial tactic gaps*, each a detour: `wp_auto` cannot load a field through a
   fractional struct points-to (two agents wrote workarounds independently); unnamed Go
   results block `wp_auto`; value methods called through a pointer need manual steps;
   short-circuit `&&` in loop conditions is split by hand; `zero_val w64` does not match
   `W64 0` syntactically; `removeOp` unfolds on one side of a goal but not the other.
3. *Bounds side conditions*: the repeated
   `rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]` before slice
   and index steps, which `wp_auto` could discharge from the context.
4. *Framing mismatches* in the Iris proof mode (44 errors), mostly a term not matching
   syntactically; normalising before framing would catch many.
5. *Boilerplate*: the 19 `BTree.*` wrappers are a few lines each and could be generated.

An estimate, a judgment from the error mix rather than a measurement: well over half the
build iterations and thinking went into items 1–4.

**What would speed it up most**, in order: interactive, incremental checking
(goal-at-position, per-tactic feedback through Lean's language server or a REPL instead
of whole-file rebuilds); shorter goal printing (hide the continuation and the GooseLang
term by default); a shared list/tree lemma library with list-segment automation; fixing
the tactic gaps of item 2; checking callee specs before agents build on them (two spec
defects were found only after an agent depended on them).
