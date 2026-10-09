# What the btree proof cost

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
`copy-memmove` branch) adds Perennial's own build, about 10 minutes wall on 24 cores.

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
