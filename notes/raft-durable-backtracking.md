# Backtracking in the raft durability proof, and what was avoidable

Started 2026-11-02; append to it as the proof goes on, one entry per event, in the format of
section 1, and update sections 0 and 2. An *event* is any time a spec, invariant, predicate, lemma
statement, piece of Go code or plan item that had already been designed, approved or proved turned
out false, too weak, too strong, unprovable or incomplete, and had to change, including changes to
proved code that then had to be re-proved. The aim is to find which mistakes are avoidable in
future proofs, not to assign blame.

The effort: the `examples/kvdurable` key-value store (kvreconf plus crash and restart from a file),
raft's durability API (candidate 12: `raftState`, `nodeVacant`, the *enter* update of a `Ready`,
`RestartNode` over an atomic update), its proof (`notes/raft-durability-proof-plan.md`), and
kvdurable's adequacy, 2026-10-31 to 2026-11-02. Sources cited below as `cN`, `rN`, `II(x)`, `kvd-*`
are the agent reports in the scratch directory `~/spec-scratch/raft-durability/` (not in the
repository). Each event's report there gives the detail.

## 0. Diagnosis

From 101 counted events (section 2): spec phase 32, plan 10, stage I 10, stage II raft 30,
stage II clients/kvdurable 19.

**What took the time.** One time sink was not a design mistake: the build cost of a statement
change (`InvRawnode` has about 1560 importers). The rest were five avoidable patterns.

1. **Invariants were stated without checking every producer and consumer (31 events, the largest
   class).**
   - Stage I added conjuncts (`durTie`, the attach record, R3–R6's ghost, `ownRawNode`'s relations)
     and restated predicates on paper, leaving their preservation as `sorry`s.
   - Stage II found that many could not be proved. For example, 16 of `durTie`'s 22 obligations
     were unprovable, and the RawNode layer was never restated for the cut.
   - Each discovery meant restating a high-fan-out file again.
   - *Avoidable by:* a producer/consumer table for each new conjunct (every allocation, step
     lemma, cut, restart, stop), and one representative preservation proof before the restatement
     lands.

2. **Specs were composed without checking that callers can establish the premises (18 events,
   about 26 counting secondary causes).**
   - Examples: the key-independent storage frame (three times), `newReplica`'s missing premises,
     `openStorage`'s fraction, `bootLen`, `readyFits`.
   - *Avoidable by:* a skeleton pass before stage II. Every function's spec on the whole chain
     (`StartCluster` → `RestartNode` → `run` → the Ready receive → `Main`'s adequacy) gets stated,
     each proof body left `sorry`, and each caller's proof is sketched far enough to discharge its
     callee's premise.

3. **The riskiest path was proved last (4 events as primary, about 12 counting secondary causes,
   and the most expensive ones).**
   - The restart path (`raft_restart` → `RestartNode` → `newRaft`) is where durable state meets a
     restart. It was proved after `run`, the Ready receive and all the clients.
   - Its discoveries were therefore API changes with the most knock-on work: R1's commit, then
     `wcommit` when `RestartNode.spec` turned out false; the freeze point; `▷ raftState`; the
     narrowed configuration point; the attach record; the `newRaft` window.
   - *Avoidable by:* proving (or sketching to the first hard step) the piece whose spec is the
     newest and the least like an existing one first.

4. **A generalization went beyond what any client produces (5 events).**
   - The spec let the stored commit lag arbitrarily (`σ.commit ≤ S.commit`). That made
     `RestartNode.spec` false: a counterexample built from configuration changes above a lagging
     commit, `notes/decisions.md`, "wcommit".
   - kvdurable only skips commit-only writes.
   - *Avoidable by:* allowing exactly what a real client does (here: the hard state written with
     each batch's entries), and generalizing only once a proof shows the general form is true.

5. **Go behavior was not walked before the spec (15 events), and Go facts were left out of the
   predicates (7 more: the plan omitted a function or window).**
   - Examples: raft's self-send panic, `HasReady`'s hard-state test, the vote never taken back,
     `MemoryStorage`'s data aliasing, the snapshot's term, `newRaft`'s window,
     `Cluster.replica` not tied to the incarnation, a double crash closing a channel twice.
   - The stale-node argument was settled only by Go reproductions, after a reviewer had endorsed
     a false argument.
   - *Avoidable by:* before specifying, list the Go code's windows (start to first write, attach
     to `newRaft`, after a crash, after a stop) and its `panic`s, and decide for each which
     conjunct or premise records it. Write a Go test for any argument about an interleaving.

**Two process failures made each of these worse.**

- **Repairs were not checked as hard as designs.** About 16 events were a fix of an earlier fix:
  R1, R3, R4, R5, R6, the attach record, `durTie`, fix D, the storage frame, `storDL` (five times),
  the storage key (six times), and others. Give a repair the same producer/consumer and
  composition checks as a new design.
- **Separation-logic properties of new predicates were found late (12 events, about 16 counting
  secondary causes).**
  - `raftState` is not timeless because it holds an invariant, which forced `▷` in
    `RestartNode`'s atomic update and a client-side workaround first.
  - Other examples: fractions handed over whole and needed back frozen, a stop answer needed
    before the receive, masks at `nroot`.
  - Before publishing a predicate, write down whether it is timeless, persistent or exclusive,
    which fractions move, and which masks clients will hold it under.

**Smaller causes.**
- Spec candidates were written in Markdown and never type-checked (unbound binders, type errors:
  r6–r8). Write candidates as Lean files with `sorry`s.
- Tooling (section H):
  - a `.lake` shared between worktrees, rebuilt under other agents;
  - the disk 98% full, preventing one build per agent;
  - agents out of context mid-proof, and the usage limit stopping every running agent twice;
  - the trust-base check skipped for lack of a full build.

**Checklist for the next multi-stage proof** (section 4 has the event mapping):
1. Prove or sketch the riskiest piece (here the restart) first.
2. Run the skeleton pass: every spec on the end-to-end chain stated, with callers sketched against
   it.
3. Keep a producer/consumer table for every new conjunct, with one preservation proof per
   conjunct before restating.
4. Walk the Go code's windows and panics.
5. Allow only what clients produce.
6. Check each repair as hard as a design.
7. Write down each new predicate's logical properties (timeless, persistent, fractions, masks).
8. Write candidates in Lean.
9. Plan the infrastructure: a build directory per agent, disk headroom, and high-fan-out
   restatements batched into one pass.

---

## How to read this

**Sources.** All files are in `/home/ubuntu/spec-scratch/raft-durability/` unless marked otherwise:
- `cN` = `candidate-N.md`, and `c12` = `candidate.md`;
- `rN` = `review-N.md`;
- `PR1` = `plan-review-1.md`;
- `plan` = `notes/raft-durability-proof-plan.md` on `origin/worktree-agent-raftrestart`;
- `I-k` = `stageI-k-*.md`;
- `II(x)` = `stageII-x-report.md`;
- `kvd-*`, `kvdurable-*` = the kvdurable reports;
- `decisions` = `notes/decisions.md` on `origin/worktree-agent-newraft`.

Commit shas are in `/home/ubuntu/etcd-grove` (worktree `kvdurable`).

**Fields of each entry:** id (the existing label, or a short name), date and stage, source, *old* →
*new*, who or what found it, cost, and the root-cause category in square brackets. The last line,
"Avoid:", says whether design time could have caught it, and by what concrete check.

**Root-cause categories:**

| code | cause |
|---|---|
| (a) | invariant designed without checking every consumer and producer |
| (b) | spec composed without checking that a caller can establish its premise, or that the callee's post suffices |
| (c) | separation logic: ownership, fractions, persistence, timelessness, laters, masks |
| (d) | Go behaviour not checked against the spec: a missing premise, or a Go fix needed |
| (e) | ordering: a riskier piece (start, restart) proved late |
| (f) | generalization beyond what clients need made a spec false |
| (g) | the plan omitted a function or a window |
| (h) | tooling and infrastructure (listed separately, section H) |
| (i) | other |

**Marks.** HF marks a change to a high-fan-out file: `InvRawnode*` (about 1560 importers), `InvApi`,
`InvNode`, `InvNodeChan`, `Protocol/Ghost*`, `StepGhost`, `ownRaftPhys*`, `RaftState`. "(?)" marks
an item the sources leave uncertain.

**Label collisions.**
- `G1`–`G3` mean different things in different places. In `I-4` and `I-6`, G1 is the attach record
  and G2 is the cut's link (`durTie`). In `I-5` and `kvdurable-image-report.md`, G1 is the
  frame not keyed by `K`, G2 is that the client has no share of the log, and G3 is that
  `Snapshot` names no snapshot.
- `G4`–`G23` and `S1`–`S5` are kvdurable's gaps, from `II(e)`, `II(h)` and `II(j)`.
- Fixes A–D are the fixes of `II(g)` round 1.
- `R1`–`R10` are the findings of `PR1`. `R-U*`, `R-I*`, `R-N*` and `R-A*` are the repairs in the
  candidate headers. `N*` in r2/r6, `A*` in r3, `F*` in r4/r5, `M*` in r7, `P*` in r8 and `G*`/`Q*`
  in r9 are review findings.

---

## 1. The events, in order

### Phase S: the spec phase (2026-10-31, candidates 1–12, reviews 1–9)

Candidate 1 is not on disk. It is reconstructed from r1's quotes and c2's change list (`c4`, the
"Candidate 2's header" section).

- **E01 · R-U1/U2, the stale restart point.**
  - Where: S, r1→c2 (r1 §U1–U2; `c4`, "Changes against candidate 1").
  - Old: c1's `RestartNode` took a persistent `restartable γ N id D`.
  - What broke: the reviewer showed that a restart from an older `D` collects delayed grants and
    acks, giving two leaders of one term.
  - Fix (c2): bind before the first step (`nodeDisk_rebind`, an exclusive `freshInc`). E13 later
    removed the whole scheme.
  - Cost: one round. **[cat c] [stage S]**
  - Avoid: yes. Ask of each persistent premise whether a stale copy of it can be replayed.

- **E02 · R-U3, a binding law without its id.**
  - Where: S, r1 §U3.
  - Old: `nodeDisk_bind` had no id premise.
  - What broke: node 2's incarnation could be bound to node 1's disk.
  - Fix (c2): `⌜ι'.id = id⌝`. **[cat a] [stage S]**
  - Avoid: yes. Check each binder of a law against each index of the predicates it relates.

- **E03 · R-U4, `Applied` above the snapshot.**
  - Where: S, r1 §U4/B3.
  - Old: `Applied = 0 ∨ prev ≤ Applied ≤ D.hs.Commit`.
  - What broke: the reviewer showed that conf changes in `(snap, Applied]` are skipped, giving two
    leaders.
  - Fix (c2): `Applied ≤ snapIndex`. Filed as `nonissues/raft-applied-above-snapshot-confstate.md`.
  - Cost: the bound was lost again in c4 (E19). **[cat d] [stage S]**
  - Avoid: yes. Read `newRaft`/`appliedTo` for safety conditions as well as panics.

- **E04 · R-U5, `readyWrite_volatile`'s unbound `prev`.**
  - Where: S, r1 §U5.
  - What broke: any vote-granting batch could be declared volatile.
  - Fix (c2): `readyWrite … p δ`, with `p` given at the receive. Removed with E13.
    **[cat a] [stage S]**
  - Avoid: yes. Tie each parameter of a law to its producer.

- **E05 · D6, restarting a bootstrapped node from empty state.**
  - Where: S, c1–c4 (r1 U6, r2 N4, c2 R-U6, c3 R-N4/N5, c4 R-A2).
  - Old: a scope premise, "to drop if raft's proof does without it". c3 dropped it for an
    empty-`ConfState` rule, and c4 brought it back.
  - What broke: r2's counterexample. A one-voter bootstrapped node restarted empty commits a
    different index 1.
  - Fix: D6 is a scope restriction again (c4).
  - Cost: four candidates and three reviews. **[cat d] [stage S]**
  - Avoid: yes. Trace the one-voter crash-before-first-write run in Go at c1.

- **E06 · R-N4/N5 → A1–A3 → R-A1/A3, the restart's configuration.**
  - Where: S, c3→c4 (r2 N5, r3 A1–A3).
  - Old (c3): no snapshot in a boot-log cluster means an empty `ConfState`. This came from r2's
    misreading of etcd.
  - What broke (r3):
    - A1: the post contradicts `nodeConfig`'s own `confAt`.
    - A2: the bootstrap replay cannot be described.
    - A3: etcd restarts at its backend's `ConfState`.
  - Fix (c4): the client names a point `a ≥ max(c, Applied)`, with
    `confAt γ a m ∗ confStateIs csm m`. **[cat d] [stage S]**
  - Avoid: yes. Read etcd's `bootstrap.go` before adopting a premise about etcd, and unfold
    `nodeConfig`.

- **E07 · The `storDL` chain (later `nodeCommitLb`).**
  - Where: S, c1→c12 (r1 I1, r2 N1, r3 A5, r5 F1, r6 N5).
  - The forms it went through:
    1. c1: over the delivered log, which is false after a restart.
    2. c2: `incCommitLb` at the rebind only, which is unobtainable while running, so every snapshot
       is blocked.
    3. c3: `nodeDriver_commitLb`, which the snapshot threads do not hold.
    4. c4: `deliveredLogLb_commitLb`.
    5. c7: `storDL := storBnd`, which breaks mid-batch `CreateSnapshot` and is unsound at the
       attach.
    6. c8: sealed, with three sources, but with no monotonicity law.
    7. c9: `storDL_mono`.
    8. c12: renamed `nodeCommitLb`.
  - Cost: about six candidates and five reviews. Each fix introduced the next finding.
    **[cat a] [stage S]**
  - Avoid: yes. Tabulate every `DL` consumer at c1: the restart, the run loop's snapshot, the
    snapshot threads of kvreconf and etcd, and mid-batch `CreateSnapshot`.

- **E08 · R-I2, the storage filled before `ι` exists.**
  - Where: S, r1 §I2.
  - What broke: `openStorage` and etcd's replay call storage specs before `RestartNode` names `ι`.
  - Fix (c2): allocate and bind first. Superseded in c6 by the detached mode (E12).
    **[cat b] [stage S]**
  - Avoid: yes. Walk each client's call order.

- **E09 · The `Stable`/`Wf` model against `MemoryStorage`.**
  - Where: S (r1 I3/I4/P5, r2 N6/N7, r3 A8/A9).
  - What broke:
    - the snapshot's term was missing;
    - `Stable.next` differs from `Append` in two cases;
    - an index-0 snapshot was allowed;
    - `ErrSnapOutOfDate` was not handled.
  - Fix: patched in c2–c4. `Stable` was later replaced by `RaftState`. Minor.
    **[cat d] [stage S]**
  - Avoid: yes. Write `next`/`compact` out against `storage.go` first.

- **E10 · I5/N8, etcd's `Save` is not one write.**
  - Where: S (r1, r2).
  - What broke: commit-only saves are unsynced, and writes can tear.
  - Fix: only the text, deferred to the WAL model. The torn-write law is still open.
    **[cat d] [stage S]**
  - Avoid: partly. Read the WAL `Save` path.

- **E11 · Minor fixes to the spec text.**
  - Where: S (r1 P1–P5, r2 N9–N11, r3 A7–A11).
  - What: wording; accessor laws; laws that dropped exclusive resources; a redundant conditional
    `confAt`. One real item: N9, where today's voters-only `ConfState` premises excluded restarts
    at joint configurations (too strong).
  - Fix: c3–c4. **[cat i] [stage S]**

- **E12 · Whether the restart storage can be built.**
  - Where: S (r2 N2 → c3 R-N2 → r3 A4 → c4 R-A4 → the user's Q3(b) in c6).
  - Old: the storage holds `D` exactly, then `D.compact c`.
  - What broke: kvdurable's placeholder-snapshot restore is refused by `ApplySnapshot`'s spec, and
    `J.B c` had no source.
  - Fix: the user ruled that "a storage no node is attached to needs no bounds" (detached mode).
  - Cost: three candidates, two reviews, one user decision. **[cat b] [stage S]**
  - Avoid: yes. Check `openStorage`'s calls and etcd's replay against each MemoryStorage
    premise.

- **E13 · N3, A6 and F7: StartNode and its crash windows.**
  - Where: S (r2 N3, r3 A6, r4 F7).
  - What broke:
    - `StartNode` was left "unchanged" while its keys moved;
    - an unused `freshBoot` had no exit;
    - `StartNode` consumed `nodeBoot`, which strands a node that crashes before its first write.
  - Fix:
    - c3: `nodeBoot_rebind`;
    - c4: `freshBoot_halt`;
    - c7: `nodeBoot` made persistent, which needs its ghost moved into `raftState` (r5 F8).
  - **[cat g] [stage S]**
  - Avoid: yes. Enumerate the windows: before the first write, between the start and the attach,
    and after the stop.

- **E14 · The user's critique of candidate 4.**
  - Where: S, c4→c5 (`c5`, "The user's critique of candidate 4").
  - Old: `nodeDisk`, `nodeInc`/`freshInc`/the rebind, `readyWrite`, `batchWritten`, `batchSafe`,
    `readyMsgs` and the write laws.
  - What broke: the user said "Ready returns an AU … no `nodeDisk` in the raft library …
    `nodeInc` seem bad."
  - Fix: one atomic update in the Ready's post, and the client-owned `raftState γ id S`.
  - Cost: the API of c1–c4 (four candidates, three reviews) was discarded. Only the Go facts F1–F8
    survived. **[cat i] [stage S]** (design shape)
  - Avoid: yes. Put the shape to the user before c1: who owns the disk, and an update versus
    obligations.

- **E15 · The user's Q1 answer on c5: `raftState` holds only the durable parts.**
  - Where: S, c5→c6.
  - Old: `S.node`, the node object currently entering states.
  - Fix: `raftState` is the durable half only. `nodeVacant` is introduced to say that the old node
    has stopped.
  - Cost: one candidate. **[cat i] [stage S]**

- **E16 · F2, the atomic update pointed the wrong way.**
  - Where: S, r4 F2 (c5–c6).
  - Old: the Ready's AU made raft the supplier of the client's `raftState`, and `storageHolds` sat
    on raft's side.
  - Fix (c7): a client-applied, mask-polymorphic `∀ E, ↑N ⊆ E → … ={E}=∗`. **[cat c] [stage S]**
  - Avoid: yes. Check against the `atomic_update` definition: the holder receives `α`.

- **E17 · The stale-node argument.**
  - Where: S, c6→c9 (r4 F1, c7 §5, r5, r6 N1/N2, c9 §5′).
  - Old: c6 said "a stale update cannot fire". c7 dropped `nodeVacant` and argued that "two nodes
    of one id are harmless". r5 endorsed this, which was a reviewer error.
  - What broke:
    - r4: a stopped node's unfired update fires after a restart from the same `S`, overwriting a
      committed entry;
    - r6 reproduced it in Go: two in-memory leaders of one term (N1) and a `commitTo` panic (N2).
  - Fix (c9): the argument withdrawn, and r4's original repair restored: `nodeVacant` plus the
    `nodeRunning` gate.
  - Cost: three candidates and three reviews, and a reversal. *Check* was later deleted (c12).
    **[cat d] [stage S]**
  - Avoid: yes. Take the reviewer's minimal repair. A Go test with two instances of one id
    settles it at once.

- **E18 · F4, ungating the committed-log facts.**
  - Where: S, r5 F4 → c8 → r6 N1.
  - Old: the facts are "global truths whichever node computed them".
  - What broke: false for a stale node's rebuilt Ready.
  - Fix: kept ungated only because of E17's one-node-per-id. **[cat a] [stage S]**
  - Avoid: yes. Check every producer of the facts.

- **E19 · F3, `RestartNode` admits panics.**
  - Where: S, r4 F3 (c4→c6).
  - Old: R-A1 replaced `Applied ≤ snapIndex ≤ Commit` by `≤ a`, with `a` unbounded.
  - What broke: the panic bounds were in prose only, so the spec admitted panics.
  - Fix (c7): the full panic bounds, plus the scope restriction `a ≤ commit`.
  - Cost: a regression introduced by a fix. **[cat d] [stage S]**
  - Avoid: yes. Re-check the Go panic list (F5) on every edit of `RestartNode`.

- **E20 · F4/Q5, the snapshot and compaction laws on `raftState`.**
  - Where: S, r4 (c5–c6).
  - What broke: the first persisted compaction makes every later exact-state update unfireable.
  - Fix (c7): the laws dropped, along with `S.snap`/`S.prev`. The restart accepts a storage
    compacted above `S`. **[cat a] [stage S]**
  - Avoid: yes. Check each law against the update's exact precondition.

- **E21 · The storage key and the attach-once token.**
  - Where: S, c2→c12 (r4 F5, r5 F2, r6 N4, r7 M1).
  - The forms the key went through:
    1. `ι` (c2);
    2. the node object (c5–c6);
    3. the storage object, which is not unique (r5 F2);
    4. `memStorFresh`, whose token is spent twice (r6 N4);
    5. `storFresh γ K` (c9), which cannot be minted (r7 M1);
    6. a fresh ghost `K` (c10);
    7. no token at all: raft picks `K` at the attach (c12).
  - Cost: about seven forms over six candidates. **[cat c] [stage S]** (with b)
  - Avoid: yes. State who mints the token, and from what, at the first design.

- **E22 · F6, the commit law did not agree with `S'`.**
  - Where: S, r4 F6.
  - Fix (c7), then dropped in c11 (E30). **[cat b] [stage S]**

- **E23 · `memStorFresh_compacted`.**
  - Where: S (r5 F3 → c8 `⌜c' = c⌝` → r6 N3 → c9 `⌜c' ≤ c⌝`).
  - What broke: generalizing `memStorFresh` dropped a law three callers use, and its repair with
    `=` over a lower-bound predicate derives `False`.
  - **[cat a] [stage S]**
  - Avoid: yes. Check the law against the predicate's monotonicity lemmas.

- **E24 · F6, `nodeDriver` is not timeless.**
  - Where: S, r5 F6.
  - Why: it holds `clusterInv`.
  - Fix (c8): a `▷` in the lock invariant. Minor. **[cat c] [stage S]**

- **E25 · F5, "the state returns to S₀, which makes the same promises".**
  - Where: S, r5 F5.
  - What broke: this was false, because promises are history, not a function of the state.
  - Fix: corrected in c8, then withdrawn with E17. **[cat i] [stage S]**

- **E26 · Unbound binders and type errors in the candidates.**
  - Where: S (r6 N5–N6, r7 M2/M5, r8 P4).
  - What: `∀ a0 k0` unconstrained; `c`, `Applied` and `commit` free; `σ.base` versus `S.base`.
  - Fix: c9–c11. Classed as tooling, since the candidates were never type-checked (section H).

- **E27 · M3, the node table pins an id's names forever.**
  - Where: S, r7 M3.
  - What broke: `Stop` discards `live` at `true`, so even sequential restarts of an id were
    impossible.
  - Fix (c10 §7): key the table by node object, with `nodeVacant` as the id's slot.
    **[cat a] [stage S]**
  - Avoid: yes. Check the internal producers of `isNode`.

- **E28 · The `InitialState` chain.**
  - Where: S, r7 M4 → c10 → r8 P1 → c11 → r9 G1. Commit `2de93b57bd`.
  - Old: r7 said kvdurable needs an attached-mode `InitialState` and that there is no race. c10
    said its spec "covers both modes".
  - What broke:
    - r8: unprovable, and a real data race (`go test -race`);
    - c11: a detached-only spec plus a Go copy of the hard state;
    - r9: the fix's round trip fails five of six, because the promoted `SetHardState` skipped the
      copy, so `SetHardState` had to be shadowed.
  - Cost: three candidates, three reviews, two Go fixes. Superseded about 12 hours later by the
    image redesign (E46). **[cat d] [stage S]**
  - Avoid: yes. Check that every storage read is legal in attached mode, and run `-race` and the
    tests after a Go edit.

- **E29 · Smaller storage repairs.**
  - Where: S (r8 P2, P3, P5; r9 Q2).
  - What:
    - `memStorFresh` did not name the stored snapshot;
    - an index-0 snapshot case;
    - the attach took `J.B c` where the invariant needs `∀ k ≤ c`;
    - "never re-attached" filed as scope.
  - Fix: c11–c12. **[cat b] [stage S]**

- **E30 · Q1 (r9), `restartStorage` lost the client's frame `F`.**
  - Where: S, r9 Q1.
  - Old: the frame was dropped silently in c8 (`candidate-8.md:189`), and r6–r8 missed it.
  - Fix (c12): a frame `F`, as `bootStorage` has. Not re-reviewed. The frame was later found too
    weak (E52, G1). **[cat b] [stage S]**
  - Avoid: yes. Diff the new definition against today's `bootStorage`.

- **E31 · B1/B2, kvdurable's Go bugs found by spec review 1.**
  - Where: S, commit `948da3229d`.
  - What broke:
    - B1: compacting past raft's applied index after a restart, which panics;
    - B2: read contexts reused across incarnations, which gives a stale read.
  - Fix: Go: `rafted`, and a cluster-wide `readSeqs`. **[cat d] [stage S]**
  - Avoid: yes. Check every `Compact` argument against "≤ applied", and ask of each identifier
    what survives a crash.

- **E32 · r3's etcd lead.**
  - Where: S, r3 §4.5.
  - What: backend `AddMember` committed before the WAL fsync.
  - Status: never confirmed; it awaits a gofail test. No `issues/` entry. **[cat d] [stage S]** (?)

- **E33 · c12's deletions.**
  - Where: S/plan, c12 and plan, "Review 1 and what it changed".
  - What was deleted: *check* (c7), `storFresh`/`storFresh_alloc` (c9–c10), the driver's `batch`
    field (c6). `snapGiven` was merged into `nodeAppliedLb`.
  - Effect: these superseded plan items I-3 (*check* at the receive), I-4 (the once-register) and
    I-8 (`batch`). The `snapGiven` merge's safety was checked "by reading the code" only (?).
  - **[cat f] [stage S]** (vocabulary beyond what the clients read)
  - Avoid: yes. For each predicate, name the client that reads it.

- **E34 · ENT, the sign extension of the entry type.**
  - Where: 10-31 23:51, kvdurable extension work (`kvdurable-ext-report.md`; `81f03c4e0a`).
  - Old: `encEntry` used `W64 (uint.Z e.Type')`, but Go's `uint64(int32)` sign-extends.
  - Fix: `sint.Z`. Small. **[cat d] [stage I]**
  - Avoid: yes. Read the conversion's semantics.

### Phase P: the proof plan and its review (2026-10-31, `PR1`, `plan` §0)

- **E35 · R1, the commit's term at a restart (plan amendment 2).**
  - Where: P (PR1 §R1; plan, "Review 1"). The idea started at c5 (E15), which took the commit out
    of the state.
  - Old (amendment 2, from survey-protocol §3D): the restarted node derives
    `commitIn … σ.commit t` (`t ≤ S.term`) from the AU's `isCommittedLogLb` plus `TermsLe`.
  - What broke: the reviewer's counterexample. A node at term 5 writes commit 10, which only term
    9's leader committed. `commitJ` needs `t ≤ tm`, and weakening it breaks `campDyn`.
  - Fix (a user decision, an API change): `RaftState.commit`; the sealed body holds the
    certificate; `StorageHolds` allows `σ.commit ≤ S.commit`; the AU loses its committed-log
    conjunct. The approved candidate 11 was amended.
  - Cost: one user round. Re-amended in II(o)/(p) (E78, `wcommit`). **[cat e] [stage P]** (also b)
  - Avoid: yes. State `raft_restart` with `sorry` against `ownLogGhost`'s `#Hcommit` during the
    spec phase, and check that the AU's facts give `commitJ`.

- **E36 · R2, the volatile half cannot reach the entered authority.**
  - Where: P (PR1 §R2).
  - Old: the D authorities' slot sits in a per-node invariant while a node runs, only `vote_excl`
    needs it, and the step lemmas keep their statements.
  - What broke: `ownRaftGhost` has no `N` and no token, and at least nine lemmas look up an
    authority: `ack_agree`, `heartbeat_commit_le_last`, `not_doomed`, `win`, and others.
  - Fix: a permanent `slotInv` at `raftN.@"slot"`. `step_app_accept`, `step_heartbeat`,
    `snap_fastfwd`, `snap_restore` and `heartbeat_commit_le_last` become fupds, and their code
    callers change (`dispatch_Heartbeat`, `ghost_stepCDM`/`CDSM`, `ownStepGhost_dyn`).
  - **[cat c] [stage P]** (with a)
  - Avoid: yes. Grep every lookup in the authorities and ask where each caller gets its
    invariant from.

- **E37 · R3, the leader's self-match at `win` is pending.**
  - Where: P (PR1 §R3). survey-protocol §3E was wrong here.
  - Old: "its own Match comes from `pselfAck`", so `matchedOk` is unaffected.
  - Fix: `matchedOk` exempts a self entry whose terms are below `s.term`. Found too weak in II(a)
    (E54). **[cat a] [stage P]**
  - Avoid: yes. Check every producer of `matchedOk`'s entries (`win`'s `acks_add`).

- **E38 · R4, a durable `ackAgree` for current-term acks.**
  - Where: P (PR1 §R4). survey-protocol §3D was wrong here.
  - What broke: *enter* cannot produce it once the base passes the ack.
  - Fix: a restart lemma from Leader Completeness for the acks in `(σ.commit, cE]`. This was itself
    wrong (E60). **[cat a] [stage P]**
  - Avoid: yes. Write the lemma's argument against `durPers`'s actual conjuncts.

- **E39 · R5, the candidate's `isCampK` in `dynEnv`.**
  - Where: P (PR1 §R5).
  - What broke: the fact cannot exist while its campaign is pending, and it has 147 uses outside
    `Protocol/`.
  - Fix: drop it; `win` takes the campaign from `voteJust` and the slot. The drop was incompletely
    propagated (E55, E56). **[cat a] [stage P]**

- **E40 · R6–R8, which half holds what.**
  - Where: P (PR1 §R6–R8).
  - R6: the leader-side maps were ambiguously in both halves. Fix: in the volatile half while a
    node runs, in `nodeVacant` otherwise. Its realization, `ledgerCamps`, later turned out
    unprovable (E57).
  - R7: the outbox wands over `πc` miss a re-granted queued vote and the self-messages. Fix: wands
    over the monotone `durFrags W`, with the driver carrying the fragments.
  - R8: `raft_restart` consumed `ownDurGhost`, and `raft_stop` cannot take the client's token.
    Fix: give `ownDurGhost` back, and a generation counter.
  - **[cat a] [stage P]** (R8 is b/c)
  - Avoid: yes. Write the `raft_restart`/`raft_stop` statements against the AU and the *enter*
    closure.

- **E41 · R9, F3 (`check_leader`) deferred.**
  - Where: P (PR1 §R9).
  - Old: "a flag, or a lemma" (plan risk 4), left for stage II.
  - Fix: a conjunct of `ownRaftGhost` (`outMsgOk`/`OutPend`), stated in stage I. Its RawNode-layer
    consequence was not propagated (E64, fix C). **[cat e] [stage P]**
  - Avoid: yes. Settle the riskiest invariant before stage I.

- **E42 · R10, the dynamic model has no *enter*.**
  - Where: P (PR1 §R10).
  - Raised to the user, and it dissolved: only the allocation lemmas are used. One user round.
    **[cat i] [stage P]**

- **E43 · PR1's notes N1–N7.**
  - Where: P (PR1, "Notes").
  - N1: `gg`/`gd` must start at `σ.b`, a precursor of E49.
  - N2: `PendOk` must equate the full logs.
  - N3: `ownRaftGhost_intro`'s signature must be fixed first (about 40 re-proofs).
  - N4: masks, since kvdurable's namespaces must be disjoint from `N`.
  - N5: seven code-proof files missing from the plan's lists.
  - N6: the stop drops read credits.
  - N7: confirmed amendments 1 and 3.
  - **[cat g] [stage P]** (N5; N1/N2 are a, N4 is c)
  - Avoid: yes. List the files by grepping the unfolded definitions.

- **E44 · Plan amendments 1 and 4.**
  - Where: P (plan §0).
  - Amendment 1: candidate 11's `bootLen ≤ S.last` corrected to `bootLen ≤ σ.commit`, because
    `Hboot` holds of the commit. Category b.
  - Amendment 4: `Advance`/`ApplyConfChange` with `delivered < a` became an obligation (I-9). Stage
    I never designed it, and it became the one `sorry` left in `RestartNode`, which was then
    narrowed (E81). Category e.
  - **[cat b] [stage P]**

### Phase I: stage I, the invariants and statements with `sorry` (2026-10-31 23:53 to 2026-11-01 16:42)

- **E45 · I1 deviations: `pendBatch`'s arguments, `ownLogGhost`'s new `W`, `raft_start_boot`.**
  - Where: I (`I-1`, deviations 1, 4, 5, 8).
  - What changed:
    - `pendBatch γ id S S' π` became `pendBatch γ id g S' W`, because the cut does not know `S`;
    - the whole `ownLogGhost_*` family (about 25 statements) gained `W`, where the plan had said
      "statements kept";
    - `termLB` could not go in `ownDurGhost`;
    - `raft_start_boot` was missing from the plan.
  - **[cat g] [stage I]**
  - Avoid: yes. Write the cut's caller first, and count the restated signatures.

- **E46 · IMG, kvdurable's own image (`I-5`'s G2 and G3).**
  - Where: I, 11-01 05:21 (`I-5`; `kvdurable-image-report.md`; `61c04f6f15`, `a74edd3978`,
    `ba982fbb34`).
  - Old: `encode` reads back the `MemoryStorage` through `kdStorView`, at `memLog (own ½)`.
  - What broke:
    - G2: raft owns the log above the commit at `own 1`, so `encode` cannot read it;
    - G3: in attached mode, `Snapshot` names no snapshot.
  - Fix: a Go redesign. `Storage.img` mirrors the storage's mutations; `kdStorView` is deleted;
    `encode`, `SetHardState`, `openStorage` and `newReplica` are restated, with about 11 new
    proofs. This also retired E28's Go fix.
  - Cost: one agent round, Go plus tests. **[cat d] [stage I]**
  - Avoid: yes. Check the client's Go reads against the ownership the storage contract gives raft.

- **E47 · I2-1, `memStorAt` cannot be framed by `wp_apply`.**
  - Where: I (`I-2`).
  - What broke: the survey's three mode-generic wrappers (survey-storage §5) were incomplete, and a
    match-defined `memStorAt` is not framed.
  - Cost: 12 client wrappers left `sorry`. **[cat i] [stage I]** (proof engineering)
  - Avoid: yes. Prototype one call site.

- **E48 · I3 deviations 1, 3, 6 and 8.**
  - Where: I (`I-3`).
  - What changed:
    - Dev1: `RestartNode` needs `isCluster γ N`, which candidate 12's premises lacked;
    - Dev3: the law "`deliveredLogLb ⊢ nodeCommitLb`" cannot be stated (no `K`), so it now needs
      `nodeDriver`, and kvreconf's snapshotter must thread `nodeCommitLb`;
    - Dev6: the plan's per-node invariant was not needed;
    - Dev8: `ownRaftPhys` was not generalized (`ownRaftPhysC` was added instead), and the raw
      triples of `RestartNode`/`StartNode` were left at the empty start. This deferral set up
      E79–E82.
  - **[cat b] [stage I]** (Dev8 is e)
  - Avoid: yes. Check that the post's `isNode` and each law can be built from the premises.

- **E49 · I3 open point 1 → the attach record (I4 G1 not made → I6 G1 as amended).**
  - Where: I (`I-3` OD1; `I-4`, "G1 not made"; `I-6` Part 1; `38f2e8f1d9`).
  - Old: survey-start §2.4 and plan I-6: "`ga`/`gdd` start at the attach bounds". Then the
    coordinator's reading of `raftDL`, case `i ≤ c0`.
  - What broke:
    - handing out `nodeAppliedLb`/`nodeCommitLb` before `newRaft` contradicts `ownRaftLog`'s
      `FlOk`/`DtOk`;
    - the decided reading broke `view_dl`/`isStorage_of_V`, which II(c) had just proved. The
      agent stopped.
  - Fix (a user decision): `StorNames.a0/c0/ct`; the disjuncts in `raftBnd`, `raftDL` and
    `nodeAppliedLbU`; `storCaught`; `newLogWithSize` as a wand over the window; `AttachRec` as a
    premise of `newRaft`/`NewRawNode`. I-4's phase-flag idea was refuted.
  - Cost: two rounds and a user decision. Amended again in II(o)/(p) (E79). **[cat a] [stage I]**
  - Avoid: yes. Check the attach's bounds against `ownRaftLog`'s invariants, and grep `raftDL`'s
    consumers before deciding.

- **E50 · G2 (I-4/I-6 namespace), `durTie`, the cut's link.**
  - Where: I (`I-3` OD2; `I-4` task 2, `78b6bb4d15`; `I-6` Part 2, `b7ec30607a`). Fixed in II(i)
    (`464ff91928`).
  - Old: `durTie` said `rs.dur` with `nextUnstable` is the full log
    (`DurFull (rs.dur.next …) (fp++sents++uents)`). Introducing it restated `RawNode.Ready.spec`,
    `acceptReady.spec`, `wp_applyConf_dyn`, `rawNode_applyCC_reseal` and the `_intro` signatures,
    and added 22 `sorry`s.
  - What broke: I-6 proved 6 of them. The other 16 step obligations were unprovable, because the
    step posts let `inprogress` rise with no relation between the old and new logs (a counter-model).
  - Fix (II(i)): tie it to the storage, `DurFull rs.dur (fp ++ stored) ∧ base ≤ prev`, over 17
    files and about 30 sites. Strengthened again in II(i) (E66).
  - Cost: `InvRawnode`/`InvRawnodeReady` (HF) changed twice; three rounds (I-4, I-6, II(i)).
    **[cat a] [stage I]**
  - Avoid: yes. Prove preservation at one step site (Tick), with the posts available, before
    restating the definition.

- **E51 · I4-T1, stage II proofs written against stale layer-2 statements.**
  - Where: I (`I-4` task 1, `0a04373a35`).
  - What broke: II(a)/(c) ran before layer 3 re-keyed the statements, and two etcd-server files
    broke (`memStorJ … id`, a stale `ileft` for the merged `snapGiven`). This contradicted the
    plan's rule that every statement is fixed before any proof.
  - Cost: a mechanical repair. **[cat e] [stage I]**

- **E52 · G1 (I-5 namespace; "G1-frame"), `restartStorage`'s frame not keyed by `K`.**
  - Where: I (`I-5`; `I-4` addendum, `78b6bb4d15`). It recurred at the server in II(l) (E86).
  - Old: `restartStorage … (F : IProp)`.
  - What broke: all five clients' start proofs, which allocate their storage invariant at the key
    `K`.
  - Fix: `F : GName → IProp`, with post `F K`.
  - Cost: the client statements and the trusted `kv_bootStorage` each changed twice (the user saw
    them); a second pass in II(l) (E97). **[cat b] [stage I]**
  - Avoid: yes. Write one client's start against the spec with `sorry` (the E30 check would have
    caught it too).

- **E53 · I5-misc, trusted statements changed, and the stopper/crasher split left open.**
  - Where: I (`I-5`).
  - What: `kv_bootStorage`, `kv_storage_isStorage` and `server_cluster_alloc_on` changed for the
    user. `Cluster.Crash`'s exclusivity was left informal, and that led to E85 and E101.
  - **[cat i] [stage I]**

### Phase II-R: stage II, raft's side (2026-11-01 to 2026-11-02)

- **E54 · A-1, `matchedOk`'s exempt arm holds vacuously (a second fix of E37).**
  - Where: II(a) round 1 → round 2 (`e791cf88e6`).
  - Old: `v = id ∧ ∀ x, plogTermAt … i = some x → x < s.term`, which is vacuous past the log's end.
  - What broke: `step_propose` and `step_commit`.
  - Fix: `i ≤ plogLastIndexZ`, with the bound at every `j ≤ i`.
  - Cost: `GhostState` (HF), one extra round. **[cat a] [stage II-R]**
  - Avoid: yes. Ask of each disjunct whether it can hold vacuously.

- **E55 · A-2, `campOwn`'s candidate arm lost `k`.**
  - Where: II(a).
  - Old: after R5, `∃ k, camps !! s.term = some (F, k)`.
  - What broke: `step_win` needs `k = s.commit`.
  - Fix: `some (F, s.commit)`. The candidate premises of `ownLogGhost_upd`/`_mono'` gain
    `s'.commit = s.commit`, beyond what was approved. **[cat a] [stage II-R]**
  - Avoid: yes. Grep the consumers of the conjunct R5 removed.

- **E56 · A-3, A-4 and A-5: R5 and R2 incompletely propagated.**
  - Where: II(a), II(d) round 1.
  - What broke:
    - `rdOwn_arrive` had no slot;
    - `ghostRestM` still held the candidate's `isCampK` (`ownStepGhost_dyn`, `ghost_stepCDM`/`CDSM`,
      `InvRawnode`'s `ownStepGhost_deliv`, `RawNode__Advance`);
    - `ownRaftGhost_init` was false, so `alloc_nodes` was rewritten.
  - **[cat a] [stage II-R]** (A-3 is c)
  - Avoid: yes. Grep every copy of a removed conjunct, and re-derive the worklist after a change to
    a definition.

- **E57 · D-1, `ledgerCamps` cannot be established at allocation (E40's R6 realization).**
  - Where: II(d) rounds 1–2 (`f9f2fb5cce`).
  - Old: `□ ∀ t, ledgerKey t -∗ ∃ F k, isCampK …`, a persistent quantifier over fragments with no
    authority.
  - What broke: `ledgerCamps_fresh`, and with it every `raftState`/`nodeVacant` handed out.
  - Fix: `campKey` carried on each leader-side fragment; `ledgerCamps` deleted.
  - Cost: `ownRaftGhost_intro`'s arity changed (about 35 callers); `lcmOwn_win`/`rdOwn_win`
    restated; `GhostState` (HF). **[cat c] [stage II-R]**
  - Avoid: yes. Check that the producer, the allocation, can establish each persistent conjunct.

- **E58 · D-2/D-raw, Stop's and Advance's raw triples and `advance_complete`.**
  - Where: II(d) round 1.
  - What changed: `node.Stop.specRaw`'s post gained `raftIdSlot`; `node.Advance.specRaw` gained
    `run`'s `dur`/`bw` halves. `advRet` lacked those halves, which was folded into fix D (E63).
    Partly anticipated by I-3. **[cat a] [stage II-R]**

- **E59 · D-3, D-4 and D-5: `committedJust`'s boot arm, the slot in `raft_enter`, the cut's
  premises.**
  - Where: II(d) rounds 3–5 (`1c77c43813`).
  - What changed:
    - D-3: the boot arm gains `∀ e ∈ reBoot, e.Term' = 1` (`GhostState`). Category a.
    - D-4: `raft_enter` lacked `slotInv`, and `batchOk` sat inside an invariant, not timeless and
      with no later credit. Fix: `RaftBatch := S' × W × E`, `batchOk` persistent in `pendBatch`,
      `ownDurGhost ∗ slotInv`. `raft_enter_slot`, proved in round 3, was deleted. `slot_open`, the
      allocation, `raft_stop`, `raft_restart` and `raft_start_boot` were re-proved. Category c.
    - D-5a: the cut gained `S'.base.index ≤ s.commit`, produced in `ownRawNode` (G-C'2). Category a.
    - D-5b: the cut gained `∀ m ∈ o', m.dst = id`. Category f.
  - **[cat c] [stage II-R]**
  - Avoid: yes. Audit what is read out of an invariant for timelessness and persistence.

- **E60 · D-6, D-7 and D-8: the restart's acks (R4's argument false).**
  - Where: II(d) rounds 3–9 (`7c93a8ba93`, `e56a4a5378`).
  - Old: R4 said "the ack's `ackIn` names the leader", but the durable state keeps no `ackIn`.
  - What broke: `durPers_restart_acks`, and so `raft_restart`. Then:
    - round 4: `ackIn` is too weak;
    - round 5: a cheap route failed;
    - round 6: a plan only (capacity);
    - round 7: `ackInF` in `promNeed`, `durPers` and `slotBody`, with `ownLogGhost_ack` restated
      and six step callers, the allocation and every Enter lemma re-proved;
    - round 8: a premise added to `step_app_stale` and then reverted in round 9 (D-7);
    - D-8: `snapStale`'s refusal acks below the leader's base, so `ackAgree` moves to full-log
      coordinates (`leadFull X`) in `Ghost.lean`.
  - Cost: about seven rounds; `Ghost`, `GhostState` and `StepGhost` (HF). **[cat a] [stage II-R]**
    (D-8 is a/d (?))
  - Avoid: yes. Write R4 out against `durPers`'s real conjuncts and every branch of `StepC`.

- **E61 · G-A, `cfgNamesOf` lacks the generation (fix A).**
  - Where: II(g) round 1 → round 2 (`ac76f0a1fa`).
  - What broke: `api_enter`.
  - Fix: `CfgNames.gen`. **[cat a] [stage II-R]**

- **E62 · G-B, `readyCut` lacks `termLB γ.bud S'.term` (fix B).**
  - Where: II(g).
  - What broke: plan amendment 3 had `termLB` taken internally, but *enter* cannot produce it.
  - Fix: `readyCut` carries it, and `run` must prove `S'.term ≤ tc`. **[cat b] [stage II-R]**

- **E63 · G-C2, G-C3 and fix D: `slotFree` and `run`'s halves after *enter*.**
  - Where: II(g).
  - Old: `slotFree` was dropped after *enter*, and `advRet` was `∃ y, dur ½ y`.
  - Fix: `slotFree` in the busy `nodeDriver`, `advanceP` and `advRet`; `bw : (W, (S', role))`, beyond
    what was approved; `runPre`'s type changed under another agent.
  - Cost: `InvApi`, `InvNodeChan` (HF). Re-restated in II(n) (E72). **[cat a] [stage II-R]**

- **E64 · Fix C, the RawNode hand-out never restated for the cut.**
  - Where: found in II(g) round 1 (C1). Stopped in II(g) round 2, deferred by II(i) for capacity,
    done in II(k) (`7480ca7b97`).
  - Old: `ownRawNodeReady`'s `Hout : [∗list] isMessage` and `readyWithoutAccept`'s
    `#Hmsgs_ok`, unconditional.
  - What broke: these contradict R9's cut, where messages are valid only behind `durFrags W`.
  - Fix:
    - `RNState.bw`;
    - `pendingRel`/`pendList` over `W`;
    - `RawNode.Advance.spec`'s `#Hbw durFrags rs.bw`;
    - `Hout` only at `h = true`, as a wand;
    - `#Hmsgl`, `#Hrdlead`;
    - the hand-out is the cut.
  - Cost: 29 files, +1.4k lines, `InvRawnode`/`InvRawnodeReady` (HF); three rounds; `acceptReady`,
    `Advance` and `ApplyConfChange` re-proved; three GAP `sorry`s left for II(m).
    **[cat g] [stage II-R]**
  - Avoid: yes. List every producer of `readyCut` (and of `ownRaftGhost`'s new conjunct) in the plan.

- **E65 · `RawNode.Ready.spec` false under the cut (an exported result).**
  - Where: II(g) round 2 C'5 → user approval in II(i) → restated in II(k).
  - Old: post `[∗list] isRaftMsg`, outright.
  - Fix: an *enter* update gated by `slotLive`, plus a leader-only clause. **[cat g] [stage II-R]**
    (the plan's stage-I list omitted it)

- **E66 · II(i)-2 and (i)-3: `durTie`'s condition too weak, and `PersistCut`.**
  - Where: II(i) (`464ff91928`).
  - What changed: `rs.slent.isSome` became `∃ l, slent = some l ∧ snap = some (snapId l.snap)`,
    because a MsgSnap can restore while a snapshot is lent. `ownRawNodeReady` gains `%Hpst`, because
    the hand-out replaces `stored`. The Advance loop invariant was restated.
  - Cost: `InvRawnode` (HF). **[cat a] [stage II-R]**

- **E67 · II(i)-1, merge repairs.**
  - Where: II(i) (`703e80cd2c`).
  - What: `storKeyNames_agree` (8 components); `nodeAppliedLbU`'s new case; `InvApiView`'s `gd`
    agreement. Caused by parallel branches (the attach record against fix A–D).
    **[cat i] [stage II-R]**

- **E68 · II(k)-3 and (k)-8: `acceptReady`'s post and `RestartNode`'s `▷ raftState`.**
  - Where: II(k).
  - What changed: `acceptReady.spec` gains `SoftState' = null → ss = none` (category b).
    `RestartNode`'s AU takes `▷ raftState`, because `raftState` holds `slotInv` and is not timeless.
    The second makes kvdurable's LENT case (E102) redundant.
  - **[cat c] [stage II-R]**
  - Avoid: yes. Check the timelessness of every predicate a client keeps in an invariant.

- **E69 · GAP 1/2, the hard-state monotonicity (`PhsOk`, `RNState.hlb`).**
  - Where: found in II(k), closed in II(m) (`e495381bf9`).
  - Old: `ownRawNode` had no relation between `rs.phs` and the node, for the empty hard state and
    the stale Ready.
  - Fix: `PhsOk` (`HsLe` of `phs` and `hlb`), `RNState.hlb`, `Hhsi`, the `_intro` signatures,
    `ownRawNodeReady_abandon_keep`, `staleOk`, Advance's loop invariants. `tickElection.spec` and
    `tickHeartbeat.spec` gain `PVoteLe`, and `wp_step_pending` gains `inprogress` monotone.
  - Cost: part of II(m)'s 52 files; `InvRawnode` (HF). **[cat a] [stage II-R]**

- **E70 · GAP 3, `r.msgs` never self-addressed (`QOk`).**
  - Where: II(k) → II(m).
  - Old: `ownRaftPhys` recorded only `AAMsgOk` for `msgsAA`, although Go's `raft.send` panics on a
    self-send.
  - Fix: `QOk` in `ownRaftPhysG`'s body (about 40 `InvRaftPhys` sites, HF); `ownRaftPhysC_msgs`
    gains a premise. **[cat a] [stage II-R]**
  - Avoid: yes. Turn Go's panics into invariant conjuncts when designing the invariant.

- **E71 · The stop handshake: `node.run`'s stop arm blocked.**
  - Where: II(k) → II(n) (option (c), `c9566d370b`).
  - What broke: the handshake takes the answer `Q` before it gives `P`, `run` has only half the
    generation, and the mask is `⊤∖nroot`.
  - Fix: `isNodeChan.Hstop := (live ½, stopAns)`; `node.Stop` runs `raft_stop` itself (its spec
    unchanged). **[cat c] [stage II-R]**
  - Avoid: yes. Walk the handshake's fractions and masks in stage I.

- **E72 · II(n)-1, fix D's `advRet` restated again.**
  - Where: II(n).
  - Old (fix D): `∃ y W, dur ½ y ∗ bw ½ (W,y)`.
  - Fix: at `run`'s own record, with agreement in `advance_complete` (`bw_back`); `advDep` carries
    `bw`. `freshOk` drops `isRaftMsg`, and `readyMsgs_termLB` is restated. **[cat a] [stage II-R]**

- **E73 · The Ready facts G4, G7–G10, G14 and G17 as raft laws; G21; the `readyCut`/`readyP`
  widening.**
  - Where: requested in II(e), (h) and (j); delivered in II(m) (`e495381bf9`).
  - Old: `readyRest` exposed none of these facts. `softStateIs` lacked `p ≠ null` (G21).
  - Fix: `ReadyFacts` at the cut through `readyCut`, as `ReadyRestFacts` laws in `NodeApiVocab`.
    `readyCut`/`readyP` gain `d ce p`. `node_ready_receive`, `readyP_take`, `readyRecv_open` and
    `isReadyChan_recvAu_impl` are restated, and the clients' `icases` repaired (kvreconf ×2, kv, the
    server). G7 is amended (E95).
  - Cost: `InvNode`, `InvApi`, `ApiVocab` (HF); II(m) as a whole was 52 files and +1.1k lines.
    **[cat b] [stage II-R]**
  - Avoid: yes. Walk kvdurable's `run` against `readyRest` before the API was frozen.

- **E74 · (q)-1, the merge of `node.run` adapted to II(m).**
  - Where: II(q) (`6637da9451`).
  - What: the `node.run` proof, written against the pre-(m) `InvRawnode`, needed `hlb := hb` in
    `runMid_head`, `staleOk`'s `Hhlb`/`Hphl`, and `ReadyFacts` framed into `readyCut`.
  - Cost: small, but a full rebuild and a TCB update. **[cat i] [stage II-R]** (parallel edits to a
    shared invariant; also e)

- **E75 · G20, every Ready entry's type is ≤ 2.**
  - Where: found in II(j) addendum. II(m) proposed the registry route; rejected in II(q).
  - Fix: `CCDecodes` gains `uint.Z ty ≤ 2`; added to `ReadyFacts`, `ReadyRestFacts` and
    `readyFacts_of`; six constructions of `CCDecodes` repaired; `InvNodeRun`/`InvApiDec` projections
    updated; new law `readyRest_ents_type`.
  - Cost: `Protocol/Ghost`, `CCModel` (HF). (?) In the working tree, not yet committed per
    `git status`. **[cat a] [stage II-R]**

- **E76 · (o)-1, `raft_start_boot`/`raft_restart` in accessor form.**
  - Where: II(o).
  - What broke: the client's AU has inner mask `∅`, but the lemma opens the slot invariant.
  - **[cat c] [stage II-R]**
  - Avoid: yes. State the Enter lemmas at the masks their callers have.

- **E77 · (o)-2 and (o)-3: `newRaft`/`NewRawNode`'s premises.**
  - Where: II(o).
  - What changed: `σ.fr = b` became `b ≤ σ.fr ≤ committedAfter …`, a cascade of S1's freeze point
    (E98). The `dt` keys `≤ b` also require `termAt` at `b`. `newRaft`'s post gains
    `applied = applying`. **[cat b] [stage II-R]**
  - Avoid: yes. Propagate a contract change to its callees in the same step.

- **E78 · (o)-4 → `wcommit`: `RestartNode.spec` false for a lagging stored commit (a second
  backtrack of E35).**
  - Where: found in II(o), fixed in II(p) (`c9f5d9b10e`; decisions, "The restart's lowest
    commit").
  - Old: R1's `StorageHolds` allowed any `σ.b ≤ σ.commit ≤ S.commit`.
  - What broke: a counterexample in which conf entries are committed at 6 and 8 but the stored
    commit is 5. The node restarts at C5, wins with a C5 quorum, and Leader Completeness fails (real
    raft is unsafe there too).
  - Fix (the coordinator's decision (b)):
    - `RaftState.wcommit`, the commit of the last batch that wrote;
    - `StorageHolds` requires `S.wcommit ≤ σ.commit`;
    - `ownDurGhost` gets `durI1`, and `batchOk` gets `durI1` at the commit;
    - `ownRaftGhost_cut`, `raft_enter` and `api_enter` get new premises;
    - `raft_restart`'s `Φ` and its output change.
  - Cost: 18 files, +544 lines, `GhostState`/`RaftState` (HF). `RestartNode` blocked for a round.
    kvdurable gets new obligations at the merge. **[cat f] [stage II-R]**
  - Avoid: yes. Ask which stored commits a real client can produce, and allow only those (kvdurable
    writes the hard state with each batch).

- **E79 · (o)-5, `SdtTie` contradicts `rawNodeAt`; `AttachRec` amended a third time.**
  - Where: II(o) → II(p) (decisions, "A restart's certified terms").
  - Old: `dtk = sdtLen`.
  - What broke: a restarted node certifies up to the stored commit but hands out only up to
    `max b A`.
  - Fix: `sdtLen ≤ dtk`, with the gap made of attach-record indices `≤ c0`. `certLink` gains
    `ctCommitted`. `AttachRec` records every index `1..c0`, below the base too. The handout's
    height is `max dtk …`. New `ownRaftLog_certify_gap`. `acceptReady` and `RawNode__Advance` are
    re-proved.
  - Cost: `InvRawnode`/`InvRawnodeReady` (HF). **[cat a] [stage II-R]** (with e)
  - Avoid: yes. Instantiate the invariant at the restart producer in stage I.

- **E80 · (p)-1 and (p)-2: `RestartNode.spec` gains `readyFits` and list bounds; `raftStateU`
  gains `budgetInv`.**
  - Where: II(p) (`0c3831427e`).
  - What changed: `last + 1 < 2^64` is `newRaft`'s premise, which nothing bounded. The conf-state
    lists get `≤ 2^62`. The restarted channels need `inv budgetN`, which `StartNode` had from
    `nodeBoot`, so four allocation and *enter* sites change. **[cat b] [stage II-R]** (with d)
  - Avoid: yes. Check every premise of the callee chain `newRaft` ← `NewRawNode` ← `RestartNode`
    with `sorry` at stage I.

- **E81 · (p)-3, a configuration point above the applied index (amendment 4 never discharged).**
  - Where: II(p) → newraft (`2f27a8c05c`, `957e720440`).
  - Old: `max σ.b Applied ≤ a`.
  - What broke: `run`'s `runCfg` needs `capplied ≤ |rsDlv|`.
  - Fix: the spec narrowed to `a = max σ.b Applied`, an API scope change. (?) kvdurable's
    `Cluster.start` uses `a` = the snapshot index, with `Applied` possibly below it, so it may need
    restating. **[cat e] [stage II-R]** (with f)

- **E82 · (o)-6, `newRaft`'s window still open.**
  - Where: II(o)/II(p).
  - What broke: no `ownRaftLog` exists between `InitialState` and `appliedTo`, and the I-6 note
    missed `switchToConfig` (589 lines) among the functions that need a window variant.
  - Status: `newRaft.wp_proof` still `sorry`; the options are undecided. **[cat g] [stage II-R]**

- **E83 · (p)-4, a planned `durTie` conjunct that would have been false.**
  - Where: II(p) notes.
  - What: `rs.dur.commit ≤ committed`, planned in the II(i)/(k) handoff, is false at a lagging
    restart. Caught before it was written; cost about zero. **[cat f] [stage II-R]**

### Phase II-C: stage II, the clients and kvdurable (2026-11-01 to 2026-11-02)

- **E84 · E-1, `persist.spec` claimed `run`'s ghost (I-fix-1).**
  - Where: II(e) → II(f) (`e9f1c73d6e`).
  - Old: pre and post `ghostVar ph ½ none`, but the snapshotter holds no half. It was proved, but
    unusable.
  - Fix: drop the conjunct; fire *enter* in the `waiting` case. **[cat b] [stage II-C]**
  - Avoid: yes. List each caller's resources.

- **E85 · E-2, the crasher token (I-fix-2).**
  - Where: II(e) → `e9f1c73d6e`.
  - Old: `crash`'s post `∃ S o, kdWriter`, with no token in `repStop`.
  - Fix: `repStop := repStopper ∗ r.crashed ↦{½} false`; `stop.spec` takes `repStopper`. The first
    of four changes to the crasher design (E101). **[cat a] [stage II-C]**

- **E86 · E-3, E-5 and S4: missing callee specs and instances.**
  - Where: II(e), II(f), II(j) (`536b84e455`, `d6ed49f5cf`).
  - What was missing: `install`, `answer`, `applyOp`, `applyConf`, `fits`, `oneIn`, `below`,
    `decode`, `encode`, `readCtx`, `decodeReadCtx`, `validConf`, `Stats.add`, and an `isStorage`
    instance for kvdurable's `Storage`.
  - **[cat g] [stage II-C]**
  - Avoid: yes. Check the call-graph closure in stage I.

- **E87 · F-1, G13, G15 and G22: `applyEntry`/`request` premises and posts.**
  - Where: II(f), II(j) (`d1032b780f`, `9076d9f668`, `5c748683d9`, `7deb6df11c`).
  - What changed:
    - `applyEntry` gains `idx = len ap`, `k ≤ len ap`, then `k < |ap| ∨ ap <+: l`, because it is
      false in the restart regime, which the Go picks two times in three;
    - `request`'s premises are made conditional, plus a new `bound ≤ |D|`;
    - `applyEntry`'s post takes the view only when the entry is uncovered, and `runInv`'s view is
      restated.
  - Cost: `applyEntry` re-proved twice. **[cat b] [stage II-C]**
  - Avoid: yes. Check each spec in the restart regime as well as the fresh start.

- **E88 · F-2, Go dropped kvreconf's `cs != nil` guard.**
  - Where: II(f) → `9076d9f668`.
  - Fix: Go change, retranslation. **[cat d] [stage II-C]**
  - Avoid: yes. Diff the port against kvreconf.

- **E89 · F-3 and F-4: `readSeqs.next` and `Replica.read`.**
  - Where: II(f) → `0a2bb0513d`.
  - What changed: `next` minted for an arbitrary `f` (category f), so it now takes `key`. `isReplica`
    lacked `1 ≤ id ≤ 9`. `next` minted without committing, so it now gives `readCtxAfter`
    (category b).
  - **[cat f] [stage II-C]**
  - Avoid: yes. kvreconf's `kvr_mint_read` already did this.

- **E90 · F-5/SNAP-TIE: the image is not tied to the `MemoryStorage`.**
  - Where: II(f) → II(h) fix 4 / decision 1 (`9583eff4de`, `00b209f16b`).
  - Old: `kdDmuInv` tied the image `M` only through the hard state. The approved stage-I fix, "tie
    the image to the MemoryStorage", was infeasible:
    - the storage gives only lower bounds;
    - raft owns the log at `own 1`;
    - `nodeCommitLb` is minted before `dmu`.
  - Fix: `KdDmuNames {ph, ic, is}`, a frozen bound `fz` with a `memLog` record, two `monoNatAuth`s,
    `snapReqOk` carrying an `ic` lower bound; the `ph` binder changed in about seven specs.
  - Cost: three rounds; snapshotter, request, crash and persist re-proved twice.
    **[cat a] [stage II-C]**
  - Avoid: yes. Draft the snapshotter's proof outline against `kdDmuInv` in stage I.

- **E91 · G5, `run` cannot know `dmu`'s durable state.**
  - Where: II(h) → `00b209f16b`.
  - Fix: the claim's value becomes `Option GName × RaftState`; `kdPhaseInv`, `runStart` and
    `persist.specRun` restated. **[cat a] [stage II-C]**

- **E92 · G6, entering after a crash (decision 3 against the Go).**
  - Where: II(h) → II(j) (`11619a2ff9`).
  - Old: `crash` takes the writer.
  - What broke: `run` keeps entering commit-only batches until `stop`, and the Go has no `dmu`
    section after `stop`.
  - Fix: Go: `crash` locks and unlocks `dmu` again after `stop`. A retired state in `kdDmuInv`;
    `stop.spec`'s post and `runDone` restated.
  - Cost: Go change, an extra decision round. **[cat d] [stage II-C]**
  - Avoid: yes. Trace the window after a crash in Go.

- **E93 · G12, G18/G19 and G23: `runStart`/`isReplicaR` too weak.**
  - Where: II(j) (`5c748683d9`, `d4895bfcdd`, `f6e1126eac`).
  - What changed:
    - G12: the image's hard state is not tied to the driver's, so a `cm` ghostVar and a file-commit
      bound;
    - G18/G19: `runStart` lacked `|l| ≤ |ap|`, the frozen delivered log and the `ic` bound;
    - G23: `isReplicaR` lacked `memSnapLb γs 0`, which kvreconf had.
  - Cost: crash, persist ×2 and snapshot re-proved. **[cat a] [stage II-C]**
  - Avoid: yes. Diff the port against kvreconf, and walk `run` against `runStart`.

- **E94 · G4, G7–G10, G14, G17 and G21, client side: raft facts kvdurable needed.**
  - Where: II(e), (h), (j).
  - What: isolated as nine private `sorry`s (`9cf764e2e8` …) until II(m)/(q) (E73, E75).
  - Cost: nine `sorry`s carried through the adequacy proof. **[cat b] [stage II-C]**
  - Avoid: partly. List the client's needs before raft's API was frozen.

- **E95 · G7's amendment.**
  - Where: II(m).
  - Old: kvdurable stated G7 with `st.durable.commit < idx`.
  - What broke: raft cannot bound that after a restart, because the durable commit can exceed the
    stored one.
  - Fix: `st.hardState.Commit`. kvdurable's lemma must be restated at the swap (pending).
    **[cat f] [stage II-C]**

- **E96 · S2/S3 and Hbl0: `newReplica`, `openStorage` and `StartCluster` premises.**
  - Where: II(j) addenda 3–5 (`50a3ca3314`, `8bbdeec567`, `0a5c81ce53`).
  - What changed: `newReplica` gains the file/image tie, `|l| ≤ |ap|`, the frozen record and
    `memSnapLb`; three more premises S2 missed (id range, map size, `|ap|` = snapshot index);
    `openStorage`'s post gains `memSnapLb`; `StartCluster` takes `bootLen = 0`.
  - Cost: two rounds. **[cat b] [stage II-C]** (with e: the start specs were written in stage I and
    went stale as `run`'s design changed)

- **E97 · II(l): the clients' start proofs.**
  - Where: II(l) (`f8a8d972f2`, `73c492596e`).
  - What changed: `isClusterC` gains `bootLen = 0` (kvreconf; kv's `kvCluster_alloc` posts it).
    The server's `newRaftNode.spec` takes `Q : GName → IProp`, which E52 had missed.
    **[cat b] [stage II-C]**

- **E98 · S1 → FREEZE: the restart storage's ownership against `CreateSnapshot`.**
  - Where: II(j) addenda 3 and 6–7 → raft `7480ca7b97` (S1 provisionally in `RestartNode`'s post)
    → `4a4f52bd29` (the freeze point); kvdurable `b98823de25`.
  - Old: `storHolds` takes every stored entry at `own 1`.
  - What broke: `(σ.b, Applied]` is never frozen again, so G19 fails, and `openStorage` needs the
    entry at the snapshot index frozen for `CreateSnapshot`.
  - Fix: `storHolds st σ f`, frozen up to a client-chosen `f` with `σ.b ≤ f ≤ σ.commit`. This
    cascaded into E77.
  - Cost: two raft revisions; a kvdurable `sorry` bridge (`restartStorage_frozen_prefix`) still on
    the adequacy path. **[cat c] [stage II-C]**
  - Avoid: yes. Check the attach's fraction against a client restore that builds a snapshot.

- **E99 · S1b, the delivered log equals the stored entries.**
  - Where: raft `7480ca7b97`; kvd-start's isolated `sorry` `2bc552a516`.
  - What: added to `RestartNode`'s post, but kvd-start was based on a branch without it, so it
    carries a `sorry` that is now redundant (?). **[cat b] [stage II-C]**

- **E100 · `openStorage`: OS-1, OS-2, OS-3, OS-5, OS-6, OS-7.**
  - Where: II(j) addenda 5–7, kvd-openstorage (`d07a92dcd2`, `1a82946ccd`, `d9fcf46b33`).
  - What changed:
    - OS-1: Go copies the snapshot data, which was aliased;
    - OS-2: Go term checks (three, two beyond what was approved), and `KdFileOk` gains
      `KdSnapTermOk`;
    - OS-3: takes the bytes at `own 1` without giving them back;
    - OS-5: `KdFileOk`'s bound made strict, with a Go check;
    - OS-6: `getSnapshot`'s post becomes `ownSnapS`;
    - OS-7: raft's detached `CreateSnapshot` refusal gains `i ≤ index`.
  - Cost: "three spec changes, one Go change and one raft spec change" (kvd-openstorage), on top of
    the addenda's two Go changes; four rounds. **[cat d] [stage II-C]**
  - Avoid: yes. Check each premise of `MemoryStorage.Append`/`CreateSnapshot` against the decoder's
    checks.

- **E101 · CB-1, CB-2, CR, RSEQ and STOP: the cluster's crasher and stopper design.**
  - Where: kvd-callees, kvd-start, kvd-restart (`bd503c14ac`, `84c445fc0f`, `16fbfebf86`).
  - What broke:
    - `StartCluster.spec` had only the voter bounds;
    - `repKnown` was missing, so `sender` panics;
    - `clusterLockInv`'s docstring promised `repStop`s the definition lacked;
    - `Crash` had no token, so a double close was possible;
    - `replica`'s `r'` was not tied to `r`;
    - the read-sequence elements were not allocatable;
    - `Cluster.Stop` was missing from the design.
  - Fix: `KdNames.cur`/`crt`, `Hcur`/`Hstops` with a stopped mode, `specPin`, `all.specStop`;
    `restart`, `Crash`, `StartCluster` and `Stop` restated.
  - Cost: `repStop`/`clusterLockInv` changed four times in about 16 hours (with E85, E92).
    **[cat a] [stage II-C]** (STOP is g)
  - Avoid: yes. Decide the crasher's exclusivity in stage I, which I-5 had flagged as open.

- **E102 · LENT, `kdFileInv`'s lent case.**
  - Where: kvd-start (`e749ca99b7`).
  - What: the AU over a non-timeless `raftState`. Made redundant 63 minutes later by raft's
    `▷ raftState` (E68), but still present. **[cat c] [stage II-C]**

- **E103 · Pending: the newraft and raftrestart changes not yet merged into kvdurable.**
  - What: `wcommit` (E78), `readyFits` and the 2^62 bounds (E80), and `a = max σ.b Applied` (E81).
    Probably `Cluster.start`/`kdCfgOk` will be restated. (?) Not counted.

### Appended after the catalog (2026-11-02 onwards; not yet in the counts of section 2)

- **E104 · G20: entry records too weak for the type bound.**
  - Where: II(q) §4 (`7a2f7b2d03`).
  - Old: II(m)'s plan was to take the bound from the proposal registry.
  - What broke: the registry records only registrations, and `prop_register` is public for any
    key. Besides, `CCDecodes` (through `propDataIs`, `entData`, `isEntryR`, `logRecs`) constrained
    only types 1 and 2, so nothing excluded type 7.
  - Fix: `CCDecodes` gains `uint.Z ty ≤ 2`; every producer of an entry record already has its type
    at hand.
  - Cost: seven one-line proof repairs, two full builds, no client affected. **[cat a] [stage II-R]**
  - Avoid: yes. When a plan says "the registry records X", check who can write to the registry.
    Put a fact about an entry in the record its producers build.

- **E105 · `newRaft.spec`'s conf-state premise was false.**
  - Where: II(r), Backtracking 1 (`58c2a9fd3a`).
  - Old (I-6): `restoreM … = some cs'` alone.
  - What broke: `Restore` accepts a repeated voter and `AutoLeave` with no outgoing voters. The
    `ConfState` raft rebuilds then differs, and `assertConfStatesEquivalent` panics, so the spec
    claimed no panic where raft panics.
  - Fix: a premise `ConfStateOk csm` on `newRaft.spec` and `NewRawNode.spec` (well-formed, `Nodup`,
    `AutoLeave` only when joint). `RestartNode` gets it from `confStateIs`'s `CSWf`, which until
    then had been discarded; the API is unchanged. Filed as
    `nonissues/raft-restore-malformed-confstate-panic.md`.
  - Cost: 2 specs and 3 proofs. **[cat d] [stage II-R]**
  - Avoid: yes. Walk every `panic` and assertion on the Go path of a spec before stating it
    (section 0, pattern 5).

- **E106 · `newRaft`'s certified-terms premise was too weak; the plan for its window does not work.**
  - Where: II(r), Backtracking 2 and 4.
  - Old (II(o)): the view may already hold certified terms at or below the base. The II(p)
    design: window variants of the callees' specs.
  - What broke:
    - The catch-up needs fresh certificates for every recorded index, which an authority cannot
      produce for terms already certified.
    - No `ownRaftLog` can hold in the window: `FlOk` needs the floor at most `applying = b`, while
      the caught-up view needs it at least `max b A`. So the callees' specs cannot be used there
      at all.
  - Fix: `σ.dt = ∅` (both callers already pass it). The window's callees are proved over their
    bodies on the raw fields, as private lemmas in `newRaft.lean`.
  - Cost: the II(p) design was dropped, and one agent round. **[cat a, with g] [stage II-R]**
  - Avoid: yes. For a window the plan names, check that the predicate the callees need can hold
    in it before choosing "variants of their specs".

- **E107 · kvdurable's stand-ins were replaced by raft's laws (II(s)).**
  - G7: kvdurable's statement used the durable commit, which raft cannot give after a lagging
    restart. It now uses the image's commit, which equals the hard state's (one statement, three
    sites).
  - `kdFileInv`'s lending case became unnecessary once the update took `▷ raftState` (E68), and
    was deleted (four sites).
  - The freeze-point bridge, S1b and G20's data-length half were one-for-one replacements.
  - Tooling: a Link namespace clash, and `MustSync` not importable. Both were latent because the
    kvdurable branches never ran `tcb-report` or `api-check`.
  - **[cat b for G7; h for the tooling] [stage II-C]**
  - Avoid: partly. State a client's stand-in lemmas against the provider's actual post (the
    composition check), and run the trust-base and API checks on every branch, not only at the
    merge.

- **E108 · `RestartNode`'s configuration point narrowed wrongly (the coordinator's decision).**
  - Where: coordinator decision after II(p); found in II(t) (`7d0415929f`, `kd_RestartNode_at`).
  - Old (II(r), decided by the coordinator): `a := max σ.b A`. A configuration above the applied
    point was judged a misuse, by analogy with `nonissues/raft-applied-above-snapshot-confstate.md`.
    That analogy had the inequality backwards: the issue is about a configuration older than
    `Applied`.
  - What broke: kvdurable's storage keeps entries below its snapshot (`σ.b = prev < si`), and its
    `ConfState` is the snapshot's (`a = si > max σ.b A`). It legitimately skips the conf changes
    raft re-delivers. Any storage that compacts lazily below its snapshot is in the same position.
  - Fix: revert to candidate 12's approved form (a parameter `a` with
    `max σ.b A ≤ a ≤ σ.commit`), and prove the case `a > max σ.b A` in raft, which was II(p)'s
    unproved case.
  - Cost: the narrowing round, a kvdurable `sorry`, and a further raft round.
    **[cat b, with i] [stage II-R]**
  - Avoid: yes. Before narrowing a spec to make a case go away, check every existing client's Go
    against the narrowed form. Narrowing is an API change like any other.

- **E109 · `RestartNode`'s `≤ 2^62` list bound was a premise clients cannot prove easily.**
  - Where: II(p) added it; II(t) (`kd_confAt_lists_le`, `sorry`).
  - What broke: `Membership.Valid` bounds the members but does not make incoming voters and
    `LearnersNext` disjoint. kvdurable's member bound therefore gives three times the count, not
    two.
  - Fix (decided): raft derives the bound itself, with `Membership.Valid` strengthened by that
    disjointness if needed, and the premise is deleted.
  - **[cat b] [stage II-R]**
  - Avoid: yes. A premise about raft's own data structures should come from raft's invariants,
    not from the client.

- **E110 · The restart's configuration index needed a `RawNode` invariant nobody recorded (`CapOk`).**
  - Where: II(u) (`e01568867a`); the report's Backtracking 1-3.
  - Old (II(p)): the case `a > max σ.b A` of `RestartNode` (the configuration index above the
    committed log handed out) left `sorry`, with the plan to "generalize `run`'s invariant" (I-9).
  - What broke: the node layer alone cannot do it. The loan rendezvous raises the monotone `cam`
    to the lent snapshot's index, which needs that snapshot past the restart's configuration index:
    a `RawNode`-level fact nothing recorded (the protocol's `applySnap` rule even lets the index go
    down). Separately, II(p)'s list-length premise was the wrong quantity (the lengths' sum, where
    raft needs the listed ids' count; E109).
  - Fix: `CapOk` (configuration index below the commit, below a lent snapshot's log, and with no
    loan below a pending snapshot's index), a fourth conjunct of `LoanOk`, kept by every step (new
    premise `hcap` on `LoanOk.step*`, from `raft.restore`'s `committed < index`); `runCfg`'s outer
    conjunct relaxed to `ca ≤ capplied ∧ (ca < capplied → capplied ≤ |rsDlv rs|)`;
    `wp_applyConf_dyn` takes the conf entry within the committed log handed out. The list bound
    derived in `RestartNode` from the membership's `CfgOk`.
  - Cost: three stages of churn on one parameter (II(p) `sorry`, II(r) narrowed, II(t) re-widened
    with a client `sorry`, II(u) proved); 12 `LoanOk` projection sites, 6 constructions, 3 step
    lemmas' signatures. **[cat a, with b] [stage II-R]**
  - Avoid: yes. When a plan says "generalize the invariant of layer X", check which facts the new
    case reads and whether layer X can see them; a fact about a lower layer's state needs that
    layer's invariant first.

- **E111 · The merge of `lean` (2026-11-02): parallel changes to the node API.**
  - Where: the merge commit "Merge branch 'lean' into worktree-kvdurable".
  - Old: stage I-4 dropped `readySnap`/`readyRest`'s node `id` (its only use, `snapGiven`, became
    `nodeAppliedLb`/`nodeCommitLb` keyed by the storage); `lean` meanwhile added `nodeSnapLocal γ id`
    (J8a), `bootLen < index` (J8b) to the same clause, made `hsCommitted` hold after a snapshot
    `Ready` (#7), and proved the server's snapshot track against the old driver state and
    `deliveredLogLb ⊢ storDL` (driver-free).
  - What broke: 57 conflicted files; `readySnap` needed the id back (15 client call sites, one more
    `_`); `api_enter` had built the driver's `hsCommitted` from the deleted escape (now a premise);
    the server's `rn_storDL` had no driver-free counterpart (restated over `rnDrv`; `ApplySnapshot`'s
    bounds taken from `readySnap`); `NodeOk`'s fourth conjunct gone (7 projection sites);
    kvdurable needed lean's no-directory fact (`%Hsl`).
  - Cost: the merge, one agent round for the server port. No new `sorry`. **[cat i] [merge]**
  - Avoid: partly. A long-lived branch that reshapes a shared API should merge `lean` often; and
    dropping a parameter nobody used *yet* invites a parallel change to re-add it.

- **E112 · The clients' start proofs were proved on a branch the coordinator never merged.**
  - Where: found at the landing (2026-11-02). Stage II (l) (`f8a8d972f2`, `73c492596e`, branch
    `worktree-agent-a09ffa1a9b805d40b`, on `cf8a03bee0`) proved the six `PORT(durability stage II)`
    stubs (`kv.StartCluster`, `kvStorage_bootStorage`, `kvreconf.StartCluster`,
    `kvreconf.Cluster.startNew`, `bootstrappedRaft.newRaftNode`, `raftNode_of_StartNode`) and was
    pushed, but never merged into `worktree-kvdurable`.
  - What broke: the first landing attempt (`landing-report.md`) found the six as `sorry`s that kv's,
    kvreconf's and the server examples' results reached, and did not land. The branch, merged at
    last (`e3d1bd00b1`), predated eight later stages: `restartStorage`'s freeze point (II (k)),
    `StorageHolds`' `wcommit` and `RestartNode`'s `readyFits` (II (p)), its AU over `▷ raftState`
    (II (k)), S1b in its post, lean's `cluster_alloc` `sl` argument, the server's `walReady`
    premise and `stopped` bag. Adapting it took 4 conflicts and about 20 proof edits. `readyFits`
    needed `receiptBound ≤ 2^61`, which narrowed kv's and kvreconf's `StartCluster`/`Run`/`Main`
    specs and adequacy results from `n < 2^63` to `n < 2^61` steps (as kvdurable's in II (t)).
  - Cost: one landing round lost, one merge-and-adapt round. Had the branch been merged after
    II (l), each later stage would have kept the proofs building and met the `readyFits` scope
    change when it made it. No new `sorry`. **[cat i] [coordination]**
  - Avoid: yes. Keep a ledger of every agent branch and its merge state, and check
    `git branch --no-merged` (local and `-r`) before landing.

---

## 2. Counts

Each event is counted once, under its primary category and stage. Where an entry groups several
findings, the "(with x)" notes give the secondary categories; they are not counted. E26 (never
type-checked) is in section H, and E103 (pending) is excluded, so the counts cover 101 events.

### By category

| category | count | events |
|---|---|---|
| (a) invariant designed without checking every consumer/producer | 31 | E02 E04 E07 E18 E20 E23 E27 E37 E38 E39 E40 E49 E50 E54 E55 E56 E58 E60 E61 E63 E66 E69 E70 E72 E75 E79 E85 E90 E91 E93 E101 |
| (b) caller cannot establish the premise / callee post insufficient | 18 | E08 E12 E22 E29 E30 E44 E48 E52 E62 E73 E77 E80 E84 E87 E94 E96 E97 E99 |
| (d) Go behaviour not checked (premise missing, Go fix) | 15 | E03 E05 E06 E09 E10 E17 E19 E28 E31 E32 E34 E46 E88 E92 E100 |
| (c) separation logic: ownership, persistence, later, mask | 12 | E01 E16 E21 E24 E36 E57 E59 E68 E71 E76 E98 E102 |
| (i) other (design taste, wrong argument, merges, engineering) | 9 | E11 E14 E15 E25 E42 E47 E53 E67 E74 |
| (g) plan omitted a function or window | 7 | E13 E43 E45 E64 E65 E82 E86 |
| (f) generalization beyond client needs made it false | 5 | E33 E78 E83 E89 E95 |
| (e) ordering: risky piece (restart) done late | 4 | E35 E41 E51 E81 |
| total | 101 | (E26 is counted under (h); E103 is pending and not counted) |

Counting the secondary categories as well (the "(with x)" notes, the grouped entries' sub-items
and the "later" re-breaks): (e) rises to about 12, because the restart path being proved last is
behind E48-Dev8, E49, E78, E79, E96 and E98; (b) rises to about 26; (c) to about 16.

**How often a fix was itself wrong.** About 16 events are a second or third backtrack of an
earlier fix:

| original event | broke again in |
|---|---|
| R1 (E35) | E78 |
| R3 (E37) | E54 |
| R4 (E38) | E60 |
| R5 (E39) | E55, E56 |
| R6 (E40) | E57 |
| the attach record (E49) | E79 |
| `durTie` (E50) | E66 |
| fix D (E63) | E72 |
| the frame (E30) | E52, E97 |
| `storDL` (E07) | five times within the entry |
| the storage key (E21) | six times within the entry |
| `InitialState` (E28) | E46 |
| the crasher (E85) | E92, E101 |
| S1 (E98) | its own provisional form |

### By stage

| stage | events | main categories |
|---|---|---|
| S, the spec phase (candidates 1–12, reviews 1–9; 10-31) | 32 (E01–E33 without E26) | d 10, a 7, b 5, c 4, i 4, g 1, f 1 |
| P, the plan and its review (10-31) | 10 (E35–E44) | a 4, e 2, c 1, b 1, g 1, i 1 |
| I, stage I statements (10-31 to 11-01) | 10 (E34 [listed under S by date], E45–E53) | a 2, b 2, d 2, e 1, g 1, i 2 |
| II-R, stage II raft (a, d, g, i, k, m, n, o, p, q) | 30 (E54–E83) | a 13, c 5, b 4, g 3, f 2, i 2, e 1 |
| II-C, stage II clients and kvdurable (e, f, h, j, l, kvd-*) | 19 (E84–E102) | a 5, b 6, d 3, c 2, g 1, f 2 |

Within stage II, the parts with the most rounds were II(d) (nine rounds), II(j) (seven addenda),
II(g) (two rounds) and fix C (three agents).

---

## 3. The most expensive events

1. **E64 + E65 + E69/E70 + E73 + E74: the RawNode layer was never restated for the cut. Fix C,
   then the GAPs, then the Ready facts.**
   - Rounds: fix C was found in II(g), stalled twice (II(g) round 2, II(i) for capacity) and done
     in II(k).
   - Size: 29 files and +1.4k lines in II(k), then 52 files and +1.1k lines in II(m).
   - Files rebuilt: `InvRawnode`/`InvRawnodeReady` (about 1560 importers), `ownRaftPhysG`
     (about 40 sites), `InvNode`, `InvApi`, `ApiVocab`.
   - Re-proved: `acceptReady`, `Advance`, `ApplyConfChange`.
   - Restated: the exported `RawNode.Ready.spec`.
   - Knock-on: the already-proved `node.run` had to be re-adapted at the merge (E74).
   - Root cause: R9's cut changed `ownRaftGhost`'s outbox, and the plan never listed its
     RawNode-layer producers (g); `ownRawNode` lacked relations that Go guarantees, such as no
     self-send and the hard state's monotonicity (a).

2. **E50, the `durTie` cycle (G2 of I-4/I-6).**
   - The definition was introduced in I-4, restating two RawNode specs and adding 22 `sorry`s.
   - In I-6, 16 of the 22 were unprovable (a counter-model).
   - It was redesigned in II(i) over 17 files and about 30 sites, and strengthened again (E66).
   - `InvRawnode`/`InvRawnodeReady` changed twice, over three rounds.
   - One preservation proof at a single step site would have caught it.

3. **E35 → E78, the restart's commit, from R1 to `wcommit`.**
   - It started in the spec phase's c5 decision (the commit out of the state).
   - R1 was an API change and took a user round.
   - Its own generalization (`σ.commit ≤ S.commit`, a commit lag) made `RestartNode.spec` false,
     with a real-raft counterexample. That gave a second API change: a `RaftState` field,
     `StorageHolds`, `ownDurGhost`, `batchOk`, the Enter lemmas (18 files, `GhostState`/`RaftState`
     HF), a blocked round, and new obligations for kvdurable.
   - Root causes: (e) the restart was worked out last, and (f) the spec allowed more than a real
     client produces.

4. **E38 → E60, the restart's acks.**
   - R4's argument read an `ackIn` that the durable state never keeps.
   - Repairing it took about seven rounds of II(d): one too-weak fix, one failed route, one round
     out of capacity, and one premise added and then reverted.
   - It ended with `ackAgree` in full-log coordinates, changing `Ghost.lean`, `GhostState` and
     `StepGhost` and re-proving every ack step lemma and Enter lemma.

5. **E14 + E17, spec-phase design churn.**
   - E14: the user's critique discarded four candidates and three reviews (`nodeDisk`, incarnations).
   - E17: the stale-node argument took three candidates and three reviews, then reverted to review
     4's minimal repair. A reviewer had endorsed a false argument; only Go reproductions settled it.
   - Cost: no proof was involved, but about 40% of the spec phase's rounds.
   - A shape question to the user before candidate 1, and a two-instance Go test, would have
     avoided most of it.

6. **E90–E101, kvdurable's `run`/start statement churn.**
   - Covers SNAP-TIE, G5, G6, G12–G23, S1–S4, `openStorage` and the crasher design.
   - Rounds: about eight restatement rounds across II(f), II(h), II(j) (seven addenda) and four
     kvd-* agents.
   - `kdDmuInv` was redesigned three times; crash, persist, snapshot, applyEntry, request, stop and
     StartCluster were re-proved repeatedly.
   - Six Go changes were forced by the proof.
   - A raft API change (the freeze point, E98) cascaded into `newRaft`/`NewRawNode`'s premises
     (E77), and a `sorry` bridge is still on the adequacy path.
   - Root cause: kvdurable's invariants and start specs were fixed in stage I without walking `run`,
     the restart regime and the window after a crash against the Go.

7. **E49 + E79, the attach record.**
   - It started from a false survey claim (survey-start §2.4).
   - Then: a decided reading that broke lemmas II(c) had just proved, a user decision, the
     phase-flag idea refuted, `newLogWithSize`/`newRaft`/`NewRawNode` restated, and in II(o)/(p)
     `AttachRec`, `certLink` and `SdtTie` amended again in `InvRawnode` (HF).
   - Still open: the `newRaft` window (E82), deferred since I-3's Dev8.

Runner-up: **E07 + E21**, the spec phase's storage threads. The storage key went through about seven
forms and `storDL` through about six, across all twelve candidates, at no proof cost.

---

## H. Tooling and infrastructure (not counted above)

**Never type-checked.**
- The candidates had unbound binders and type errors (E26: r6 N5–N6, r7 M2/M5, r8 P4).

**Capacity and context.**
- II(d) round 6 was a plan only, and round 4 skipped repairs 1 and 4.
- II(i) ran out of capacity, so items 2–3 slid into II(k)/(m).
- II(j) addenda 4 and 7 ran out of context.
- II(e), (f) and (h) never started `Replica.run`.
- kvd-start left `StartCluster` unstarted.

**The shared `.lake`.**
- Other worktrees rebuilt it mid-session, deleting oleans whose traces remained (kvd-start,
  kvd-openstorage, II(j) addendum 6).
- Agents built private copies: a 1.2 GB build in kvd-callees, hard-link copies in kvd-openstorage
  and kvd-restart.

**Disk.**
- 98% full, 18 GB free against a 19 GB build (kvd-restart).

**`lean-check`.**
- It served a stale spec olean (II(h)).
- Its server belonged to another worktree and gave "bad import" (II(j) addendum 5).
- Incremental checks hid two errors (kvd-openstorage).

**Kernel and tactics.**
- `word`'s cache leak produced a term the kernel rejected (kvd-openstorage).
- `wp_auto`/`iunfold` unfold a token down to its model (kvd-restart; recorded in
  perennial-changes).

**Builds.**
- `pkill -f "lake build"` may have killed other sessions' builds (II(i)).
- Raft's `Linked` failed at `b98823de25`, mid-II(i), which blocked interface regeneration
  (kvd-openstorage) (?).
- The TCB `--check` was skipped for lack of a full build in II(l), (n), (o) and (p); II(l) edited
  the baseline by hand.
- The TCB baseline and STATUS went stale after II(a), (c) and (d) (parallel conflicts).

**Scripts and code duplication.**
- `gen-link` had no kvdurable mode at first, then needed a binder fix (`a01202251b`).
- A duplicate `Storage.wp_FirstIndex` (`4bb782f085`).
- kvreconf's `Assumptions` section variable forced kvdurable to copy lemmas and the codec (II(f)).
- `readyMsgs_sent` existed in three copies because raft files were off-limits (II(e), merged in
  II(i)).
- `logRecs_*` were copied into `Enter.lean` to avoid a rebuild (II(d) round 3).

**Sandbox and policy.**
- Writes were allowed only in a worktree holding someone else's edits, so commits went through a
  temporary index (kvdurable-ext).
- A push instruction was declined in II(d) round 7.

---

## 4. What design-time checks would have caught most of these

| check | what it addresses | events |
|---|---|---|
| **The composition check.** For every new or restated spec, state each callee's premises at the caller with `sorry`, and each caller's use of the post, before stage II. | most of (b), and (e) | E30/E52/E97 frame, E35 R1, E62, E77, E80, E81, E84, E87, E96 |
| **The consumer/producer table.** For every new conjunct or law, grep every producer (allocation, each step lemma, the cut, the restart) and every consumer, and prove preservation at one representative site before restating. | about two thirds of (a) | E07, E37–E40, E50, E54–E57, E60, E66, E69, E70, E79 |
| **Fix-of-a-fix review.** Apply the producer/consumer check again to every repair. | about 16 events were broken repairs | see the table in section 2 |
| **A Go walk of each window and panic.** List the windows (start to first write, attach to `newRaft`, after a crash, after a stop) and every `panic` in the Go, and turn them into conjuncts or premises. | (d) and (g) | E05, E13, E17, E19, E70, E82, E92, E100 |
| **Restart first.** Prove (or sketch with `sorry`) `raft_restart` / `RestartNode` / `newRaft` before the run path. | the costliest late discoveries | E35/E78, E49/E79, E60, E81 |
| **Allow only what clients produce.** Allow only what a real client produces (kvdurable writes the hard state with each batch's entries). | (f) | E78 (commit lag), E83, E89, E95 |
| **A kvreconf diff.** For each ported kvdurable function, diff the Go and the spec against kvreconf. | | E88, E89, E93 (G23), E86 |
