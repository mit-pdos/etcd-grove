# Model checking the reconfiguration design (2026-10-14)

Task 5 of `notes/parallel-work.md`: search the abstract membership model
(`issues/raft-conf-lag-model/model.py`) far deeper than its Python BFS (depth 10-11), find
the lagging-mode counterexamples by search rather than by hand, and search the faithful
mode (the precondition of `issues/raft-advance-before-applyconfchange.md` respected)
exhaustively at small bounds, as evidence for the B1 paper proof
(`notes/reconfiguration-safety.md`). Checker: `issues/raft-conf-lag-model/checker/`
(Go, no dependencies; its README says how to run it and lists every flag); the runs below
are `checker/runs.sh`.

## Summary

- **Faithful mode: no violation** of state machine safety, log matching, election safety
  or leader completeness (nor read-index linearizability where read index is on) in any
  run. Eight runs are exhaustive, up to 1.6·10^9 states (up to symmetry), BFS diameters
  37-44: 3-4 nodes (one of them addable), terms ≤ 2 (≤ 3 at 3 nodes), logs ≤ 4-5 entries,
  ≤ 2 conf changes, simple or joint changes, with or without read index, a leader removing
  itself, a removed leader staying leader. Two larger ones (terms ≤ 3 at 4 nodes; 5 nodes)
  are complete to depths 23 and 17 only. Nothing here contradicts B1.
- **Lagging mode: the checker finds counterexamples on its own**, shorter than the
  hand-made ones (BFS gives shortest traces): a leader-completeness violation at depth 18
  and a state-machine-safety violation at depth 17 (20 steps in `model.py`'s terms),
  versus 25-27 steps for `trace-leaderlag.txt` / `trace-followerlag.txt`. The new SMS traces
  need only 3 nodes and two removals (`trace-check-lag3-sms.txt`: depth 20 with every node
  allowed to lag, in `model.py`'s own terms). The crash mode gives an SMS violation at depth 16
  (`trace-crash.txt`: 20). All replay in `model.py` (UNSAFE at the last step).
- **Guard-fix mode** (`issues/raft-conf-lag-model/guard-fix.md`'s semantics, every node's
  application allowed to lag): no violation. Exhaustive at 3 nodes (terms ≤ 3, logs ≤ 5,
  2 conf changes: 5.0·10^8 states, diameter 51), where the unfixed lag mode fails at
  depth 20; at 4 nodes complete to depths 22-25 (1.6-1.7·10^9 states), past the depths
  (17-18) at which the unfixed mode fails at the same bounds.
- **Read index**: the model's read index with the `committedEntryInCurrentTerm` check is
  safe in every run with `-read`. Without the check the checker finds the classic stale read
  (depth 6); with the pinned raft's single-voter shortcut (`-read-singleton-bug`) it finds
  both executions of the B1 review's finding 1 (`issues/raft-readindex-singleton-stale.md`),
  a new leader at `{L}` (depth 11, 2 nodes) and a removed leader (`StepDownOnRemoval`
  off, depth 17). So the read-index model is not vacuous.
- Validation of the transcription: with symmetry and the ghost off, the per-depth state
  counts equal `model.py`'s exactly (4 configurations, to depths 6-8), and the three
  hand-made traces replay to the same final states.

## What is modelled

`model.py`'s transition system, transcribed action by action (`checker/model.go`):

- Nodes `1..N`; `C0 = {1..init}`; nodes above `init` are addable. A node's state: term,
  role (follower/leader; candidates are not separate, elections are atomic), log, commit,
  applied, `cfgidx` (the prefix whose conf entries `ApplyConfChange` has applied),
  leader's `match` and `pendingConfIndex`, persisted commit (crash mode).
- `elect`: a non-leader member of its configuration, with no conf entry in
  `(applied, commit]` (`hasUnappliedConfChanges`), wins with any set of voters whose logs
  are at most as up to date and which form a (joint) quorum of its configuration; all take
  term `max + 1`; the winner appends its empty entry and sets `pendingConfIndex` to its last
  index. Pre-vote is the same check. Voters need not be members (raft votes regardless).
- `propv`, `propc` (add / remove a node other than the leader; `-joint`: enter a joint
  configuration; at a joint configuration only auto-leave proposes), guarded by
  `pendingConfIndex > applied`.
- `app i j q`: one AppendEntries round trip: `j` takes `i`'s log up to `q` (truncating on a
  conflict), its commit `max(commit_j, min(commit_i, q))`, term and follower role; `i`'s
  `match[j]`.
- `commit`: the leader's largest index of its term acknowledged by a quorum of its
  configuration.
- `apply`: applied + 1; in `faithful` mode the configuration moves with it; in `lag` mode
  only `applyconf` moves it (Advance before ApplyConfChange). After either: a removed
  leader steps down (`StepDownOnRemoval` on); `-joint`: auto-leave.
- `crash` (crash mode): restart with the commit persisted before the last append.
- Bounds: `-maxt` (terms), `-maxlog`, `-maxconf` (conf proposals; auto-leave not counted),
  `-maxval` (value proposals). Values are unique, so two different committed entries at
  one index are always distinguishable.

Added (checker README, "Additions"): the invariants beyond `model.py`'s `safe` (log
matching; election safety through a ghost bit per term won; leader completeness checked at
each win); read index (`-read`: one pending request, a ghost of the largest commit at its
arrival, confirmation by a quorum of the leader's current configuration of nodes of term
`≤` the read's, a violation if that largest commit exceeds the read index); `-remself` (a
leader may remove itself); `-nostepdown` (`StepDownOnRemoval` off, raft's default);
`-lagnodes` (lag at some nodes only); the `fix` mode.

## Results

Times are wall clock with 12 worker goroutines on the shared 24-core machine (other
sessions' Lean builds running); memory under 25 GB (table `2^31` fingerprints, 17 GB, or
`2^30` with parent slots, 12.9 GB; frontier packed, spilled to disk for the large runs).
All bounds are `-n 4 -init 3` unless stated; "states" are distinct up to symmetry
(permutations of `{1,2,3}` and of the addable nodes).

### Counterexamples (lagging and crash modes)

| Run | Bounds | Result | States | Time |
|---|---|---|---|---|
| `lag-all-lc` | lag, t2 l4 c2 v1 | leader completeness violated at depth 18 | 2.6·10^8 | 219 s |
| `lag-1-sms` | lag at node 1 only, `-inv sms`, t2 l4 c2 v1 | state machine safety violated at depth 17 | 2.0·10^8 | 128 s |
| `lag-n3-sms` | lag, `-n 3`, `-inv sms`, t2 l4 c2 v1 | state machine safety violated at depth 20 | 1.1·10^7 | 15 s |
| `crash-sms` | crash, `-inv sms`, t2 l4 c2 v1 | state machine safety violated at depth 16 | 6.2·10^7 | 62 s |
| `read-noterm` | `-n 3`, `-read -read-no-term-check`, t2 l3 c0 v1 | read index violated at depth 6 | 10^3 | 0 s |
| `read-single-a` | `-n 2 -init 2`, `-read -read-singleton-bug -remself`, t2 l4 c1 v1 | read index violated at depth 11 | 6·10^3 | 0 s |
| `read-single-b` | `-n 3`, `-read -read-singleton-bug -remself -nostepdown`, t2 l4 c2 v1 | read index violated at depth 17 | 4.3·10^6 | 4 s |

(At 4 nodes the unrestricted lag mode with only `sms` checked would reach its first SMS
violation beyond what fits in 25 GB: depth 17 alone adds 1.2·10^8 states. Restricting the
lag to one node, as the Go test does, brings it to depth 17; at 3 nodes it is depth 20.)

**`lag-all-lc`** (`issues/raft-conf-lag-model/trace-check-lag-lc.txt`): the leader-lag
class. Node 1 leads term 1, commits `add 4` (index 2) with `{1,3}`, applies indices 1-2
without `ApplyConfChange` (still on `C0`), proposes `rem 3` (index 3; `pendingConfIndex` 2
`≤` applied 2) and `x` (index 4), commits index 4 with `{1,3}` under `C0`. Node 4 receives
indices 1-3 and applies both changes: `{1,2,4}`. Node 4 wins term 2 with `{2,4}` (node 2's
log is empty) -- without index 4, which is committed.

    ('elect', 1, (1, 3), 1)  ('propc', 1, ('add', 4))  ('app', 1, 3, 2)  ('commit', 1, 2)
    ('apply', 1, 1)  ('apply', 1, 2)  ('propc', 1, ('rem', 3))  ('propv', 1, 1)
    ('app', 1, 3, 4)  ('commit', 1, 4)  ('app', 1, 4, 3)  ('apply', 4, 1)  ('apply', 4, 2)
    ('apply', 4, 3)  ('applyconf', 4, 1)  ('applyconf', 4, 2)  ('applyconf', 4, 3)
    ('elect', 4, (2, 4), 2)

**`lag-1-sms`** (`trace-check-lag-sms.txt`, in `model.py`'s form, with the `applyconf` of
the non-lagging node 2): the follower-lag class, three nodes, removals only. Node 2 leads
term 1 and commits `rem 3` (`{1,2}` from then on at node 2), proposes `rem 1` (index 3),
sends it to node 1 with commit 2. Node 1, lagging, applies indices 1-2 without applying
`rem 3`: it is on `C0 = {1,2,3}`, has no conf entry in `(applied 2, commit 2]`, and wins
term 2 with `{1,3}` (node 3, removed, still votes). Node 2 commits `rem 1` with `{1,2}`
(node 1 had acknowledged index 3 before it voted), applies it (`{2}`), commits `x` at index 4 alone; node 1
commits its empty entry at index 4 with `{1,3}`. Index 4 differs.

    ('elect', 2, (1, 2, 3), 1)  ('propc', 2, ('rem', 3))  ('app', 2, 3, 2)  ('commit', 2, 2)
    ('apply', 2, 1)  ('apply', 2, 2)  ('propc', 2, ('rem', 1))  ('app', 2, 1, 3)
    ('apply', 1, 1)  ('apply', 1, 2)  ('elect', 1, (1, 3), 2)  ('propv', 2, 1)
    ('commit', 2, 3)  ('apply', 2, 3)  ('commit', 2, 4)  ('app', 1, 3, 4)  ('commit', 1, 4)

**`crash-sms`** (`trace-check-crash-sms.txt`): node 1 leads, commits and applies `rem 2`
(`{1,3}`), proposes `rem 3`; node 3 receives index 3 with commit 2 and restarts with commit
0 (persisted before that append), back on `C0`; it wins term 2 with `{2,3}` (node 2 removed)
and commits its empty entry at index 4; node 1 commits `rem 3` with `{1,3}`, applies it
(`{1}`) and commits `x` at index 4 alone.

**`lag-n3-sms`** (`trace-check-lag3-sms.txt`, every node allowed to lag, as in `model.py`):
both windows. Node 1 leads term 1, commits and applies (without `ApplyConfChange`) `rem 2`,
proposes `rem 3` and `x`; node 3 receives index 3 with commit 2, applies indices 1-2 without
`ApplyConfChange`, so it is on `C0` with nothing unapplied in `(2, 2]`, and wins term 2 with
`{2,3}` (node 2 removed), committing its empty entry at index 4; node 1 (on `C0`) commits
`rem 3` with `{1,3}`, applies all three conf changes (`{1}`) and commits `x` at index 4
alone.

### Faithful mode, exhaustive

| Run | Bounds | States | Diameter | Time | Result |
|---|---|---|---|---|---|
| `f-n4-t2-l4-c2-v1` | t2 l4 c2 v1 | 311,416,811 | 38 | 357 s | no violation |
| `f-n4-t2-l4-c2-v1-rs` | same, `-remself` | 438,558,109 | 38 | 506 s | no violation |
| `f-n4-t2-l4-c2-v1-read` | same, `-read` | 1,594,668,298 | 41 | 2109 s | no violation |
| `f-n3-t3-l5-c2-v1` | `-n 3`, t3 l5 c2 v1 | 29,057,574 | 37 | 38 s | no violation |
| `f-n3-t3-l5-c2-v1-rs` | same, `-remself -nostepdown -read` | 350,584,692 | 40 | 346 s | no violation |
| `fj-n4-t2-l5-c1-v1` | `-joint`, t2 l5 c1 v1 | 637,910,293 | 44 | 946 s | no violation |
| `f-n4-t2-l5-c2-v1` | t2 l5 c2 v1 | 1,627,363,607 | 43 | 2135 s | no violation |
| `fj-n4-t2-l5-c2-v0` | `-joint`, t2 l5 c2 v0 | 437,613,740 | 44 | 653 s | no violation |
| `f-n4-t3-l4-c2-v1` | t3 l4 c2 v1 | 1,672,014,248 through depth 23 | (23) | 2233 s | no violation; not exhaustive (table full at depth 24) |
| `f-n5-t2-l4-c2-v1` | `-n 5` (2 addable), t2 l4 c2 v1 | 1,561,796,062 through depth 17 | (17) | 3194 s | no violation; not exhaustive (table full at depth 18) |

(`-read` adds the read-index invariant; `-rs` runs let a leader remove itself and, at
`n 3`, keep leading after its removal.)

### Guard-fix mode

| Run | Bounds | States | Depth | Time | Result |
|---|---|---|---|---|---|
| `fix-n3-t2-l4-c2-v1` | `-n 3`, every node lagging, t2 l4 c2 v1 | 16,535,726 | 43 | 26 s | no violation |
| `fix-n3-t3-l5-c2-v1` | `-n 3`, every node lagging, t3 l5 c2 v1 | 504,421,887 | 51 | 495 s | no violation |
| `fix-n4-t2-l4-c2-v1` | every node lagging, t2 l4 c2 v1 | 1,714,817,564 through depth 23 | (23) | 2111 s | no violation; not exhaustive (stopped by hand before the table filled) |
| `fix1-n4-t2-l4-c2-v1` | node 1 lagging, t2 l4 c2 v1 | 1,694,124,022 through depth 25 | (25) | 1619 s | no violation; not exhaustive (table full at depth 26) |
| `fixj1-n4-t2-l5-c1-v1` | node 1 lagging, `-joint`, t2 l5 c1 v1 | 1,643,975,326 through depth 22 | (22) | 1619 s | no violation; not exhaustive (table full at depth 23) |

The 3-node bounds are meaningful for the fix: the unfixed lag mode at `-n 3`, t2 l4 c2 v1
violates state machine safety at depth 20 (`lag-n3-sms`, 1.1·10^7 states, 15 s;
`trace-check-lag3-sms.txt`, replayable in `model.py` as is), while the fix mode at the same
bounds is exhaustive and safe (diameter 43). At `-n 4` the fix-mode spaces are larger than
the table; their searches go 5-8 levels past the depths (17-18) at which the unfixed mode
fails at the same bounds.

## What the exhaustive faithful search covers, and what it does not

Covers, within the bounds: every interleaving of the model's atomic actions, so every
order of elections, replication of any prefix to any node, commits, applies and conf
proposals, including stale leaders that keep committing in their old configuration,
removed nodes that keep voting, an added node catching up, leaders removed by others'
entries (and, with `-remself`, by their own; with `-nostepdown`, staying leader), joint
configurations with auto-leave (`-joint`), and read index confirmed at the leader's
current configuration (`-read`). B1's case analysis (adjacent and far configurations, the
winners table, the witnesses) is exercised only as far as two conf changes reach: with
`c2`, configuration indices differ by at most 2, so the far cases `|j - j'| ≥ 2` can arise
(both conf entries committed and a stale node on `C0`), but not longer chains.

Does not cover:

- **Messages in flight.** A request and its response are one step, so there are no
  delayed, duplicated or reordered messages: no stale `MsgApp` arriving after a newer one,
  no vote granted at one time and counted later, no heartbeat response of an old term. B1
  argues over a network with arbitrary delays; here only "the message was never sent" is
  modelled (any action may simply not happen).
- **Elections are atomic**: no candidate state, no split votes, no voter that votes and
  then learns entries before the candidate wins; pre-vote equals vote. `MsgTimeoutNow`
  (leader transfer) is not modelled.
- **Snapshots, compaction, learners, restarts** (outside the crash mode, which is
  `issues/nonissues/raft-commit-lost-with-entries-kept.md`'s fault): none. So
  `issues/raft-snapshot-during-apply-stale-confchange.md` is out of scope.
- **Joining nodes start from `C0`.** An addable node starts with an empty log and the
  initial configuration `C0` (it is not a member of it, so it cannot campaign until it has
  applied its own `add`). This is the bootstrap assumption B1 makes and the fix that
  `issues/nonissues/raft-joiner-empty-confstate.md` asks for; that issue's execution (a joiner whose
  configuration is the fold of the changes onto an empty one, winning alone) is excluded
  by construction.
- **Conf change shapes**: `add`/`rem` of one voter (simple), or entering a joint
  configuration that toggles one voter, with auto-leave; no learners, no demotion, no
  multi-node joint changes, no explicit (non-auto) leave, no rejected changes. A leader does
  not remove itself unless `-remself`.
- **The commit index** reaches followers only through `app` (which also covers heartbeats,
  `q = p`). `app` is skipped when the leader's log diverges below the follower's commit
  (as in `model.py`); such a state already violates the checked invariants.
- **Read index** is one pending request at a time, and its heartbeat round is one atomic
  step at confirmation that changes no node's state: fewer executions than raft's.
- **Bounds**: at most 2 conf changes, 1 value (2 at the smaller sizes), terms 2-3, logs 4-5.
  An execution that needs a third conf change, a fourth term or a sixth entry is not
  explored. The lagging-mode counterexamples need t2 l4 c2 v1, the bounds of most runs.
- **Fingerprints**: the visited set stores 64-bit hashes; a collision would silently
  drop a state. The probability of any collision is about `n^2 / 2^65`: 0.3% at
  3·10^8 states, about 7% at 1.6·10^9 (the read run). TLC's exposure is the same.

## Reproducing

    cd issues/raft-conf-lag-model/checker && go build -o /tmp/rcc .
    ./runs.sh /tmp/rcc /tmp/runs                          # all of the above, hours
    ONLY="lag-1-sms crash-sms" ./runs.sh /tmp/rcc /tmp/runs
    /tmp/rcc -n 4 -mode lag -replay ../trace-leaderlag.txt
    cd .. && python3 model.py 4 3 lag 2 4 2 1 simple trace-check-lag-sms.txt   # ends UNSAFE
