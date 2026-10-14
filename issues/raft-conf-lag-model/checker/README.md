# An explicit-state checker for `../model.py`

A Go transcription of the membership model `../model.py` with a parallel breadth-first
search, symmetry reduction and a fingerprint visited set. Results and what they cover:
`notes/reconfiguration-model-check.md`.

    cd issues/raft-conf-lag-model/checker
    go build -o /tmp/rcc .            # Go 1.26, no dependencies
    /tmp/rcc -n 4 -mode faithful -maxt 2 -maxlog 4 -maxconf 2 -maxval 1 -tablelog 30
    /tmp/rcc -n 4 -mode lag -replay ../trace-leaderlag.txt      # replay a model.py trace
    ./runs.sh /tmp/rcc /tmp/runs      # every run of the notes (hours; set ONLY="name ..." for some)

## Semantics

`model.go` follows `model.py`'s `succ` action by action (`elect`, `propv`, `propc`, `app`,
`commit`, `apply`, `applyconf`, `crash`, `after_cfg`'s step-down and auto-leave), with the
same arguments: `-n N -init I -mode M -maxt -maxlog -maxconf -maxval [-joint] [-reduced]`
are `model.py N I M MAXT MAXLOG MAXCONF MAXVAL simple|joint` (`REDUCED=1`). Checked
against it: with `-sym=false -es=false` the cumulative state counts per BFS depth equal
`model.py`'s output ("finished all states at depth d states so far k") at every depth
compared (lag 4/3/3/5/2/2 to depth 7, crash 4/3/3/5/2/2 to depth 7, faithful joint
4/3/2/4/1/1 to depth 8, lag joint 5/3/2/4/2/1 to depth 6), and the three traces
`../trace-*.txt` replay to the same final states (`-replay`, which prints model.py's action
tuples). Every counterexample the checker prints replays in `model.py` too (with
`-lagnodes`, use the second listing it prints).

Modes: `faithful`, `lag`, `crash` as in `model.py`; `fix` is `lag` with the guards of
`../guard-fix.md` (the opt-in `TrackConfChangeApplication`): the campaign guard scans
`(cfgidx, commit]` (some committed conf entry not yet passed to `ApplyConfChange`), the
leader's check is `pendingConfIndex > confApplied()` and auto-leave compares
`confApplied()` with `pendingConfIndex`, where `confApplied()` is the applied index, or the
index before the oldest conf entry at or below it that `ApplyConfChange` has not had.

Additions, not in `model.py` (each can be switched off):

- `-es` (default on): a ghost bit per term, set when the term is won; a second win of the
  same term is an **election safety** violation. It is part of the state (off for the
  count comparison with `model.py`).
- Invariants (`-inv`, default all): `sms` is `model.py`'s `safe` (two nodes' committed
  prefixes agree); `lm` log matching (an index with the same term in two logs has equal
  prefixes); `es` above; `lc` leader completeness, checked at each win (the winner's log
  extends every node's committed prefix); `read` below.
- `-read`: read index. `readreq i` (leader `i`, the entry at its commit is of its term,
  no other read pending) records `(i, term, commit, largest commit of any node)`;
  `readok i` (still leader of that term, and the nodes of term `<=` it, with `i`, are a
  quorum of `i`'s current configuration) answers it, and a violation is a read index below
  the largest commit at arrival; `readdrop` forgets the request. One read pending at a
  time; the heartbeat round is one atomic step at confirmation that changes no node's
  state (so it covers fewer executions than raft's, where acknowledgements arrive one by
  one and update terms). `-read-no-term-check` drops the committed-entry-in-term check, a
  known bug the checker must (and does) find, at depth 6.
- `-read-singleton-bug`: read index as the pinned `stepLeader` does it when
  `IsSingleton()` (one incoming voter, no outgoing half, whoever it is): `readsingle i`
  answers at once with `i`'s commit, a violation if some node's commit is larger
  (`notes/reconfiguration-safety-review.md`, finding 1; `issues/raft-readindex-singleton-stale.md`).
  The checker finds both of the review's executions (with `-remself`, and `-nostepdown`).
- `-remself`: a leader may propose its own removal (`model.py` excludes it: `rem j` for
  `j != i` only; with `-joint`, also a joint change that drops it).
- `-nostepdown`: `StepDownOnRemoval` off (raft's default); `model.py` always steps a
  removed leader down (`after_cfg`).
- `-lagnodes 1,2`: in the lagging modes, only these nodes' applications lag (the others
  apply as in `faithful`, which `model.py` expresses as `apply` then `applyconf`).

## Search

Level-synchronous BFS, `-workers` goroutines over chunks of the frontier. Successors are
canonicalized under the permutations of the node ids that preserve the model's classes
(initial voters / addable nodes, lagging / not), as the lexicographically least encoding
over the group, and hashed to 64 bits (`hash/maphash`); the visited set is an
open-addressing table of fingerprints (`-tablelog k`: `2^k` slots, 12 bytes each with the
parent slot for traces, 8 with `-noparents`), lock-free inserts. Frontier states are stored
4 bits per field, in memory or (`-spill DIR`) in files. A violation stops the search at the end of its depth (`-all`: keep
going, one report per invariant) and prints the shortest trace (BFS) rebuilt from the
parent slots. The search is exhaustive when a level adds no state ("exhaustive: no new
states"); it stops early, saying so, at `-maxdepth` or when the table is 85% full.

Fingerprints may collide (two different states with one fingerprint: the second is taken
as visited): with `n` states the chance of any collision is about `n^2 / 2^65`, 0.3% at
3·10^8 states (TLC has the same exposure).

Messages are not modelled as a network: as in `model.py` a request and its response are
one atomic step (`app` replicates a prefix and updates the leader's `match`; an election
is one step with its votes). There is no message loss, duplication or reordering to bound.
