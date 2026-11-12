# RR-raft-core: second re-review of the raft node API (R1) and raft core (R2)

Reviewer: fresh and independent, read-only. HEAD `41c6c3a39f`. Diffs are against `4a6a9b6b6e`.

**What changed in the area.** Four spec files changed:
- `Api.lean`
- `ApiCore.lean`
- `ApiLog.lean`
- `raft__hasUnappliedConfChanges.lean`

No snippet in `examples/specreq/{raftnode,raftcore}` changed.

**How I checked.**
- I wrote my verdict on each finding of `R-A4-raft-node-core.md` before I read `repair-raft-core.md` ("Re-review of A4"). It agrees with mine on every point except N2, where I find a residue (N3 below).
- `etc/lean-check.py -a` passes on the four files (0 errors).
- Go source: `.lake/src/raft`.

## Verdicts

| batch | verdict | why |
|---|---|---|
| **R1** (node API: `Model`, `Api`, starts, `Ready`, `MemoryStorage`) | **PASS WITH OPEN DECISIONS** | N1 is fixed. S-c and S-d are fixed. The open decisions are: 2.8 (crash scope `confAboveOk`), C33 (`storedLb`), C34 (`loggerOk` without argument ownership), and 5.1 (the step bound, through `ReqTick`). |
| **R2** (`ApiCore`, `raft.go`, the `Ready` phases) | **FAIL** | N3: `hasUnappliedConfChanges.spec`, with the repaired premise, still claims "no panic" in a state its precondition admits and in which Go panics. The fix is one conjunct. Without N3, R2 would be PASS WITH OPEN DECISIONS: 2.1, 2.2 (`ConfigOk`), C32 (`coreIdle`), 5.1. |

## Findings of R-A4 rechecked

| finding | status | evidence at HEAD |
|---|---|---|
| **N1** `raftState_crash`, batch record at `j = 0` | **Resolved** | `Api.lean:918-919`: the second disjunct now requires `j = b.ents.length`. This excludes R-A4's counterexample: `j = 0` with `[2:t2]` would need `j = 1`. The old-record case at any `j` is still safe. Its commit is at most `D.commit ≤ st.hs.commit`, and `BatchOk` gives `st.hs.commit < entsFrom` (`Model.lean:375`), so it never covers a replaced entry. The WAL's `Recs.crashedMid` (`wal/Api.lean:168-172`) and `disk_crash`'s realization (`ApiBoot.lean:130-134`, `:148-150`) use the batch record only with all entries written. The WAL's empty-entries `Save` with a state record is `j = 0 = |ents|`, which still matches. |
| **N2** `hasUnappliedConfChanges` with a snapshot pending | **Resolved for the reported state; residue N3** | `raft__hasUnappliedConfChanges.lean:34` now takes `compactFloor ≤ applied`, where `compactFloor = max base (max applied floor)` (`ApiLog.lean:285`). This excludes the reported state (pending snapshot, `applied < base`, `ErrCompacted` → `Panicf` at `raft.go:1035`). It does not exclude a pending snapshot with `base ≤ applied` and a `lastIndex` short of `committed` (N3). The source of `base ≤ applied` is also not stated as a law (S-e). |
| **S-a** `rawNodeAt_advance` with a snapshot batch | **Resolved** (realization text) | `ApiCore.lean:551-554`: for a snapshot batch, the floor is `logStor_install`'s `logFloor l s.index s.term`, kept in `readyStor rn none j []`. `readyStor_install`'s COMM (`Api.lean:945-946`) gives `appliedLb n s.index`, which is consistent with this. |
| **S-b** `coreIdle` outside the apply acknowledgement | **Resolved** | `ApiCore.lean:368-374`: the token stays in `rawNodeAdv` and returns at `rawNodeAdv_open`'s closing. Only an apply acknowledgement lends it. |
| **S-c** downward closure of `logStored`/`logFloor` | **Resolved** | `ApiLog.lean:628-636` adds `logStored_mono` and `logFloor_mono` (`∃ t'`), which `storedLb_mono`/`appliedLb_mono` (`Api.lean:872-879`) rest on. Both are true under the stated realization: below a stored or published committed index, the committed log has a term at each index, and a compacted or snapshotted index answers `ErrSnapOutOfDate`. They are consistent with `logFloor_agree` (`:644`) if `t'` is the committed log's term at `j`, which the realization should say. That is a one-word gloss, not a finding. |
| **S-d** `DescribeConfChange` assumed | **Resolved** | `notes/perennial-changes.md:2092-2101` has a new entry, "No specs of `fmt.Fprintf` / `strings.Builder`". |

## New first-tier finding

### N3. `raft.hasUnappliedConfChanges.spec` panics in Go on a state its precondition admits

**Location:** `SpecPlan/Spec/go_etcd_io/raft/v3/raft__hasUnappliedConfChanges.lean:31-36`.

**Principle:** Sound (a no-panic post over a premise checked against the states it does not pin down). This is the same class as N2.

**The state.** It satisfies the precondition `raftOpen r γ id o ∗ ⌜o.log.compactFloor ≤ o.log.applied⌝`, and `LogState.Wf` (`ApiLog.lean:412-424`) allows it:
- `us.snap = some s`, with `base = s.index`;
- `us.ents = []`, with `offset = committed + 1`;
- `base ≤ applied < committed`.

Every conjunct of `Wf` holds:
- `base < offset`;
- `s.index < offset`;
- `applied ≤ applying ≤ committed ≤ end = offset - 1`;
- the "nothing unstable" clause is vacuous because `snap ≠ none`.

**What Go does there.**
1. `hasUnappliedConfChanges` scans `[applied+1, committed+1)` (`raft.go:1020-1027`).
2. `scan` calls `slice`, which calls `mustCheckOutOfBounds` (`log.go:482-500`, `:551-563`).
3. `firstIndex() = s.index + 1` (`maybeFirstIndex`). `lastIndex() = s.index`: `maybeLastIndex` returns the snapshot's index when there are no entries (`log_unstable.go:67-75`; the spec's `lastIndex`, `ApiLog.lean:160-162,271`).
4. So `length = 0`, and `hi = committed + 1 > fi + 0` reaches `Panicf("slice[%d,%d) out of bound …")` (`log.go:562`).

The spec instead claims a Boolean result. Its proof plan does not close either, because `raftLog.scan.spec` requires `hi ≤ lastIndex + 1` (`raftLog__scan.lean:41`).

**Reachability.** Go never reaches this state:
- `restore` requires `s.index > committed ≥ applying`;
- while a snapshot is pending, `nextCommittedEnts` hands out nothing, so `applying` (and with it `applied`) stays below `s.index`;
- `appliedSnap` clears the snapshot before `appliedTo(s.index)` (`raft.go:766-769`).

The fact "snapshot pending → `applied < base`" is not in `Wf` or in any stated law, so the spec relies on it without stating it. The R-A4 author's own fix offered `us.snap = none` as an alternative.

**Caller.** `hup` (`raft.go:997-1001`) calls it only after `promotable()`, which `raft__promotable.lean:35` states as including `o.log.us.snap = none`. So `hup` can supply the conjunct, and nothing else is affected. The R3 snippet `ReqScanConfChanges` (`examples/specreq/raftlog/reads.go:89-91`) has the same gap: it assumes `applied >= base` but does not assume that no snapshot is pending. That snippet is R3's, so I only note it here.

**Fix.** Take `⌜o.log.us.snap = none ∧ o.log.compactFloor ≤ o.log.applied⌝`. With `snap = none`:
- if there are no entries, `lastIndex = base + stored.length = stable = end` by `Wf`, which is at least `committed`;
- otherwise `lastIndex = end`.

In both cases `scan`'s `hi ≤ lastIndex + 1` holds.

## Second tier (new)

- **S-e. `hup`'s source of `base ≤ applied` is not stated** (`ApiCore.lean:673-675`; `raft__hasUnappliedConfChanges.lean:5`).
  - The docstring says `hup` has the premise "after `promotable` (no pending snapshot: the base is then at most `applied`, the invariant's) and … `coreIdle_floor`".
  - `coreIdle_floor` gives only `floor ≤ applied`. `Wf` does not give `snap = none → base ≤ applied`: it fails inside `appliedSnap`, between `stableSnapTo` and `appliedTo` (`raft.go:768-769`). `ApiCore.lean`'s realization (items 1-6) does not list it either.
  - The fact is true of Go at every step boundary. `newLogWithSize` sets `applied = firstIndex - 1 = base` (`log.go:94-96`), `appliedTo` only grows `applied`, and `appliedSnap` sets `applied = s.index` as soon as the snapshot is cleared.
  - This is the gap P3 had before `coreIdle_floor` was added.
  - Fix: extend `coreIdle_floor`'s conclusion with `⌜o.log.us.snap = none → o.log.base ≤ o.log.applied⌝`, or add it as a law of `raftOpen ∗ coreInv`. It holds outside `appliedSnap`, which runs with the invariant broken.
- **S-c gloss** (optional): say in `logFloor_mono` that `t'` is the committed log's term at `j`, so that `logFloor_agree` stays evidently consistent.

## Regressions (the four changed files)

- **`Api.lean`**: only `raftState_crash`'s docstring and its `j = b.ents.length` conjunct changed. The law is now plausible: every allowed state is a prefix of the record stream that etcd's WAL and kvdurable write. Its users are unchanged (above).
- **`ApiCore.lean`**: docstrings only (S-a, S-b). Both agree with the code:
  - `node.run` steps the acknowledgements in the `advancec` arm (`node.go:441-444`);
  - `appliedSnap` runs at a non-leader.
- **`ApiLog.lean`**: the two new `_mono` laws are plausible and not vacuous (S-c). There is no way to derive `False` from them, given `logFloor_agree` under the committed-term reading.
- **`raft__hasUnappliedConfChanges.lean`**: N3 and S-e.

Apart from N3, I found no way to prove `False` and no panicking program proved safe.

**Snippets.** None changed since `4a6a9b6b6e`. R-A4's snippet verdicts still stand: `raftnode/*`, and `raftcore/{ready,step,conf,status}.go`, close.

## Go code

I found no new bug. N3's state is unreachable in Go, so it is a spec issue, which belongs in `notes/` and not in `issues/`.

## Counts

- **R-A4 findings rechecked:** 2 first-tier and 4 second-tier.
  - N1, S-a, S-b, S-c and S-d are resolved.
  - N2 is resolved for the state it reported, with the residue N3.
- **New findings:** 1 first-tier (N3) and 1 second-tier (S-e), plus one optional gloss.
- **Spec files re-checked:** 4 changed. 3 close; 1 does not (`raft__hasUnappliedConfChanges.lean`).
- **Snippets re-checked:** 0 changed.

## Ranked by need of revision

1. `raft__hasUnappliedConfChanges.lean`: add `o.log.us.snap = none` to the premise (N3).
2. `ApiCore.lean` `coreIdle_floor`: also give `us.snap = none → base ≤ applied` (S-e).
3. `ApiLog.lean` `logFloor_mono`: name `t'` (gloss).
