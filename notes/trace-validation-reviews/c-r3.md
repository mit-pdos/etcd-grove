# Review round 3: trace-check, Draft of layer C (NewTrace / CheckTrace / Result.TLCOK specs, Rep, Base)

Reviewed at `2295d4f7cf`. Round 2's repair (the `stateRO` map-domain conjunct) is on top of `5d2445f0a6`. The Go
(`examples/raft/tracecheck/etcdraft/*.go`) and the Lean transcription (`Tla/*.lean`) have not changed since round 1
(`git diff --stat 5cf76a35aa HEAD`: only Rep, the three specs, and round 1's `Check.lean`/`Trace.lean` edits). So this
round re-read every predicate against the Go, and the Go against the Lean, function by function.

Scratch: `/tmp/claude-1000/-workspace-etcd-grove/8e48033c-792a-435a-bae3-16d75b0d1a02/scratchpad/c3/`.

**Does anything first-tier remain? No, apart from Q7, which is known and open with the user.** Under Q7's premise
(the Lean `lineFuel` is never exhausted), I found:
- no state `traceRO` admits on which the Go panics with something other than an `EvalError`;
- no Go/Lean divergence on a field `resultRel` relates;
- no gap in what `Main`'s proof needs.

One finding is second tier and new: a third option for Q7 that needs neither a reachability invariant nor a change to
the transcriptions' meaning (S1).

## Checks run

- `etc/lean-check.py -q` on the five targets: 0 errors each.
- The crafted `cfg7` trace from round 2, re-run at HEAD:
  - Go: `go run ./cmd/checktrace .../c2/traces/cfg7.ndjson` gives `trace not matched: no behavior steps through line 23`.
  - Lean: `go run ./cmd/leanexport ... > c3/cfg7.lean && lake env lean c3/cfg7.lean` gives
    `tlcOK false ok false branched 0 line 23 violation none evalError none`.
  - They agree. Since the code is unchanged, round 2's 16-trace agreement still applies.

## Round 2's findings at HEAD

| Round 2 | Status at `2295d4f7cf` |
|---|---|
| F1 (map domain) | **Addressed**, Rep.lean:164-166. Correct: NewTrace builds `S` with exactly `t.Server`'s keys (trace.go:300-323). `clone` copies the map (spec.go:72-79). `mut` writes only an existing key (spec.go:83-87). Ids are below 2^64 by `parseID` in both (trace.go:73-90, Trace.lean:75-82), so `uint.nat k ∈ st.server` and `W64 (Int.ofNat i)` agree. |
| S1 (lineFuel) | Now Q7. See S1 below for a third option. |
| T1 (stale `2^62`) | **Addressed** (plan:290-291). |
| T2 ("only NewTrace produces it") | **Open**: Rep.lean:239-240 still says "which only `NewTrace` produces". See T1 below. |
| T3 (`numBound` docstring) | **Addressed** (Rep.lean:66-69). |
| T4 (`Trace.Valid.*` laws) | Open, deferred to S6 with sealing. Fine. |
| T6 (overflow margin in S6's loop invariant), T7 (branching untested) | Open. See T3 and T4 below. |

## Why nothing first-tier remains (evidence)

### Representation predicates vs. what `NewTrace` builds
Every field of every Go struct is related:
- `Event`: 8 fields; `EventMsg`: 11; `line`: 7; `Trace`: 5; `State`: 5; `Server`: 11; `Durable`: 5; `Config`: 2;
  `Msg`: 13; `Entry`: 3; `Value`: 4; `bagItem`: 2.

The initial state matches `newTrace`'s:
- **Log**: `make([]Entry, lb.ev.Log)` with each entry `Entry{Term:1, ConfigEntry, ConfRecord cfg, Learners nil}`
  (trace.go:307-310) is the Lean `List.replicate lb.ev.log.toNat {term:=1, .config, .conf cfg []}` (Trace.lean:240).
- **Nil fields**: `VotesResponded`, `VotesGranted`, `Joint[1]` and `Learners` are nil, which is `setRO _ []`.
- **MatchIndex** is `map[ID]int{}`, which agrees with `fun _ => 0` (serverRO's `getD 0`).
- **Durable** is `durableOf(v)` in both.
- **Bags** are the zero `Bag{}`, which is `bagRO _ []`.

### `newTrace` errors iff Go's `NewTrace` errors
The checks match one for one, and the spec only distinguishes error from success:
- parse checks: trace.go:177-216 vs. `parseLine`, Trace.lean:153-178;
- the added server: trace.go:221-235 vs. `addedServer`;
- the missing bootstrap line: trace.go:245-272 vs. `bootstrapOf` and the `per.find?` throw;
- `bootstrappedConfig`, the `InitSrv ⊆ Server` check and the per-server configs: trace.go:274-306 vs.
  Trace.lean:228-238.

Lean's `parseID` works on characters and Go's on bytes. They agree: any non-ASCII character is a non-digit in both,
and an all-digit string is ASCII.

`Event.Bounded` keeps `make` from panicking: `ev.Log ≥ 0` and `< 2^40`.

### The Go's only non-`EvalError` panics are unreachable from `traceRO` and the search's invariant
I went through every indexing, map dereference and slice operation:
- `ts.S.S[i]` for `i ∈ t.Server` (trace.go:803, 829, spec.go throughout): present, because `stateRO`'s domain is
  `st.server`, and `st.server = tr.server` by `Trace.Valid`. `State.Server` is never written.
- `Receive` (spec.go:668-671), `stateMatches` (trace.go:448-451) and `QuorumLogInv` (invariants.go:95) look up a
  possible non-server by `ok`. The Lean uses `server.contains`, which is round 2's F1, now repaired.
- `HasNoConflict`'s `log[index+k-2]` (spec.go:569) needs `index ≥ 1`, that is `m.PrevLogIndex ≥ 0`. Messages are built
  only by `AppendEntriesInRangeToPeer` with `prevLogIndex = b-1`:
  - `b = ev.Index+1`, and `ev.Index ≥ 0` by `numOk m.index`;
  - `b = 1` for heartbeat and snapshot.
  This holds. S6's invariant must carry `prevLogIndex ≥ 0` for every message.
- `applyConfigUpdate`'s `v.Log[k-1]` (spec.go:174) and `ApplySimpleConfChange`'s loop (spec.go:440-444) are guarded
  by the `CommitIndex > len(Log)` `EvalError` (spec.go:434-436).
- `AdvanceCommitIndex` (spec.go:376) is within bounds.
- `LeaderCompletenessInv`'s `s.S[i].Log[idx-1]` (invariants.go:127) satisfies `idx ≤ len(Committed) ≤ len(Log)`.
- `SubSeq` slices only after its own check (types.go:226-229).

### The `EvalError` strings and the evaluation order agree
- The three `EvalError` sites have the same `What` strings, character for character:
  - types.go:227 = Spec.lean:38;
  - spec.go:435 = Spec.lean:276;
  - invariants.go:132 = Invariants.lean:94.
  `resultRel` relates `EvalError` by `What` only, so this is what it needs.
- Where an `EvalError` can be preempted by an earlier `false`, the Lean short-circuits as the Go does:
  - `List.allM` in `logInv`, `quorumLogInv`, `moreUpToDateCorrectInv` and `leaderCompletenessInv`;
  - `foldlM` in `violated`;
  - `Committed(j)` evaluated only under the guard (invariants.go:111-112 vs. Invariants.lean:79-81).
- `handleAppendEntriesRequest` evaluates `accept` before `reject`/`returnToFollower` (Spec.lean:381-382), unlike the Go
  (spec.go:633-634). Both of those are pure, so the order cannot change which error wins, and the output list order
  is the Go's.

### The search
`CheckTrace` (check.go:60-106) against `checkTrace`/`checkFrom`/`checkLine` (Check.lean:246-282), and `StepLine`
(trace.go:903-942) against `stepRound`/`stepLoop` (Trace.lean:572-614), agree on every field `resultRel` relates
(round 2's analysis, re-checked):
- the violation-before-branch order;
- `fresh` (always appended, since `out` and `visited` are disjoint by `L`);
- the recovered-panic `Branched`: a frontier of more than one state implies `Branched ≠ 0` from the previous line,
  which S6 needs as a lemma.

Goose's `wrapDeferRecover`/`recoverPanic` (Perennial `Golang/Defn/Defer.lean:32-51`) give the Go's recover semantics.
`TypeAssert2 EvalError.ty` then distinguishes the transcription's panics (Code `etcdraft.lean:549-575`).

### Sufficient for `Main`
`Main` (main.go:21-26) does `NewTrace(ConvertEvents(...))`, panics on `err ≠ nil`, then calls
`CheckTrace(tr, true).TLCOK()`. The specs chain:
1. `NewTrace`'s `.ok tr` branch gives `traceRO t tr`.
2. `CheckTrace` gives `resultRel r (checkTrace tr true)`.
3. `TLCOK` gives `(checkTrace tr true).tlcOK`, which is `traceAccepts evs` (Check.lean:286-289).

`Main` needs from layers B and D: `eventsRO` of `ConvertEvents`' slice (persisted by `Main`, which does not reuse
it), `Event.Bounded`, the length bound, and `traceAccepts evs`.

## Second tier

### S1. Q7 has an option that needs no reachability invariant and changes no meaning: a counting fuel
- **Principle**: Provable. A spec's truth should rest on what its proof can establish locally. Q7's (a) needs a global
  invariant of `etcdraft.tla` (Restart, persistence, any initial roles). Q7's (b) changes both transcriptions' meaning
  (a trust question) and adds an obligation to layer B.
- **Observation**: within one line, a step that keeps `L` is a `Receive` handler that does not consume `m`.
  `oneLessMessage` holds for every step that discards or replies, so those go to `L+1`: `Reply`/`Discard` decrement
  `m`'s count by one, and `m ∈ DOMAIN messages`. The non-consuming handlers are `UpdateTerm`, `ReturnToFollowerState`,
  `ConflictAppendEntriesRequest` and `NoConflictAppendEntriesRequest` (spec.go:536-593, 649-656). Every matching
  message has `Dest = ln.to` (all four `isX` predicates). So every state in `visited` equals `ts` except in server
  `ln.to`'s 4-tuple `(currentTerm, state, votedFor, log)`, and:
  - **term**: `ts`'s, or some `m.term` with `m ∈ dom messages`;
  - **state**: `ts`'s, or follower;
  - **votedFor**: `ts`'s, or `nil`;
  - **log**: a list of length at most `Lmax = max(|log₀|, max_m (m.prevLogIndex + |m.entries|))`, whose entry at
    position `k` is `log₀[k]` or the aligned entry of some `m`'s entries. `NoConflict` gives
    `log ++ entries[len-index+2..]`, and `Conflict` truncates by one.
- **Consequences**:
  - `|S(ts)| ≤ (|M|+1)·2·2·(Lmax+1)·(|M|+1)^Lmax`, with `M = dom(ts.s.messages)`.
  - Each round of the Go loop with a non-empty frontier adds new (`TState.Equal`-distinct) states to `visited ⊆ S(ts)`.
  - So the number of rounds is at most `|S(ts)|`.
- **Repair (option (c) for Q7)**: define `lineFuel ts` as that closed-form bound plus 1, computed from `ts` alone.
  - Fuel size costs nothing at run time: `stepLoop` returns as soon as the frontier is empty (Trace.lean:609), so an
    astronomically large fuel only costs computing one big `Nat` per line.
  - S6 then proves two things, both local to the Lean definitions:
    1. a closure lemma: the within-line successors stay in `S(ts)`;
    2. pigeonhole on `visited`: `memEq`-distinct members of `S(ts)` differ in the 4-tuple.
  - It needs no Go change, no change to the TLA+ meaning (no new evaluation error) and no layer-B obligation.
  - Compared with (b), it keeps the transcriptions as reviewed in S4.
  - I recommend presenting it to the user next to (a) and (b) in Q7.
  - **Uncertain**: I did not mechanize the counting. The bound's components rest on reading spec.go:536-593 and
    649-686.

## Third tier

- **T1. `traceRO`'s docstring overclaims** (Rep.lean:239-240, also NewTrace header, plan:299 "only `NewTrace`
  produces it"): `traceRO` is an exposed definition, buildable by anyone holding the points-to facts and a
  `Trace.Valid` witness. Say "carries `Trace.Valid tr`, which `NewTrace` establishes" until sealing. Round 2's T2,
  unaddressed.
- **T2. `Trace.Valid`'s docstring** (Rep.lean:233-235) lists what "the Go's search relies on". The map's domain, which
  the Go relies on just as much, is in `stateRO` (Rep.lean:164-166). Add "the state's map holds exactly the servers
  (`stateRO`)" to the list, or drop "what the Go relies on".
- **T3. Facts S6's loop invariant must carry** (record them with Q7's obligations; T6 of round 2 extended):
  - every message's `prevLogIndex ≥ 0`, which the Go's `HasNoConflict` index needs to avoid an index-out-of-range
    panic;
  - every `matchIndex ≥ 0`;
  - `State.server = tr.server`, with the map's domain equal to it;
  - every number `< (lines+2)·numBound`.
- **T4. Branching is still untested** (round 2 T7). A recipe for a witness:
  `LoglineIsAppendEntriesRequest` ignores `mcommitIndex` for subtype `snapshot` (trace.go:388-390, Trace.lean:278).
  So two `SendSnapshot`s of the same `index` from a leader whose commit index moved in between leave two bag messages
  that both match one `ReceiveSnapshot` line, and their receipt gives distinct successors (`commitTo`). A hand-made
  NDJSON with `MsgSnap` lines would exercise the `Branched` paths of both checkers.
- **T5. `lineFuel`'s docstring** (Trace.lean:566-568, not a target) states as fact that the Go loop "needs no bound"
  and that the fuel bounds a line's steps. Until Q7 is settled, say that it is assumed (Q7).

## What is good

- **Round 2's repair** is one conjunct, placed where S6's loop invariant can reuse it (it is part of `stateRO`, not
  `traceRO`), and it is exactly what the Go's lookups need. The Persistent instances still elaborate.
- **The specs are minimal and close `Main`'s chain** with no extra premise:
  - `NewTrace.spec`: the error is iff, plus `traceRO`;
  - `CheckTrace.spec`: one pure relation;
  - `Result.TLCOK.spec`: the method on the value receiver, as `Main` calls it.
- **The representation is canonical where the Go compares by value**:
  - `Value`'s empty sets when the kind is not a configuration record, which makes `applyConfigUpdate`'s `([], [])`
    fallback (Spec.lean:131-134) agree with the Go's unconditional field read;
  - `matchIndex` as a total function;
  - sets as sorted `uint.nat` lists.
  So the Go's `Equal`s are the Lean's `==`.
- **`resultRel`** relates exactly the Lean `Result`'s fields, and the strings it relates agree verbatim.

## Ranking by need of revision

1. **`Spec/.../etcdraft/CheckTrace.lean`**: true modulo Q7 only. Settle Q7, and consider S1's option (c), which
   moves no meaning.
2. **`Proof/.../etcdraft/Rep.lean`**: correct. Docstrings: T1 and T2.
3. **`Spec/.../etcdraft/NewTrace.lean`**: correct. Its header repeats T1's "only".
4. **`Spec/.../etcdraft/Result__TLCOK.lean`**: correct, nothing to change.
5. **`Proof/.../etcdraft/Base.lean`**: `True` is fine for the Draft. S6 strengthens it with the tables and
   `Invariants`.

**Bugs in the Go code**: none found. No `issues/` or `nonissues/` entry is warranted. The non-`EvalError` panics I
examined (T3) need states `NewTrace` and the search never build.
