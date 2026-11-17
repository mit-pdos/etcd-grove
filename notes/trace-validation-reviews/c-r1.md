# Review round 1: trace-check, Draft of layer C (NewTrace / CheckTrace specs, Rep, Base)

Reviewed at HEAD `5cf76a35aa` ("trace-check, Draft: layer C's specs ..."). The brief names commit
`4ab0dbe53d`, which does not exist in this repository (`git log 4ab0dbe53d` says "unknown
revision"). `5cf76a35aa` is the only commit that adds the four targets, so I reviewed it.

`etc/lean-check.py` on the four targets: 0 errors. The Go checker and the Lean transcription
agree on a generated trace: `full-1`, 696 events, not matched at line 459, gives the same result
from both (`go run ./cmd/checktrace` vs `cmd/leanexport` + `lake env lean`). Scratch work is in
`/tmp/claude-1000/-workspace-etcd-grove/8e48033c-792a-435a-bae3-16d75b0d1a02/scratchpad/c1/`.

## First-tier

### F1. `CheckTrace.spec` is false: it accepts any `tr` with `traceRO`, and the Go panics on traces `NewTrace` never builds
- **Principle**: Sound (no panic under the precondition).
- **Evidence**: `traceRO t tr` (Rep.lean:222-226) relates the Go fields to the Lean ones and
  nothing more. It does not say that `tr` is well formed. The Go relies on several facts that hold
  only for a trace `NewTrace` built:
  - `tr.init.server = tr.server`. `nonReceive` walks over `t.Server` (trace.go:748) and
    dereferences `ts.S.S[i]` (trace.go:777; spec.go:348 and others). A server missing from the
    state's `S` map gives a nil `*Server`, so Go hits a nil-pointer panic. That is not an
    `EvalError`, so `CheckTrace` re-panics (check.go:64-66).
  - `tr.bootstrap.length = tr.lines.length`. `t.bootstrap[ts.L-1]` (trace.go:879) panics with an
    index out of range, where the Lean uses `getD … false`.
  - The `matchIndex` keys outside `st.server` (see F4).

  I ran a scratch copy of the package
  (`/tmp/claude-1000/-workspace-etcd-grove/8e48033c-792a-435a-bae3-16d75b0d1a02/scratchpad/c1/tc/etcdraft/wf_scratch_test.go`).
  The trace has one `Replicate` line for server 1, `Server = {1}`, and an init `State` with
  `Server = {}` and an empty `S`. `traceRO` holds of it, with the Lean `init.server = []`. Output:
  `panic escaped CheckTrace: runtime error: invalid memory address or nil pointer dereference`.
  The Lean `checkTrace` returns a `Result` on the same trace.
- **Caller affected**: `Main` itself is unaffected, since it only passes `NewTrace`'s output. The
  spec as stated, though, cannot be proved.
- **Repair**: have the trace's only producer carry the fact (spec skill: "a workload premise …
  goes on the resource's only producer, carried by the resource"). Let `traceRO t tr` include
  `⌜Trace.Valid tr⌝`, where `Trace.Valid tr := ∃ evs, (∀ e ∈ evs, e.Bounded) ∧ evs.length < B ∧
  newTrace evs = .ok tr`. Alternatively, use an explicit `Trace.WF` with laws: `init.server =
  server`, `bootstrap.length = lines.length`, every line's `nid ∈ server`, sets sorted,
  `init.s i`'s `matchIndex = fun _ => 0`, and so on. `NewTrace` gives it, and `CheckTrace` takes
  only `traceRO` (its pure premises on `tr.lines` disappear). This also removes `CheckTrace`'s two
  Lean implications (T1).

### F2. `resultRel`'s `Branched` disagrees between Go and Lean when a violation is found
- **Principle**: Sound. The spec relies on the two transcriptions agreeing on every field
  `resultRel` relates (Rep.lean:230-234).
- **Evidence (by reading; I did not run it, because building a violating trace is costly)**:
  - **Go `StepLine`**: the state `s2` goes into `fresh` (trace.go:925-926) *before* the invariant
    check. On a violation it returns at once (trace.go:928-931), so it never reaches `if
    len(fresh) > 1 { info.Branched = true }` (trace.go:935-936) for that `f`.
  - **Lean `stepRound`**: it adds `s2` to `fresh` (Trace.lean:590) and records the violation
    (Trace.lean:593). The fold then ends, and line 598 sets `branched := true` when `fresh.length
    > 1`, violation or not.
  - **The divergence**: take an `f` whose successors are an out-state `o` (l+1) and then an
    intermediate `x` (l) that violates an invariant, with no branching earlier. Go returns
    `Result{Violation, ViolLine: l, Branched: 0}` (check.go:81-85). The Lean returns `branched :=
    l` (Check.lean:63-65).

  `tlcOK` agrees, because `ok = false` on both sides, but `uint.nat g.Branched' = r.branched` is
  false there.
- **Caller affected**: none needs `Branched` on a violation, but the spec as stated is false.
- **Repair (either)**:
  - Change `stepRound` to leave `info` unchanged at line 598 when `info.violation.isSome`. The Lean
    transcription mirrors the Go, and the Go is the program run.
  - Or weaken `resultRel` to `g.OK' = r.ok ∧ (g.Branched' = 0 ↔ r.branched = 0) ∧ …`, and relate
    `Branched` exactly only when `r.violation = none`.

  I recommend the first. Also check `Check.lean:63` in the same way: on a violation the Go never
  evaluates `len(next) > 1` (check.go:98).

## Second-tier

### S1. `lineFuel`'s sufficiency seems to need a reachability invariant of `etcdraft.tla` over arbitrary traces
- **Principle**: Sound/provable; know what it rests on.
- **Evidence**:
  - `stepLoop` returns silently when the fuel runs out (Trace.lean:603). The Go loop is unbounded
    (trace.go:906), so the spec's truth needs "BFS rounds ≤ lineFuel ts" (Σ initial log lengths +
    8, Trace.lean:569) for every reachable `ts`. The plan defers this to S6 (plan:301-302).
  - The L-preserving steps of a received message are UpdateTerm, ReturnToFollower, Conflict (one
    truncation) and NoConflict (an append). The bound holds only if every AppendEntries that
    matches the line (same source, term, prevIndex and entry count) carries the *same* entries.
  - With two matching messages that conflict, the chain is "append m1, truncate it entry by entry,
    append m2". It is longer than the *initial* log's length plus 8, e.g. 9 rounds from an empty
    log with 5-entry messages and one UpdateTerm.
  - Ruling that out needs "one source's AppendEntries in a term agree", an inductive invariant of
    the TLA+ actions from an arbitrary `TraceInit`. It is plausible, because a leader's log only
    grows within its term, but it is a real proof about the specification and not a function
    equivalence.
  - Empirically (instrumented scratch copy, 4 generated traces): at most 2 rounds per line, 15
    under the fuel.
- **Caller affected**: S6's proof of `CheckTrace.spec`.
- **Repair**: choose a fuel that a local counting argument proves, not an invariant. For example,
  the rounds are at most the number of distinct L-preserving states, which is at most 2 (term) ×
  2 (role) × (number of prefixes of the initial log and of `prefix_p(log) ++ m.entries` for the
  matching `m` in the bag). Or record the obligation explicitly as an invariant of the plan's S6,
  with its statement now, so that the Review can judge it.

### S2. `Event.Bounded` allows bootstrap `log` values where real Go's `make` panics
- **Principle**: Sound ("a post that says a call returns claims it returns on every input the
  premise admits: check Go's … memory"; precedent `porcupine-dag-check.md`, where `ClientIdsOk`
  bounds ids by gc's `maxAlloc` because "Perennial does not model the limit").
- **Evidence**: `log := make([]Entry, lb.ev.Log)` (trace.go:308). `Entry` is 80 bytes. In a
  scratch program, `make([]Entry, 1<<45)` gives `runtime error: makeslice: len out of range`
  (Go 1.27). `Event.Bounded` allows `log < 2^62` (Rep.lean:67-72), and `wp_slice_make2` only
  requires `0 ≤ len` (Perennial `Golang/Theory/Slice.lean:870-875`). So `NewTrace.spec` is
  provable but false of the real program for `log ∈ [~3.5·10^12, 2^62)`.
- **Caller affected**: `Main` is unaffected (raft's log sizes are tiny), but the spec's meaning
  is.
- **Repair**: bound `log` (and, for the overflow margin, every number) by a named constant well
  below `maxAlloc/80`. Example: `traceNumMax := 2^40` with `numOk n := 0 ≤ n < traceNumMax`, and
  `evs.length < traceNumMax`.
  - **Margin**: with `2^62` the reachable log length can reach `2^63-2`. `hi := len(log)+1`
    (trace.go:777) and `b+ev.Entries` (trace.go:563) then come within one of `int` overflow, or
    wrap. The Go wraps while the Lean does not, and they happen to agree, but the proof must show
    that. A `2^40` bound leaves ample room.
  - This is a reachable panic in this repository's own Go code, on absurd input. It belongs in
    `nonissues/` ("a precondition `Main` meets"), or as a note. I did not file it (read-only
    review).

### S3. `serverRO` relates `matchIndex` only on `st.server`, but the Go and Lean read other keys
- **Principle**: Complete (the representation must cover every value the code reads).
- **Evidence**:
  - `AdvanceCommitIndex` reads `v.MatchIndex[k]` for `k ∈ GetConfig(i)` (spec.go:366; Lean
    Spec.lean:237).
  - `bootstrappedConfig` of any server other than the first line's is not checked `⊆ Server`
    (trace.go:295 checks only `InitSrv`; trace.go:304 does not), so a configuration may name a
    node that never logs.
  - `serverRO`'s `⌜∀ j ∈ srv, …⌝` (Rep.lean:149) does not fix the Lean `matchIndex k` there.

  For `NewTrace`'s output, both sides are 0 everywhere, so with F1's repair the spec holds. But
  S6's loop invariant (a state representation reused for every reached state) needs every key.
- **Repair**: `⌜∀ k : w64, sint.Z ((mm !! k).getD (W64 0)) = v.matchIndex (uint.nat k)⌝`. It is
  canonical, free for `NewTrace` (empty map against `fun _ => 0`), and preserved by
  `BecomeLeader`/`HandleAppendEntriesResponse`.

### S4. `Main` needs a spec of `Result.TLCOK`, which does not exist
- **Principle**: Complete; layout (one spec per Go function `Main` calls across packages).
- **Evidence**: `main.go:25` calls `etcdraft.CheckTrace(tr, true).TLCOK()`. `Spec/.../etcdraft/`
  has only `NewTrace.lean` and `CheckTrace.lean`. The docstring of CheckTrace.lean:7-8 claims
  "`Result.TLCOK()` is `(checkTrace tr invariants).tlcOK`", which needs that spec. Without it,
  `Main` (package `tracecheck`) must unfold `resultRel` and the method body.
- **Repair**: add `Result.TLCOK.spec : ∀ r res, {{ ⌜resultRel r res⌝ }} r.TLCOK() {{ RET
  #(res.tlcOK) }}`. With it, `resultRel`'s body can be sealed.

### S5. The predicates are not shown to be persistent, and lack the laws callers need
- **Principle**: Law coverage; a client does not unfold.
- **Evidence**: Rep.lean's header says "every predicate here is persistent", but it declares no
  `Persistent` instances. Instance search does not unfold a `def`.
  - `NewTrace.spec` consumes `eventsRO sl evs` and does not return it. A caller can keep a copy
    only through `Persistent (eventsRO …)`.
  - S6 will need the same for `traceRO`, `stateRO`, `logRO`, `bagRO`, `msgRO` (shared across
    states).
  - `Main`/`ConvertEvents` (package `tracecheck`) must *produce* `eventsRO` from Go `Event` values.
    Without intro laws (`eventsRO_intro` from `sl ↦*□ gs` and per-element facts), it unfolds
    `eventRO`.
- **Repair**: add a `Persistent` instance per predicate, plus `eventsRO`/`eventRO` intro laws.
  Then seal the bodies (`@[no_expose]`) behind those laws (see T2).

## Third-tier

- **T1. Pure premises go in the precondition** (the user's critique, `porcupine-dag-check.md`).
  Both specs use Lean implications `(∀ e ∈ evs, e.Bounded) → evs.length < 2 ^ 62 → {{ … }}`
  (NewTrace.lean:36, CheckTrace.lean:85). Move them to `⌜…⌝` conjuncts of the pre. F1's repair
  removes `CheckTrace`'s anyway.
- **T2. Coupling/abstraction**: Rep.lean is `@[expose]`, and its bodies name the Go struct's
  fields, unexported ones included (`g.lines'`, `g.init'`, `g.bootstrap'`, `it.count'`).
  `NewTrace`'s and `CheckTrace`'s client, `Main`, sees all of it. Following "Package APIs", seal
  `traceRO`, `stateRO`, `resultRel` and the rest, and export only the laws (S4, S5). `eventsRO`
  stays the one predicate `Main` builds, through intro laws.
- **T3. Named constant**: `2 ^ 62` appears in `numOk` and in both specs. Name it
  (`traceNumMax`, `@[word_unfold]`) next to `Event.Bounded`.
- **T4. Strings**: `eventRO` needs each Go string to be `stringToGoString` of a Lean `String`,
  which is valid UTF-8 only. `Main`'s events are ASCII (ids from `FormatUint`, constant names and
  roles), so this is fine. Still, state in the docstring that `eventsRO` admits only UTF-8 strings,
  as a scope restriction, because `NewTrace` itself accepts any bytes.
- **T5. Exported mutable fields**: `Trace.Server` and `InitSrv` are exported (trace.go:157-158),
  so a Go client could rewrite them between `NewTrace` and `CheckTrace` and reach F1's panic. The
  persistent `traceRO` correctly rules that out for verified callers. Optionally mention it in
  `CheckTrace`'s doc.
- **T6. Base.lean**: `True` is fine for the Draft. When S6 strengthens it, the facts about
  `Invariants` (a mutable `var` of closures) and the three maps must be persistent read-only
  points-to plus the closures' specs. The specs' text does not change, as the header says.

## What is good

- **`NewTrace.spec`'s shape**: error exactly when `newTrace` refuses, else `traceRO` of
  `newTrace`'s trace. That is the strongest the code allows, and the error case is right.
  - I compared `parseLine`/`addedServer`/`bootstrapOf`/`bootstrappedConfig` against the Go check
    by check (trace.go:180-326 vs Trace.lean:148-245). They refuse on the same inputs: `parseID`'s
    byte-vs-char length and leading-zero tests agree on digit strings, and the overflow test `id >
    (max-d)/10` is `n ≥ 2^64`.
  - The order of the checks differs only between error cases.
  - `SetIds.mk` of `nids ++ added` against the Go's interleaved list gives the same sorted set.
- **`traceRO` is true of what `NewTrace` builds**, under F1's repair:
  - canonical `Value`s: `ConfRecord` with `Val = 0`, `Learners = nil`; `Kind`s built only at
    spec.go:352/393/397;
  - `Conf` arrays `[cfg, nil]`, an empty `MatchIndex` map, empty bags;
  - lines' `from/to = 0` without a message, and the `*Event` pointers into the events slice.
- **Persistence is justified**: every write after `NewTrace` is on a `clone()`/`mut()` copy
  (spec.go:72-86). Logs are extended with three-index slices (spec.go:343, 605), and bags and
  sets are rebuilt fresh (types.go:209, 453, 468, 487).
- **`resultRel` is enough for `TLCOK()`**: `g.OK' = r.ok` and `uint.nat g.Branched' = r.branched`
  give `OK && Branched == 0 ↔ tlcOK`. `checkTrace`'s EvalError, init-violation and success paths
  match `CheckTrace`'s, including `ErrLine = l` and `Branched` across a recovered panic.
  - The second of those holds because a frontier larger than one implies `Branched` was already
    set at the previous line. S6 needs that argument.
- **`Main`'s chain**: from `NewTrace`'s `.ok` branch, through `CheckTrace`, to `traceAccepts`, it
  closes once S4 exists.

## Ranking by need of revision

1. **`Spec/.../etcdraft/CheckTrace.lean`**: false as stated (F1, F2); needs a `TLCOK` sibling
   (S4) and the `lineFuel` obligation settled (S1).
2. **`Proof/.../etcdraft/Rep.lean`**: carry trace validity in `traceRO` (F1); `matchIndex` on all
   keys (S3); the bound and margin (S2); `Persistent` and intro laws, then sealing (S5, T2, T3).
3. **`Spec/.../etcdraft/NewTrace.lean`**: true in the model. It needs a `log` bound for real Go
   (S2), its premises in the precondition (T1), and to give the validity fact (F1).
4. **`Proof/.../etcdraft/Base.lean`**: fine for the Draft (T6).

**Bugs in Go code**: none upstream. In this repository's checker (`examples/raft/tracecheck/
etcdraft`), `NewTrace` panics (`makeslice: len out of range`) instead of erroring on a bootstrap
line with a huge `log` (S2). It is unreachable from `Main` and belongs in `nonissues/` or a note;
I did not record it (read-only).
