# Review round 2: trace-check, Draft of layer C (NewTrace / CheckTrace / Result.TLCOK specs, Rep, Base)

Reviewed at `5d2445f0a6` (round 1's repairs on top of `5cf76a35aa`). Scratch work is in
`/tmp/claude-1000/-workspace-etcd-grove/8e48033c-792a-435a-bae3-16d75b0d1a02/scratchpad/c2/`:
- `tc/`: a copy of the Go module, with `cmd/full` (prints every field `resultRel` relates) and
  `cmd/extrakey` (the witness for F1 below);
- `lean/`: the exported traces, with an `#eval` that prints every field `resultRel` relates;
- `traces/cfg7.ndjson`: the crafted trace.

`etc/lean-check.py -a` on the seven files (the three specs, `Rep`, `Base`, `Tla/Trace`,
`Tla/Check`): 0 errors. On the first multi-file call, `Rep.lean` hit a tool crash (`AttributeError:
'NoneType' object has no attribute 'split'`); checked alone, it gave 0 errors.

**Does anything first-tier remain? Yes, one finding (F1).** `traceRO` does not fix the domain of
the Go state's server map, and the Go and the Lean decide "is a server" differently (`map` lookup
vs. `server.contains`). I have a witness on which the Go panics while the Lean returns a result.
The repair is one conjunct. Round 1's F2 repair is correct and introduced no new divergence.
`lineFuel` (round 1 S1) stays open: second tier, but its justification is harder than round 1 or
the plan say (S1 below).

## Round 1's repairs: checked

- **F1 (`Trace.Valid` in `traceRO`)**: made, Rep.lean:233-242. It fixes the Lean-side facts the Go
  relied on: `init.server = server` and `bootstrap.length = lines.length`. It does not cover the
  Go-side shape of the initial state's map (new F1).
- **F2 (order at a violation)**: made correctly. The details are below.
- **S2 (`numBound = 2^40`)**: made, Rep.lean:70.
  - `sizeof(Entry)` is 80, so `80·2^40 ≈ 8.8·10^13 < maxAlloc = 2^48`, and Go's `makeslice` no
    longer panics with `len out of range`.
  - I checked this (scratch `c2/mk`, `ulimit -v 4000000`): `make([]Entry, 1<<40)` gives `fatal
    error: out of memory`, not a panic. That is outside the model, as for every allocation.
  - The docstring's "is a real allocation" overstates it slightly (T3).
- **S3 (`matchIndex` at every id)**: made, Rep.lean:157.
- **S4 (`Result.TLCOK.spec`)**: made.
  - It is `Result.TLCOK.impl` (Code `etcdraft.lean:292-304`: `OK && Branched == 0`) applied to
    the value receiver, as `Main` calls it (Code `tracecheck.lean:1301`, `MethodResolve Result.ty
    "TLCOK"`).
  - `uint.nat g.Branched' = r.branched` gives `Branched == 0 ↔ r.branched = 0`, so the post
    `RET #(res.tlcOK)` holds.
- **S5 (`Persistent` instances)**: made for all 17 predicates, Rep.lean:255-306, and they compile.
  The intro laws S5 also asked for (`eventsRO` from `sl ↦*□ gs` and per-element facts) are not
  there. The plan defers them, with sealing (T2), to S6.
- **T1 (pure premises in the pre)**: made, NewTrace.lean:84. `CheckTrace` has none left.

### F2 in detail: the Lean and the Go now agree at a violation
I compared trace.go:903-942 (`StepLine`) with Trace.lean:575-614 (`stepRound`/`stepLoop`), and
check.go:77-103 with Check.lean:46-72 (`checkLine`/`checkFrom`).

- **A state `f` whose successor violates**: the Go returns before `len(fresh) > 1`
  (trace.go:928-931). The Lean now leaves `info` alone when `info.violation` is set
  (Trace.lean:599-600).
- **Later `f`s and later successors**: both skip them (Trace.lean:580, :585).
- **`CheckTrace`**: per `ts`, the Go sets `r.Branched` from `info.Branched` and then returns at a
  violation (check.go:81-85). The Lean ORs the `branched` of every `ts` it processed, the violating
  one included (Check.lean:53), and applies it before the violation's return (Check.lean:65-67).
  The two agree. The line's own `len(next) > 1` is now applied only on the no-violation path
  (Check.lean:71; check.go:98), and the not-matched path (`next = []`) keeps the line's `info`
  branching, as the Go's `return r` does.
- **The recovered-panic path** (`Branched: r.Branched` at check.go:68 vs. the Lean's `r.branched`
  from before the line, Check.lean:61) still agrees, by round 1's argument: a frontier of more
  than one state means `Branched` was already set at the previous line, and line 1's frontier is
  `[init]`. S6 needs that as a lemma.

### Empirical agreement on all relevant fields
Go `cmd/full` and Lean `#eval` agree on `tlcOK`, `ok`, `branched`, `line`, `violation`,
`violLine`, `evalError` and `errLine` for all 15 traces I ran:
- `r2/lc`: `LeaderCompletenessInv` at line 110;
- `r3/mutd`: `MoreUpToDateCorrectInv` at line 249;
- `r2/p9`: not matched at line 63;
- `bad-Commit` 311, `bad-ReceiveAppendEntriesRequest` 302, `bad-nosend` 323, `full-2` 797,
  `full-3` 188: not matched at those lines;
- `bad-term`, `seed-1..5`, `full-1`: accepted.

On my crafted `cfg7` both give "not matched at line 23". None of these traces, nor
`full-4..20` and the `conc*` traces (Go only), has `Branched ≠ 0`. So the branching paths of the
F2 repair are checked by reading only. That part is uncertain empirically.

## First tier

### F1. `traceRO` leaves the Go state's server map free outside `st.server`, so `CheckTrace.spec` fails on a valid trace
- **Principle**: Sound. A triple must hold for every heap its precondition admits. Round 1's F1
  repair added a Lean-side fact (`Trace.Valid`); the Go side needs one too.
- **What `stateRO` says** (Rep.lean:161-166): it asks that each `i ∈ st.server` have a key in
  `g.S'`, and says nothing about other keys.
- **The Go and the Lean decide "is a server" differently**:
  - The Go uses map membership: `QuorumLogInv` does `if v, ok := s.S[j]; !ok || …` for `j ∈
    GetConfig(i)` (invariants.go:94-95). Also `Receive` (spec.go:671) and `stateMatches`
    (trace.go:448).
  - The Lean uses list membership: `!st.server.contains j` (Invariants.lean:70; Spec.lean:418;
    Trace.lean:310).
- **Reachable from a valid trace**: a configuration can name a node outside `Server`, because
  only `InitSrv ⊆ Server` is checked (trace.go:295; round 1's S3). For such a `j`, a heap
  satisfying `traceRO` may map `j` to anything, including `nil`.
- **Witness** (`c2/tc/cmd/extrakey`, `c2/traces/cfg7.ndjson`):
  - The trace is seed-1, with the bootstrap `newconf` of servers 2 and 3 set to `["1","2","3","7"]`
    and the bootstrap commits and logs zeroed so that the earlier invariants hold. `NewTrace`
    accepts it, and `Trace.Valid` holds of the Lean `newTrace`'s result: `Server {1,2,3}`, config of
    2 `{1,2,3,7}`, `|S| 3`.
  - The Go `CheckTrace(tr, true)` on that trace returns "not matched at line 23", and so does the
    Lean.
  - With `tr.init.S[7] = nil` added, `traceRO` still holds: `setRO`, the `[∗list]` over
    `{1,2,3}` and `Trace.Valid` are unchanged. The Go then gives:
    ```
    with S[7] = nil: panic escaped CheckTrace: runtime error: invalid memory address or nil pointer dereference
    ```
  - With a non-nil `S[7]`, the Go returns a different `QuorumLogInv` verdict from the Lean's. In
    the proof, the load of `v.Log` has no points-to, so it is stuck.
- **Caller affected**: none in practice. `NewTrace` builds `S` with exactly `Server`'s keys
  (trace.go:300-323), and `Main` passes only its output. The spec as stated, though, cannot be
  proved, and S6's loop invariant (`stateRO` of every reached state) needs the fact.
- **Repair**: in `stateRO`, fix the domain:
  `⌜∀ k : w64, (sm !! k).isSome ↔ uint.nat k ∈ st.server⌝`, or `dom sm = st.server.map (W64 ∘ …)`
  (with the ids `< 2^64`, which `Trace.Valid` gives).
  - `NewTrace` gives it (trace.go:300-322). It is preserved by `clone` (copies the map,
    spec.go:72-79) and by `mut` (writes only an existing `i`, spec.go:83-84).
  - Update `Trace.Valid`'s docstring (Rep.lean:230-232), which lists what "the Go's search relies
    on", to point at it.

## Second tier

### S1. `lineFuel`'s justification needs persistence reasoning, not only "a leader's log grows"; consider making it unnecessary
- **Principle**: Sound/provable: know what the spec's truth rests on (round 1 S1, still open,
  plan:293-296).
- **Why it matters**: `CheckTrace.spec` is true only if the Go's unbounded per-line loop
  (trace.go:906) never needs more rounds than `lineFuel ts`. `lineFuel` is the sum of the log
  lengths at the line's start state, plus 8 (Trace.lean:569). The plan's paragraph calls it "the
  initial logs' lengths" (plan:293), which is not what it is.
- **The invariant it needs**: every AppendEntries in `Messages` from one source in one term with
  the same `prevLogIndex` and entry count carries the same entry terms. Otherwise the truncate,
  append, truncate chain runs past the fuel (round 1's example).
- **Leader growth is not enough**: the spec's `Restart` (spec.go:219-235) puts a server back to
  its *durable* term (`v.CurrentTerm = v.Durable.CurrentTerm`) and truncates its log. A leader of
  `T` whose term was not persisted can, after `Restart`, time out into `T` again
  (spec.go:237-251), win again (the voters' `votedFor` is already it), and send different entries
  at the same indices.
- **What rules that out**: `Ready` persists before it sends (`persistState` then
  `SendPendingMessages`, spec.go:456-463), and `Restart` drops the server's pending messages
  (spec.go:227). So no message of the first leadership reached `Messages`.
- **Adversarial initial states**: `TraceInit`'s roles come from the events (`State: lb.role`,
  trace.go:315), and `CheckTrace.spec` quantifies over `invariants = false`. The invariant
  therefore cannot use election safety.
- **Where that leaves it**: the invariant is plausible, but it is a several-part invariant of
  `etcdraft.tla` over `Ready`/`Restart`/`persistState`/`BecomeLeader`.
- **Repair (suggested)**: make the bound part of both checkers. In `StepLine`, after `lineFuel(ts)`
  rounds with a non-empty frontier, call `evalError("StepLine: the line's steps exceed the fuel",
  …)`, and do the same in the Lean `stepLoop` at fuel 0 (`throw`). The agreement then holds by
  construction, and S6 has no reachability invariant to prove.
  - This only makes the checker stricter (it rejects where TLC might not), and `Main`'s statement
    (`Main` returns ⇒ `traceAccepts`) is unaffected.
  - On the 15 traces above, it changes nothing (round 1 measured at most 2 rounds per line).
  - The cost is a change to the S4-reviewed Go, which the plan must record. Otherwise S6 must
    state and prove the invariant above, Restart included.

## Third tier

- **T1. Stale plan text**: plan:280-281 still says "the events' numbers in `[0, 2^62)` … fewer
  than `2^62` events". It is `numBound = 2^40` now.
- **T2. "Only `NewTrace` produces it"** (Rep.lean:236-237, plan:287): nothing enforces this.
  `traceRO` is an exposed definition, buildable from points-to facts, and F1 is exactly that gap.
  Say "carries `Trace.Valid`, which `NewTrace` establishes", until sealing (deferred T2 of round 1)
  makes "only" true.
- **T3. `numBound`'s docstring** (Rep.lean:66-69): "small enough that the Go's `make` … is a real
  allocation". Say instead "within gc's `maxAlloc` (`80·2^40 < 2^48`: no `len out of range`
  panic); running out of memory is outside the model, as for every allocation". Round 1 T3's
  `@[word_unfold]`/naming is otherwise done.
- **T4. `Trace.Valid`'s consequences as laws**: S6 will need `tr.init.server = tr.server`,
  `tr.bootstrap.length = tr.lines.length`, ids `< 2^64`, each line's `nid ∈ server`, and the
  numbers' bounds. Stating them now as lemmas `Trace.Valid.*` next to the definition keeps callers
  from unfolding `newTrace`, and documents what the Go relies on. That list is what round 1's F1
  repair meant to capture.
- **T5. `Result.TLCOK.spec`'s `isPkgInit`**: the method reads no package state. The pre is
  harmless and consistent with the other two specs.
- **T6. The `Event.Bounded` margin through the search**: with `numBound = 2^40`, the reached
  states' numbers stay far below `2^63`. Terms come from lines or messages; logs grow by at most
  the line count plus the bootstrap log; counts and `reconfigCount` stay at most the line count.
  S6's loop invariant must still carry an explicit bound per reached state (e.g. every number
  `< (lines + 2)·numBound`). Record it with S1's obligations.
- **T7. The branching paths are untested**: no available trace branches. A small trace that
  branches and then violates (or two lines whose search branches) would let the F2 repair be
  checked by running it, as the violation paths were.

## What is good

- **Round 1's repairs**: each was made as recommended (where one was deferred, the plan records
  it), and the Lean transcription's change is minimal and exactly the Go's order at a violation.
- **Agreement holds where it was tested**: across 16 traces (two invariant witnesses, eight
  not-matched, six accepted), the two checkers agree on every field `resultRel` relates.
- **`Result.TLCOK.spec`**: minimal, with the right receiver form, and it closes `Main`'s chain:
  `NewTrace`'s `.ok tr` branch, `CheckTrace`'s `resultRel r (checkTrace tr true)`, then
  `TLCOK = (checkTrace tr true).tlcOK`, which is `traceAccepts evs` (Check.lean:86-89).
- **The representation**: `resultRel` covers exactly the Lean `Result`'s fields, and the
  invariant names agree string for string (Invariants.lean:105-112 vs. invariants.go:166-175).
  Every field of the Go structs (`Server`, `State`, `Durable`, `Config`, `Msg`, `Entry`, `Value`,
  `Bag`, `line`, `Trace`, `Event`, `EventMsg`) is related. The one gap is F1's map domain.
- **`NewTrace.spec`**: true as stated with the new bound. `traceRO`'s new `⌜Trace.Valid tr⌝`
  follows directly from its premises and `newTrace evs = .ok tr`.

## Ranking by need of revision

1. **`Proof/.../etcdraft/Rep.lean`**: `stateRO` needs the map-domain conjunct (F1). Also the
   docstrings of `Trace.Valid`, `traceRO` and `numBound` (T2, T3), and optionally the
   `Trace.Valid.*` laws (T4).
2. **`Spec/.../etcdraft/CheckTrace.lean`**: false as stated until F1 is repaired (through
   `traceRO`), and its truth still rests on S1. Choose the fuel-as-`EvalError` repair or record
   the invariant, Restart and persistence included.
3. **`Tla/Trace.lean` / `Tla/Check.lean`**: the F2 repair is correct. If S1's repair is taken,
   `stepLoop` throws at fuel 0.
4. **`Spec/.../etcdraft/NewTrace.lean`**: fine. Its post must also give F1's conjunct, which it
   can.
5. **`Spec/.../etcdraft/Result__TLCOK.lean`**: fine (T5 optional).
6. **`Proof/.../etcdraft/Base.lean`**: unchanged. `True` is fine for the Draft (round 1 T6).
- **`notes/trace-validation-plan.md`**: plan:280-281 is stale (T1), and plan:293 misdescribes
  `lineFuel` (S1).

**Bugs in Go code**: none.
- F1's panic needs a heap `NewTrace` never builds, so it is a gap in the spec, not a bug in the
  Go. It belongs in `notes/` with the repair, not in `issues/` or `nonissues/`.
- `make([]Entry, 2^40)` fails with an out-of-memory fatal error, which is outside the model.
