# Review round 4: trace-check, layer C after the Probe (strRel, Own, and the six new specs)

Reviewed at `efc3e34c0f`. What changed since round 3 (`78232aa5a1`), on the two layer-C directories:
- `Rep.lean`: `stringToGoString` is replaced by `strRel` (ASCII, a byte per character) in every string field, plus
  `asciiBytes_inj` and `strRel_inj`.
- New `Own.lean`: `serverOwn`, `stateOwn`, `stateOwnHole`, and the laws `serverOwn_persist`, `stateOwn_persist`
  and `stateOwnHole_close`.
- Six new specs with proofs: `Set.Has`, `State.GetConfig`, `Server.copy`, `State.clone`, `State.mut` and
  `State.Timeout`, plus the proof of `Result.TLCOK`.

The Go (`examples/raft/tracecheck/etcdraft/*.go`) and the Lean transcription (`Tla/`) have not changed.

Checks run: `etc/lean-check.py -q` on `Own.lean`, `State__mut.lean` (spec and proof) and `State__Timeout.lean`
(proof). All have 0 errors. The worktree is still clean.

**Does anything first-tier remain? Yes, one: `State.mut`'s spec cannot be applied by two of its callers (F1).** The
`strRel` change itself is sound, and `NewTrace`/`CheckTrace` still say what they should (see "strRel" below). Every
ASCII premise is dischargeable by `Main`'s chain, with one forward obligation on layer B (S3).

## Round 3's findings at HEAD

| Round 3 | Status at `efc3e34c0f` |
|---|---|
| S1 (counting fuel, option (c) for Q7) | Out of scope here (Q7). |
| T1 (`traceRO` "only NewTrace produces it") | **Addressed**: Rep.lean, `traceRO`'s docstring now says "carries `Trace.Valid tr`, which `NewTrace` establishes". |
| T2 (`Trace.Valid`'s docstring and the map domain) | **Addressed**: the docstring now points at `stateRO` (round 2, F1). |
| T3 (facts S6's loop invariant must carry) | Open. It gains two items (S1 and S2 below): `st.server.Nodup`, and terms below `numBound`. |
| T4 (branching untested), T5 (`lineFuel` docstring) | Open, not in scope. |

## First tier

### F1. `State.mut.spec` cannot be applied twice to the same server, and two Go callers do exactly that
- **Principle**: Complete (sufficient for every caller); No unneeded premise.
- **Evidence**:
  - The spec (`Spec/.../State__mut.lean`) takes `uint.nat i ∉ M`: the server must not be a copy of this clone yet.
  - Two actions call `mut(i)` twice on one clone:
    - **`ApplySimpleConfChange`** (spec.go:446-451): `t.applyConfigUpdate(i, k)` (which does `s.mut(i)`,
      spec.go:184), then `t.mut(i).PendingConfChangeIndex = 0` (spec.go:450) when `v.State == Leader &&
      v.PendingConfChangeIndex >= k`.
    - **`reconfigure`** (spec.go:390-399), which `AddNewServer`, `AddLearner` and `DeleteServer` call:
      `t.replicate(...)` (which does `s.mut(i)`, spec.go:341), then `w := t.mut(i)` (spec.go:394) when no change is
      pending.
  - After the first `mut` and `stateOwnHole_close`, the clone is `stateOwn … (i :: M)`. So the second call's
    premise `i ∉ (i :: M)` is false.
  - The proof shows that the premise is not needed (`Proof/.../State__mut.lean`). `HiM` is used only to choose the
    `serverRO` branch of `stateOwn`'s `if i ∈ M` (`simp only [HiM, ite_false]`) before `Server.copy`. In the
    `i ∈ M` case the server is `serverOwn q0 …`; `serverOwn_persist` (Own.lean) turns it into `serverRO q0 …`, and
    `copy` applies as before. The old copy becomes unreachable once `s.S[i] = c`, so freezing it costs nothing.
  - The Go itself is fine: copying an already-copied server again is merely wasteful.
- **Callers affected**: the specs of `ApplySimpleConfChange`, `reconfigure`, `AddNewServer`, `AddLearner` and
  `DeleteServer` (S6), and through them `CheckTrace`'s proof. The Probe's plan entry ("Spec problems found ... none
  in a triple's shape", `notes/trace-validation-plan.md`, "Probe set") should record this one.
- **Restatement**:

  ```
  {{ isPkgInit … ∗ stateOwn p st M ∗ ⌜uint.nat i ∈ st.server⌝ }}  s.mut(i)
  {{ (c : Loc), RET #c; stateOwnHole p st M (uint.nat i) c ∗ serverOwn c (st.s (uint.nat i)) }}
  ```

  The proof gains an `if` on `uint.nat i ∈ M` that calls `serverOwn_persist` first. `stateOwnHole_close`
  already accepts any `M` and returns `i :: M`, which is harmless with a duplicate.
  - The `st.server.Nodup` conjunct is not needed by `mut` either. With duplicates, the other occurrences of `i`
    become `emp` and are dropped; only the closing law needs `Nodup`. See S1 for removing it everywhere.
  - Update the docstring ("of a clone whose server `i` is not yet copied") to match.

## Second tier

### S1. `st.server.Nodup` should live in `stateRO`/`stateOwn`, not in every action's premise
- **Principle**: a fact that holds of every reachable state is one law of the vocabulary, not a conjunct of each
  operation's pre ("No constant or conjunct whose reason you do not know"; Size, Caller burden).
- **Evidence**:
  - `Timeout.spec` and `mut.spec` both take `st.server.Nodup`. Every action that calls `mut` will take it too,
    which is about twenty of them (spec.go:219-702).
  - `State.Server` is never written: `clone` copies the struct (spec.go:72-79); no action assigns `Server`.
  - It is built only by `NewTrace` as `NewSet(server...)` (trace.go:239), the Lean `SetIds.mk`, which is sorted
    and duplicate-free by `insertSorted` (Types.lean:57-62).
  - Nothing in the predicates gives it today. `stateRO`'s `[∗list] i ∈ st.server` is persistent, so duplicates are
    not excluded. `Trace.Valid` gives it only through an unproved `SetIds.mk` lemma.
- **Restatement**:
  - Add `⌜st.server.Nodup⌝` to `stateRO`, `stateOwn` and `stateOwnHole`. It is a single extra conjunct, kept by
    `clone` (same `st.server`), `mut`, `stateOwn_persist` and `stateOwnHole_close`.
  - Drop the premise from `mut`, `Timeout` and `stateOwnHole_close` (the law reads it from `stateOwnHole`).
  - `NewTrace`'s proof discharges it once, with `SetIds.mk_nodup`.
  - Alternatively, put it in `setRO` with sortedness, since the Go `Set` claims both (types.go). But `setRO` is
    also used for sets the code builds by hand, so `stateRO` is the smaller change.

### S2. `Timeout`'s `numOk currentTerm` is stronger than the code needs, and stronger than the invariant the plan records
- **Principle**: No unneeded premise; Complete (the caller is S6's search loop, through `timeoutIfLogged`,
  trace.go:615-628).
- **Evidence**:
  - The Go's `v.CurrentTerm + 1` (spec.go:245) wraps; it does not panic. The premise exists only so that
    `sint.Z (w + 1) = n + 1` holds (`timeout_term`, Proof/.../State__Timeout.lean:30).
  - That needs only `currentTerm < 2^63 - 1`. `numOk` asks for `0 ≤ currentTerm < 2^40`.
  - The plan says S6's invariant is "every number below `(lines + 2) · numBound`" (plan "Probe set", item 3;
    round 3, T3). That does **not** give `numOk`.
  - A finer invariant does hold, I believe: every server's term, durable term and message term is below
    `numBound`. My reasoning:
    - Initial terms are `lb.ev.State.Term`, which is `Bounded`.
    - A `Timeout` successor is kept only if its term equals the line's event term (trace.go:623-625).
    - `UpdateTerm` copies a message's term; messages carry their sender's term.
    - `Restart` restores a durable term.
  - **Uncertain**: I did not check every action for this; it is S6's to prove.
- **Restatement**: take `⌜(st.s (uint.nat i)).currentTerm < 2 ^ 63 - 1⌝` (a library-local overflow bound, as
  PRINCIPLES allows a literal), or a named constant for S6's bound. Either way, record in T3 which per-field bound
  S6 must carry. Otherwise one invariant per action's premise accretes.

### S3. Layer B's obligation from the ASCII premise: state `MessageType.String`'s value as bytes, not `stringToGoString`
- **Principle**: Complete (`Main` must supply `eventsRO`, now ASCII); every premise has a source the client sees.
- **Evidence**: every string of a raft event is ASCII, and almost all of them come from literals or digits:
  - `Name`: `stateMachineEventType.String()`, a table of literals (`.lake/goose/raft/state_trace.go:53-74`).
  - `Role`: `stmap` literals (raft.go:114-123).
  - Ids, votes and configuration members: `strconv.FormatUint` (state_trace.go:129, 150-156, 173, 194), whose spec
    gives `fmtUint`, a byte list of digits (`Proof/strconv/FormatUintDefs.lean:67`).
  - `Action`: the literal constants at state_trace.go:77-80.
  - **The exception is the message type**, `m.GetType().String()` (state_trace.go:148). Its spec
    (`Spec/go_etcd_io/raft/v3/raftpb/MessageType__String.lean`) is `fmt.stringMethodSpec`: "returns some
    string".
  - Layer B already needs a stronger (trusted) statement of it, because `NewTrace` looks the type up in
    `RaftMsgType` (trace.go:196) and the matching compares it.
  - If that statement is written with `stringToGoString "MsgApp"`, discharging `strRel` needs exactly the
    `String.toUTF8` evaluation lemma that the decision ("Layer C's strings: `strRel`, ASCII") says is missing.
- **Restatement**: when layer B strengthens `MessageType.String`, state its result as a `go!"…"` literal (Goose's
  `go!` already gives byte lists, `Perennial/Std/ByteString.lean:27`), or directly as `strRel s (msgTypeName t)`.
  Also cover protobuf's unknown-value case: its decimal form is ASCII too. Note this in the plan's layer-B
  obligations next to `Event.Bounded`.

### S4. Missing laws for string comparison and for reading a server being written
- **Principle**: Law coverage; a client does not re-prove the owning module's facts.
- **Evidence**:
  - **String comparison.** `State__Timeout.lean:139-145` proves inline, twice, the bridge
    `strRel g a → strRel go!"Lit" lit → (g = go!"Lit" ↔ a = lit)`, and `:79` proves a literal's `strRel` by
    `unfold strRel …; decide`. Every action compares roles (`v.State == Leader`, ...) or subtypes
    (`m.Subtype == "heartbeat"`, spec.go:569, 576), and `NewTrace` compares names and actions. That is dozens of
    copies.
  - **Reading a server being written.** `persistState` (spec.go:209-212) calls `durableOf(v)` on the `mut` copy
    and then writes it. If `durableOf`'s spec takes `serverRO`, the caller cannot persist the copy without losing
    the write.
- **Restatement**:
  - Export from Rep.lean `strRel_eq_iff (ha : strRel g a) (hb : strRel g' b) : g = g' ↔ a = b`, plus `strRel` facts
    for the constants the code compares with (`follower`, `candidate`, `leader`, `"heartbeat"`, `"snapshot"`,
    `"app"`, the event names), or a `simp`/`decide` lemma `strRel_lit`.
  - Give `durableOf` (and any other helper that reads an owned server) a spec over the fields read, or over
    `serverOwn` returned unchanged.

## Third tier

- **T1. `NewTrace`'s header** (Spec/.../NewTrace.lean:4-10) lists the premises (`Event.Bounded`, read-only) but not
  the new one that `eventsRO` carries: the events' strings are ASCII. Add "whose strings are ASCII (`strRel`)".
  Also say that this is a scope restriction of the representation, not something the Go needs: the Go accepts or
  rejects non-ASCII input as it does any other, and `cmd/checktrace` reads arbitrary NDJSON (decision recorded in
  `notes/decisions.md`).
- **T2. `strRel`'s docstring** says `stringToGoString` "a proof cannot evaluate on a constant". That is true of
  `decide` (and so `native_decide` is excluded) but needs qualifying: a lemma would evaluate it, and the decision
  keeps that option open. **Uncertain**: I did not try `simp`/`decide` on `stringToGoString "StateFollower"`.
- **T3. `Own.lean`'s header** says a state is read-only "except while the action building it holds it". F1 shows
  that this window can include two copies of one server. Mention that `mut` may be called again on a server
  already copied.
- **T4. The plan's Probe entry** says "none in a triple's shape". Amend it after F1.

## strRel: why NewTrace and CheckTrace still say what they should

- **The Lean side's strings are all ASCII**. A grep for non-ASCII inside string literals in `Tla/*.lean` finds
  none. This covers:
  - the roles (`Types.lean:47-49`);
  - the three `EvalError` `what`s (Spec.lean:38, 276; Invariants.lean:94);
  - the invariant names.

  So `resultRel`'s `strRel g.Violation' …` and `strRel g.EvalError' …` hold of the Go's literals, which Goose
  translates as byte lists (`go!`), by `decide`. `strRel [] ""` covers the empty case.
- **The Go side's strings are all ASCII.** The Go strings compared or stored are:
  - literals: roles, types.go:42-46; subtypes, spec.go:301/308/313/318/529; names and actions, trace.go:222,
    242-243;
  - and strings copied from events: `ln.role`, and `Server.State := lb.role` (trace.go:314).

  So every `serverRO`/`lineRO` `strRel` conjunct `NewTrace` must give follows from `eventsRO`'s.
- **Byte equality matches Lean string equality.** `strRel_inj` together with the definition gives Go byte
  equality iff Lean string equality, which is what the Go's `==` and `RaftMsgType[...]` lookups need. It also makes
  round 3's `parseID` argument (bytes vs. characters) immediate.

## What is good

- **The copy-on-write discipline is captured precisely and minimally.**
  - `serverOwn` is `serverRO` with only the struct and the `MatchIndex` map owned: exactly what an action writes.
    `Log`, sets and bags are always replaced, never written in place. I checked `replicate`'s and
    `NoConflictAppendEntriesRequest`'s full-slice `append` (spec.go:343, 605) and `Bag.add`'s fresh slice
    (types.go:347).
  - `stateOwn` keeps unchanged servers shared (`serverRO`) and lists the copies in `M`.
  - The two persistence laws freeze an action's result as the `stateRO` the next line reads.
- **Each new spec matches its Go function and is the strongest the code allows**, except `mut` (F1) and `Timeout`'s
  bound (S2):
  - `Set.Has` returns `decide (… ∈ s)` and needs nothing.
  - `GetConfig` takes `i ∈ st.server`, which the nil dereference at spec.go:174 needs.
  - `copy` and `clone` take a read-only argument and give an owned result.
  - `Timeout`'s post is the transcription's `timeout` as an option. Its guard agrees with spec.go:239-240, and
    `VotedFor = i` agrees with `votedFor := i` by `uint.nat`.
- **`stateOwnHole_close` is the right shape**: one law from "copy written" to "clone with the update". It is stated
  over `State.upd`, the transcription's own helper.
- **`strRel` is a good replacement**: decidable on constants, injective, and it removes a dependency on lemmas that
  Lean core lacks. The decision is recorded with its cost.

## Ranking by need of revision

1. **`Spec/.../State__mut.lean`** (and its proof): F1. Drop `i ∉ M` (and `Nodup`, S1); persist the old copy in the
   `i ∈ M` case.
2. **`Proof/.../Own.lean` and `Rep.lean`**: S1 (`Nodup` in the state predicates) and S4 (the `strRel` bridge
   laws). T3.
3. **`Spec/.../State__Timeout.lean`**: S2 (the term bound), S1 (drop `Nodup`).
4. **`Spec/.../NewTrace.lean`**: T1, the header. Plus S3, which is layer B's obligation recorded against it.
5. **`Set__Has`, `State__GetConfig`, `Server__copy`, `State__clone`, `Result__TLCOK`, `CheckTrace`**: correct,
   nothing to change (`CheckTrace` still modulo Q7).

**Bugs in the Go code**: none found. The double `mut` (F1) is correct Go, only a wasted copy. No `issues/` or
`nonissues/` entry is warranted.
