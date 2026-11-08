# Review round 5: trace-check, layer C after round 4's repairs (mut, Nodup, Timeout's bound, strRel_eq_iff)

Reviewed at `28a64a23c5`. What changed since round 4 (`efc3e34c0f`), on the two layer-C directories:
- `Spec/.../State__mut.lean`: the premises `uint.nat i ∉ M` and `st.server.Nodup` are gone. The proof
  (`Proof/.../State__mut.lean:55-61`) freezes server `i` with `serverOwn_persist` when `i ∈ M`, then copies it.
- `Rep.lean`: `⌜st.server.Nodup⌝` is a conjunct of `stateRO` (:250). New: `insertSorted_mem`,
  `insertSorted_sorted`, `SetIds.mk_sorted`, `SetIds.mk_nodup` (:77-124), and `strRel_eq_iff` (:154-156).
- `Own.lean`: the same conjunct in `stateOwn` (:77) and `stateOwnHole` (:114). `stateOwnHole_close` no longer takes
  `hnd`; it reads it from the hole.
- `State__Timeout.lean` (spec): `numOk currentTerm` is replaced by `currentTerm < 2 ^ 63 - 1`, and `Nodup` is
  dropped. The proof uses `strRel_eq_iff`.
- `State__clone`, `State__GetConfig` (proofs): the extra `icases` pattern only.
- `notes/trace-validation-plan.md`: the Probe entry's items 1 and 3, and a paragraph on round 4.

The Go (`examples/raft/tracecheck/etcdraft/*.go`) and the transcription (`Tla/`) have not changed.

Checks run: `etc/lean-check.py -q -a` on `Rep.lean`, `Own.lean`, both `State__mut.lean`, both `State__Timeout.lean`,
`State__clone.lean` and `State__GetConfig.lean`. All have 0 errors. (One run of the proof of `mut` ended in a
`lean-check` `AttributeError: 'NoneType' object has no attribute 'split'`. That is a script bug, not a Lean error;
the rerun was clean.) The worktree is clean apart from this file.

**Does anything first-tier remain? No.** Every round-4 repair is correct, and none adds a defect to a triple.
- `NewTrace`'s spec can still be proved with the new conjunct: one line, `SetIds.mk_nodup`.
- Every state an action builds keeps the conjunct.

One second-tier finding is new. The plan's argument for discharging `Timeout`'s new premise rests on a line bound
that nothing provides (S1).

## Round 4's findings at HEAD

| Round 4 | Status at `28a64a23c5` |
|---|---|
| F1 (`mut` twice on one server) | **Addressed.** The spec takes only `uint.nat i ∈ st.server`; the proof freezes an existing copy. See "mut" below. |
| S1 (`Nodup` into the predicates) | **Addressed.** It is in `stateRO`, `stateOwn` and `stateOwnHole`, and dropped from `mut`, `Timeout` and `stateOwnHole_close`. `SetIds.mk_nodup` is proved. See "Nodup" below. |
| S2 (`Timeout`'s term bound) | **Addressed in the spec**: `currentTerm < 2^63 - 1` is exactly what `timeout_term` needs. **Not addressed in the plan**: the bound S6 must carry is recorded with a wrong justification (S1 below). |
| S3 (layer B: `MessageType.String` as a `go!` literal) | Deferred to layer B; now recorded in the plan. Fine. |
| S4 (string-comparison law; `durableOf` on an owned server) | **First half addressed** (`strRel_eq_iff`). Constant facts are still `by unfold strRel …; decide` at each use (T2 below). The second half is deferred to S6 and recorded in the plan. |
| T1 (`NewTrace`'s header: ASCII) | **Open**: NewTrace.lean:4-10 still does not mention the ASCII restriction `eventsRO` carries. |
| T2 (`strRel`'s docstring, "cannot evaluate") | **Open**, unchanged (Rep.lean:126-128). |
| T3 (`Own.lean`'s header: double `mut`) | **Open**: Own.lean:4-12 still says read-only "except while the action building it holds it". The double-`mut` case is now explained in `mut`'s docstring, which is enough; the header remains a nicety. |
| T4 (plan: "none in a triple's shape") | **Partly addressed.** The new round-4 paragraph records F1, but the Probe entry (plan:298-299) still says "Spec problems found, all in layer C's representation, none in a triple's shape". F1 was in a triple's shape. |

## First tier

None.

## Second tier

### S1. The plan says `Timeout`'s term bound follows from the coarse invariant "for fewer than `2^22` lines", but nothing bounds the lines below `2^40`
- **Principle**: Complete. The caller, S6's search loop through `timeoutIfLogged` (trace.go:615-628), must be able to
  establish the premise from what `CheckTrace`'s pre gives. Each premise needs a source the client sees.
- **Evidence**:
  - The plan (notes/trace-validation-plan.md:311-313) says: "S6's loop invariant must give it at each action:
    every number below `(lines + 2) · numBound` (round 3's T3) does, `numBound = 2^40`, for fewer than `2^22`
    lines."
  - The arithmetic is right: `(2^22 + 2) · 2^40 < 2^63 - 1`.
  - But no spec gives `lines < 2^22`:
    - `CheckTrace.spec` takes only `traceRO t tr`.
    - `traceRO` carries `Trace.Valid tr` (Rep.lean:321-322), which says `evs.length < numBound = 2^40`.
    - `NewTrace.spec` takes the same bound.
  - With up to `2^40` lines, `(lines + 2) · numBound` is about `2^80`, so the coarse invariant does not imply
    `currentTerm < 2^63 - 1`. As recorded, S6 would be stuck on this premise for long traces, or `Main` would have
    to gain a `2^22` premise that nothing in the Go needs.
  - The finer invariant suggested in round 4 (S2) does give it. **I have now checked it against every write of a
    term in the Go.** Every term is some state's `currentTerm`, and the only increment is `Timeout`'s, whose
    successor is kept only if its term equals the line's `ln.ev.State.Term`:
    - the initial `CurrentTerm: lb.ev.State.Term` (trace.go:313), bounded by `Event.Bounded`;
    - the only increment, `w.CurrentTerm = v.CurrentTerm + 1` (spec.go:245), with the check in `timeoutIfLogged`
      (trace.go:623-625);
    - `v.CurrentTerm = v.Durable.CurrentTerm` (spec.go:228); a durable term is `durableOf(v)` (spec.go:150) of an
      earlier server;
    - `becomeFollowerOfTerm(i, term)` (spec.go:469), with `term` either `v.CurrentTerm` (StepDownToFollower) or
      `m.Term` (UpdateTerm, spec.go:653);
    - messages' `Term: v.CurrentTerm` (spec.go:260, 263, 289, 301, 502, 529, 579); entries' `Term: v.CurrentTerm`
      (spec.go:342).

    So "every server's `currentTerm` and `durable.currentTerm`, and every message's `term`, is `numOk`" holds of
    every state the search keeps. **Uncertain**: the `Timeout` successor that the check discards is never a kept
    state, which is all the invariant needs, but S6's proof must take the check's conjunct before re-establishing
    it.
- **Caller affected**: S6's loop invariant, and so `CheckTrace`'s proof.
- **Restatement**: in the plan's Probe entry item 3, and in round 3's T3 list (plan:368-370), replace "every number
  below `(lines + 2) · numBound` does, ..., for fewer than `2^22` lines" with:

  > S6's invariant carries `numOk` of every server's `currentTerm` and `durable.currentTerm` and of every message's
  > `term` (initial terms are an event's; the only increment, `Timeout`'s, is kept only when it equals the line's
  > event term, trace.go:623-625; all other terms are copied). That gives `currentTerm < 2^63 - 1`.

  The coarse bound stays for the lengths and indices it was meant for. `Timeout`'s spec needs no change.

## Third tier

- **T1. `Timeout`'s premise is required even where the action is disabled.** The Go adds 1 only past the guard
  (spec.go:239-245), so `enabled → currentTerm < 2^63 - 1` would be the exact need.
  - This is not worth changing: S1's invariant gives the bound at every server, and the conditional form would cost
    every caller a case split.
  - Recorded only so that a later round does not raise it as an unneeded premise.
- **T2. The constant facts of `strRel` are still proved inline** (`by unfold strRel follower; decide`,
  State__Timeout.lean:140, 142). Each action that compares a role or subtype will repeat this.
  - A lemma `strRel_lit (s : String) (h : ∀ c ∈ s.toList, c.toNat < 128 := by decide) : strRel (s.toList.map …) s`,
    or `strRel go!"…" …` facts for the dozen constants (`follower`, `candidate`, `leader`, the subtypes, the event
    names), would make each use one term.
  - **Uncertain**: I did not test whether `decide` stays cheap on the longer names (`"ReceiveAppendEntriesResponse"`,
    28 characters).
- **T3. The plan's Probe entry** still says "none in a triple's shape" (plan:298-299). Change it to "one in a
  triple's shape, found by round 4 (`mut`'s `i ∉ M`)", or point to the round-4 paragraph.
- **T4. Round 4's T1 and T2** (the `NewTrace` header's ASCII restriction, and `strRel`'s "cannot evaluate") are still
  open. See the table.

## Evidence for the repairs

### mut (round 4, F1)
- **The spec is now the strongest the code allows.** `mut` (spec.go:82-86) needs only `s.S[i]` present (a nil
  `copy` receiver would panic), and `uint.nat i ∈ st.server` with `stateOwn`'s key conjunct gives that.
- **The post is right whether or not `i ∈ M`:**
  - `stateOwnHole p st M (uint.nat i) c` replaces server `i`'s resource with `emp`, whatever `M` says of it.
  - `stateOwnHole_close` then gives `i :: M`. A duplicate `i` in `M` changes nothing, since only membership is
    read (Own.lean:79).
  - The frozen old copy is the right thing to drop: after `s.S[i] = c` (spec.go:84) nothing in the state reaches
    it.
- **No caller holds a first copy across a second `mut` of the same server.** I checked every `mut` call
  (spec.go:184, 191, 210, 221, 243, 328, 341, 394, 450, 467, 500, 513, 541, 591, 603, 640). In the two
  double-`mut` sites, the first copy is local to a helper that returns before the second `mut`:
  - `reconfigure`: `replicate`'s `v` (spec.go:341-343), then `w := t.mut(i)` (spec.go:394);
  - `ApplySimpleConfChange`: `applyConfigUpdate`'s `v` (spec.go:184-186), then `t.mut(i)` (spec.go:450).

  `send`, `reply` and `discard` (spec.go:157-166) never `mut`. If some code did write a stale `w` after a nested
  `mut` (a lost write in Go), the spec would refuse it: the caller must give up `serverOwn` to close the hole
  before it can call `mut` again. That is the right behavior.
- `strict_test.go:21`'s `s.mut(1).State = Leader` on a `clone` of `Init().S` is within the spec too (it is a
  test, not a caller in the proof).

### Nodup (round 4, S1)
- **`NewTrace` can establish it.** The state `newTrace` builds has `server := SetIds.mk (lines.map Line.nid ++ …)`
  (Trace.lean:206, 237), so `SetIds.mk_nodup` gives the conjunct directly. The proof is by sortedness:
  `insertSorted_sorted` and `SetIds.mk_sorted` (Rep.lean:92-121) are proved without `sorry`, and `Pairwise (· < ·)`
  implies `Nodup`.
  - It is a fact of the Lean list, so it does not depend on the Go `NewSet` (trace.go:237). `setRO`'s
    `xs.map uint.nat = st.server` then gives the Go words' distinctness as well, since `uint.nat` is injective.
- **Every built state keeps it.**
  - No action writes `State.Server`. A grep of `spec.go`/`trace.go` finds only reads.
  - No Lean action changes `server`. `State.upd` (Spec.lean:98-99) changes only `s`. The only other constructors
    are `init` (Spec.lean:105-109), which `checkTrace` does not use (it starts from `t.initState`, Check.lean:76),
    and `newTrace`'s.
  - In the predicates: `clone` copies `Hnd` (State__clone.lean:106-107); `mut` re-proves it on the split list
    (`hnd'`); `stateOwnHole_close` and `stateOwn_persist` pass it through.
- **The cost is one `%Hnd` in each `icases` of `stateRO`.** Those are the four proof edits of this commit. It is a
  persistent pure fact, so it costs no client anything to keep.

### Timeout's bound and strRel_eq_iff (round 4, S2, S4)
- `timeout_term` (State__Timeout.lean:30-33) needs `sint.Z w + 1 ≤ 2^63 - 1`, so `n < 2^63 - 1` is exact. Since
  `sint.Z` of a word is below `2^63`, the premise excludes only `n = 2^63 - 1`, the one value at which the Go's
  wrap would make the Go and `timeout` disagree. So the premise is needed for the post's truth, not for safety
  (the Go does not panic). Its caller's source is S1.
- `strRel_eq_iff` is correct and the right shape: Go `==` on two related strings is Lean `=`. Both directions are
  proved from `strRel_inj` and the definition. It replaces the two inline bridges in `Timeout`'s proof
  (State__Timeout.lean:139-142).

## What is good

- **The repairs are minimal and match round 4's restatements exactly.** No new predicate, no new spec, and the
  hole/close laws keep their shape.
- **Duplicate-freedom is now an invariant of the vocabulary, not of each action.** About twenty future action specs
  will not carry it.
- **`mut`'s docstring says why a copied server is copied again** and names the two Go sites. A reader of the spec
  learns what it admits without reading the proof.
- **The sortedness lemmas are general** (`SetIds.mk_sorted`, not only `_nodup`). `Set.Union`/`Add`/`Minus` specs in
  S6 will need sortedness of their results too, and can reuse them.

## Ranking by need of revision

1. **`notes/trace-validation-plan.md`** (not a spec file, but where S6's obligations live): S1 (the term invariant
   and its justification), T3.
2. **`Spec/.../NewTrace.lean`**: the header (round 4's T1, still open).
3. **`Proof/.../Rep.lean`**: T2 (a `strRel` constant lemma), round 4's T2 (the docstring).
4. **`Proof/.../Own.lean`**: round 4's T3 (the header), optional.
5. **`State__mut`, `State__Timeout`, `State__clone`, `State__GetConfig`, `Set__Has`, `Server__copy`,
   `Result__TLCOK`, `CheckTrace`**: correct, nothing to change (`CheckTrace` still modulo Q7).

**Bugs in the Go code**: none found. No `issues/` or `nonissues/` entry is warranted. The `lean-check` crash noted
above is a tooling glitch in this repository's script, not in the verified code.
