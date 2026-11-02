# Porcupine PR #46 (the DAG search): plan

Verifying the linearizability checker of anishathalye/porcupine#46 (head `29a6b8e6c` of
`practical-systems-iitd/porcupine`), vendored in `third_party/porcupine-dag/`, translated into the
part `PorcupineDag/` (project `porcupine-dag` of `etc/goose.py`). The target: the spec proved for
v1.3.1 (`notes/decisions.md`, "Porcupine: sound and complete"), or the closest true one.

Process (the task's): a spec plan, reviewed, then frozen; an invariant plan, checked
exhaustively, then frozen; then the proofs. Amendments after a freeze are dated, below the plan
they amend, with the reason.

## Early findings (2026-11-02, before the spec plan)

A random comparison of the PR with v1.3.1 (register model, up to 7 operations, up to 3 clients,
200000 histories per mode; the harness was a scratch Go module with both copies side by side):

- every operation's call at most its return, each client's operations sequential in the order
  listed (operation `i` before `j` of one client: `ret_i < call_j`): **no disagreement** in
  200000 (64049 linearizable). In particular the suspected skip after a pop (`liftFrom =
  unlifted_id - 1` while `unlift`/`addToFrontier` reorder the frontier) does not show: the
  frontier is a strictly sorted list of the candidates (sorted by call time, then client id,
  descending; candidates are never related in real time, so the comparator is a strict total
  order on them), hence a function of the set of linearized operations, so after `unlift` it is
  the list the popped operation was lifted from, and `frontierIdx - 1` resumes exactly after it.
  The invariant plan makes this an invariant (`CandList`, uniqueness of a sorted list).
- arbitrary intervals and client ids: both directions of disagreement. The PR **accepts
  non-linearizable histories** when a client's operations are listed out of real-time order
  (unsound), and rejects linearizable ones when a client's operations overlap (the known
  incompleteness). `issues/porcupine-dag-client-order.md`, both with reproductions.
- a negative `ClientId` panics (index out of range in `makeEntries`); a huge one overflows
  `maxClientId + 1` or `n * numClients`. `issues/porcupine-dag-clientid-range.md`.
- calls after returns (`Call > Return`): disagreements too, but v1.3.1's spec already excludes
  them (`HistOk`).

## Spec plan (candidate 1, 2026-11-02)

### What changes from v1.3.1's specs

- One new premise on the history, `ClientsOk ops`, on every spec whose history is a slice of
  `Operation`s (the three public ones, `checkOperations`, `makeEntries`), and its counterpart on
  the chains (`ChainsOk`) where the history is already split by client.
- `checkSingle`, `checkParallel` take the partition as an `operationHistory` (one slice of
  `clientOperation`s per client), the PR's representation, instead of v1.3.1's sorted entries.
- The package fact is no longer `True`: it holds `Linearizability`, the consistency value the
  public entry points read (its two oracles and `RVal`), with the specs of its closures.
- Every post is v1.3.1's.

### Premises

    /-- The PR's premise on a history: client ids are non-negative and small enough that the
    chains' arrays fit (`numClients * n` ints), and each client's operations are sequential,
    in the order listed: of two operations of one client, the one listed first returns
    strictly before the other is called. -/
    def ClientsOk (ops : List Operation) : Prop :=
      (∀ o ∈ ops, 0 ≤ sint.Z o.ClientId' ∧ (sint.Z o.ClientId' + 1) * ops.length < 2 ^ 63) ∧
      ∀ i j oi oj, i < j → ops[i]? = some oi → ops[j]? = some oj →
        oi.ClientId' = oj.ClientId' → sint.Z oi.Return' < sint.Z oj.Call'

Kept beside `HistOk` (unchanged: `n < 2^60`, every call at
most its return).

Why each part, with the counterexample without it (register model, `Init` 0):

1. **Sequential clients, listed in order.** The search linearizes a client's operations only in
   the order listed (`client.head` moves forward), and `computeFirstUnk` assumes that along a
   client's chain the returns increase (its exponential/binary search finds the first operation
   that does not precede, and takes all before it to precede).
   - Without it, incomplete: client 0 lists `{read → 1, [0,10]}, {write 1, [1,5]}`: linearizable,
     the PR answers `false` (v1.3.1 `true`).
   - Without it, unsound: client 0 lists `{read → 0, [2,3]}, {write 1, [0,1]}`: not linearizable,
     the PR answers `true` (v1.3.1 `false`).
   - Weakest: any pair `i < j` of one client with `¬ (ret_i < call_j)` either overlaps or is
     listed against real time; in both cases a register history around that pair alone (`j` a
     write, `i` a read of `j`'s value; or `i` a read of the initial value with `j` a write that
     returns before `i` is called) is a counterexample, whatever the other operations. So no
     weaker condition on the pairs is enough for every model; what is left is a condition on the
     model and outputs, not something a caller can check.
   - Not in v1.3.1's spec: a scope decision of this work, recorded here and in
     `issues/porcupine-dag-client-order.md` (`ClientId` is documented as optional).
2. **`0 ≤ ClientId`.** `makeEntries` indexes `operationHistory[ClientId]`: a negative id panics
   (`issues/porcupine-dag-clientid-range.md`, a Go test).
3. **`(ClientId + 1) * n < 2^63`.** `checkOperations` computes `maxClientId + 1`, `newChains`
   `make([]int, n * numClients)` and slices it at `[id*numClients : (id+1)*numClients]`: an
   overflow is a negative length (`make` panics) or wrong slice bounds (a panic). The bound is
   exactly that `n * numClients` is an `int`. (No memory limit is modelled: the size itself is no
   premise.) When `n = 0` it says nothing, and nothing is allocated.

No other premise: the model specs (`isModel`, `isModelFilled`) and `opsIoOk` are v1.3.1's.

### The package fact (new)

    /-- What `initialize'` leaves: `Linearizability` holds the consistency value
    `{Oracles: [RealTime, GeneralLikely], Valid: RVal}`, read-only. -/
    def linInit : IProp GF :=
      ∃ v : Consistency.t, globalAddr Linearizability ↦□ v ∗ isLinearizability v

    /-- A consistency value that is linearizability: its oracles slice holds `RealTime`'s and
    `GeneralLikely`'s closures (read-only), and its validity `RVal`'s. -/
    def isLinearizability (v : Consistency.t) : IProp GF :=
      ∃ rt gl, v.Oracles' ↦*□ [rt, gl] ∗ realTimeSpec rt ∗ generalLikelySpec gl ∗
        rvalInitSpec v.Valid'.Init' ∗ rvalStepSpec v.Valid'.Step'

    -- an oracle compares two operations it is given pointers to, reading their times
    def realTimeSpec (f : GoFunc) : IProp GF :=
      □ ∀ pa pb (a b : Operation) dqa dqb,
        {{ pa ↦{dqa} a ∗ pb ↦{dqb} b }} f #pa #pb
        {{ RET (#(rtOrder a b), #interface.nil); pa ↦{dqa} a ∗ pb ↦{dqb} b }}
      -- rtOrder a b = HardBefore if a.Return < b.Call, else HardAfter if a.Call > b.Return,
      -- else DontKnow
    def generalLikelySpec (f : GoFunc) : IProp GF :=   -- likewise, glOrder:
      -- SoftBefore if a.Call < b.Call, SoftAfter if a.Call > b.Call, else DontKnow
    def rvalInitSpec (f : GoFunc) : IProp GF :=
      □ ∀ σ (S : ModelSpec GF σ) m, {{ initSpec S m.Init' }} f #m {{ v, RET #v; S.rep 0 v S.M.init }}
    def rvalStepSpec (f : GoFunc) : IProp GF :=
      -- f(ctx, state, input, output, model) is model.StepContext(ctx, state, input, output):
      □ ∀ σ S m c cs k v s i o, {{ stepCtxSpec S m.StepContext' ∗ context.isContext c cs ∗
          ⌜k < 2^60⌝ ∗ S.rep k v s ∗ S.ioOk i o }} f #c #v #i #o #m
        {{ the post of stepCtxSpec }}

`isPkgInit pkg_id.github_com.anishathalye.porcupine` is `linInit` (`define_is_pkg_init`). The
closures' specs are proved on the closures the translation's `initialize'` stores (they are
func literals). A client holding `isPkgInit` cannot write `Linearizability` or its oracles
slice (read-only points-to): a Go client that assigns `porcupine.Linearizability` (or
`LinearizabilityOracles[0]`, which shares the array) is outside the spec, the usual reading of
a package variable's fact.

### Public results (exported, `Link.lean`: `porcupine.wp_CheckOperations*`)

    CheckOperations.spec : ∀ σ (S : ModelSpec GF σ) m sl ops dq,
      HistOk ops → ClientsOk ops →
      {{ isPkgInit porcupine ∗ context.isClosedchanInit ∗ isModel S m ∗ sl ↦*{dq} ops ∗
          opsIoOk S ops }}
        CheckOperations #m #sl
      {{ (b : Bool), RET #b; ⌜b = true ↔ Linearizable S.M (histOf ops)⌝ }}

    CheckOperationsTimeout.spec : ∀ σ S m sl ops dq dur, HistOk ops → ClientsOk ops →
      {{ same }} CheckOperationsTimeout #m #sl #dur
      {{ (r : GoString), RET #r;
          ⌜(r = go!"Ok" ∧ Linearizable S.M (histOf ops)) ∨
           (r = go!"Illegal" ∧ ¬ Linearizable S.M (histOf ops)) ∨
           (r = go!"Unknown" ∧ 0 < sint.Z dur)⌝ }}

    CheckOperationsVerbose.spec : the same, returning (r, info), no claim on info.

`Linearizable`, `histOf`, `HistOk`, `ModelSpec`, `isModel`, `opsIoOk`: v1.3.1's definitions,
copied into the part (`PorcupineDag/Proof/.../{Theory,Defs}.lean`).

### Internal

    checkOperations.spec : ∀ σ S m (c : Consistency.t) sl ops dq verbose dur,
      HistOk ops → ClientsOk ops →
      {{ isPkgInit ∗ context.isClosedchanInit ∗ isModel S m ∗ isLinearizability c ∗
          sl ↦*{dq} ops ∗ opsIoOk S ops }}
        checkOperations #m #c #sl #verbose #dur
      {{ (r, info), RET; ⌜the three outcomes of histOf ops⌝ }}

The partitions, as the PR represents them: an `operationHistory` is one slice of
`clientOperation`s per client. Its abstract value: the chains `cs : List (List Nat)` (client `c`'s
operation ids, in order) over the history `h`:

    /-- The chains partition the ids of `h`, and each chain is sequential (`Prec` in order). -/
    def ChainsOk (h : List (Op OpV)) (cs : List (List Nat)) : Prop :=
      cs.flatten.Perm (List.range h.length) ∧ ∀ ch ∈ cs, ch.Pairwise (Prec h)

    /-- An `operationHistory` (a slice of per-client slices) holding the chains `cs` of `h`:
    each `clientOperation` has its id, the operation (its input, output, times; its other
    fields any), `firstUnk` nil, `visited` false (as `makeEntries` builds them). -/
    def ohistOwn (ohsl : GoSlice) (h) (cs) : IProp GF :=
      ∃ sls, ohsl ↦* sls ∗ ⌜sls.length = cs.length⌝ ∗
        [∗list] c ↦ sl ∈ sls, ∃ cos, sl ↦* cos ∗ ⌜CoFresh h (cs[c]) cos⌝

    makeEntries.spec : ∀ sl ops dq (nc : w64), HistOk ops →
      (∀ o ∈ ops, 0 ≤ sint.Z o.ClientId' < sint.Z nc) →
      {{ isPkgInit ∗ sl ↦*{dq} ops }} makeEntries #sl #nc
      {{ (esl ohsl), RET; (∃ es, esl ↦* es) ∗ ohistOwn ohsl (histOf ops) (chainsOf ops (sint.nat nc))
          ∗ sl ↦*{dq} ops }}
      -- chainsOf ops k : client c ↦ the ids of ops with ClientId c, in order (c < k);
      -- the entries are built and sorted but no longer read by anything (no claim)

    checkParallel.spec : ∀ σ S m c hsl ohsls (hs : List (List (Op OpV))) (css) cp dur esl,
      ohsls.length = hs.length → css.length = hs.length → hs.length < 2^32 →
      {{ isPkgInit ∗ context.isClosedchanInit ∗ isModelFilled S m ∗ isLinearizability c ∗
          hsl ↦*□ ohsls ∗
          [∗list] i ↦ ohsl ∈ ohsls, ∃ h cs, ⌜hs[i]? = some h ∧ css[i]? = some cs ∧
            ChainsOk h cs ∧ HistWf h ∧ cs.length * h.length < 2^63⌝ ∗
            ohistOwn ohsl h cs ∗ histIoOk S h }}
        checkParallel #m #c #hsl #esl #cp #dur
      {{ (r, info), RET; ⌜(r = Ok ∧ ∀ h ∈ hs, Lin h) ∨ (r = Illegal ∧ ¬ ∀ h ∈ hs, Lin h) ∨
          (r = Unknown ∧ 0 < dur)⌝ }}
      -- HistWf h : h.length < 2^60 ∧ ∀ o ∈ h, o.call ≤ o.ret  (v1.3.1's EntriesOk third part)
      -- the entries argument is not read: no premise on it

    checkSingle.spec : ∀ σ S m (ctx : GoInterfaceOk) cs_ctx c ohsl h cs cp,
      ChainsOk h cs → HistWf h → cs.length * h.length < 2^63 →
      {{ isPkgInit ∗ context.isContext ctx cs_ctx ∗ isModelFilled S m ∗ isLinearizability c ∗
          ohistOwn ohsl h cs ∗ histIoOk S h }}
        checkSingle #ctx #m #c #ohsl #cp
      {{ (b longest), RET; (⌜b = true ∧ Linearizable S.M h⌝ ∨
            (⌜b = false⌝ ∗ (⌜¬ Linearizable S.M h⌝ ∨ □ cs_ctx.PDone))) ∗
          longestOwn longest h.length }}
      -- the ohist's ownership is not returned: checkSingle has written firstUnk/visited into
      -- it, and nobody reads it after (checkParallel keeps the slice in its LinearizationInfo
      -- for the visualizer, which has no claim)

The DAG search's helpers have specs over the chains' representation and the search's abstract
state, both fixed by the invariant plan (they are its interface):

- `Consistency.Check(a, b)` on `isLinearizability`: returns `(linOrder a.Op b.Op, nil)`:
  `HardBefore` iff `a.Return < b.Call`; `HardAfter` iff not that and `a.Call > b.Return`;
  otherwise `SoftBefore`/`SoftAfter`/`DontKnow` as `a.Call` is `<`/`>`/`=` `b.Call`. Never
  `Concurrent`, never an error (the conflict panic and the `%+v` formatting are unreachable).
- `newclientOperation(op, n, id)`: `{Op: op, globalId: id, id: id, firstUnk: nil, visited: false}`.
- `newChains`, `chains.computeFirstUnk`, `chains.addToFrontier`, `chains.removeFromFrontier`,
  `chains.isComplete`, `client.lift`, `client.unlift`, `chains.lift`, `chains.unlift`: the
  invariant plan.
- `fillDefault`, `noPartition`, the bitset's functions, `byTime.{Len,Swap,Less}`: v1.3.1's specs
  (the code is unchanged; `entry` has new fields, which the specs do not constrain).

### Callers

Nothing calls the part: `lintest` and the examples use v1.3.1 (`third_party/porcupine`). The
specs are the part's exported results (`PorcupineDag/Proof/.../Link.lean`).

### Out of scope

`CheckEvents*` (`checkEvents` matches a return to the client's latest call; it would need its own
premise on event histories), `Check*Consistency` with a general `Consistency` (oracles of
arbitrary specs; the DAG search's correctness then needs properties of the oracles, e.g. a hard
order that is a strict partial order compatible with the chains), the visualizer.

## Spec plan (candidate 2, 2026-11-02)

After the first spec review (fresh `spec-reviewer`; its findings F1-F6, each taken or answered
below). Candidate 1 stays above for the record; this section is the whole spec plan.

### Review round 1: what changed and why

- **F1 (taken): the size bound admitted a Go panic.** Candidate 1 bounded `(ClientId + 1) * n` by
  `2^63` and said the size itself was no premise. But gc refuses an allocation above `maxAlloc`
  (2^48 bytes on 64-bit platforms) with a recoverable `makeslice: len out of range` panic, and
  Perennial does not model it (its `docs/KNOWN_LIMITATIONS.md`, "Allocation"). v1.3.1 has the
  same gap only for inputs over 128 TiB; the PR's allocations grow with the *client id*, so a
  single operation with `ClientId` 2^50 panics in Go while the model runs it. The premise now
  bounds the PR's id-dependent allocations by `maxAlloc` (below).
- **F2 (taken, in a weaker form than proposed): a stronger spec under a weaker premise.** What
  the PR decides is linearizability that respects, besides real time, each client's listed order
  (`LinearizableCO`); for that the code needs only that along a client's listed order the
  *returns* do not decrease (`MonoRet`). The reviewer proposed calls and returns non-decreasing;
  the calls are not needed: `computeFirstUnk` starts from the previous operation's bound, which
  may then over-count the operations preceding the head, but those precede the previous
  operation, which the head follows in the client order, so they are forced anyway. Checked: 300000
  random register histories with returns non-decreasing per client and calls arbitrary (call at
  most return), the PR against a brute-force checker of `LinearizableCO`: no disagreement (100738
  accepted). The reviewer's runs: 300000 with `ret_i ≤ call_j`, and 300000 with calls and returns
  non-decreasing, no disagreement. Candidate 1's strict premise (sequential clients) becomes the
  condition of a law that turns the post into v1.3.1's (`linCO_iff_lin`), so the v1.3.1-shaped
  spec is a corollary (`Results.lean`). This also covers lintest-like callers whose clocks give
  only `ret_i ≤ call_{i+1}`.
- **F3 (taken): `makeEntries` with `nc < 0` and no operation panics.** Premise `0 ≤ nc` added.
- **F4 (taken): `checkParallel`'s `css` constrained nothing.** Dropped (each partition has `∃ cs`).
  `CoFresh` no longer requires `firstUnk = nil` (overwritten by `newChains`); it keeps
  `visited = false` (`computeFirstUnk` reads it).
- **F5 (taken, the alternative): the package fact names the closures.** The closures capture
  nothing, so the fact states the stored values (`linV`, the oracles slice holding `rtV`, `glV`,
  `RVal`'s `rvInitV`, `rvStepV`: the translation's func literals, generated from it), and their
  specs are lemmas. No quantification over model specs inside `isPkgInit`, and no `hasLC`
  specialization of the instance.
- **F6 (answered): margins.** (a) The caller's slice `sl ↦*{dq} ops` could be returned (the
  goroutines read only copies); v1.3.1's specs do not return it either; kept as v1.3.1's, said in
  the docstrings. (b) The PR never calls the model's `Hash` (its cache hashes the bitset only), so
  `isModel`'s `Hash` disjunct is not needed; kept to share v1.3.1's `isModel`, said in `Defs.lean`.
- Not an issue: the PR prints `Total_pop: N` to stdout from `checkSingle` (debug output; Perennial's
  `fmt.Printf` model, output not modelled).

### Premises

    /-- gc's largest allocation, in bytes (`maxAlloc` on 64-bit platforms): a larger `make`
    panics. -/
    def maxAllocBytes : Int := 2 ^ 48

    /-- The PR's premise on a history: client ids are non-negative and small enough that the
    allocations sized by them fit (`numClients = maxClientId + 1`: `8·n·numClients` bytes of
    `firstUnk`s, `48·numClients` of clients, `24·numClients` of per-client slices,
    `8·numClients` of frontier), and along each client's listed order the returns do not
    decrease. -/
    def ClientsOk (ops : List Operation) : Prop :=
      (∀ o ∈ ops, 0 ≤ sint.Z o.ClientId' ∧
        (sint.Z o.ClientId' + 1) * (ops.length + 6) * 8 ≤ maxAllocBytes) ∧
      ∀ i j oi oj, i < j → ops[i]? = some oi → ops[j]? = some oj →
        oi.ClientId' = oj.ClientId' → sint.Z oi.Return' ≤ sint.Z oj.Return'

    /-- The client order: `i` listed before `j`, with the same client id. -/
    def clientOrder (ops : List Operation) (i j : Nat) : Prop :=
      i < j ∧ ∃ oi oj, ops[i]? = some oi ∧ ops[j]? = some oj ∧ oi.ClientId' = oj.ClientId'

    /-- Sequential clients (candidate 1's premise): of two operations of one client, the one
    listed first returns strictly before the other is called. -/
    def ClientsSeq (ops : List Operation) : Prop :=
      ∀ i j oi oj, i < j → ops[i]? = some oi → ops[j]? = some oj →
        oi.ClientId' = oj.ClientId' → sint.Z oi.Return' < sint.Z oj.Call'

Why each part, with the counterexample without it (register model, `Init` 0):

1. **Returns non-decreasing per client (`MonoRet`).** `computeFirstUnk` finds the first operation of
   another client's chain that does not precede the head in real time, and takes those before it
   to precede: that is right only if the preceding operations are a prefix of the chain, which
   non-decreasing returns give. Without it, unsound (for `Linearizable` as for
   `LinearizableCO`): client 1 lists `{write 1, [0,10]}, {write 2, [1,2]}`, client 0
   `{read → 0, [5,6]}`. The read follows `write 2` in real time, so no linearization has it see
   0; v1.3.1 answers `false`, the PR `true`: the read's `firstUnk` on client 1 stops at index 0
   (`write 1` does not precede the read), so the read is linearized first. Weakest: any client
   whose returns decrease somewhere (`ret_i > ret_j`, `i < j`) gives such a history, with a read
   of another client called between `ret_j` and `ret_i`.
2. **`0 ≤ ClientId`.** `makeEntries` indexes `operationHistory[ClientId]`: a negative id panics.
3. **The allocation bound.** Without it, `makeslice: len out of range` (F1) or, past 2^63, an
   overflow (`n * numClients` wraps: a negative `make` length or slice bound, a panic). Exact up to
   the constant 6 (it bounds the three per-client allocations together: `48 + 24 + 8 ≤ 6 · 8 + 8·n`
   only once `n ≥ 4`; the conjunct is sufficient, slightly stronger than the four bounds separately
   for `n < 4`, which a caller does not notice).

The post is about `LinearizableCO`; `ClientsSeq` is not a premise of any spec, only of the law
giving v1.3.1's post. Under `ClientsSeq` (strict), `ClientsOk`'s second part holds
(`ret_i < call_j ≤ ret_j`).

### The vocabulary (`Theory.lean`, generalized)

v1.3.1's `Completes`/`Good` with the order to respect as a parameter:

    def CompletesR (M h) (R : Nat → Nat → Prop) (S t π) : Prop :=
      π.Nodup ∧ (∀ k, k ∈ π ↔ k < h.length ∧ ¬ S k) ∧ (run M t (vals h π)).isSome ∧
        π.Pairwise fun a b => ¬ R b a
    def GoodR (M h R S t) : Prop := ∃ π, CompletesR M h R S t π
    /-- v1.3.1's, unchanged in meaning. -/
    def Linearizable (M h) : Prop := GoodR M h (Prec h) (fun _ => False) M.init
    /-- Linearizable by an order that also respects `co` (the client order). -/
    def LinearizableCO (M h) (co : Nat → Nat → Prop) : Prop :=
      GoodR M h (fun a b => Prec h a b ∨ co a b) (fun _ => False) M.init

Laws (`Defs.lean`):

    theorem linearizable_of_co : LinearizableCO M h co → Linearizable M h
    theorem linCO_iff_lin (hwf : HistOk ops) (hseq : ClientsSeq ops) :
        LinearizableCO M (histOf ops) (clientOrder ops) ↔ Linearizable M (histOf ops)
      -- under ClientsSeq the client order is contained in Prec
    theorem checkResult_complete  -- v1.3.1's, unchanged

### The package fact

    /-- The closures the translation's `initialize'` stores (func literals, capturing nothing):
    `RealTime`, `GeneralLikely`, `RVal.Init`, `RVal.Step`; generated from the translation
    (`Closures.lean`, by `etc/gen-init.py`). -/
    def rtV : GoFunc := …; def glV : GoFunc := …; def rvInitV : GoFunc := …; def rvStepV : GoFunc := …

    /-- A consistency value that is linearizability: its oracles slice holds `RealTime` and
    `GeneralLikely` (read-only), and its validity is `RVal`. -/
    def isLinearizability (v : Consistency.t) : IProp GF :=
      v.Oracles' ↦*□ [rtV, glV] ∗ ⌜v.Valid' = { Init' := rvInitV, Step' := rvStepV }⌝

    /-- `isPkgInit`'s fact: `Linearizability` holds such a value, read-only. -/
    def linInit : IProp GF := ∃ v, globalAddr Linearizability ↦□ v ∗ isLinearizability v

    -- lemmas (proved on the closures' bodies):
    theorem wp_rtV : {{ pa ↦{qa} a ∗ pb ↦{qb} b }} rtV #pa #pb
        {{ RET (#(rtOrder a b), #interface.nil); pa ↦{qa} a ∗ pb ↦{qb} b }}
      -- rtOrder a b = HardBefore if a.Return < b.Call, HardAfter if a.Call > b.Return, else DontKnow
    theorem wp_glV : likewise, glOrder (SoftBefore / SoftAfter / DontKnow by a.Call vs b.Call)
    theorem wp_rvInitV : {{ initSpec S m.Init' }} rvInitV #m {{ v, RET #v; S.rep 0 v S.M.init }}
    theorem wp_rvStepV : {{ stepCtxSpec S m.StepContext' ∗ isContext c cs ∗ ⌜k < 2^60⌝ ∗
        S.rep k v s ∗ S.ioOk i o }} rvStepV #c #v #i #o #m {{ stepCtxSpec's post }}

A client holding `isPkgInit` cannot write `Linearizability` or its oracles array (read-only
points-to): a Go client assigning `porcupine.Linearizability` or `LinearizabilityOracles[k]`
(which shares the array) is outside the spec. Assigning `RealTime`, `GeneralLikely` or `RVal`
does not matter (copied at initialization).

### Public results (exported, `Link.lean`: `porcupine.wp_CheckOperations*`)

    CheckOperations.spec : ∀ σ (S : ModelSpec GF σ) m sl ops dq,
      HistOk ops → ClientsOk ops →
      {{ isPkgInit porcupine ∗ context.isClosedchanInit ∗ isModel S m ∗ sl ↦*{dq} ops ∗
          opsIoOk S ops }}
        CheckOperations #m #sl
      {{ (b : Bool), RET #b; ⌜b = true ↔ LinearizableCO S.M (histOf ops) (clientOrder ops)⌝ }}

    CheckOperationsTimeout.spec : ∀ σ S m sl ops dq dur, HistOk ops → ClientsOk ops →
      {{ same }} CheckOperationsTimeout #m #sl #dur
      {{ (r : GoString), RET #r;
          ⌜(r = go!"Ok" ∧ LinearizableCO S.M (histOf ops) (clientOrder ops)) ∨
           (r = go!"Illegal" ∧ ¬ LinearizableCO S.M (histOf ops) (clientOrder ops)) ∨
           (r = go!"Unknown" ∧ 0 < sint.Z dur)⌝ }}

    CheckOperationsVerbose.spec : the same, returning (r, info), no claim on info.

Corollaries (`Results.lean`, from the specs and `linCO_iff_lin`, `linearizable_of_co`): under
`HistOk`, `ClientsOk` and `ClientsSeq`, v1.3.1's posts verbatim (`b = true ↔ Linearizable …`; the
three outcomes with `Linearizable`); under `HistOk` and `ClientsOk` alone, `true`/`Ok` implies
`Linearizable` (soundness for plain linearizability).

### Internal

    checkOperations.spec : ∀ σ S m (c : Consistency.t) sl ops dq verbose dur,
      HistOk ops → ClientsOk ops →
      {{ isPkgInit ∗ context.isClosedchanInit ∗ isModel S m ∗ isLinearizability c ∗
          sl ↦*{dq} ops ∗ opsIoOk S ops }}
        checkOperations #m #c #sl #verbose #dur
      {{ (r, info), RET; ⌜the three outcomes, with LinearizableCO S.M (histOf ops) (clientOrder ops)⌝ }}

The partitions: an `operationHistory` (one slice of `clientOperation`s per client), abstractly
the chains `cs : List (List Nat)` over the history `h` (`Chains.lean`):

    /-- The chains hold every operation once; along each, the returns do not decrease. -/
    def ChainsOk (h) (cs) : Prop :=
      (∀ c, (chain cs c).Nodup ∧ (chain cs c).Pairwise (fun a b => ret a ≤ ret b)) ∧
      (∀ y, y < h.length ↔ ∃ c, c < cs.length ∧ y ∈ chain cs c) ∧
      (∀ y c c', y ∈ chain cs c → y ∈ chain cs c' → c = c')
    /-- The chain order. -/
    def chainOrder (cs) (a b : Nat) : Prop := ∃ c i j, i < j ∧ (chain cs c)[i]? = some a ∧ (chain cs c)[j]? = some b

    def ohistOwn (ohsl) (h) (cs) : IProp GF :=
      ∃ sls, ohsl ↦* sls ∗ ⌜sls.length = cs.length⌝ ∗
        [∗list] c ↦ sl ∈ sls, ∃ cos, sl ↦* cos ∗ ⌜CoFresh h (chain cs c) cos⌝
      -- CoFresh: cos[k].id = cos[k].globalId = chain[k], cos[k].Op's input/output/times are
      -- h[chain[k]]'s, visited = false

    /-- The allocation bound, per partition (`nc` clients, `n` operations). -/
    def AllocOk (nc n : Nat) : Prop := (nc : Int) * (n + 6) * 8 ≤ maxAllocBytes

    makeEntries.spec : ∀ sl ops dq (nc : w64), HistOk ops → 0 ≤ sint.Z nc →
      (∀ o ∈ ops, 0 ≤ sint.Z o.ClientId' < sint.Z nc) →
      {{ isPkgInit ∗ sl ↦*{dq} ops }} makeEntries #sl #nc
      {{ (esl ohsl), RET; (∃ es, esl ↦* es) ∗
          ohistOwn ohsl (histOf ops) (chainsOf ops (sint.nat nc)) ∗ sl ↦*{dq} ops }}
      -- chainsOf ops k: client c ↦ the ids of the operations with ClientId c, in order

    checkParallel.spec : ∀ σ S m c hsl ohsls (hs : List (List (Op OpV))) (cos : List (Nat → Nat → Prop)) cp dur esl,
      ohsls.length = hs.length → cos.length = hs.length → hs.length < 2^32 →
      {{ isPkgInit ∗ context.isClosedchanInit ∗ isModelFilled S m ∗ isLinearizability c ∗
          hsl ↦*□ ohsls ∗
          [∗list] i ↦ ohsl ∈ ohsls, ∃ h cs, ⌜hs[i]? = some h ∧ cos[i]? = some (chainOrder cs) ∧
            ChainsOk h cs ∧ HistWf h ∧ AllocOk cs.length h.length⌝ ∗
            ohistOwn ohsl h cs ∗ histIoOk S h }}
        checkParallel #m #c #hsl #esl #cp #dur
      {{ (r, info), RET; ⌜(r = Ok ∧ ∀ i h co, hs[i]? = some h → cos[i]? = some co → LinearizableCO S.M h co) ∨
          (r = Illegal ∧ ¬ (that)) ∨ (r = Unknown ∧ 0 < dur)⌝ }}
      -- (the partitions' client orders are an index of the spec: the post is about them)

    checkSingle.spec : ∀ σ S m (ctx : GoInterfaceOk) cs_ctx c ohsl h cs cp,
      ChainsOk h cs → HistWf h → AllocOk cs.length h.length →
      {{ isPkgInit ∗ context.isContext ctx cs_ctx ∗ isModelFilled S m ∗ isLinearizability c ∗
          ohistOwn ohsl h cs ∗ histIoOk S h }}
        checkSingle #ctx #m #c #ohsl #cp
      {{ (b longest), RET; (⌜b = true ∧ LinearizableCO S.M h (chainOrder cs)⌝ ∨
            (⌜b = false⌝ ∗ (⌜¬ LinearizableCO S.M h (chainOrder cs)⌝ ∨ □ cs_ctx.PDone))) ∗
          longestOwn longest h.length }}

Bridge (`checkOperations`): `chainOrder (chainsOf ops nc) = clientOrder ops` (as relations) and
`ChainsOk (histOf ops) (chainsOf ops nc)` from `HistOk`, `ClientsOk`.

The helpers (`Consistency.Check`, `newclientOperation`, `newChains`, `chains.*`, `client.*`):
the invariant plan. `fillDefault`, `noPartition`, the bitset's, `byTime.*`: v1.3.1's.

### Callers, out of scope

As candidate 1: nothing calls the part; `CheckEvents*` and a general `Consistency` out of scope.

## Spec plan (candidate 3, 2026-11-02)

Candidate 2 with the repairs of the second review (a fresh `spec-reviewer`; 1.2M more random
histories against brute-force `LinearizableCO`, up to 9 operations and 5 clients, sparse client
ids, two models: no disagreement; with calls after returns 26.5k disagreements, so `HistOk`'s
call ≤ return stays). Everything not restated is candidate 2's.

1. **`makeEntries.spec` was false**: `ops = []`, `nc = 2^46` meets its premises, and
   `make(operationHistory, nc)` asks for 24·2^46 bytes, above `maxAlloc` (a Go test panics). Premise
   `AllocOk (sint.nat nc) ops.length` added.
2. **The allocation bound, exact.** `maxAlloc` limits each allocation, not their sum. The PR's
   allocations sized by the client count `nc`: `firstUnks` `8·n·nc` bytes, the clients `48·nc`,
   the per-client slices `24·nc`, the frontier `8·nc`; the largest is `8·nc·max n 6`:

       /-- gc's largest allocation, in bytes: `maxAlloc` on 64-bit linux (2^48; ios/arm64 has
       2^40); a larger `make` panics (`makeslice: len out of range`). Perennial does not model it:
       the premises below that mention it keep the specs true of Go, and the proofs never use
       them. -/
       @[word_unfold] def maxAllocBytes : Int := 2 ^ 48

       /-- The allocations sized by `nc` clients over `n` operations fit (`newChains`,
       `makeEntries`): the largest is `8·nc·max n 6` bytes. -/
       def AllocOk (nc n : Nat) : Prop := (nc : Int) * (max n 6 : Nat) * 8 ≤ maxAllocBytes

   The allocations that grow with `n` only (`longest`, the bitset, the entries) are smaller than
   the caller's slice of `Operation`s or are grown by `append` from a live slice: Go runs out of
   memory (the heap is at most 2^47 bytes) before one of them could exceed `maxAlloc`; this is
   said in `Defs.lean`'s header.
3. **`ClientsOk` names its two parts**, which a caller proves from different sources (its client
   numbering, its clock):

       def ClientIdsOk (ops : List Operation) : Prop :=
         ∀ o ∈ ops, 0 ≤ sint.Z o.ClientId' ∧ AllocOk (sint.nat o.ClientId' + 1) ops.length
       def MonoReturns (ops : List Operation) : Prop :=
         ∀ i j oi oj, i < j → ops[i]? = some oi → ops[j]? = some oj →
           oi.ClientId' = oj.ClientId' → sint.Z oi.Return' ≤ sint.Z oj.Return'
       def ClientsOk (ops : List Operation) : Prop := ClientIdsOk ops ∧ MonoReturns ops

4. **`checkParallel.spec` is indexed by the chains**, not by relations (equality of `Prop`-valued
   functions would need function and propositional extensionality in the caller):
   `css : List (List (List Nat))`, `css.length = hs.length`, each partition's premise
   `hs[i]? = some h ∧ css[i]? = some cs ∧ ChainsOk h cs ∧ HistWf h ∧ AllocOk cs.length h.length`,
   and the post `(r = Ok ∧ ∀ i h cs, hs[i]? = some h → css[i]? = some cs →
   LinearizableCO S.M h (chainOrder cs)) ∨ (r = Illegal ∧ ¬ (that)) ∨ (r = Unknown ∧ 0 < dur)`.
5. **Laws**: `linCO_iff_lin` drops `HistOk` (under `ClientsSeq`, `clientOrder i j` gives
   `Prec i j` directly). New introduction law, for a client proving completeness:

       theorem linearizableCO_intro {M h co π} (hπ : Completes M h (Prec h) (fun _ => False) M.init π)
           (hco : π.Pairwise fun a b => ¬ co b a) : LinearizableCO M h co

   The corollaries are named, in the shape `CheckOperations.spec → CheckOperations.specSeq`
   (`specSeq`: candidate 2's v1.3.1-shaped posts under `HistOk`, `ClientsOk`, `ClientsSeq`), for
   the three public functions, in `Results.lean`; and `CheckOperations.spec →
   CheckOperations.specSound` (`true → Linearizable`, under `HistOk`, `ClientsOk`).
6. **The vocabulary's names**: the code's `Completes`/`Good` take the order `R` as an extra
   argument (v1.3.1's take none: same names, one more argument; `Theory.lean`'s header says so).
   The plan's `CompletesR`/`GoodR` are those.
7. **The caller's slice is returned**: the public specs and `checkOperations` give back
   `sl ↦*{dq} ops` (only `makeEntries` reads it, in the calling thread; the goroutines read copies).
   v1.3.1's specs do not; this is a strengthening, harmless to callers.
8. `issues/porcupine-dag-client-order.md`'s "Where" no longer says `computeFirstUnk` assumes calls
   increase.

Not repaired, answered: none.

## Invariant plan (candidate 2, 2026-11-02)

After the exhaustive checks of candidate 1 (two agents: one on sections 1, 2, 5 and the lift/unlift
specs, one on section 3, the other helpers of section 4 and section 6; hand arguments per user,
and executable checks: 132000 + 194392 histories and exhaustive `computeFirstUnk` cases, every
assertion below asserted at every use) and the move to spec candidate 2 (`LinearizableCO`, the
returns-only premise). Candidate 1 stays below for the record; this section is the plan, as
amendments to it: everything not restated here is candidate 1's.

### What the checks found in candidate 1, and the fixes

1. **`bad_here`, `bad_pop`, `bad_fail` were false** without "some operation is not linearized"
   (`B` every id, `fr = []`: the empty completion is good). Premise `hinc : ∃ y < n, y ∉ B`
   added; `checkSingle` has it from `isComplete = false` at the loop head, kept across a failed
   `chains.lift` (its post: nothing changed). (Already so in `DagTheory.lean`.)
2. **`bad_push` needed `Chain M h fs s`** (the new cache entry is `OnStack` through the new
   frame's chain): it takes `Struct`. (So in `DagTheory.lean`.)
3. **Cursor types**: `bad_skip`/`bad_down`, `struct_push`, `bad_push` take the position as a
   `Nat` `q` with the hypotheses at `(q : Int)` and the result at `(q : Int) - 1`; every cursor
   `fr.length - 1`, `f.pos - 1` is `Int` subtraction. (So in `DagTheory.lean`.)
4. **`deps_unlift`** stated: it is `deps_lift` read at `H' = H.set c (H[c] - 1)`; the code's test
   `firstUnk[c] == head + 1` (after the decrement) is `FUe … = H'[c] + 1`.
5. **The heads ↔ stack link was missing.** Added (`Chains.lean`, proved): `headsOf cs B` (per
   chain, how many of its operations are in `B`), `PosOk cs B H` (the operations of `B` are each
   chain's first `H[c]`, by position), `heads_ids` (on a stack of candidates: `PosOk` and
   `HeadsOk` at `headsOf cs (ids fs)`), `headsOf_cons` (the newest frame lifted its client's
   head, the heads move by one there: what `chains.unlift`'s precondition and `chains.lift`'s
   post need), `ids_iff_headsSet`, `posOk_push`, `headsOf_eq`. The loop invariant uses
   `st.heads = headsOf cs (ids fs)`.
6. **`computeFirstUnk`'s exponential invariant was false** (indices between probes are not
   probed: `start = 0`, `FU = 2`, probes at 0 and 1, then `i = 3`, `step = 4`, and `P 2` false).
   Now: `step = 2^m`, `i = start + step - 1`, `fdk = -1`, `i - step/2 ≤ L`, and
   `∀ j, start ≤ j → j < i - step/2 → P j` (`step/2` truncating: `start` before the first
   iteration, the last index probed after). The binary loop's `low ≤ high` initially needs
   `i - step/2 ≤ L`; `start ≤ low` since `step/2 ≤ step - 1` (the `low < firstUnk` clamp is dead).
   Bounds inside the body only: the guard `i < L` with `i = start + step - 1` gives `step ≤ L`, so
   `step * 2`, `i + step < 2L < 2^61`.
7. **`computeFirstUnk` needs `c < nc`** (true at both call sites); `heads[c] ≤ len` not needed.
8. **`makeEntries` needs `0 ≤ nc`** (also spec review F3); its loop carries each per-client
   slice's capacity (`append`), dropped at the end.
9. **`addToFrontier` takes `c ∉ frontier`** (true at all four call sites; the dedup return is
   never taken) instead of "members distinct from `c` or `c`".
10. **`removeFromFrontier`'s spec is a plain `List.erase`**, no `Pairwise` premise and `c`
    possibly absent (it is, at `unlift`'s first call): between `client.lift`'s `head++` and
    `removeFromFrontier(i)` the frontier mapped through the new heads need not be sorted. Sorted
    after it: the mapping is unchanged off `i`.
11. **The j-loops' invariants** exclude `i` (resp. `c`) from the "not yet processed" half and
    require unfinished clients for the `nDeps` equalities; `chains.unlift`'s carries
    "`c` not in the frontier, `nDeps[c] = 0`"; "every member is a candidate of `H'`" holds at
    every step of `chains.lift`'s loop but in `chains.unlift` only after its loop (at
    `addToFrontier(c)`).
12. **`client.lift`'s post** is a disjunction `chains.lift` splits: refused (`step = none` or
    `□ Done`), cached (`step = some t'` and the abstract cache has `(y :: B, t')`), or lifted; its
    precondition has `y ∉ B` (from `Cand`), needed for "set then clear restores the bitset".
    `chains.lift`'s success post exposes `step s o.val = some t'` (`ok = true` is
    `stepCtxSpec`'s first arm even on a done context); its failure post: heads, frontier,
    bitset, cache, stack unchanged.
13. **`checkParallel`**: `consistency` is captured by the goroutine closure by reference: its
    local cell is made read-only (persistent) before the goroutines start, as v1.3.1 does for
    `model`.
14. `stackEntry.opIdx` is never read: no invariant on it.

### What changes with spec candidate 2

- **The order**: the search respects `Before h cs a b := Prec h a b ∨ chainOrder cs a b`;
  `Cand`, `CandList`, `PrefixBad`, `FramesStruct`, `FramesBad`, `Struct`, `Bad` take the order `R`
  as a parameter (instantiated at `Before h cs`), `Good`/`SuccBad`/`CacheOk` too; `bad_here`,
  `bad_pop`, `bad_fail` need `R` irreflexive (`before_irrefl`, from call ≤ ret and the chains'
  `Nodup`) and relating only operations of `h` (`before_dom`); `sound_done` and `bad_fail` are
  about `Good M h R (fun _ => False) M.init`, which is `LinearizableCO M h (chainOrder cs)` at
  `R = Before h cs`. (`DagTheory.lean`, `Theory.lean`, proved.)
- **`ChainsOk`**: returns non-decreasing along each chain (`RetLe`), not `Prec`.
- **`firstUnk` holds `FUe`**, not `FU`: `FUe h cs c d 0 = FU h cs c 0 d`,
  `FUe … (k+1) = max (FUe … k) (FU h cs c (k+1) d)`. `FuOk`: a visited operation's slice is
  `FUe` (for `d ≠ c`). `deps` counts `d` with `H[d] < FUe …`. `computeFirstUnk`'s searches start
  at `start = FUe … (k-1)` (or 0) and compute `max start FU` (`fue_search`, proved), which is
  `FUe … k`; their invariants (fix 6) are relative to `start`, with no claim below it.
- **`cand_iff`** needs `B` closed under `Before` (`∀ z w, w ∈ B → Before z w → z ∈ B`): `FUe`
  counts operations preceding *earlier* operations of the chain, linearized because those are
  and `B` is closed. On a stack of candidates the ids are closed (`framesStruct_below`).
  Proved.
- **`deps_lift`** with `FUe` (proved).
- **Frontier members unrelated in real time**: `cand_not_prec` gives `¬ Before`, so `¬ Prec`
  both ways, so `Check` answers no `Hard*` among them.

### Executable check of candidate 2

The instrumented copy with `firstUnk` checked against `FUe` and the frontier against the sorted
`Before`-candidate list: 100000 histories with returns non-decreasing per client and calls
arbitrary (call ≤ return), 500225 loop iterations, no violation, every answer equal to a
brute-force `LinearizableCO` checker's; and the 60000 sequential-client histories of candidate 1
again, no violation.

## Invariant plan (candidate 1, 2026-11-02)

Against the spec plan. Notation: `h : List (Op OpV)` the partition's history (`n = h.length`),
`cs : List (List Nat)` its chains (`nc = cs.length`), `B` the ids linearized (the stack's, newest
first), `H : List Nat` the heads (`H[c]` the number of client `c`'s operations linearized),
`headOp H c = cs[c][H[c]]`, `clientOf cs y` the chain holding `y`. Premises available everywhere
below: `ChainsOk h cs`, `HistWf h` (`n < 2^60`, `call ≤ ret`), `nc * n < 2^63`.

### 1. The search, in pure terms (`DagTheory.lean`, beside the copied `Theory.lean`)

Reused from v1.3.1's `Theory.lean` (copied, its entry-list part dropped): `Op`, `SeqModel`, `run`,
`Prec`, `vals`, `Completes`, `Good`, `Linearizable`, `good_congr`, `Chain`, `chain_det`,
`SuccBad`, `OnStack`, `CacheOk`. `Frame` changes: it records the candidate list it was lifted from.

    structure Frame (σ) where id : Nat; pre : σ; pos : Nat; fr : List Nat

    /-- `y` may be linearized next after `B`: not linearized, and everything that precedes it in
    real time is. -/
    def Cand (h) (B : List Nat) (y : Nat) : Prop := y < h.length ∧ y ∉ B ∧ ∀ z, Prec h z y → z ∈ B

    /-- The frontier's order (`addToFrontier`): later call first, then larger client. -/
    def KeyGt (h) (cs) (y z : Nat) : Prop :=
      call y > call z ∨ (call y = call z ∧ clientOf cs y > clientOf cs z)

    /-- `l` is the candidates of `B`, sorted by `KeyGt`. -/
    def CandList (h cs B l) : Prop := l.Pairwise (KeyGt h cs) ∧ ∀ y, y ∈ l ↔ Cand h B y

    theorem candList_unique : CandList h cs B l → CandList h cs B' l' → (∀ y, y ∈ B ↔ y ∈ B') → l = l'
      -- KeyGt is asymmetric; two Pairwise-KeyGt lists with the same members are equal

    /-- Lifting `fr[q]` for `q > p` leads only to configurations without completion. -/
    def PrefixBad (M h) (B) (t : σ) (fr : List Nat) (p : Int) : Prop :=
      ∀ q y, p < q → fr[q]? = some y → SuccBad M h B t y

    /-- What survives a cancelled step: each frame lifted the candidate at `pos` of the candidate
    list below it. -/
    def FramesStruct (h cs) : List (Frame σ) → Prop
      | [] => True
      | f :: fs => FramesStruct fs ∧ CandList h cs (ids fs) f.fr ∧ f.fr[f.pos]? = some f.id
    def FramesBad (M h) : List (Frame σ) → Prop
      | [] => True
      | f :: fs => FramesBad fs ∧ PrefixBad M h (ids fs) f.pre f.fr f.pos

    /-- The structure (kept by every branch, cancelled or not). -/
    def Struct (M h cs fs s fr p) : Prop :=
      Chain M h fs s ∧ FramesStruct h cs fs ∧ CandList h cs (ids fs) fr ∧ -1 ≤ p ∧ p < fr.length
    /-- The completeness invariant (lost on a cancelled step: carried as `⌜Bad⌝ ∨ □ Done`). -/
    def Bad (M h fs s fr p cache) : Prop :=
      FramesBad M h fs ∧ PrefixBad M h (ids fs) s fr p ∧ CacheOk M h fs cache

Lemmas (one per branch of `checkSingle`/`chains.lift`, plus the exits):

    theorem struct_init : CandList h cs [] fr → Struct M h cs [] M.init fr (fr.length - 1)
    theorem bad_init : Bad M h [] s fr (fr.length - 1) []                -- vacuous
    -- a candidate not lifted, its configuration cached: cursor down
    theorem bad_skip (hb : Bad M h fs s fr p cache) (hy : fr[p]? = some y) (hcand : Cand h (ids fs) y)
        (hcached : ∀ o t', h[y]? = some o → M.step s o.val = some t' →
          ∃ c ∈ cache, (∀ i, c.1 i ↔ i ∈ y :: ids fs) ∧ c.2 = t') :
        Bad M h fs s fr (p - 1) cache
    -- a candidate the model refuses: cursor down
    theorem bad_skip_step (hb) (hy : fr[p]? = some y) (hst : ∀ o, h[y]? = some o → M.step s o.val = none) :
        Bad M h fs s fr (p - 1) cache
    -- a candidate lifted (the model steps, not cached): pushed with the new candidate list
    theorem struct_push (hs : Struct M h cs fs s fr p) (hq : 0 ≤ q ≤ p) (hy : fr[q]? = some y) (ho)
        (hst : M.step s o.val = some t') (hfr' : CandList h cs (y :: ids fs) fr') :
        Struct M h cs (⟨y, s, q, fr⟩ :: fs) t' fr' (fr'.length - 1)
    theorem bad_push (hb : Bad M h fs s fr q cache) (hy) (ho) (hst) :
        Bad M h (⟨y, s, q, fr⟩ :: fs) t' fr' (fr'.length - 1) ((· ∈ y :: ids fs, t') :: cache)
      -- `hb` at the cursor `q`: the candidates between `q` and the entry cursor were skipped
      -- (`bad_skip`s); the new frame's PrefixBad is that of q; the new cursor's is vacuous
    -- every candidate tried: no completion (needs only call ≤ ret)
    theorem bad_here (hes : HistWf h) (hfr : CandList h cs B fr) (hall : PrefixBad M h B s fr (-1)) :
        ¬ Good M h (· ∈ B) s
    -- backtrack: the frame's configuration was bad; resume below it, after its position
    theorem struct_pop (hs : Struct M h cs (f :: fs) s fr p) : Struct M h cs fs f.pre f.fr (f.pos - 1)
    theorem bad_pop (hes) (hs : Struct …) (hb : Bad M h (f :: fs) s fr (-1) cache) :
        Bad M h fs f.pre f.fr (f.pos - 1) cache
    theorem bad_fail (hes) (hs : Struct M h cs [] s fr p) (hb : Bad M h [] s fr (-1) cache) :
        ¬ Linearizable M h
    -- soundness: every frame lifted a candidate; with every id lifted, the stack is a linearization
    theorem sound_done (hes) (hs : Struct M h cs fs s fr p) (hall : ∀ y < h.length, y ∈ ids fs) :
        Linearizable M h       -- π = (ids fs).reverse

Cancellation (`stepCtxSpec`'s `□ Done` arm) is handled as in v1.3.1: `Struct` is unconditional,
`Bad` is under `⌜Bad⌝ ∨ □ Done`; a refused step on a done context keeps `Struct` (nothing changes)
and gives the `□ Done` arm.

### 2. The chains, in pure terms (`Chains.lean`)

    /-- The ids linearized, from the heads: client `c`'s first `H[c]`. -/
    def headsSet (cs) (H : List Nat) (y : Nat) : Prop := ∃ c k, k < H[c] ∧ cs[c][k]? = some y
    def HeadsOk (cs H) : Prop := H.length = cs.length ∧ ∀ c, H[c] ≤ cs[c].length

    /-- The number of client `d`'s operations that precede client `c`'s `k`-th. -/
    def FU (h cs c k d) : Nat := ((cs[d]).filter (fun z => decide (Prec h z (cs[c][k])))).length
    /-- The number of other clients with operations preceding `c`'s head not all linearized. -/
    def deps (h cs H c) : Nat :=
      ((List.range cs.length).filter (fun d => d ≠ c ∧ FU h cs c H[c] d > H[d])).length

Lemmas (all under `ChainsOk h cs`, `HistWf h`):

    theorem fu_prefix : i < cs[d].length → (i < FU h cs c k d ↔ Prec h (cs[d][i]) (cs[c][k]))
      -- the operations of d preceding x are a prefix of d's chain (d's chain is sequential)
    theorem fu_mono : k + 1 < cs[c].length → FU h cs c k d ≤ FU h cs c (k+1) d
      -- what makes computeFirstUnk's start from the previous operation's bound exact
    theorem cand_iff : HeadsOk cs H → (∀ y, y ∈ B ↔ headsSet cs H y) →
        (Cand h B y ↔ ∃ c, H[c] < cs[c].length ∧ cs[c][H[c]] = y ∧ deps h cs H c = 0)
    theorem cand_not_prec : Cand h B y → Cand h B z → ¬ Prec h y z
      -- frontier members are unrelated in real time: Check never answers Hard among them
    theorem deps_lift (j ≠ i) : deps h cs (H.set i (H[i]+1)) j
        = deps h cs H j - (if FU h cs j H[j] i = H[i] + 1 then 1 else 0)
      -- and in the decremented case deps h cs H j ≥ 1; symmetric `deps_unlift`

### 3. The chains in the heap (`ChainsOwn.lean`)

One record of pure values for the chains' state:

    structure ChSt where
      heads : List Nat
      nDeps : List w64
      frontier : List Nat          -- client indices
      vis : List (List Bool)       -- per client, per operation
      fu : List (List (List w64))  -- per client, per operation: its firstUnk slice

    /-- The chains value `chV`: its clients slice (each client: `id = c`, `cltOps` holding client
    `c`'s operations (`Op`, `id`, `globalId` = the chain's ids; `firstUnk` a slice holding
    `st.fu[c][k]`, of length `nc`; `visited = st.vis[c][k]`), `head = st.heads[c]`,
    `nDeps = st.nDeps[c]`), `numOps = n`, its frontier slice holding `st.frontier` (with its
    capacity: `append`). -/
    def chainsRepr (chV : chains.t) (h cs) (st : ChSt) : IProp GF
    def chainsOwn (ch : Loc) (h cs) (st : ChSt) : IProp GF := ∃ chV, ch ↦ chV ∗ chainsRepr chV h cs st

    /-- The chains' invariant, at heads `st.heads`. -/
    def ChainsInv (h cs) (st : ChSt) : Prop :=
      HeadsOk cs st.heads ∧ shapes (lengths of nDeps, vis, fu match cs) ∧
      FuOk h cs st ∧
      (∀ c k, k < cs[c].length → k ≤ st.heads[c] → st.vis[c][k] = true) ∧
      (∀ c, st.heads[c] < cs[c].length → sint.Z st.nDeps[c] = deps h cs st.heads c) ∧
      (∀ c ∈ st.frontier, st.heads[c] < cs[c].length) ∧
      CandList h cs (headsList cs st.heads) (st.frontier.map (headOp cs st.heads))
    /-- Every visited operation's firstUnk is exact (except its own client's entry, never written). -/
    def FuOk (h cs st) : Prop := ∀ c k, st.vis[c][k] = true → ∀ d ≠ c, sint.Z st.fu[c][k][d] = FU h cs c k d

`ChainsInv`'s last conjunct is what makes `liftFrom` right: the frontier, mapped to the head
operations, is the sorted candidate list, hence (`candList_unique`) after `unlift` the list the
popped frame was lifted from.

### 4. The helpers' specs and their loops

- `Consistency.Check(&consistency, a, b)` on `isLinearizability`, `a ↦{qa} coa`, `b ↦{qb} cob`:
  `(linOrder coa.Op cob.Op, nil)`. Its loop over the (two) oracles: `ok` is the fold of the first
  `i` answers; after RealTime `ok ∈ {DontKnow, HardBefore, HardAfter}`; GeneralLikely's Soft or
  DontKnow changes only a DontKnow; no conflict (RealTime gives at most one Hard, GeneralLikely
  none), so the error branches (`errors.New`, `fmt.Sprintf("%+v")`) are unreachable.
- `chains.computeFirstUnk(c, consistency)`: pre `chainsOwn ch h cs st`, `FuOk h cs st`,
  `st.heads[c] > 0 → st.vis[c][st.heads[c] - 1]`; post `st` with `vis[c][heads[c]] := true` and
  `fu[c][heads[c]][d] := FU … d` for `d ≠ c` (if `heads[c] < len` and not yet visited; else `st`),
  `FuOk` kept. Loop invariants. Outer loop over `d`: the entries `d' < d` (`d' ≠ c`) of the head's
  slice are exact. For one `d`, with `start` (the previous op's `fu[d]`, or 0; `start ≤ FU … d` and
  `∀ j < start, P j`, by `fu_mono`/`fu_prefix`), `P i := Prec (cs[d][i]) x` (downward closed on
  `[0, L)`, `fu_prefix`), `L = cs[d].length`:
  - exponential: `start ≤ i`, `step = 2^m ≥ 1`, `i = start + step - 1`, `∀ j < i, P j` when
    `i ≤ L`... precisely `∀ j, j < i → j < L → P j` — every index probed so far is `P` and by
    downward closure all below; `fdk = -1`; exit: `i ≥ L` (`fdk = -1`) or `¬ P i` (`fdk = i < L`);
    bounds `step ≤ 2L`, `i < 2L + 1` (no overflow: `L < 2^60`).
  - binary: `start ≤ low ≤ high ≤ L`, `∀ j < low, P j`, and
    `(fdk = -1 ∧ high = L) ∨ (fdk = high ∧ high < L ∧ ¬ P high)`; exit `low = high`.
  - result: `fdk = -1` → `result = low = L = FU`; else the linear scan's first iteration sees
    `¬ P fdk`, so `result = fdk = low = FU` (linear loop invariant: `j = fdk` until it breaks).
- `chains.addToFrontier(c, consistency)`: pre `chainsOwn`, `st.frontier` Pairwise `KeyGt` on head
  ops, `heads[c] < len`, every member's head op unrelated to `c`'s head op both ways (`¬ Prec`),
  members' heads `< len`, members distinct from `c` or `c` itself; post: `st.frontier'` Pairwise,
  members = members ∪ {c}, rest unchanged. Loops: dedup: `c ∉ frontier[0..i)`; insertion:
  `∀ v ∈ frontier[0..i), KeyGt (headOp v) (headOp c)` (Check answers SoftAfter iff
  `call_c > call_v`, DontKnow iff equal, as they are unrelated); inserting before `frontier[i]`
  (`KeyGt c frontier[i]`) or at the end keeps it sorted.
- `chains.removeFromFrontier(c)`: loop `c ∉ frontier[0..i)`; post: erase (Pairwise kept, members
  minus c).
- `chains.isComplete()`: loop `∀ c' < i, heads[c'] = len`; result `decide (∀ c, heads[c] = len)`.
- `newChains(history, consistency)`: post the `ch` value with `ChainsInv h cs st0` at heads 0.
  Loops: (1) clients built for `i' < i`, `n = Σ lens`; (2) firstUnk slices assigned for `i' < i`
  (`firstUnks` split into `n` disjoint pieces by id, regrouped by chain: `cs.flatten` is a
  permutation of `range n`); (3) for `i' < i`, `vis[i'][0]` and `nDeps[i'] = deps … i'` (inner loop
  counts `j' < j`); (4) frontier = a Pairwise list of `{i' < i : len > 0 ∧ nDeps = 0}` (each
  addition unrelated to the members: all are candidates of `[]`).
- `client.lift(ctx, model, consistency, oldState, cache, serialized)` (receiver `&clients[i]`):
  v1.3.1's `lift` + `cacheContains` steps of `checkSingle`: a refused step (model `none`, or
  `□ Done`): `(false, _)`, nothing changed; a step to a cached configuration: `(false, oldState)`,
  bitset restored (set then clear), and the abstract cache has `(y :: B, t')`; else `head + 1`,
  bitset with `y`, cache with `(y :: B, t')` (bucket append; the new state shared in the pool),
  `(t'_val, true)`. Loop over the bucket: v1.3.1's `cacheContains`'s.
- `client.unlift(top, serialized)`: `c.id = top.clientId` (frames record their client), head − 1,
  bitset without `top.opId`.
- `chains.lift(…, liftFrom)` (the frontier loop): invariant over `idx` (from `liftFrom` down):
  state unchanged; under `⌜Bad … liftFrom …⌝ ∨ □ Done` at the entry, `⌜Bad … idx …⌝ ∨ □ Done`
  (`bad_skip`, `bad_skip_step`). Exit with no success: `Bad … (-1)` (or Done). On success at
  `idx`: push the frame (`stackEntry{opId, clientId, state, opIdx = head, frontierIdx = idx}`),
  `computeFirstUnk(i)` (the new head's `vis`), `removeFromFrontier(i)`, recount `nDeps[i]` (loop:
  `k' < k` counted), maybe `addToFrontier(i)`, then the loop over `j` (invariant: for `j' < j`,
  `j' ≠ i`, unfinished: `nDeps[j'] = deps H' j'`, and `j'` in the frontier iff a candidate of
  `H'`; for `j' ≥ j`: `nDeps[j'] = deps H j'`, frontier membership as at `H` minus `i`; the
  frontier Pairwise throughout; every member a candidate of `H'`, so additions are unrelated to
  members). At the end `ChainsInv` at `H' = H.set i (H[i]+1)` (`cand_iff`, `deps_lift`).
- `chains.unlift(stack, serialized, consistency)`: `removeFromFrontier(clientId)`, `unlift`, the
  loop over `j` (invariant: `j' < j` processed: `nDeps[j'] = deps H' j'` with
  `H' = H.set c (H[c]-1)`, removed from the frontier if they became blocked; `j' ≥ j`: as at
  `H`), `addToFrontier(clientId)` (its head op, the popped one, is a candidate of `H'`: it was
  lifted from the frontier at `H'`; members are candidates of `H'`, so unrelated). Post
  `ChainsInv` at `H'`; returns `(top.state, top.frontierIdx)`.

### 5. `checkSingle`'s loop (`Search.lean`)

    searchInv := ∃ fs s fr p cache st,
      chainsOwn ch h cs st ∗ ⌜ChainsInv h cs st ∧ st.heads = headsOf cs fs ∧
        st.frontier.map (headOp cs st.heads) = fr⌝ ∗
      stack ↦ stk ∗ stackOwn stk fs (entries: opId = f.id, clientId = clientOf f.id, opIdx = its
        chain position, frontierIdx = f.pos, state a shared value of f.pre) ∗
      serialized: bitset of `ids fs` ∗ state: shared value of `s`, index |fs| ∗
      cache map with `cacheP n cache` ∗ liftFrom = p ∗
      ⌜Struct S.M h cs fs s fr p⌝ ∗ (⌜Bad S.M h fs s fr p cache⌝ ∨ □ Done) ∗ longestOwn longest n

- `isComplete` true: every head at its chain's length, so every id in `ids fs` (`ChainsOk`'s
  permutation); `sound_done` → `true ∧ Linearizable`.
- `ctx.Err() ≠ nil`: `false` and `□ Done` (`isContext`'s `Err`).
- lift success: `struct_push`, `bad_push`; `liftFrom = len(frontier) - 1`.
- lift failure, empty stack: `bad_fail` → `false ∧ ¬ Linearizable` (or Done).
- lift failure, nonempty: `struct_pop`/`bad_pop`; the frontier after `unlift` is `f.fr`
  (`candList_unique`), so `liftFrom = f.pos - 1` is the theory's cursor.
- the `computePartial` loop and the final `seq`: memory only (`longestOwn`), as v1.3.1.

### 6. `checkParallel`, `checkOperations`, `makeEntries`

- `checkParallel`: v1.3.1's invariants (`resultP`, `Hok`, `Hsnd`, `Hfull`) unchanged; each goroutine
  gets its partition's `ohistOwn` (not returned) and a copy of `isLinearizability c` (persistent).
- `makeEntries`: loop invariant over `ops[0..k)`: the entries so far (memory only) and
  `ohsl ↦* sls` with `sls[c]` holding client `c`'s ids `< k` in order; index `ClientId <
  numClients` from the premise.
- `checkOperations`: the `maxClientId` loop (`maxClientId` = max of `0` and the ids seen, so
  `(maxClientId + 1) * n < 2^63` from `ClientsOk`); `ChainsOk (histOf ops) (chainsOf ops nc)` from
  `ClientsOk` (sequential clients) and `HistOk`.

### 7. Executable check (before the review)

A copy of the PR with the invariants asserted (scratch module): at every iteration of
`checkSingle`'s loop, `ChainsInv` (each visited op's `firstUnk` against a brute-force count, the
prefix property, `nDeps`, the frontier against the brute-force sorted candidate list), the stack
(heads, ids, states, each frame's recorded frontier against the candidate list of the ids below
it, `fr[pos] = client`, each frame a candidate), the bitset, the cursor's range, `PrefixBad` of the
cursor and of every frame, and `CacheOk` (by a brute-force search for a completion); at every
failed lift, that the configuration has no completion; after every `unlift`, that the frontier is
the one the popped frame was lifted from. Random histories satisfying the premises (register and
append-log models, up to 8 operations and 4 clients, ties in call times, a quarter of the reads
corrupted): 80000 histories, 456511 loop iterations, no violation; the answer agrees with v1.3.1
on every one.
