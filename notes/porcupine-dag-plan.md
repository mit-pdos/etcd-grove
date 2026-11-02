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
