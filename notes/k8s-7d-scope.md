# k8s etcd3 stage 7d, the replay: Scope (2026-11-07, branch `k8s-7d`; to etcd-grove-81 for review)

The stage in `notes/k8s-etcd3-plan.md`, "Phase 7", 7d: the verified porcupine returns the
linearization it found, with a spec saying it is one. The driver's `Check` replays the model along
it, as `TestCorrectness` does (`correctness.NewReplay`, then `Replay.Validate` of every operation),
and the replay is proved to accept. The pins:
- the test is `k8s.io/kubernetes` `878cfa6c4cc7`, `test/integration/apiserver/storage/correctness_test.go:362-390`;
- the replay is `k8s.io/apiserver` `9c4ec15b8038`, `pkg/storage/testing/correctness/replay.go`.

No Lean is edited until 81 approves. The Go side is prototyped on the branch, in the second commit
(translations not regenerated), and checked in Go (§7).

## 1. What the replay adds, and for which of the test's reads

**For the driver's current traffic it adds nothing that porcupine does not already check.** This
section answers "which of the test's reads does the replay matter for, before 7e".

- `Replay.Validate` checks only `OpGet` and `OpList`, and for a Get only one with
  `GetReadConsistency(opts) ≠ Consistent`, i.e. `ResourceVersion ≠ ""`.
- For these reads, upstream's `Model.validateGet` (`NotOlderThan`) checks only the answer's resource
  version ("contents are validated later during replay").
- The driver's model is stricter. `mget` (`k8setcd3.go`) checks **every** Get's whole answer
  against the store at the Get's linearization point, minimum or not. This is right for etcd3:
  `store.Get` always reads etcd's latest state with a linearizable `Get`
  (`store.go:299`, `kubernetes.GetOptions{}`), and uses the resource version only as a minimum
  (`validateMinimumResourceVersion`). Stage 7b chose this, and `k8s_etcd3_safe` proves it.
- So the etcd3 store has **no stale Gets**. The replay's Get check is then implied by porcupine's
  `Ok`. The proof below shows this exactly: the replay accepts every operation sequence the model
  accepts. The Go check (§7) confirms it: a stale or invented Get answer is rejected by porcupine
  as well as by the replay.

**Stale reads in the etcd3 store are lists only (7e).** `storage.ValidateListOptions`
(`interfaces.go:372`) reads at a past revision (`withRev ≠ 0`) in two cases:
- `ResourceVersionMatch = Exact` with an RV;
- the legacy match `""` with `Recursive`, `Limit > 0` and RV > 0;
- continue tokens would be a third case, but the test never sets `Predicate.Continue`.

In the test's distribution these come from lists with RV not in `{"", "0"}`:
- Match `Exact` (25%);
- Match `""` (50%) with limit 1 or 2 (30%) and `Recursive`.

`NotOlderThan`, `"0"` and consistent lists read the latest revision, so they are linearizable, and
the model's in-step check (made exact as for Gets) suffices. The replay matters for the past-revision
lists only.

**Consequence for the order.** 7d is still worth doing now, as infrastructure:
- porcupine's linearization, with a spec, is needed by any replay, by 7e's design (a) below, and by
  7g (the maintainers' `Replay` takes it);
- the driver's `Check` gets the test's shape;
- the proof pattern is in place.

But 7d alone does not make the closed theorems cover any read they did not already cover. The
plan's sentence "the closed theorems ... should then cover stale reads' contents" holds vacuously
until 7e brings stale lists.

## 2. A soundness trap for the list replay (decide in 7e's Scope; recorded now)

Upstream's replay is sound because the maintainers' model has no failed writes: `Model.Step`
panics on a write error. With only successful writes, each write's answer fixes its resource
version and the key's new object. So the store at each revision is a function of the answers,
whatever linearization porcupine picked. The driver's model keeps failed writes pending (they take
effect later or never). That breaks this independence.

Example:
- Two writes fail: W, which really took effect at revision r, and W2, which did not.
- B, a successful Create at r+1, follows them.
- Porcupine may linearize W2 before B (applied at r) and W after B. B's answer does not depend on
  which write filled r.
- If no later consistent read looks at W's key, nothing refutes this order.
- A list at `Exact` r then returns the real contents (with W's object). No store of the replay at r
  has them (they have W2's), so the replay rejects a correct store.

Porcupine's search order makes this unlikely, but the theorem would be false. Two designs, for 7e:

- **(a)** The test's structure: the model checks a past-revision list's resource version only, and
  the replay along porcupine's linearization checks its contents. This is sound only in runs where
  no failed write took effect. The simplest gate: skip the list contents check when some write of
  the history failed (an `EOther` write). Single-member and cluster runs have essentially none.
  Partition runs have 0-4 per run (`TestPartitionFailures`), so most partition runs would skip.
- **(b)** The history in the model: each configuration keeps its stores by revision, and the
  porcupine step checks a past-revision list's contents in-step. This is sound in every run: the
  real linearization keeps the real history, and porcupine is complete. The replay is again implied
  by porcupine. This departs further from `correctness.Model`'s split (D30m), and the porcupine
  states grow (`Equal` compares the histories).

Recommendation for 7e: (b) if partition coverage matters, which I think it does, since the user
asked for faults. Otherwise (a) with the gate. Not needed for 7d, but 7d's replay is written so
that either works.

**The Get replay of 7d is sound in every run, failed writes included.** At a Get's place in the
linearization, porcupine's step accepted it against some configuration c. The replay records every
configuration's store after every step, so it holds c's store, with `c.st.rv ≥` the minimum (else
`mget` answers `EOther`). That store gives the same answer. The argument is pure and does not
depend on what really happened (§4).

## 3. The Go changes (prototype: the branch's second commit)

**Porcupine (`third_party/porcupine`): unchanged.** The test reads `info.PartialLinearizations()`,
which is upstream's and already translated (`porcupine.toml` lists
`LinearizationInfo.PartialLinearizations`).

**`examples/lib/lintest/lintest.go`:**
- `RunLin(model, apply, gen, clock, clients, ops, timeout) (porcupine.CheckResult, []porcupine.Operation)`
  is new. It is Run's body, then:
  - on `Ok`, it returns the trace's operations in the order of `info.PartialLinearizations()[0][0]`,
    as the test does (`orderByLinearization`);
  - otherwise, or for an empty trace (porcupine then records no linearization), it returns `nil`.
- `orderByLinearization(ops, linearization)` is new, a copy of the test's.
- `Run` becomes `r, _ := RunLin(...); return r`. Its spec is unchanged (§4).
  - The fully additive alternative leaves Run's Go untouched and duplicates its 264-line proof for
    RunLin. Not recommended: no statement differs either way, only Run's translated body.
- Test: `TestRunLinCounter`. The result is the whole trace, accepted in order by the model, real
  time respected; an empty trace gives an empty result.

**`examples/k8s/etcd3/k8setcd3.go`** (the driver's trusted checker grows; D30m):
- `type replay struct{ states []mstore }`.
- `newReplay(st0, lin)` is `NewReplay`:
  - it steps `Model(st0)` along `lin`, keeping every configuration's store after each step, and
    `st0`;
  - it returns `false` if the model refuses a step;
  - `states` is a list, not upstream's map keyed by RV, because a resource version may have several
    stores, one per configuration.
- `(*replay).validate(in, out)` is `Validate` for the driver's reads (Gets):
  - it skips writes, consistent Gets (`MinRV == ""`), and Gets whose minimum does not parse;
  - it skips failed Gets (`EOther`: the driver does not tell the too-large error from the client's;
    upstream skips `IsTooLargeResourceVersion`);
  - otherwise it requires `outEqual(mget(in, st), out)` for some recorded `st` with `st.rv ≥` the
    minimum (`validateGet`'s `state.get(req.Key, opts) == resp`);
  - it leaves out upstream's second, prefix-less comparison, which only the watch cache's
    NotFound needs.
- `replayOk(st0, lin)` runs NewReplay, then validate of each operation in order.
- `Check` calls `lintest.RunLin`. On `Ok`, it panics with "the replay rejected an operation along
  porcupine's linearization" unless `replayOk` holds. It returns porcupine's verdict as before.
  - Why a panic and not `Illegal`: `Main` turns `Illegal` into a panic whose message says "not
    linearizable", which would mislead.
- Test: `replay_test.go`, `TestReplay` (§7).

`Main`, `MainCluster`, `MainPartition` and everything else in the driver are unchanged.

## 4. The specs, old → new

### Porcupine (pure, `Theory.lean`): one definition added

```lean
/-- `π` linearizes `h`: every operation once, run by the model from its initial state, real time
respected. (`Linearizable M h` is `∃ π, IsLinearization M h π`, by definition.) -/
def IsLinearization (M : SeqModel σ α) (h : List (Op α)) (π : List Nat) : Prop :=
  Completes M h (fun _ => False) M.init π
```

### Porcupine (`Defs.lean`): two predicates added

Both are persistent.

```lean
/-- A read-only `[]int` holding a linearization of `h`. -/
def linSlice (M) (h) (sl : GoSlice) : IProp GF :=
  ∃ xs : List w64, sl ↦*□ xs ∗ ⌜(∀ x ∈ xs, 0 ≤ sint.Z x) ∧
    IsLinearization M h (xs.map fun x => (sint.Z x).toNat)⌝
/-- `LinearizationInfo.partialLinearizations` of an `Ok` check of the partitions `hs`: for each
partition its linearizations (a `[][]int`), at least one if the partition is not empty. -/
def linInfoOk (M) (info : LinearizationInfo) (hs : List (List (Op OpV))) : IProp GF :=
  ∃ psls, info.partialLinearizations' ↦*□ psls ∗ ⌜psls.length = hs.length⌝ ∗
    [∗list] i ↦ psl ∈ psls, ∃ lsls, psl ↦*□ lsls ∗ ⌜hs[i]! ≠ [] → lsls ≠ []⌝ ∗
      [∗list] lsl ∈ lsls, linSlice M hs[i]! lsl
```

### Porcupine specs (postconditions strengthened; preconditions unchanged)

- **`checkSingle.spec`**:
  - old: `(⌜b = true ∧ Linearizable S.M h⌝ ∨ (⌜b = false⌝ ∗ (⌜¬ Linearizable S.M h⌝ ∨ □ cs.PDone))) ∗ longestOwn longest h.length`
  - new: `(⌜b = true⌝ ∗ ∃ p sl, longest ↦* replicate h.length p ∗ p ↦□ sl ∗ linSlice S.M h sl) ∨ (⌜b = false⌝ ∗ (⌜¬ Linearizable S.M h⌝ ∨ □ cs.PDone) ∗ longestOwn longest h.length)`
  - The `true` case implies the old one: `linSlice` gives `Linearizable`, and the pointers are an
    instance of `longestOwn`.
  - The Go code sets every `longest[i] = &seq`, and `seq` is the stack's ids oldest first. That is
    `sound_done`'s `(ids fs).reverse`.
- **`checkParallel.spec`**: the post gains `∗ (⌜r = go!"Ok" ∧ cp = true⌝ -∗ linInfoOk S.M info hs)`.
  The old text is kept.
- **`checkOperations.spec`**: the post gains
  `∗ (⌜r = go!"Ok" ∧ verbose = true⌝ -∗ linInfoOk S.M info [histOf ops])`. The model has no
  `Partition` (`isModel`), so there is one partition, and the ids index into `ops`.
- **`CheckOperationsVerbose.spec`**: the post gains `∗ (⌜r = go!"Ok"⌝ -∗ linInfoOk S.M info [histOf ops])`.
  The header loses "LinearizationInfo has no claim".
- `CheckOperations.spec` and `CheckOperationsTimeout.spec` are unchanged. They drop the info, and
  their proofs only adapt intro patterns.
- **New, `LinearizationInfo__PartialLinearizations.spec`**:
  `{{ li ↦{dq} info }} li.PartialLinearizations() {{ RET #info.partialLinearizations'; li ↦{dq} info }}`.

### lintest

- **`Run.spec`: unchanged.** It is proved from RunLin's.
- **New, `orderByLinearization.spec`**: on `ops ↦*□ os` and `lin ↦*□ xs`, with every `x ∈ xs` a
  valid index, it returns `r ↦* (xs.map (os[·]!))`.
- **New, `RunLin.spec`**: Run.spec's binders, premises and precondition, and:

  ```lean
  {{ (r : GoString) (lsl : GoSlice), RET (PairV #r #lsl);
      ⌜r ≠ go!"Illegal" ∧ (sint.Z dur ≤ 0 → r = go!"Ok")⌝ ∗
      (⌜r = go!"Ok"⌝ -∗ ∃ lops : List Operation, lsl ↦*□ lops ∗ opsIoOk S lops ∗
         ⌜lops.length = (sint.Z clients * sint.Z ops).toNat ∧
          IsLinearization S.M (histOf lops) (List.range lops.length)⌝) }}
  ```

  This says that on `Ok` the result holds all `clients*ops` operations. In its own order it is a
  linearization of itself: the model runs it from its initial state, and no operation returns
  before an earlier one is called.
  - The trace is not named in Run's spec, so "a permutation of the trace" is shown by the length
    and by the code, not stated.
  - Alternative: `∃ hist π, IsLinearization S.M hist π ∧ lops = π.map (hist[·]!)` with
    `hist.length = clients*ops`. It is equivalent for a client, and wordier.

### The driver (`Spec/.../k8s/etcd3/`)

- **`Check.spec`: text unchanged.** The post is still `r ≠ Illegal ∧ (dur ≤ 0 → r = Ok)`, so "no
  panic" now includes the replay. Only the header changes.
- **New, `replayOk.spec`**:

  ```lean
  {{ storeOwn s0 g0 ∗ lsl ↦*□ lops ∗ opsIoOk (k8setcd3S g0) lops ∗
     ⌜IsLinearization (kSpec g0) (histOf lops) (List.range lops.length)⌝ }}  -- (the model's M)
    replayOk #s0 #lsl
  {{ RET #true; storeOwn s0 g0 }}
  ```

  This says the replay accepts every sequence the model accepts: the redundancy of §1, stated.
  Only `run`'s part of the premise is used. 7e changes this spec when lists come.
- **New, `newReplay.spec`, `replay__validate.spec`**:
  - `replayOwn rp sts` is the `states` list, with `storeOwn` of each;
  - newReplay gives `sts = replayStatesL g0 (lops vals)`;
  - validate returns `validateL sts x y`.

## 5. The replay's model in Lean, and KModel/Refine

There is a new file, `Proof/.../k8s/etcd3/Replay.lean`, pure:
- `replayStatesL g0 xs : List GSt`. It is the stores of the configuration lists along `xs`, as the
  Go model's `Step` computes them: KSteps' `stepAllL`, closure and `setOf`. The list starts with
  `g0`.
- `validateL sts x y : Bool`, the Go `validate`.
- `replay_accepts`: if `(run (kSpec g0).M init (xs)).isSome`, then for every `(x, y) ∈ xs`,
  `validateL (replayStatesL g0 xs) x y`. Its key step, for a Get at position k: the step from `S_k`
  succeeded, so some `c ∈ S_k` has `mgetL x c.st = y` (KSteps' `stepL_sound`/`stepL_complete`),
  and `c.st` is recorded. Writes and skipped Gets are trivially accepted.

It reuses KModel's `mgetL`, `mstepL` and `kSpec`, and KSteps' configuration lemmas. **It needs
nothing from Refine** (the store's `KSt` against the driver's model): the replay is about the
porcupine model alone, not about etcd.

## 6. Premises, the trust base, the closed theorems

- **New premises: none.** `replayOk`'s premise is produced by RunLin's post. RunLin's is produced
  by `CheckOperationsVerbose`'s, which is produced by `checkParallel`'s and `checkSingle`'s
  (`sound_done`, already proved). `PartialLinearizations` is a field read.
- **Trust base**: no axiom or `sorry` added or removed. **The trusted text grows**: the driver's Go
  `replay`/`newReplay`/`validate`/`replayOk` (~70 lines) join the Go model as the trusted copy of
  the maintainers' checker (D30m), until 7g translates the real `Replay`. lintest's `RunLin` and
  `orderByLinearization` are verified code, not trusted.
- **Closed theorems: no statement changes.**
  - `k8s_etcd3_safe`, `k8s_etcd3_cluster_safe` and `k8s_etcd3_partition_safe` keep their text.
    Their programs now run the replay inside `Check`, so "no panic" includes "the replay accepted".
  - Every other theorem over `lintest.Run` keeps its text and proof, via the unchanged `Run.spec`.
    These are `kv_porcupine_safe`, `raft_kv*_porcupine_safe` (kv, kvdurable, kvreconf, kvwitness),
    `etcd_txnlin_safe`, `etcd_partition_safe`, restart's `Main`, and the lintest counter/logkv*
    adequacies. Their programs' translated `Run` changes (it calls RunLin), and they are re-checked
    by the build.
  - **Exported/frozen statements that change**: the five porcupine specs above, each a
    strengthened post with the same preconditions. Two specs are new (`PartialLinearizations`,
    `orderByLinearization`, `RunLin`, and the driver's three).
- **The PorcupineDag part**: untouched (its own copy, its own specs). Its `CheckOperationsVerbose`
  spec then says less than the main one. A matching change there is optional and not part of 7d.
- `etc/gen-link.py --porcupine/--lintest/--k8setcd3` gain the new functions. The `k8setcd3`
  collection's axioms are unchanged. Translations are regenerated with `etc/goose.py --project
  lintest`/`k8s-apiserver`.

## 7. The Go check (done; under `systemd-run --scope -p MemoryMax=32G`, `GOWORK=off`)

- **lintest**: `go test ./...` in `examples/lib/lintest` passes, including the new
  `TestRunLinCounter` and the existing counter and logkv* tests.
- **The driver**: the full `go test -v` of `examples/k8s/etcd3` passes in 87s. This covers:
  - every cluster test, in its own process (`inChild`), with the replay inside `Check`:
    `TestMainLinearizable`, `TestMainCluster`, and `TestMainPartition`'s five schedules (drop,
    mixed, isolate, election, blackhole), all `Ok`;
  - `TestPartitionFailures` (1-4 failed writes per schedule in that run);
  - the unit tests.
- **`TestReplay`** (new, in its own process) uses Main's member, client, seeds and store, then
  `RunLin` of 8 clients × 250 operations, then the replay:
  - the real history: `Ok`, 2000 operations, 265 Gets, 180 of them validated by the replay
    (minimum set, no error), 0 failed writes; the replay accepts;
  - **corrupted to a stale read**: one non-consistent Get's answer is replaced by the answer of a
    store below its minimum, which no store at or above the minimum gives. In the recorded run,
    `Get a` with minimum 9 had answered `{a, "z", RV 9}` and was corrupted to `{a, "x", RV 2}`, the
    seeded object. **The replay rejects it.** Porcupine (`CheckOperations` on the corrupted
    sequence) also rejects it, which is §1's redundancy;
  - **corrupted to an answer no store held** (a value never written): both reject.

### 7a. Repeated runs

`go test -count=3` of `TestMainLinearizable`, `TestMainCluster`, `TestMainPartition` (all five
schedules) and `TestReplay`: all pass (128s); with the first round, the theorem's partition program ran
20 of 20 schedule runs `Ok` with the replay inside `Check`, and `TestReplay` 4 of 4 (171-204 Gets
validated by the replay per run, both corruptions rejected every time).

## 8. Stages, checkpoints, estimate

1. **7d-1, porcupine returns its linearization** (`Theory`/`Defs` additions, `checkSingle`,
   `checkParallel`, `checkOperations`, `CheckOperationsVerbose`, `PartialLinearizations`; Link).
   - `checkSingle`'s exit already sets every `longest[i]` to the persistent `seq` and has
     `sound_done`; what is new is the content relation of `seq` to the stack.
   - `checkParallel`'s `computeInfo` branch carries the linearization for each set key.
   - ~350-450 lines. **Checkpoint**: porcupine builds, and `CheckOperationsVerbose.spec`'s new post
     is proved. Report the diff of the five specs.
2. **7d-2, lintest**: `orderByLinearization`, `RunLin` (Run's proof moved, plus the linearization
   part), `Run` from RunLin, Link, translation. ~200-300 lines. **Checkpoint**: every lintest user
   still builds, statements unchanged.
3. **7d-3, the driver**: `Replay.lean` (pure, ~150-250 lines), `newReplay`/`validate`/`replayOk`
   specs and proofs (~250), `Check`'s proof (~50), Link, translation, gen-init if needed.
   **Checkpoint**: `k8s_etcd3{,_cluster,_partition}_safe` rebuilt with unchanged text, and
   `tcb-report --check` and the `k8setcd3` collection unchanged. Then the Freeze package.

Estimate: ~1000-1300 lines of Lean, about 2-3 agent-days, the porcupine part the riskiest (the map
over pointer keys in `checkParallel`). Builds: porcupine and lintest are cheap. The driver's
modules sit above the server stack, so `Check` and everything up to `Results` rebuilds (targeted,
under the 64G cap).

## 9. Interaction with the work in flight

- **c9's per-type branch** (`per-type-proto`, `per-type-models`) rewrites `InvProto`, `InvGrpc`, the
  client's `PerType*` and `pbutil`. 7d touches none of these. The only shared file in either diff
  is `cluster3/SchedLit.lean`, which 7d does not edit.
  - The driver's `Check.lean` imports the server stack transitively, so whichever lands second
    rebuilds the driver's top modules. A textual conflict is unlikely: 7d-3 changes `Check.lean`'s
    proof (its use of RunLin and replayOk), not its use of the store or client specs.
- **Sweep repairs 1** (`sweep-repairs-1`, the server, zap, WAL, the start contract): no file in
  common. `k8s_etcd3*_safe` keep their premises in 7d. If R1-4a/L4 change those premises, that is
  their change, and 7d does not touch the premises.
- **Order**: 7d-1 and 7d-2 are independent of everything in flight and can land on their own.
  7d-3 is best landed after any per-type landing that rebuilds the driver, to rebuild once.

## 10. Decisions asked of 81

- **Q1.** Proceed with 7d although it adds no read coverage now (§1)? Recommendation: yes, as
  7d-1..3. Porcupine's linearization is needed by 7e(a) and 7g.
  - Alternative: do only 7d-1/7d-2 now, and fold the driver's replay into 7e.
- **Q2.** Keep the driver's strict `mget` (every Get's contents checked in-step, a stronger theorem),
  rather than weaken it to upstream's RV-only `validateGet`, which would give the replay real work?
  Recommendation: keep it strict. Weakening loses strength (upstream's replay accepts any state at
  or above the minimum, even a future one) for fidelity only.
- **Q3.** `Run` refactored to call `RunLin` (recommended) vs. RunLin added with Run's Go untouched
  (fully additive, ~260 lines of duplicated proof). No statement differs either way.
- **Q4.** The RunLin post's form: `IsLinearization S.M (histOf lops) (range)` plus the length
  (recommended) vs. the existential over the trace.
- **Q5.** For 7e, recorded now (§2): the list replay with failed writes. (a) gated, or (b) the
  history in the model. Recommendation: (b), decided in 7e's Scope.
- **Q6.** The replay failure panics in `Check` (recommended), not returning `Illegal`, which `Main`
  reports as "not linearizable".
