# Review round 1: the informer API, the controller's lifecycle, the driver (tracks A and C)

Reviewer: a fresh spec reviewer, 2026-11-04. Read-only. State reviewed: `HEAD` `0e4d57dcaa`, plus the
working tree's uncommitted edits as they stood during the review. Track B was editing
`daemon/Defs.lean`, `SyncDefs.lean`, `S1Inv.lean` and the sync-path specs while I read, and
`isDsc`'s `Hunamb` (R8) is uncommitted. Go sources:
`k8s.io/client-go@v0.0.0-20261021054439-569675c57fa3` (`informers/factory.go`,
`informers/apps/v1/daemonset.go`, `tools/cache/{shared_informer,controller,thread_safe_store}.go`,
`listers/apps/v1/*`), and `k8s.io/kubernetes@v1.38.0-alpha.2.0.20261021173803-878cfa6c4cc7`
(`pkg/controller/daemon/daemon_controller.go`, "DC" below; `pkg/controller/controller_utils.go`,
"CU"). Also `examples/k8sdaemonset/{dsmain,apimodel}`. I judged by `.claude/skills/spec/PRINCIPLES.md`,
with `apply-uber-contract.md` (callback contracts), `reply-size.md`/`watch-compaction.md` (who
carries a workload premise) and `c3-store-law.md` (a predicate fixed at creation).

Every spec reviewed is a Lean-first stub (`sorry`), except `runWorker`/`runNodeUpdateWorker`
(proved glue) and the laws in `InformerApi.lean`/`Reader.lean` (proved). So "the proof needs X"
below is my reading of what each proof must do. It is not a failed proof.

## Summary of findings, by severity

| # | Severity | Target(s) | Finding |
|---|---|---|---|
| H1 | hard rule (sound), in progress | `NewDaemonSetsController` (working tree) | The post gives `isDsc`, which now carries `⌜cfg.AmbiguousWrites' = false⌝`, but the pre has no such premise. So the spec is false at Main's `dsCfg`, and `Pending.lean`'s `daemon_NewDaemonSetsController_pending` supplies a `sorry` from which `run`'s proof can derive `False`. That hides the known stuck point. |
| H2 | hard rule (complete; one callee spec false) | `RunWithContext`, `infRunOk`, factory `Start`/`StartWithContext`, `NewSharedIndexInformerWithOptions`; `newQueueFIFO` | No client-facing informer spec carries the feature gates that the run path reads (`InOrderInformers`, `AtomicFIFO`, `WatchListClient`). `newQueueFIFO.spec` promises a `RealFIFO` without them, which is false when `InOrderInformers` is off. `gatesSet` lacks `InOrderInformers`. |
| H3 | hard rule (complete) | `NewDaemonSetsController` | `isDsc`'s `isCons … (getterContract c)` needs the pod store's `LastStoreSyncResourceVersion` contract. That spec takes `features.gateIs AtomicFIFO true`, and the constructor's pre does not have it. |
| H4 | hard rule (complete), likely | `evFacts` (`.delete`), for `deleteDaemonset` | `goneAfter` never says that the deleted object's UID was at its key. So `Clear(owner, uid)` can be neither shown harmless (`clear_noop`, `clear_notfound_noop`) nor refuted. Go gives more, and the fact is cheap to state. |
| M1 | locality + complete | `isFactory`'s `Fams`, `AddIndexers`, `NewDaemonSetsController`'s `podFamOk` and `podCtlIndexed` | Index relations are numbered and fixed by the factory's creator. (a) Main must know the controller's private index relations. (b) `AddPodControllerIndexer` skips a name that already exists (CU:1158), so `podCtlIndexed` cannot be proved if anyone registered `podController` earlier. |
| M2 | sound, not marked | `dsmain.run`, `Main`, `Adequacy.lean`'s docstring | `run.spec` (`∀ cfg`) is false at `AmbiguousWrites = true`, and nothing says so. Under R8 the premise belongs on `run`, and the false step is `Main`'s call. The Adequacy docstring is stale: it still names `syncNodes`' branch. |
| M3 | complete (proof feasibility) | `getDaemonSetsForPod` (and `addPod`/`updatePod` through it) | DC:451 is a reachable `fmt.Errorf("… %+v", pod.Labels)` with a `map[string]string` argument, which `fmt.argOk` cannot take. Same class as review-1-sync's M2. |
| M4 | closed theorem's premises | `metrics.Register`, `dsonepod_safe` | `MustRegister` panics on a taken name. The spec says "returns" with no premise, and the theorem has no `namesUnclaimed` premise (k8setcd3 has one). `Pending.lean` hides it. |
| M5 | abstraction, coupling | `isInformer`/`evFacts` (scope), `isDsc`'s `infAt`/`podCtlIndexed`, `Lister()` | Not marked: the informer API is fixed to the model API server. `isDsc` restates `infView`'s body (`isCache ∗ infInv`) and reads the raw index registry. `Lister()` hands out the lister struct's field. |
| L1 | unneeded premise (model) | `keysOk` (factory, informer) | A property of every writer's keys. The model does not validate names (kube-apiserver rejects `/`). If the model did, this would be a law of `apimodel`. |
| L2 | bounds | `infReaders`, `NewDaemonSetsController`, `Main`/`run` | `infReaders`' `□ (⌜threadBound ≤ …⌝ → ∃ pool)`, and `threadBound` in client-facing specs (`etc/bounds-check.py --check` fails on them). |
| L3 | margin | factory `Start` | It uses up all four tokens. A second `Start` and handlers on an informer made after `Start` (both allowed in Go, factory.go:313-316) are outside the spec. This is fine for Main but should be stated. |
| L4 | trust, conditional | `NewTyped*InformerWithOptions` (gap D2), `InformerFor`, `setFeatureGates` | If D2's body stays a hypothesis, `isInformer`'s reader pool comes from a trusted statement. `InformerFor` needs a stronger `reflect.TypeOf` axiom. `setFeatureGates` rests on a gate model that does not exist yet (gap C7). |
| L5 | shape | `handlerSpec`'s `H` | A caller predicate stored in an invariant (HoCAP). It is acceptable as a callback contract (`apply-uber-contract.md`), but its only client uses `H := True`. Say that it departs, or drop it. |
| L6 | docs | `LifeDefs.lean` header, README R6, `Adequacy.lean` | Stale text (below). |

## What is good

- **The not-started token and the deferred handler contract (R6, R7) are sound and small.**
  `nsAlloc`, `nsLock_agree`, `nsLock_start`, `handlerPending_activate` and `handlerCell_started` are
  proved (`InformerApi.lean:178-363`). A pending handler keeps its fraction until it is activated,
  and `RunWithContext` needs the whole token, so no informer can start with a handler whose contract
  is missing. This matches Go: before the start, `AddEventHandlerWithOptions` cannot fail, because
  `stopped → started` (shared_informer.go:1023-1031, `siiLocked`'s `⌜stopped = true → started = true⌝`).
  It also lets the controller prove its handlers after `s1Inv` exists, which it must.
- **`apiReader` is the right shape for read access** (`Reader.lean`). It is a persistent
  `|={⊤,∅}=> ∃ σ, apiState γ σ ∗ (apiState γ σ ={∅,⊤}=∗ True)`, so a read cannot change the state,
  and the owner's laws are proved (`apiReader_of_inv`, `_past`, `_read`). The informers need nothing
  of S1, and `s1Reader` is the same shape plus S1.
- **The delete facts do not overclaim.** A watch `Deleted` event carries the object at the
  deletion's version, which no table ever holds (`apimodel/server.go:299-308`; `doc.go:36-37`). So
  `evFacts.delete` correctly avoids `inLog`, and `goneAfter`'s "absent at `v ≥` its version" is true
  for watch deletes and for relist tombstones. H4 asks for a different fact, not that one.
- **The controller's handlers have a good split.** Each closure's callee takes the event's facts
  (`evFacts`). `deletePod`/`deleteHistory` take the weaker `delArg`, which every caller (the delete
  handler, and `addPod`/`updatePod` with the pod itself, DC:591-595) can supply. The swapped
  arguments of `updateDaemonset` (DC:233 vs DC:302) are named as the event names them, and the bug
  is filed (`nonissues/k8s-daemonset-updatedaemonset-swapped-args.md`).
- **`Run`'s thread accounting is right.** The caller's token comes back. Every `wg.Go` goroutine runs
  on the fork's fresh token (`wp_fork_tok`). There is no bound on `workers`: at zero fuel, `Fork`
  stutters, which partial correctness allows. A handler borrows its listener goroutine's token
  (`lhOk`). That token comes from the processor's fork, not from an axiom.
- **The closed theorem has the required shape.** Its program is the generated initializer then
  `Main` (`dsProgram`). Its premises are pure and satisfiable: `IsInit`, one thread,
  `n + 2 ≤ 2^30 − 1`, as k8setcd3's `n + 2 ≤ 2^28`. Its conclusion (no thread panics or is stuck,
  main returns `#()`) covers what `TestMainNeverPanics` checks, which is the checker's panic. It is
  stronger in two respects: it covers every `nchk`, and every goroutine after `Main` returns. The
  test's `klog.SetLogger(logr.Discard())` (dsmain_test.go:25) is not part of the program, so the
  theorem covers the default logger too.

## H1. `NewDaemonSetsController`'s post asserts no ambiguous writes from nothing (working tree)

`isDsc` now has `"%Hunamb" ∷ ⌜cfg.AmbiguousWrites' = false⌝` (`daemon/Defs.lean:232`, uncommitted).
`NewDaemonSetsController.spec`'s pre (`Spec/.../NewDaemonSetsController.lean:67-73`) has
`clientIs kc γa cfg` for any `cfg`, and no premise on the flag. Go's constructor returns
`(dsc, nil)` whatever the model's configuration is (DC:158-294). So the spec is false at any `cfg`
with the flag set, and Main's `dsCfg` sets it (`dsmain/Defs.lean`, `⟨true, true, …⟩`; dsmain.go:51-54).

The danger is in `Pending.lean`. `daemon_NewDaemonSetsController_pending` is a `sorry` for this
spec. `run`'s proof calls the constructor at `dsCfg`, gets `⌜true = false⌝`, and closes every later
goal. So the theorem would rest on a quiet, false pending spec, not on a named stuck point.

**Restatement.** Do what README's R8 says: add `⌜cfg.AmbiguousWrites' = false⌝` to the
constructor's pre. The false obligation then surfaces at the caller (M2).

## H2. The informer run path's feature gates are on no client-facing spec

What Go reads:

- `newQueueFIFO` builds a `RealFIFO` only if `InOrderInformers` is on, with atomic events only if
  `AtomicFIFO` is on; otherwise it builds a `DeltaFIFO` (controller.go:1084-1114).
- The reflector reads `WatchListClient` (reflector.go:361). `RefInf.reflFixed1` fixes
  `useWatchList ↦□ false`.
- `controller.processLoop` reads `InOrderInformersBatchProcess` (controller.go:241).

What the specs say:

- `newQueueFIFO.spec` (`Spec/k8s_io/client_go/tools/cache/newQueueFIFO.lean`) promises
  `RET … RealFIFO …` with no gate premise. Its docstring says "with the gates … on (Main's)", but no
  premise states it. Its proof file lists the gates as "missing callee specs (next round)". As
  stated, the spec is false: with `InOrderInformers` off it returns a `*DeltaFIFO`.
- Its callers carry no gate either: `RunWithContext.spec`, `infRunOk`, `isInformer`,
  `NewSharedIndexInformerWithOptions.spec`, `isFactory`, and `Start`/`StartWithContext`. Main's
  proof has the gates (`gatesSet`, from `setFeatureGates`) but has no spec to pass them through.
  Once the informer's proof is written, every one of these statements must grow.
- `gatesSet` (`dsmain/Defs.lean:68-71`) has `AtomicFIFO` and `WatchListClient`, but not
  `InOrderInformers`. GateDefs' header says that gate is "GA and locked on", but nothing gives it.

**Restatement.** Define one persistent `informerGates` in `features` (or `cache`):
`gateIs InOrderInformers true ∗ gateIs AtomicFIFO true ∗ gateIs WatchListClient false`, with
`InOrderInformersBatchProcess` and `UnlockWhileProcessingFIFO` at any value, as `processLoop` and
`newQueueFIFO` already allow.

- Take it once, where the informer is produced (`NewSharedIndexInformerWithOptions`, so
  `NewTyped*InformerWithOptions`, so `newInfFnOk` and `NewSharedInformerFactory`). Carry it in
  `siiAt`, so that `infRunOk`, `Start` and `RunWithContext` keep their signatures. This is the
  "premise on the resource's only producer" rule.
- Give `newQueueFIFO.spec` the premise.
- Add `InOrderInformers` to `gatesSet`, together with whatever gate model gap C7 settles on.

## H3. The constructor cannot establish the consistency store's getter contract

`isDsc` holds `∃ S, isCons c.cons c.γc (ownerTok c) S (getterContract c)` (`Defs.lean`). `isCons`
needs `getterOk v (G gr)` for each getter (`consistency/Defs.lean:365`), and the pod getter's
contract is `infRvLb c.podI.γi (decVal rv)`. In Go the getter is `podInformer.Informer().GetStore()`
(DC:172-174), and its `LastStoreSyncResourceVersion` spec takes
`features.gateIs AtomicFIFO true` (`cache__LastStoreSyncResourceVersion.lean`). The constructor's
pre has only `dsGateIs StaleControllerConsistencyDaemonSet true`. So the post cannot be proved
from the pre.

There is a second missing piece: a law turning the store's `storeSt` version into `infRvLb` of the
informer. That law is internal to `InformerInv`.

**Restatement, per "a contract states the receiver's need".** Put the contract on the informer API.
Add a conjunct to `isInformer`: the store value's `LastStoreSyncResourceVersion` returns `rv`,
well formed or empty, with `infRvLb γi (decVal rv)`. Carry the gate inside that conjunct, as in H2.
The constructor then neither takes the gate nor reads `infInv`. Otherwise, add the gate premise to
`NewDaemonSetsController` (Main has it in `gatesSet`).

## H4. `evFacts.delete` is too weak for `deleteDaemonset`

`deleteDaemonset` fires `Clear(owner, ds.UID)` inside `s1Inv`. Its docstring says the owner with
that UID is dead. The step lemmas need, at the current `σ`, one of two things:

- `clear_noop`: no DaemonSet at the owner, or `uid ≠ []` and the stored one's UID differs.
- `clear_notfound_noop`: the DaemonSet was added after `Ld` (`S1Steps.lean:540-573`).

`evFacts.delete` gives `infObjIs γi r y o ∗ goneAfter γa r o`: the key is absent at some version
`v ≥ o`'s version. Nothing says that `o.UID` was ever at the key. So:

- Take a scenario where the DaemonSet is created at `c > v` with UID `u`. A registered `o` with
  UID `u` and version `≤ v` satisfies `goneAfter`, and `Clear` would wipe the live record. The
  record can exist: `Ld` (the DS informer's lower bound) can pass `c` before the listener delivers
  the old notification, because listeners are buffered.
- In the general model, the "UID is dead" argument needs the UID to have existed at the key before
  `v`, and the facts do not give that.
- `infObjIs` does not tie `o` to the log, and no exported law of the registry does either (the
  registry's tie to the log is in `infInv`, internal).

Go guarantees more:

- A watch `Deleted` event's object is the stored object at the deletion's version `n`. Its key holds
  that UID at `n − 1` (`server.go:296-308`: `obj := copyObject(stored)`, recorded as `Deleted` at `n`).
- A relist tombstone's object is the store's last object, a logged version.

In both cases the object is the object of a change of the log.

**Restatement.** Add to `.delete` the fact that `o` is the object of a change of the past state's
log, in track B's `dsSeen` shape (`SyncDefs.lean:82-83`):
`∃ σp, pastSt γa σp ∗ ⌜∃ ch ∈ (σp.tbl r).log, ch.obj = o⌝`.

- Combined with `goneAfter`: a change carries `o.UID` at `o.RV ≤ v`, and the key is absent at `v`.
  The UID was deleted, and model UIDs are fresh, so `clear_noop` applies.
- In the scenario (no DaemonSet deletes), it contradicts `sceneOk`, so the branch is dead, as the
  docstring wants.
- The same fact is true of `.add` and `.update`, and would let one name (`seen γa r o`) replace
  `inLog`.

Uncertain only in that the proof is a stub. I found no route through the current facts.

## M1. Index relations: numbered, fixed at the factory, and the constructor's post

`isFactory f γF γa cfg Fams` fixes `Fams : Res → Nat → Fn GF` at `NewSharedInformerFactory`.
`AddIndexers` takes caller-chosen ids `nids` with `fnsOk … (GMap.fmap Fam nids)`, and
`NewDaemonSetsController` takes `⌜podFamOk (Fams .pods)⌝` (`∃ j1 j2, Fam j1 = podNodeFn ∧ Fam j2 =
podCtlFn`). There are two problems.

**(a) Locality.** The factory's creator (`run`) must choose a family that holds the DaemonSet
controller's two private index relations (`LifeDefs.podNodeFn`/`podCtlFn`). A change to the
controller's indexers changes Main's proof.

**(b) Completeness.** Go's `AddPodControllerIndexer` returns `nil` without adding when the name
already exists (CU:1157-1161; likewise `AddPodNodeNameIndexer`, CU:1126-1130), whatever function is
registered there. The constructor's post `podCtlIndexed` claims the `podController` index computes
`PodControllerIndexKey`. If another client registered `podController` with another relation before
(possible: the factory is shared and only the not-started token is required), that cannot be proved.
No premise excludes it, and the API has no predicate for "no such index". The constructor docstring's
"R6's not-started fraction gives the former" is not right. The fraction rules out "stopped", not a
name conflict.

**Restatement.** Key the relations by index name: `Fams : Res → GoString → Fn GF`.

- `AddIndexers`/`NewSharedIndexInformerWithOptions` take `fnsOk (infObj γi r) nfv (fun n => Fams r n)`
  on `nfv`'s names.
- `infIdx I n` has no id.
- `podFamOk` becomes `Fams .pods podCtlIndex = podCtlFn ∧ Fams .pods podNodeIndex = podNodeFn`.

Every registration of `podController`, by anyone, then has the controller's relation, so the skip
path is fine, and `nids` goes away. This is the approved departure (a persistent predicate fixed at
creation, `c3-store-law.md`): index names are a global convention in client-go, and Go itself trusts
the name. Say that it departs. (a) shrinks to Main stating one equation per controller index; I see
no faithful way to remove it.

## M2. `run.spec` is false at Main's configuration, and nothing says so

`run.spec` quantifies over every `cfg` and promises no panic. At `cfg.AmbiguousWrites' = true`, Go
refutes it: `TestAmbiguousWritesDetected` caught the checker panicking in 5 of 200 runs (README,
"Driver gate 1"). Its docstring and `Main.lean`'s say nothing about this. R8's own argument (a
`sorry` inside a spec leaves a false spec under its callers) applies to `run.spec` too.

`Adequacy.lean`'s header still says "the ambiguous create's branch of `syncNodes` is the one place
its proof cannot pass". R8 superseded that.

**Restatement.**

- `run.spec` takes `⌜cfg.AmbiguousWrites' = false⌝`, a scope restriction marked and filed (the
  issue).
- `Main.wp_proof` is the one place that is false: `run(serverConfig())` with
  `dsCfg.AmbiguousWrites' = true`. It is a named `sorry` there, beside `ambiguous_create_breaks_S1`.
- Update `Adequacy.lean`'s and `Main.lean`'s docstrings.

`TestScheduled` and the other drivers of `run` are unaffected.

## M3. `getDaemonSetsForPod` formats a map

DC:449-452: when more than one DaemonSet selects the pod's labels,
`utilruntime.HandleError(fmt.Errorf("user error! … %+v", pod.Labels))`.

- `fmt.argOk` admits only `nil`, `ArgWf` (basic types, `fmt/Base.lean:517`) or values with an
  `Error`/`String` method. A `map[string]string` is none of these.
- The spec's pre is `isDsc ∗ threadTok ∗ □ podAt pod …`, with no `s1Inv`/`sceneOk`. So two
  DaemonSets in the namespace with overlapping selectors reach the call.
- The callers are `addPod`/`updatePod`'s orphan paths.

**Restatement.** A local trust-boundary spec of `fmt.Errorf` with `%+v` of a string map (fmt prints
it without calling a method), as track B did for `%#v` of a DaemonSet (`ErrorfDaemonSetV.lean`,
uncommitted), with an entry in `notes/perennial-changes.md`. Alternatively, a premise on the spec,
but `addPod` cannot supply one without `sceneOk`.

## M4. A metric registration that can panic, and no premise for it

`metrics.Register()` (DC:292) does `legacyregistry.MustRegister(DaemonsetRequeueSkips)` once
(`metrics/metrics.go:44-48`). `MustRegister` panics on a name already registered.
`dsmetrics.Register.spec` promises "returns" with no premise; its docstring calls this open.

`dsonepod_safe` has no premise like k8setcd3's
`HNs : prometheus.namesUnclaimed (k8setcd3Program …) k8setcd3Names` (`k8setcd3/Adequacy.lean:124`).
So once `metrics.Register` is proved, either the theorem gains a premise or a fact of the initializer
must discharge it. `Pending.lean` hides this, because the controller's constructor is a `sorry` there.

**Restatement.** Give `dsmetrics.Register.spec` the registration right as a premise. Have
`NewDaemonSetsController` take it from its caller, so that the closed theorem takes
`namesUnclaimed (dsProgram nchk) [daemon_controller_requeue_skips…]` (pure, decidable over the
program), as k8setcd3 does.

## M5. Abstraction and coupling

- **The informer API is about one fake server.** `isInformer`, `evFacts`, `isFactory`, `lwOk` and
  `keysOk` are in `apimodel`'s terms (`ApiNames`, the four `Res`, `apimodel.St`'s logs,
  `clientsetAt`). A client of the real API server cannot use them. This is a reasonable scope for
  the run, but say so in `InformerApi.lean`'s and `informers/Defs.lean`'s headers as a scope
  restriction (review-1-sync's M3 made the same point for `pkg/controller`).
- **`isDsc`'s `infAt γa r I Fam` (`Defs.lean`) is `infView`'s body, copied.** It is
  `isCache … ∗ infInv …` over `InfLoc`, so the controller's predicate names the informer's internal
  invariant. `podCtlIndexed` reads the raw registry `podCtlIndex ↪[I.γi.ix]□ j`, not `infIdx`.
  Write `infView γa r I.h Fam` and `infIdx I.h podCtlIndex j`. With M1, the latter becomes
  `infIdx I.h podCtlIndex`. The four `InfLoc.res` fields belong to the listers (`riVal`), not to the
  informer's names.
- **`Lister()`'s post hands out the lister struct's field** (`ll.[daemonSetLister, "ResourceIndexer"]
  ↦ listers.riVal I.ca res []`, exclusive), and `isDsc` then stores it. A listers-package predicate
  (`isDsLister ll I` with its `Get`/`List` contracts) would hide `ResourceIndexer`'s layout from
  `daemon`.
- No `etc/api/` list or `interface/` exists for client-go's informers or `daemon`, so none of this is
  enforced. Every unfold of `infInv`/`isCache` in `daemon/` is a missing law of the informer API.

## L1-L6

- **L1 `keysOk`.** "Every state the server reaches has good keys" (`RefInf.lean:309-311`) is taken
  by the factory and the informer constructor. It is a property of every writer. Main can prove it
  from `sceneOk`, so it is not wrong. The cleaner source is the model: kube-apiserver rejects `/` in
  names, and the model does not validate names (`doc.go:22-28`, no check in `server.go`). If the
  model rejected `/`, `keysOk` would be a law of `apimodel`, and client-go's specs would lose a
  premise.
- **L2 bounds.** `infReaders` is `□ (⌜threadBound GF ≤ 2^30 − 1⌝ → ∃ γp, isThreadPool …)`. Each use
  needs the bound, and two uses need not agree on `γp`. The owner (the informer's constructor) should
  take the bound once (`[ThreadBoundLe GF (2^30 − 1)]`, as `NewWatchFromWatchClient` does) and give an
  unconditional pool. `NewDaemonSetsController`, `Main` and `run` mention `threadBound`;
  `etc/bounds-check.py --check` now fails on `spec-thread` (dsmain 2, daemon 1) and `spec-receipt`
  (dsmain 2). The README records this for Stage 6.
- **L3 `Start`'s margin.** It uses up all four resources' tokens, including those of informers not
  made yet. So a second `Start` and handlers on an informer created after `Start` are outside the
  spec. Go allows both: factory.go:313-316, and `AddEventHandlerWithOptions` after the start,
  shared_informer.go:1061-1087. One sentence in the docstring.
- **L4 trust, conditional.**
  - `NewTyped*InformerWithOptions` is names only (gap D2), with "its body a named hypothesis to
    come". If that hypothesis ever stands in for the body, `isInformer`'s `infReaders` (a pool of
    the store lock's reader slots) would come out of a trusted statement. That breaks "a trusted
    statement never gives out a counted resource". R3's regeneration must close D2 before the
    informer's proof relies on it.
  - `InformerFor` needs `reflect.TypeOf` to be deterministic and injective on the four types, which
    is stronger than `Spec/reflect/TypeOf.lean` (its docstring says so). List the collections that
    would rest on it.
  - `setFeatureGates.spec`'s persistent `gatesSet` over mutable gates rests on a gate model that
    does not exist yet (gap C7). Go panics if `SetFromMap` errors (dsmain.go:68-74). The tests show
    it does not today, but the spec does not say why.
- **L5 `handlerSpec`'s `H`.** `handlerPending`/`handlerCell` store the caller's `H : List Ev → IProp`
  in an invariant, which is HoCAP. A callback contract parametric in the client's state is the
  approved form (`apply-uber-contract.md`), but its one client uses `H := fun _ => True` (the thread
  token now goes through `lhOk`). Either say that `H` departs and why (a handler that keeps state in
  order), or drop it and keep the contract over `threadTok` alone.
- **L6 docs.**
  - `LifeDefs.lean`'s header still offers both "`H evs := threadTok`" and the listener-token form;
    R7 chose the latter.
  - README R6 says "`Informer()` hands out the callers' part". The factory's constructor does
    (`NewSharedInformerFactory.spec`).
  - `Adequacy.lean`: `dsGF`'s docstring mentions "the counter's `counterGF`'s". The header's
    stuck point predates R8 (M2).
  - `NewDaemonSetsController`'s "Open" paragraph claims the not-started fraction ensures
    `AddIndexers` succeeds (M1).

## The closed theorem, the questions asked

- **Does it say what the Go test checks?** Yes. `TestMainNeverPanics` fails on any panic in `Main`,
  and the checker's panic is the S1 check (dsmain.go:132-136). The theorem excludes a panic in every
  thread, adds "not stuck" and main's `#()`, and covers every `nchk`. It is partial correctness
  (`TestScheduled`'s liveness is not claimed), as the README says.
- **Are the premises pure and satisfiable?** Yes: `IsInit σ`, `σ.threads = 1`,
  `n + 2 ≤ 2^30 − 1`, `RealNsteps`, and the generated `dsmain.Assumptions` instance
  (`Code/.../dsmain.lean:660`). The one missing pure premise is M4's `namesUnclaimed`.
- **The rule (generated initializer then Main, only pure premises)** holds: `dsProgram` is
  `initialize' #() ;; Main #nchk`, and the proof is `init_adequate` with `wp_initialize'` and
  `wp_Main_closed`. Like k8setcd3's, it says nothing about executions longer than about 2^30 steps,
  because the thread bound is tied to `n`.
- **What `Pending.lean` hides.** It holds nineteen `sorry`s, one per unlinked callee:
  - the five `apimodel` pending specs, including the model's own `watcher.run` goroutine;
  - the whole informer factory chain;
  - the controller's constructor and `Run`;
  - `NewBackOff` and `GetTargetNodeName`.

  Beyond "not proved yet", it hides statements that must still change:
  - the constructor's spec, which is currently false (H1) and incomplete (H3, M1);
  - `Start`'s, which must gain the gates (H2);
  - the metric registration's premise (M4);
  - the stronger `reflect.TypeOf` axiom (L4).

  `Main.wp_proof` is itself a `sorry`, so today nothing below `Main` is used.

## Ranking of the targets by need of revision

1. **The informer API (track A).** Its vocabulary feeds every caller: the gates (H2), the delete
   facts (H4), the name-keyed index families (M1), the store-version contract (H3's preferred fix),
   and the scope note (M5).
2. **The controller's lifecycle (track C).** Mostly `NewDaemonSetsController`: H1 (in progress), H3,
   M1(b), M4's registration premise, and M5's `infAt`/`podCtlIndexed`. Also `getDaemonSetsForPod`
   (M3), and `deleteDaemonset` once H4 lands. The handler, `enqueue*`, `resolveControllerRef`,
   `Run`, worker and node-update specs are otherwise sound and complete as far as I could check.
3. **The driver (track C).** `run`/`Main`'s premise and docstrings (M2), the theorem's
   `namesUnclaimed` premise (M4), and `gatesSet`'s `InOrderInformers` (H2). The closed theorem's
   statement is otherwise right.

No new Go bug was found. The swapped `updateDaemonset` arguments and the ambiguous create are already
filed (`nonissues/k8s-daemonset-updatedaemonset-swapped-args.md`,
`issues/k8s-daemonset-ambiguous-create-duplicate-pod.md`).
