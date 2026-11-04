# Review round 1: the sync path's specs (track B)

Reviewer: a fresh spec reviewer, 2026-11-04. Read-only. State reviewed: `HEAD` `0a84a58533` (the target
specs are unchanged since `947b16adba`), plus the working tree's uncommitted `daemon/Defs.lean` edit
(the informers' reader pools moved onto `infReaders`), which no finding below depends on. Go:
`k8s.io/kubernetes@v1.38.0-alpha.2.0.20261021173803-878cfa6c4cc7` (`daemon/daemon_controller.go`,
`daemon/update.go`, `controller/controller_utils.go`, `controller/controller_ref_manager.go`),
`client-go@v0.0.0-20261021054439-569675c57fa3/util/consistency/consistency.go`. The principles are
`.claude/skills/spec/PRINCIPLES.md`. I checked the code against `range.md`, `put.md` (vacuous
disjuncts, slack), `compaction-in-place.md` (arms the precondition excludes) and
`apply-uber-contract.md` (library specs that take a contract).

Line numbers below are of those files. "DC" is `daemon_controller.go`.

## Summary of findings, by severity

| # | Severity | Target(s) | Finding |
|---|---|---|---|
| H1 | hard rule (sound), known | `syncNodes`, then `manage`, `updateDaemonSet`, `syncDaemonSet`, `processNextWorkItem` | False of Go at `cfg.AmbiguousWrites`: the ambiguous create (R1/D51). Only `syncNodes`' docstring says so. |
| H2 | hard rule (sound) | `podsShouldBeOnNode` (and `podsView`/`nodesFree`) | False: a map entry `n ↦ []` with surge allowed makes Go ask to create on `n`, but the post says `Mp !! n = none`. |
| H3 | hard rule (complete/sound) | `updateDaemonSetStatus`, `syncNodes` (their `WroteAt`s) | `wroteAt_step`/`wrote_step` need `addedRv σ.dss.log o ≤ Ld` (`recDs`), and no premise supplies it. |
| H4 | hard rule (complete) | `getDaemonPods`, `getNodesToDaemonPods` (`podsListView`, `podsView`), for the caller `rollingUpdate` | The posts never say a listed pod is controlled by `u`, so `rollingUpdate` cannot show that no node has an old pod (surge creates, `make` with a negative cap). |
| M1 | complete | `RealPodControl.DeletePod`, `ClaimPods`, `ClaimControllerRevisions`, `syncNodes` | Nothing supplies the error facts: `syncNodes`' `fmt.argOk err` (an aggregate), `IsNotFound(err)` on `DeletePod`'s error, and the claims' `err = nil` (`NewAggregate.spec` says nothing). |
| M2 | proof feasibility | `updateDaemonSetStatus` (also `syncNodes`, `syncDaemonSet`; those paths are unreachable) | A reachable `fmt.Errorf("... %#v: %w", ds, err)` (DC:1263) has a `*DaemonSet` argument, which `fmt.Errorf.spec` cannot take. Not recorded anywhere. |
| M3 | abstraction, coupling | `FilterPodsByOwner`, `ClaimPods`, `ClaimControllerRevisions`, `NewPodControllerRefManager`, `RecheckDeletionTimestamp`, `ComputeHash`, `RealPodControl.DeletePod` | `pkg/controller`'s library specs import `daemon.SyncDefs`, are fixed to a `*DaemonSet` owner and to the model server's clientset, and `computeHashD` lives in `daemon/Scene.lean`. |
| M4 | trust base (outside the targets) | every target's `⌜ctx ≠ nil⌝`; `syncNodes` | `klog.FromContext.spec` and `apierrors.HasStatusCause.spec` hold "for any non-nil ctx / any err". That is false in general (`ctx.Value` and `errors.As` call the argument's methods). |
| L1 | unneeded premises | `dedupCurHistories`, `updatedDesiredNodeCounts`, `nodeShouldRunDaemonPod`, `podsShouldBeOnNode` | They take `dscEnv`, `threadTok`, `ctx` and `dsArg` where at most `□ dsAt` (and pure facts) is used. |
| L2 | margins not stated | `nodeShouldRunDaemonPod`, `FilterPodsByOwner`/`getDaemonPods`, `claimNoop` | The code guarantees more than the specs say (see below). |
| L3 | scope | `dsWf.noCollision`, `sceneOk.crNameInj` | No reason is given for `noCollision`. `crNameInj` is a creator's premise over the opaque `computeHashD`. |
| L4 | shape | `processNextWorkItem`, `syncDaemonSet`; glue proofs | The four conjuncts of `dscEnv` are spelled out. `updateDaemonSet`'s glue unfolds `dscEnv`, `isDsc`, `dscPools` and `dsArg`. |
| — | stale | `runWorker` (a caller) | The leftover `∀ [QItem GoString go.string]` binder is gone at `0a84a58533`. |
| Go | bug (code reading) | `constructHistory` (`update.go:311`) | A write to a nil map, reachable for a claimed ControllerRevision without labels. Not filed: it belongs in `nonissues/` (below). |

None of the specs is specialized to the driver's constants. There is no `default/ds-1`, no node name,
and no fixed UID. `burstReplicas ↦□ 250` (`isDsc`) is Go's constant `BurstReplicas` (DC:66, DC:207).
The specs are general over keys and owners. They are restricted to the model API server (`apimodel`'s
clients and `sceneOk`) and to DaemonSets satisfying `dsWf`. Both are scope restrictions, documented in
`Scene.lean`'s header.

## What is good

- **General over keys and owners.** The invariant keeps per-owner bookkeeping (`Lm`, `C`, records
  keyed by `Owner`). `syncDaemonSet` takes `keySyncTok` of the owner the key names, or nothing for
  a key `SplitMetaNamespaceKey` rejects. `Main`'s S1 is one instance (`S1Steps.lean`'s header argues
  this well).
- **Faithful to concurrency, and placed where Go needs it.** `EnsureReady`'s documented precondition
  ("Must not be called concurrent with WroteAt for the same owner", `consistency.go:150`) is the
  exclusive `ownerTok c o 1`. The create goroutines hold fractions of it. The worker trades the work
  queue's exclusive `keyTok` for `syncTok` inside `s1Inv` (`S1Trade.lean`, now proved). `keyCanon`
  (R5) makes distinct canonical keys distinct owners.
- **The S1 argument does not rest on the expectations.** `updateDaemonSet` and `syncDaemonSet` reach
  `manage` only when `SatisfiedExpectations` holds (DC:1358, DC:978), but no spec needs that. The
  argument is the consistency store's bound plus the claims, which is the right thing to rely on
  (the expectations are lowered on errors).
- **Lower bounds that can be combined.** Callers pass `infRvLb c.podI.γi L`, and the views come back
  "at a version `v ≥ L`". `FilterPodsByOwner` handles its two `ByIndex` calls soundly: picking the
  later past state works because logs only grow.
- **Pure helpers have pure models.** `maxRevD` matches DC/`update.go:399`'s signed comparison.
  `Match`'s result is `decide (r.Data'.Raw' = getPatchD …)`. `findUpdatedPodsOnNode`'s post is exactly
  `¬IsPodUpdated` for a live pod (`hashMatches` needs `len(hash) > 0`, `util/daemonset_util.go:169`).
- **Scope restrictions are in the docstrings.** `claimNoop`/`crClaimNoop` (no `Patch` in the model),
  `dedupCurHistories`' `rs.length = 1`, and `RecheckDeletionTimestamp`'s uncalled closure each say why.
  `cleanupHistory`'s `*ds.Spec.RevisionHistoryLimit` (`update.go:363`) is covered by `dsWf.histLimit`,
  which the model's defaulting establishes (`apimodel_test.go:139`).
- **Checked and sound as far as I could see:** `constructHistory`, `controlledHistories` (`crsOfDs`:
  one key `crName d` per namespace, `uidInj`, `selCovers`), `snapshot` (`crNameInj` excludes the
  collision branch, `update.go:564-583`), `cleanupHistory`, `storeDaemonSetStatus` (DC:1155-1207: the
  copy keeps the collision count, `dsSame`), `maxRevision`, `Match`, `getPatch` (template-only modulo
  the json boundary), `findUpdatedPodsOnNode`, `NewPodControllerRefManager`, `RecheckDeletionTimestamp`,
  `FilterPodsByOwner`, `ComputeHash` (modulo M3 and the boundary).

## Findings

### H1. The chain from `syncNodes` up is false at `cfg.AmbiguousWrites` (known: R1, D51)

- **Principle:** hard rule "Sound: true of the code".
- **Evidence:** `syncNodes.spec` returns `syncTok γ c o`. On a create that commits and returns an error
  (DC:1093-1104, the `CreatePods` error branch), the claim's fraction of `ownerTok` stays in `s1Inv`,
  so the token cannot be reassembled. `ambiguous_create_breaks_S1` shows that no proof can do it, and
  `TestAmbiguousWritesDetected` shows Go panicking in 5 of 200 runs
  (`issues/k8s-daemonset-ambiguous-create-duplicate-pod.md`). `cfg` is universally quantified in every
  spec, and nothing restricts `cfg.AmbiguousWrites'`. So `syncNodes`, `manage`, `updateDaemonSet`,
  `syncDaemonSet` and `processNextWorkItem` are not all true. The chain proves S1, and Go refutes S1.
- **Callers affected:** every result above `syncNodes`, `dsonepod_safe` included.
- **Restatement.** The rules allow a scope restriction that is marked and filed, and the issue is filed.
  The sound statement gates the one false spec:

  ```lean
  -- in syncNodes.spec's precondition (or once, in isDsc, where cfg is fixed):
  ⌜cfg.AmbiguousWrites' = false⌝ ∗ …
  ```

  `dsonepod_safe` then states its scope (configurations without ambiguous writes), and the `sorry`
  disappears. The cost is that the theorem no longer covers the driver's all-flags configuration. That
  choice is the user's: D51 reserves the controller's fix, not the specs' truth. If the run keeps the
  false spec, then at least the docstrings of `manage`, `updateDaemonSet`, `syncDaemonSet` and
  `processNextWorkItem` should say that they are false at `AmbiguousWrites` and rest on `syncNodes`'
  named `sorry`. Today only `syncNodes`' docstring says so.

### H2. `podsShouldBeOnNode` is false: an empty map entry

- **Principle:** hard rule "Sound".
- **Evidence:**
  - The post says `⌜∀ x ∈ ns, x = n.ObjectMeta'.Name' ∧ Mp !! x = none⌝`. The pre is
    `podMapAt m Mp ∗ podsView γa u L Mp`, and neither excludes an entry `Mp !! n = some []`.
  - In Go, with that entry, `exists` is true (DC:860). Then `case shouldContinueRunning` runs, which
    holds whenever `shouldRun` holds (`nodeShouldRunDaemonPod` returns `(true, true)` or a pair with a
    false first, DC:1413-1433). `daemonPodsRunning` is empty. If `util.AllowsSurge(ds)`, line DC:923
    (`len(daemonPodsRunning) == 0 && shouldRun`) appends `node.Name`.
  - `AllowsSurge` depends on `MaxSurge`, which `dsWf` and `sceneOk` leave free (`rollingUpdate`'s
    docstring: "the model's defaulted `MaxSurge` is opaque"). So the post fails for
    `Mp = {n ↦ []}`, surge allowed, `shouldRun`.
- **Callers affected:** `manage`. Its map comes from `getNodesToDaemonPods`, whose post (`podsView`)
  does not exclude empty entries either, so `manage` cannot dodge the case. `nodesFree` inherits the
  `= none` form.
- **Restatement.** State "free" by the node's pods, not by the key's absence. This is also what
  `updatedDesiredNodeCounts`' `some []` entries need:

  ```lean
  def podsView (γa : ApiNames) (u : GoString) (L : Nat) (Mp : GMap GoString (List kd.core.Pod)) :
      IProp GF :=
    iprop(∃ (σp : St) (v : Nat), pastSt γa σp ∗ ⌜L ≤ v ∧
      (∀ n k p, informer.tableAt σp.pods.log v !! k = some p → dsPodOn keyName opIn u n p →
        ∃ dp, p = .pod dp ∧ dp ∈ podsOn Mp n) ∧
      (∀ n p, p ∈ podsOn Mp n → ctlBy u p ∧ ∃ ch ∈ σp.pods.log, ch.obj = .pod p)⌝)   -- ctlBy: H4
  def nodesFree … := iprop(∃ Mp, podsView γa u L Mp ∗ ⌜∀ n ∈ ns, podsOn Mp n = []⌝)
  -- podsShouldBeOnNode's post:
  ⌜∀ x ∈ ns, x = n.ObjectMeta'.Name' ∧ podsOn Mp x = []⌝
  ```

  The surge case now satisfies the post: the node's list is empty. The alternative is to keep
  `= none` and add `⌜∀ n, Mp !! n ≠ some []⌝` to `podsView`. That breaks after
  `updatedDesiredNodeCounts`, and the restatement above is the more robust of the two.

### H3. No premise supplies the DaemonSet informer's bound that the `WroteAt` steps need

- **Principle:** hard rule "Complete" (a premise the proof needs and no caller supplies). As stated,
  it is also a soundness failure, below.
- **Evidence:**
  - `s1Ok.recDs` (`S1Steps.lean`) requires a record only for an owner whose DaemonSet was added at a
    version `≤ Ld`. `Ld` is the bound in `s1Res`, held as `infRvLb c.dsI.γi Ld`.
  - `wroteAt_step` and `wrote_step` both take `hLd : ∃ c, addedRv σ.dss.log o = some c ∧ c ≤ Ld`.
  - `updateDaemonSetStatus` calls `WroteAt` (DC:1266), and `syncNodes`' create goroutines call it
    through `OnWrite` (`onWriteFnOk`). Their preconditions hold only `dsArg γa ds o d`, which is a past
    *API* state's log and says nothing about the DaemonSet informer, plus `ownerTok`/`seenTok`.
  - `Ld` has no persistent lower-bound fragment, so a callee cannot learn `Ld ≥ addedRv o`. It cannot
    raise `Ld` itself either: `raiseLd_step` needs `infRvLb c.dsI.γi v` with `v ≥ addedRv o`, and
    neither function reads the DaemonSet informer.
  - The README's plan, "`syncDaemonSet` raises `Ld` before any `WroteAt`", happens in the caller, and
    the callee's spec does not carry it.
  - Soundness: for a `d` the informer has not reached (with `Ld < addedRv o`), the `WroteAt` leaves
    `s1Res` unclosable.
- **Callers affected:** the proofs of `updateDaemonSetStatus` and `syncNodes`, and so `manage`,
  `updateDaemonSet` and `syncDaemonSet`.
- **Restatement.** Make `dsArg` what its docstring says it is: "the DaemonSet the sync read from its
  lister", that is, the lister's view with the informer's bound:

  ```lean
  def dsArg (γa : ApiNames) (c : DscComp) (ds : Loc) (o : Owner) (d : kd.apps.DaemonSet) : IProp GF :=
    iprop(□ dsAt ds DFrac.discard d ∗ ∃ (σp : St) (v : Nat), pastSt γa σp ∗
      informer.infRvLb c.dsI.γi v ∗ ⌜informer.tableAt σp.dss.log v !! o = some (.ds d)⌝)
  ```

  A `WroteAt` site then raises `Ld` to `max Ld v` (`raiseLd_step`) and gets `addedRv σ.dss.log o ≤ v`
  from `dsFixed` (never deleted), as one pure lemma. `syncDaemonSet` builds `dsArg` from the
  DaemonSet lister's `Get`. Uncertain: I did not check that the lister `Get` spec (track A) returns
  `infRvLb` of its view. If it does not, that spec needs it. This also replaces `dsSeen`, which every
  spec uses only through `sceneOk.dsFixed`, an equivalent use.

### H4. The pod lists never say their pods are the DaemonSet's, and `rollingUpdate` needs it

- **Principle:** hard rule "Complete for every caller"; "The postcondition says what the caller
  inspects".
- **Evidence:**
  - `podsListView`'s and `podsView`'s second conjuncts say only that each pod "is a logged one".
    `sceneOk.pods` then gives `podOf d'' p` for *some* stored `d''`, whose hash label is `dsHash d''`.
  - `rollingUpdate`'s argument ("every pod of the DaemonSet carries its hash label, so
    `findUpdatedPodsOnNode` finds no old pod") needs `d'' = d`, which needs `ctlBy d.ObjectMeta'.UID' p`
    and then `uidInj`.
  - Go does give it: `ClaimPods` keeps only pods whose controller UID is the DaemonSet's (`claimKeeps`,
    `controller_ref_manager.go:69-80`). But `getDaemonPods`' post drops it.
  - Without it, the surge branch (`update.go:157-270`) may see an old pod. It then creates a pod on a
    node with a pod, and `make([]string, 0, maxSurge)` (`update.go:216`), like
    `make([]string, 0, maxUnavailable)` (`update.go:112`), runs with a count that
    `updatedDesiredNodeCounts`' post leaves arbitrary, possibly negative: a panic.
- **Callers affected:** `rollingUpdate`, and through it `updateDaemonSet`.
- **Restatement:** add `ctlBy u p` for every listed pod. That is `∀ p ∈ ps, ctlBy u p ∧ ∃ ch ∈ σp.pods.log,
  ch.obj = .pod p` in `podsListView`, and the same in `podsView`, as in H2's text.

### M1. Nothing supplies the error facts `syncNodes` and the claims need

- **Principle:** "Complete"; "The postcondition says what the caller inspects".
- **Evidence:**
  - `syncNodes`' post has `fmt.argOk err`, where `err = utilerrors.NewAggregate(errors)` (DC:1152).
    `NewAggregate.spec` (`Spec/k8s_io/apimachinery/pkg/util/errors/NewAggregate.lean`) returns
    "some `a`" with nothing about `a`: not `nil` for an empty list, though its docstring says so, and
    no `Error()` spec.
  - The elements come from `CreatePods` (`podCreateRet … err`) and `DeletePod`, and `DeletePod`'s post
    says nothing of `err` but `err = nil → ∃ w, oc = .ok w`.
  - `syncNodes` also calls `apierrors.IsNotFound(err)` on it (DC:1136). That goes through `errors.As`,
    so the error's dynamic type matters, and there is no `IsNotFound` spec yet.
  - `ClaimPods`' and `ClaimControllerRevisions`' `⌜err = interface.nil⌝` (code:
    `NewAggregate(nil)`, `controller_ref_manager.go:217, 481`) likewise has no source in
    `NewAggregate.spec`.
- **Restatement:**
  - `RealPodControl.DeletePod`'s post gains `fmt.argOk err` and the shape `IsNotFound`'s spec will
    need (the `NotFound` case is the client's `errIs err .notFound`, the others `fmt.Errorf`'s).
  - `NewAggregate.spec` gains `⌜(∀ e ∈ es, e = interface.nil) → a = interface.nil⌝`, and
    `fmt.argOk a` from `[∗list] e ∈ es, fmt.argOk e`.
  - `NewAggregate` is a trust-boundary hypothesis "pending approval", so this is an axiom change for
    the user. List what rests on it.

### M2. A reachable error path formats `*DaemonSet` with `%#v`

- **Principle:** "Know what it rests on" (proof feasibility). The specs' own text is fine.
- **Evidence:**
  - DC:1263 is `return fmt.Errorf("error storing status for daemon set %#v: %w", ds, err)`. It is
    reachable: `storeDaemonSetStatus` fails under `FailWrites`/`FailReads`.
  - `fmt.Errorf.spec` needs `fmt.argsOk`: `ArgWf`, which covers predeclared basic types only
    (`Perennial/Proof/fmt/Base.lean:517`), or a `stringMethodSpec` of `Error`/`String`.
  - `*apps.DaemonSet` has a gogo-generated `String()` (`k8s.io/api/apps/v1/generated.pb.go:2313`). Go
    does not call it under `%#v`, and no spec of it exists.
  - The same pattern appears at DC:1045 (`syncNodes`) and DC:1340 (`syncDaemonSet`). `KeyFunc` cannot
    fail for a namespaced object, so those two paths are unreachable.
  - Not in `notes/perennial-changes.md` or the run's notes.
- **Restatement.** None needed in the target. Record the limitation and choose: a trust-boundary
  `stringMethodSpec` of `(*DaemonSet).String`, or a Perennial `fmt` model for `%#v` of a struct pointer
  with no `GoString` (Go calls no method then).

### M3. `pkg/controller`'s library specs are written in the DaemonSet controller's vocabulary

- **Principle:** "The spec of an API, not of an implementation"; "Coupling"; "One spec per function"
  (a second controller would need a second spec); "A client does not unfold … any other package's".
- **Evidence:**
  - `FilterPodsByOwner`, `RecheckDeletionTimestamp`, `NewPodControllerRefManager`,
    `PodControllerRefManager__ClaimPods`, `ControllerRevisionControllerRefManager__ClaimControllerRevisions`
    and `ComputeHash` all `public import Proof.k8s_io.kubernetes.pkg.controller.daemon.SyncDefs`. That
    pulls in `S1Inv`, `Defs`, `Scene` and `apimodel`. `RecheckDeletionTimestamp` uses none of it.
  - `FilterPodsByOwner` is stated over `dsctl.infAt γa .pods` and `podCtlIndexed` (daemon's `Defs`)
    and over the model server's log (`pastSt`, `tableAt`). The function itself only calls
    `Indexer.ByIndex` (`controller_utils.go:1176-1212`).
  - The ref managers fix the owner to `interface.mkOk (*DaemonSet) #ds` and
    `d : kd.apps.DaemonSet`, where Go takes any `metav1.Object` and calls only `GetUID`,
    `GetDeletionTimestamp` and `GetNamespace`.
  - `computeHashD`, the model of a `pkg/controller` function, is in `daemon/Scene.lean`.
  - `RealPodControl.DeletePod` is stated over the model's clientset (`clientIs … γ cfg`, `deleteAU`,
    `∀ [ApiDeps]`).
- **Restatement:**
  - Move `computeHashD`, `podsAt`, `crsAt`, `int32PtrD`, `podCtlIndexed` and `podCtlKey` to a
    `pkg/controller` defs module that the daemon package imports, not the reverse.
  - State `FilterPodsByOwner` over client-go's cache (`isCache`/`tsReader` and the index relation)
    with the owner's three fields as values. The informer-log view becomes a law in the daemon
    package.
  - State the ref managers over an owner contract (UID, deletion timestamp, namespace, persistently).
  - This is internal to the run (the only client is this controller) and can wait for the freeze, but
    it is cheaper before more proofs use these specs.

### M4. Two named hypotheses below the targets claim more than Go does (outside the targets)

- **Principle:** hard rule, from the compactor's lesson: "every value the body reads from an argument
  (a context's `Value(key)`) needs a premise".
- **Evidence:**
  - `klog.FromContext.spec` (`Spec/k8s_io/klog/v2/FromContext.lean`) holds for every non-nil `ctx`.
    `FromContext` calls `ctx.Value`, which is arbitrary code for an arbitrary context.
  - `apierrors.HasStatusCause.spec` returns "some boolean" for any `err`, through `errors.As`.
  - Every target's `⌜ctx ≠ interface.nil⌝` rests on the first, and `syncNodes` on the second.
  - True for `Main`'s context and for the model client's errors. Uncertain: whether the run lists both
    among the hypotheses to approve. They are `?` in `etc/link-lean-first-k8sdaemon.txt`.
- **Restatement:**
  - Give `ctx` a contract: a persistent `ctxOk ctx`, produced by `context.Background`/`WithCancel` and
    carried in `isDsc` or the worker's spec.
  - Give `HasStatusCause`'s `err` the shapes its callers pass (`errIs err e` or `nil`).

### L1. Premises the code does not need

- `dedupCurHistories`: at its scope (`rs.length = 1`), Go returns `curHistories[0], nil`
  (`update.go:410-412`). `dscEnv`, `threadTok`, `ctx` and `dsArg` are unused. Either take only
  `crsAt` and the length, or specify the general case.
- `updatedDesiredNodeCounts` reads nothing of `dsc` (`update.go:590-626`): it does not need `dscEnv`,
  `threadTok` or `dsSeen`, only `□ dsAt`, `nodesAt` and `podMapAt`.
- `podsShouldBeOnNode` takes `dscEnv` and `threadTok` only to reach `sceneOk`, so that the failed,
  succeeded and terminating branches are dead. A pure premise `⌜∀ n p, p ∈ podsOn Mp n →
  p.Status'.Phase' = "Pending" ∧ p.DeletionTimestamp' = none⌝`, which the caller derives once, would
  make it local. Optional: these are internal helpers ("Scope").

### L2. Margins (where the code gives more than the spec, for the docstrings)

- `nodeShouldRunDaemonPod`: `b1 → b2` (DC:1413-1433).
- `FilterPodsByOwner` and `getDaemonPods`: for a `dsWf` DaemonSet, `err = nil` always.
- `claimNoop` misses the no-op case "owned by `d`, not matching, `d` being deleted" (`controller_ref_manager.go:76-83`).
- `RecheckDeletionTimestamp`: the closure's behaviour is unspecified.

### L3. Scope premises whose reason is not given

- `dsWf.noCollision`: `dsSame` already keeps the collision count across versions, and the status
  writes keep it (DC:1179, a copy of the cached object). So `computeHashD … cc` is constant for any
  `cc`, and I found no use beyond the preservation lemma (`S1Writes.lean:289`). Either drop it or
  give the reason.
- `crNameInj` (on `dsCreate_step`): a creator must show the new DaemonSet's `crName` differs from
  every stored one's. `crName` mentions the opaque `computeHashD`, so only a creator with one
  DaemonSet per namespace (`Main`) can discharge it. Say that the hash-collision path
  (`update.go:564-583`) is excluded by this scope.

### L4. Shape

- `processNextWorkItem.spec` and `syncDaemonSet.spec` spell out `isPkgInit ∗ isDsc ∗ apiInv ∗ s1Inv`,
  where `runWorker` and the helpers use `dscEnv`. Use `dscEnv` throughout.
- `updateDaemonSet`'s glue proof `iunfold`s `dscEnv`, `iNamed`s `isDsc`, and `iunfold`s `dscPools` and
  `dsArg` (lines 65, 67, 68, 85 of its proof). Projection laws (`dscEnv → isDsc`,
  `dsArg → □ dsAt`, a pool's borrow) would remove them. These are internal, so low.

## Go bug found by code reading (not filed)

`constructHistory` (`update.go:309-311`): for a claimed history without the hash label,
`toUpdate := history.DeepCopy(); toUpdate.Labels[apps.DefaultDaemonSetUniqueLabelKey] = toUpdate.Name`.
If the history's `Labels` is `nil`, this is a write to a nil map, a panic. It is reachable when
`controlledHistories` returns a ControllerRevision with no labels, which happens in two ways:

- An orphan with no labels in the DaemonSet's namespace is adopted (`ClaimObject` adopts on `match`).
  `match` is `Selector.Matches(labels.Set(nil))`, which is true for a selector of only
  `DoesNotExist`/`NotIn` expressions. Such a selector is valid for a DaemonSet whose template has no
  matching labels.
- Or a ControllerRevision already controlled by the DaemonSet's UID has nil labels.

The returned slice holds the cached pre-patch object, so the adoption's patch does not help. The
controller's own revisions always have labels (`CloneAndAddLabel`, `update.go:539`), so this takes a
third party creating such a ControllerRevision. Found by code reading, no test written. Per CLAUDE.md
it belongs in `nonissues/` (`blocks-proof: no`: `crOf.lbls` excludes it in the model) unless a test
reproduces it, and in `issues/` if one does. Upstream status unchecked. `Scene.lean`'s header notes
the path ("label write into a possibly `nil` map not reached") but nothing records it as a finding.

## Targets ranked by need of revision

1. `podsShouldBeOnNode`, with `podsView`/`nodesFree` (H2): false as stated. The fix is a vocabulary
   change that also carries H4.
2. `syncNodes` (H1, H3, M1): false at `AmbiguousWrites`, missing the `Ld` source, missing the error
   facts.
3. `updateDaemonSetStatus` (H3, M2): missing the `Ld` source. Its reachable `%#v` path is unprovable
   with today's `fmt`.
4. `getNodesToDaemonPods`, `getDaemonPods` (H4, with H2's restatement): the posts drop `ctlBy u`.
5. `rollingUpdate`: unprovable until 4 is fixed.
6. `manage`, `updateDaemonSet`, `syncDaemonSet`, `processNextWorkItem`: they inherit 1-3. Add the H1
   docstrings or gate. `dsArg`'s restatement (H3) changes their text.
7. `RealPodControl.DeletePod` (M1, M3): the error shape.
8. `PodControllerRefManager.ClaimPods`, `ControllerRevisionControllerRefManager.ClaimControllerRevisions`
   (M1, M3): `err = nil` without a source; owner fixed to a DaemonSet.
9. `FilterPodsByOwner`, `ComputeHash`, `NewPodControllerRefManager`, `RecheckDeletionTimestamp` (M3):
   layering only. Sound.
10. `dedupCurHistories`, `updatedDesiredNodeCounts`, `nodeShouldRunDaemonPod` (L1, L2): premises and
    margins.
11. `constructHistory`, `controlledHistories`, `snapshot`, `cleanupHistory`, `storeDaemonSetStatus`,
    `findUpdatedPodsOnNode`, `getPatch`, `Match`, `maxRevision`: no finding beyond `dsArg`'s
    restatement (H3).

## Not verified (uncertain)

- That the DaemonSet lister's `Get` spec (track A) returns the view with `infRvLb` (H3's restatement
  needs it).
- That `infRvLb γi 0` can be obtained from `infAt`. `rollingUpdate` and `updateDaemonSetStatus` call
  `getNodesToDaemonPods` with no bound of their own, and the in-file plans say "from the pod
  informer's invariant", but I found no law.
- That `isPkgInit` of the daemon package covers `utilfeature.DefaultFeatureGate.Enabled(...)`
  (DC:1429). `Enabled` panics on an unregistered feature, and the `pkg/features` init registers it.
- That `computeHashD` is a function of the Lean model `kd.core.PodTemplateSpec`. `DeepHashObject`
  dumps unexported fields with `spew` (`DisableMethods`), for instance `resource.Quantity`'s cached
  string. Harmless for templates without resources, but the specs are general over DaemonSets.
