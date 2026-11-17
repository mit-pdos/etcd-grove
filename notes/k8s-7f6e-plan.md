# k8s 7f-6 stage E, the wiring (with stage F): plan (2026-11-17, branch `k8s-7f6`, for etcd-grove-03)

Scope: `notes/k8s-7f6-scope.md` §5 rows E and F, §2 (the planned closed statements), §6. Stage E's
obligations from B (handoff, History "stage B done"): (a) `ioOk`'s `x.Kind' ≠ W64 5` goes, the model
giving watches their meaning; (b) `step.spec`'s two watch premises discharged where watches reach
`Step`. From C (`notes/k8s-7f6c-plan.md` §1, "Premise sources (stage E)"): `KHistW` (`comp`: compacted
`= 0`; `wf`; `one`) at the linearization point, `1 ≤ σ0.rev` from E's `Q`. This plan is a hard stop:
no Lean is edited before the coordinator's go.

## 0. What changed since the Scope

- **7f-5b is done**: `store.Watch.spec` has no `concurrentDecodeOff` and is linked (D linked the whole
  watch run). F has no external blocker left, so E and F land together (§7).
- **Found while planning: the watch environment at `k` members** (§3.7). `store.Watch` needs
  `storeWatchOk`, which `New`'s post gives from `clientWatchOk cl γk` (the kubernetes client's watcher
  over the cluster's KV). Building it needs every member's watch server registered behind its bridge
  and the watch condition `srvOnce` (no revision writes a key twice). The 3-member start had these as
  axioms (stage A removed them with it); the `k`-member start (`startCluster`, `clusterUp`) and `Main`'s
  one-member start register only the KV calls. Not in the Scope's E row nor its §6. Estimate below.
- **Found while planning: the watcher's cached object** (§2, Go G1/G2). `Apply` caches a watch's last
  non-error event object, which may be a bookmark (only a resource version, maybe annotated) or a
  Deleted event's object: not a `cachedObjOk` (the cache invariant asks every entry to be one, for the
  unary clients' `GuaranteedUpdate`). And `genWatchFrom`'s future RV `r + d + 1` from the cached
  object's `r` may pass `2^63 - 1` (`runWatch.spec`'s premise) unless `r` is bounded: `minRV` clamps
  `r ≥ 2^62`, `genWatchFrom` does not.

## 1. The model gives watches their meaning (obligation (a))

`stepL`'s watch branch keeps `g` iff `watchOkL x y g.st`; linkv's `PendSpec` (`txnlin/PendModel.lean`)
has only a deterministic step, so no `PStep` can say that.

- **`PendSpec` gains an observation** (generic): fields `isObs : I → Bool`, `obsOk : I → St → O → Prop`;
  `PStep.ok`/`errW`/`errR` take `P.isObs i = false`; new `PStep.obs (h : P.isObs i = true)
  (ho : P.obsOk i c.st o) : PStep c i (.ok o) c` (an observation answers `ok` and changes nothing).
  `txnSpec`: `isObs := fun _ => false`, `obsOk := fun _ _ _ => False` (txnlin's `Steps.lean`: the new
  case is absurd, the three constructors get `rfl`). `kSpec`: `isObs x := x.Kind' = W64 5`,
  `obsOk x h y := watchOkL x y h = true`.
- **`ioOk`**: `∃ x y, i = boxIn x ∧ o = boxOut y ∧ (x.Kind' = W64 5 → y.Err' ≠ W64 4 ∧ ∀ n,
  parseRVD x.MinRV' = some n → uint.Z n < 2^63)` in place of `x.Kind' ≠ W64 5`. A watch's output is
  `wFailedOut` or `wEventsOut _` (`Err' = 0`, `runWatch.spec`), so `ansOf y = .ok y`; the parse bound
  is `GenIn`'s (§2).
- `stepL_sound`/`stepL_complete`/`step_closure_ok`/`step_result` take `x.Kind' = W64 5 → y.Err' ≠ W64 4`
  in place of `x.Kind' ≠ W64 5`; the watch case is `PStep.obs` both ways.
- **Obligation (b)**, `step.spec`'s premise at `Model.wp_proof`: the parse bound from `ioOk`; the store
  revision `uint.Z g.st.st.rv < 2^63` from `Bounded`, which gains `uint.nat g.st.st.rv ≤
  g.st.hist.length` (a write moves `rv` by one exactly when `advanceL` grows the history;
  `stepL_bounded`, `succAt_bounded`), and `Model.spec` gains the seeded `g0`'s instance of it
  (`Check` discharges it: `g0s` has `rv = 3 = hist.length`).
- `kOk_obs` (as `kOk_errR`): an observation keeps `KOk` at the same `σ` and pending writes.

## 2. The Go changes (on `k8s-7f6`, from `k8s-7f6-target` plus G1/G2)

Port the target's `k8setcd3.go` (the cache's watcher fields and `newWCache`, `Gen`'s watcher branch,
`Apply`'s `KWatch` branch and `done.Add(1)`, `Check` over `lintest.RunLin2`, `newStore`, `Main`/
`MainCluster`/`MainPartition` with `watchers, wops`) and its tests, then:

- **G1**: `genWatchFrom` treats a cached object with `r ≥ 2^62` as none (as `minRV`'s clamp; never
  reached in a real run). Then every drawn RV parses below `2^62 + 201`, with no fact on the cache.
- **G2**: the watchers' cached objects in their own map (`cache.wobjs`, `getW`/`putW`): `Gen`'s
  watcher branch reads it, `Apply`'s `KWatch` branch writes it. Its entries carry no fact (`genWatch`
  only reads the resource version, bounded by G1); `objs` keeps `cachedObjOk`. (Alternative: one map
  and the invariant `(watch ∧ unary ≤ id) ∨ cachedObjOk`, which `Apply` cannot discharge without
  knowing the client is a watcher.)

Both keep the traffic of every real run; rerun `TestGenWatchCases`, `TestMainWatch`, `TestWatchCorrupt`
and `watchruns.sh 2 "1 3"`, then `etc/goose.py --project k8s-apiserver`.

## 3. The Lean work, in order (each step builds; checkpoints marked ⏸)

1. **Model** (§1): `PendModel`, txnlin `Steps`, `KList.kSpec`, `MDefs.k8setcd3S.ioOk`, `KSteps`,
   `Model.lean`, `Bounded`. ~250 lines.
2. **Inputs**: `GenIn x := GenInU x ∨ GenInW x` (today's `GenIn` renamed `GenInU`; `GenInW`: kind 5,
   `UseCached' = false`, and unless `Skip'`: `WKey'` one of the three forms (`"/objs/" <+: WKey'`,
   `prepareKeyM` some, length ≤ `opKeyMax`), `parseRVD MinRV' = some n` with `n < 2^62 + 201`,
   `WatchInOk x n`, `SendInit' = 2 → Bookmarks'`, `SendInit' ≠ 2 → SendInit' = 1 ∨ 0 < n`, selectors
   and `Behavior'` in range). `genWatchFrom.spec`/`genWatch.spec` (post `GenInW`; the 15 `pick`s as
   `genFrom`'s), `isCache` with the read-only `watch`/`unary`/`total` fields, `wobjs`, and the `done`
   counter's invariant (`∃ v, ownInt64 done v`: Go's `Add` wraps and Perennial's `Int64.Add.spec`
   has no premise, so the Scope's `done ≤ total` is not needed); `getW`/`putW` specs; `Gen.spec`
   unchanged in shape (post `GenIn`). ~500 lines.
3. **The instance's invariant**: `KNames` gains `γ.ch`, a mono list of etcd's changes (authority in
   `kInvBody`); `KOk` gains `σ.compacted = 0`, `σ.base = σb.base` and `OneChange σ` (`∀ cs ∈
   σ.changes, cs.length ≤ 1`), kept by `KvExt`/`KvOne` in every `kOk_*` and given at the seed
   (`σs2`: concrete, `seedOp_one`). Then `KHistW` at the current state: `comp`, `wf` (`kvWfHist`
   with `CfgD`), `one` (from `OneChange`), and `kvWritesDec` (from `kvWfHist` and `OneChange`). ~350.
4. **The watch's read update** (Draft D3): `watchQ γ c lb σ := ⌜lb ≤ σ.rev ∧ 1 ≤ σ.rev ∧ kvWf c σ ∧
   kvWfHist c σ ∧ kvKeysShort σ ∧ kvWritesDec c σ ∧ kvRevFits σ.rev ∧ σ.compacted = 0 ∧ σ.base =
   σb.base⌝ ∗ monoListLbOwn γ.ch σ.changes`. Its laws: the first by its pure part; two firings are
   of one history by `mono_list_lb_valid` (`kvSameHist`). Producers, as `list_later_au`: `kInv ⊢
   kvReadAu γk (watchQ … 0)` and `kInv ∗ □ watchQ … lb σ ⊢ kvReadAu γk (watchQ … σ.rev)` (the
   authority's prefix of the earlier bound gives `lb ≤ σ'.rev`), at every member (`kInv_same`), so
   `readAus`. ~250.
5. **`Apply`'s `KWatch` branch**: `runWatch` with `watchQ`; then the commit, one ghost step before
   `putW`: open `kInv` and the atomic update (masks as `plain_read_au`/`linU_commit`), the current
   `σe` and configuration `cf ∈ S` (`KOk.cfg`: `KRelH cf.st σe`, `cf.st.hist.length = σe.rev`); the
   stream's `σ` a prefix of `σe` (`mono_list_auth_lb_valid`), so `kStreamOk_hist`; then
   `streamOkL_of_kStreamOk` (with `kModeOk_of`, `hlk`, `KHistW σe`, `1 ≤ σ0.rev` from `watchQ`),
   `histWf_of_krel`, `watchOkL_of_stream`: `watchOkL x y cf.st`, so `PStep.obs` and `kOk_obs`; and
   the two cases with nothing to check: `WFailed`/`Skip` (`watchOkL` true at once) and no non-error
   event (`kSeen`'s first disjunct: a new pure lemma, `watchOkL` of only Error events is true).
   `kWEvRel` gets `e.t = 4 → w.o = zObj` (`toWEvent`'s, a stronger post) for `WEvOk` of the Error
   events. The unary branches gain `done.Add(1)`. `Apply.spec` gains `γk`, `kInv γ c g0 γk`,
   `storeWatchOk sp c driverW γk`, `watchListOn`. ~500.
6. **`Check`** over `RunLin2.spec` (`newWCache`, `watchers`, `wops`, its bounds; premises as `Apply`'s
   new ones). ~150.
7. **The watch environment** (§0). (i) A registration lemma without the watch condition: split
   `etcd_watch.wk_served_nd` (`examples/etcd/watch/Served.lean`) into the registration at `Serve`
   (watch server, `srvWOk`, the `Watch` stream at the address) and `srvOnce` supplied later, with
   `wk_served_nd` re-derived (its users unchanged). (ii) `startCluster`'s ghost step registers each
   member's watch server and its stream forwarded to the bridge (`forwards`, as the KV calls' D27);
   `clusterUp` gains them (an internal spec). `Main`'s one-member start the same. (iii) `srvOnce` of
   every member from `kInv`'s `OneChange` (`srvOnce_of_one` with a `kvReadAu γk OneChange` from
   `kInv`, after the seed: the compactor's `NoDup.lean`, moved to a shared place if both need it).
   (iv) A `k`-member `WatchEnv` (cluster3's `WatchEnv.lean` over a list: `watchConnFacts_of_members`),
   then `isNewClient_watcher_of`, `clientWatchOk cl γk`. (v) `watchContractOk driverSpec driverW codec`
   (the driver's `runtime.Decode` and `AnnotateInitialEventsEndBookmark`; no producer exists yet) and
   `newItemOk driverSpec newObj`; `storeWatchOk` from `New`'s persistent wand. ~800-1200.
   ⏸ **Checkpoint E-1** after (ii): the registration's shape, before (iv)-(v).
8. **`newStore`** (the target's helper: seed, features, `etcd3.New`): spec and proof, replacing the
   three inline copies. ~200, minus the copies.
9. **`Main`/`MainCluster`/`MainPartition`** with `watchers, wops`: the watch environment, `Check`.
   ~300. ⏸ **Checkpoint E-2 (hard stop): the closed statements** (below), before any linking.
10. **F**: `etc/link-lean-first-k8setcd3.txt` (Gen/Apply/Check/newStore/Main* and the new specs),
    `Link`/`MainLinked`/`Adequacy`/`Results` (`#print axioms`), interfaces, the tcb collection, bounds
    check, STATUS. ~300. ⏸ land stop.

**Estimate: 3400-4600 Lean lines** (the Scope's E+F: 1400-2400). The difference is the watch
environment (§3.7, 800-1200), the model's observation and `Bounded` (§1), and the cache (G2).

## 4. Statements that move

- **Internal (forms, decided as the common rules allow, listed at each checkpoint)**: `PendSpec`/
  `PStep` (generic, txnlin's proofs follow), `kSpec`, `ioOk`, `Bounded`, `GenIn`, `kWEvRel`, `KNames`,
  `KOk`, `isCache`, `Apply.spec`, `Check.spec`, `Model.spec`, `Gen.spec` (shape unchanged),
  `startCluster.spec`'s `clusterUp`, `wk_served_nd` (re-derived, same statement), new specs
  (`genWatchFrom`, `genWatch`, `getW`, `putW`, `newStore`).
- **Closed (to the user, at checkpoint E-2)**: `k8s_etcd3_safe`, `k8s_etcd3_cluster_safe`,
  `k8s_etcd3_partition_safe`, their `k8setcd3_Main*` spec results, `Adequacy`'s `_adequate`,
  `MainLinked`, and `Main.spec`/`MainCluster.spec`/`MainPartition.spec`: as the Scope's §2 sketch
  (`watchers`, `wops`, `Hw0`, `Hwops`, `Hc31 : clients + watchers < 2^31`, `Hmul : clients·ops +
  watchers·wops < 2^60`, `Hcec : ContextErrsClient`; Q1 and Q4 already approved by the user). No other
  new premise is expected; if the watch environment needs one (a class premise, a member fact), stop.
- **Trust base**: nothing added by E/F expected (7f-5's items reach the theorems through `store.Watch`'s
  link, already on lean). Any axiom: stop.

## 5. Risks

- The watch environment's registration may need more than `forwards` for streams (cluster3's 3-member
  version used axioms); if a stream forwarding lemma is missing, it is a lemma about the bridge, local.
- `watchContractOk` for the driver: `runtime.Decode` and `storage.AnnotateInitialEventsEndBookmark`
  are translated with bodies but have no spec yet (the latter goes through `meta.Accessor` and the
  annotations map: maybe 200 lines more). If a callee turns out trusted with no spec: stop.
- Changing `KNames`/`KOk` touches every `kOk_*` lemma and the 6 producers in `InvSteps.lean` (mostly
  mechanical: the new conjuncts are carried by `KvExt`/`KvOne`).
- `Apply.lean`'s per-kind proofs grow by `done.Add(1)` each.

## 6. Decisions asked (etcd-grove-03)

1. G1/G2 (the Go changes of §2). Recommended: yes.
2. E and F land together, one land stop after checkpoint E-2's approval. Recommended: yes (E alone
   cannot land: the Go change breaks the linked `Main*` proofs, and `etc/goose.py --check` gates it).
3. The model's observation in linkv's `PendSpec` (generic, txnlin follows) rather than a k8s-only copy
   of `PendModel`. Recommended: generic.
4. The watch environment inside 7f-6 (§3.7) with the revised estimate. Recommended: yes; alternative,
   a separate stage before E's step 9.
5. Drop the Scope's `done ≤ total` (not needed: Go's atomic `Add` wraps, nothing reads the bound).
   Recommended: yes.

## 7. Landing

One land after step 10: merge lean, full build, gates under `flock /shared/tmp/etcd-grove-full-build.lock`,
`LAKE_PACKAGES=/shared/tmp/manifest-e9e.json PERENNIAL_CHECKOUT=/shared/perennial-e9e6351d9 etc/land.sh`
(GOWORK unset), only on the coordinator's go.

## 8. Checkpoint E-1: the watch registration's shape (2026-11-17)

Reordered (form): §3.7's (i) and (iv) first, since they were the risk; steps 1-6 not started.

- **(i) done, without touching `wk_served_nd`**: `etcdstart.kvWatch_served`
  (`Proof/.../examples/lib/etcdstart/WatchServed.lean`, built). It is `kv_served` plus the watch side:
  same premises (`grpcUp`, the serving stocks, `isServerReq`/`isServerRead`) and `srvServeFacts s E
  cfg`, v3rpc's method sets, the thread bound and the two mvcc laws `srvWOk_of_up` reads (proof
  hypotheses, which the link discharges as the compactor's do). Post: the serve token,
  `etcdKVAt addr …` and
  `watchRegAt addr s E γr R := isGrpcStreamMd addr Watch (watchUp R) (watchSpec R (srvWOf E γr false)) ∗
  (∃ pw, isWatchServer pw R) ∗ srvWLaws (srvWOf E γr false) ∗ ⌜R.s = s ∧ R.E = E⌝`.
  No `srvOnce` here: it comes later from `kInv`'s `OneChange` (step 3), when `clientWatchOk` is built.
- **(iv) done**: `etcdstart.watchEnvL m0 ms γr pfx` (`WatchEnvL.lean`, built): cluster3's `watchEnv`
  over a list `ms : List (addr × WSrv × SrvW)`, and `watchEnvL_conn`: `□ [∗list]` of the members'
  `Watch` streams at their addresses, each member's `watchMemberFacts`, distinct addresses, give
  `□ ∀ conn ics, grpcConn conn (ms.map (·.1)) ics [] -∗ watchConnFacts {…}` (by
  `watchConnFacts_of_members`). One lemma for the `k` bridges and for `Main`'s one address.
- **(ii) next, the shape proposed for `clusterUp`** (startCluster's post; internal): 
  `∃ (ws : List (Loc × WSrv GF)) (γrc : ReadNames), ([∗list] sv; w ∈ svs; ws,
  watchRegAt sv.addr w.1 sv.E sv.γr w.2 ∗ isServerRead w.1 sv.E sv.γr) ∗
  ⌜kvSame γrc.kv γk ∧ γrc.kv.log0 = [[], []] ∧ ∀ sv ∈ svs, v3rpc.memberOf γrc.raft γrc.kv sv.γr⌝`,
  with `sv.addr` the bridge's (each registration moved there by `isGrpcStream_forwards` and the
  bridge's `forwards`), `γrc` the first member's read names (the members' raft names are the cluster's
  `{γ with reg := r}`: `memberGOk`). `startCluster`'s Serve ghost step calls `kvWatch_served` in place of
  `kv_served`; its loop invariant carries `ws`. `Main`'s one member: the same at `clientAddr`, no bridge.
- **(iii)** then, per member, `cluster3.memberWatch γrc s E ρ R` from that, `srvOnce` (from a
  `kvReadAu γk OneChange` that `kInv` gives, `srvOnce_of_one`) and `memberOf`; `cluster3.memberWatch_facts`
  gives each `watchMemberFacts`; `watchEnvL_conn` and `isNewClient_watcher_of` give `clientWatchOk`.
