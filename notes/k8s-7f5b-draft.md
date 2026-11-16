# k8s 7f-5b Draft: the watcher's concurrent branch, and the rest of 7f-5a's step 6

Branch `k8s-7f5` (worktree `/shared/etcd-grove-k8s7f`). Scope: `notes/k8s-7f5-scope.md` row 7f-5b and
Q6; `notes/k8s-7f-scope.md` §5.3; the 7f-5a Draft (`notes/k8s-7f5a-draft.md`, §§2-4: `k8sWatch`,
`store.Watch.spec`, the protocol). Decided by etcd-grove-02 (2026-11-16): the wait group is a local
idiom over Perennial's raw `WaitGroup` specs (option (a)); this session also takes 7f-5a's step 6.

**Trusted text: none. Axioms: none. Exported statement change: `store.Watch.spec` loses
`concurrentDecodeOff`, nothing else.** Everything else below is internal (specs of internal Go
functions, the idiom, vocabulary), proved.

## 1. The Go (`watcher.go` at the pin, `k8s.io/apiserver@…-9c4ec15b8038`)

- `run` (`:269-292`): `resultChanWG.Add(1); go { defer Done(); startWatching(...) }`;
  `processEvents(&resultChanWG)`; select on `watchClosedCh` / `wc.ctx.Done()`; `wc.cancel()`;
  `resultChanWG.Wait()`; `close(wc.resultChan)`.
- `processEvents` (`:546`): `Enabled(ConcurrentWatchObjectDecode)` picks `concurrentProcessEvents(wg)`
  or `wg.Add(1); go serialProcessEvents(wg)`.
- `concurrentProcessEvents` (`:577`): `p := concurrentOrderedEventProcessing{wc, processingQueue:
  make(chan chan *processingResult, 9), ...}`; `wg.Add(1); go { defer Done(); p.schedule…(wc.ctx, wg) }`;
  `wg.Add(1); go { defer Done(); p.collect…(wc.ctx) }`.
- `scheduleEventProcessing` (`:611`): loop: select (`ctx.Done` → return | `e = <-incomingEventChan`);
  `rc := make(chan *processingResult, 1)`; select (`ctx.Done` → return | `processingQueue <- rc`);
  **`wg.Add(1)`**; `go { defer wg.Done(); res, err := transform(e); select (ctx.Done | rc <- &{res, err}) }`.
- `collectEventProcessing` (`:637`): loop: select (`ctx.Done` → return | `rc = <-processingQueue`);
  select (`ctx.Done` → return | `r = <-rc`); `r.err != nil` → `sendError`, return; `r.event == nil` →
  continue; `!sendEvent(r.event)` → return.

The scheduler's `wg.Add(1)` runs concurrently with `run`'s `Wait()`, at a count of at least 1 (the
scheduler's own unit, released by its deferred `Done` after its last `Add`). Go allows it: `Add`'s
"called concurrently with Wait" panic needs the count at 0 before the add; Perennial's
`sync.WaitGroup.Add.spec` agrees (its `oldc ≠ 0` disjunct needs no waiter state). `transform`'s spec
returns `err = nil` (every raw event decodes, `kRawDecOk`), so the collector's `sendError` arm is
dead, as the serial goroutine's is.

## 2. The wait group: `InvRunWg.lean` (local idiom, namespace `k8s.rwg`)

Neither `sync.tokJoin` nor `sync.tokJoinL` lets a goroutine of the group `Add` (only the exclusive
`ownAdder`, which `Wait` consumes): `notes/perennial-changes.md`, first "Open" entry, the general fix
proposed separately. Here, over the raw `Add`/`Done`/`Wait` specs (hypotheses `wp_Add`, `wp_Done`,
`wp_Wait`, as in Perennial's `*_of` theorems):

- **Two kinds of slots.** *Top-level* slots, added by the adder (`run`; at most `K` of them, `K = 3`
  for `run`), each with a `Done` proposition (Perennial's `ownAprop`, as tokJoinL), not token-backed
  (their goroutines run with a whole fresh thread token: `startWatching.spec` takes `threadTok`).
  *Member* slots, added by the holder of a top-level slot (the scheduler) at a positive count, `Done`
  proposition `True`, backed by thread tokens as tokJoinL's at pending level `1`: the adder's
  `levelTok 1` while pending, the forked goroutine's level `0` once started.
- **Invariant** (`rwgInv γ K`):
  ```lean
  ∃ (ctr : w32) (added done d q : Nat) (Pdone : IProp GF),
    ownWaitGroup γ.wgGn ctr ∗ ownTokAuthDfrac γ.ndGn (DFrac.own ½) added ∗ ownToks γ.ndGn done ∗
    ownApropFrag γ.apGn Pdone done ∗ Pdone ∗
    levelToks 0 d ∗ ownTokAuth γ.depGn d ∗ levelToks 1 q ∗ ownTokAuth γ.pendGn q ∗
    ⌜sint.Z ctr = (added : Int) - done + d + q ∧ added ≤ K⌝
  ```
  `isRunWg N K wg γ := isWaitGroup wg γ.wgGn (N.@"wg") ∗ inv (N.@"inv") (rwgInv γ K) ∗
  ⌜K + 2 * threadBound GF ≤ 2 ^ 31 + 1⌝` (so `ctr ≤ K + 2 (T - 1) < 2^31`; `run`: `K = 3` from
  store.Watch's `threadBound GF ≤ 2^30 - 1`).
- **Resources** (each `∃ γ, … ∗ isRunWg N K wg γ`): `rwgAdder N K wg n P` (waiters at `0`, the
  `added` half at `n`, `ownApropAuth` of `P`; tokJoinL's `ownAdder`), `rwgDone N K wg P` (a top-level
  slot: `ownAprop P ∗ ownToks γ.ndGn 1`), `rwgPending N K wg` (`ownToks γ.pendGn 1`), `rwgMemDone N K wg`
  (`ownToks γ.depGn 1`).
- **Laws** (the statements; proofs from tokJoinL's):
  - `init`: `isWaitGroup wg γwg (N.@"wg") ∗ ownWaitGroup γwg 0 ∗ ownWaitGroupWaiters γwg 0 ∗
    ⌜K + 2T ≤ 2^31 + 1⌝ ⊢ |={E}=> rwgAdder N K wg 0 True`;
  - `wp_Add_top`: `{rwgAdder N K wg n P ∗ ⌜n < K⌝} wg.Add(1) {rwgAdder N K wg (n+1) (P ∗ P') ∗ rwgDone N K wg P'}`;
  - `wp_Add_member`: `{rwgDone N K wg P ∗ levelTok 1} wg.Add(1) {rwgDone N K wg P ∗ rwgPending N K wg}`
    (the slot's count gives `oldc ≠ 0`: `Add.spec`'s first disjunct);
  - `wp_fork_member`: `rwgPending N K wg ∗ ▷ (threadTokFrom 1 ∗ rwgMemDone N K wg -∗ WP e {v, ⌜¬panic⌝ ∗
    threadTok}) ∗ ▷ (levelTok 1 -∗ Φ #()) ⊢ WP Fork e {Φ}` (`wp_fork_tok_upd`: the fresh token's level 0
    replaces the pending level-1 token, which goes back to the forking thread);
  - `wp_Done_top`: `{rwgDone N K wg P ∗ P} wg.Done() {True}`;
  - `wp_Done_member`: `{rwgMemDone N K wg ∗ threadTokFrom 1} wg.Done() {threadTok}`;
  - `wp_Wait`: `{rwgAdder N K wg n P} wg.Wait() {P}` (count `0`: every slot done, `added = done`).
  - `rwgAdder_wand`: `(P -∗ P') -∗ rwgAdder N K wg n P -∗ rwgAdder N K wg n P'`.

## 3. The concurrent protocol (`WatchConc.lean`, internal)

- **The response channel** `rc` (`chan *processingResult`, capacity 1; an SPSC: producer the
  per-event goroutine, consumer the collector). Element (`kRcElem c W sel emp σ r`, at index `0` only):
  ```lean
  fun i v => ⌜i = 0⌝ ∗ ∃ res : Loc, v ↦ {event := res, err := nil} ∗
    match kRawToEv c.S.dec sel emp c.S.zero σ r with
    | none => ⌜res = null⌝ | some e => ∃ ev, res ↦ ev ∗ wevAt c.S W ev e
  ```
- **`processingQueue`** (an SPSC of response channels: producer the scheduler, consumer the
  collector). Element `i` (`kQElem`): the `i`-th incoming element's facts with its raw event `r` at
  `σ` exposed (`kInElemX …`, `kInElem`'s body: `kInElem i p = ∃ …, kInElemX … i p r …`, a form
  refactoring), and `isSpsc γrc rc (kRcElem c W sel emp σ r) (fun _ => True) ∗ spscConsumer γrc []`.
  The scheduler forwards in order, one queue element per incoming element (the received and sent
  counts are equal), so element `i` of the queue is element `i` of `incomingEventChan`.
- **The collector** is the serial goroutine with one more step: it takes queue element `n` (`n =
  procd`), then the response, and makes the serial goroutine's ghost step (`kResInv_step`,
  `kResInv_send_acc`/`kResInv_filter`; `kProcExited_refute` with its `procEx` fraction). The
  scheduler passes `kInElemX`'s `kProcExited` disjunct along unrefuted.
- **The per-event goroutine** gets `ep ↦□ x ∗ kEvIs σ x r` (persistent, from `kInElemX`), the
  response's producer half, `threadTokFrom 1 ∗ rwgMemDone`; it calls `transform` (pure premises from
  §5's lemma), sends `kRcElem` in the select (or gives up on `ctx.Done`), and exits through
  `wp_Done_member` with `threadTok`.

## 4. The internal specs (one Spec/Proof file each)

Shared bundle, **`kWcCons wc sp c W γk γ cd sel emp inS m Q procd alive ctx kp recur`** (persistent):
`kWcProd …` plus what `transform` and `sendEvent` read: `wc.internalPred ↦□ p` with
`selPredOk c.S p sel emp`, `wc.resultLogger ↦□ lg` with `blockLoggerOk lg`, `storeWatchOk sp c W γk`,
`transformerOk c.S c.ti`, `versionerOk c.S c.vi`. The processing side's resources,
**`kProcSt γ procd alive q`** := `spscConsumer γ.inc [] ∗ dghostVar procd (own ½) 0 ∗
dghostVar γ.procEx (own 1) false ∗ kResAlive alive q`. `rwgN := nroot.@"k8sRunWg"`, `K = 3`.

7f-5b:
- `concurrentOrderedEventProcessing.scheduleEventProcessing.spec`:
  `{isPkgInit ∗ pp ↦□ {wc, chQ, …} ∗ kWcCons … ∗ spscConsumer γ.inc recvI ∗
   isSpsc γq chQ (kQElem …) True ∗ spscProducer γq sentQ ∗ ⌜recvI.length = sentQ.length⌝ ∗
   rwgDone rwgN 3 wg P ∗ levelTok 1}
   pp.scheduleEventProcessing(ctx, wg) {rwgDone rwgN 3 wg P ∗ levelTok 1}`
  (`ctx` the value of `wc.ctx`);
- `concurrentOrderedEventProcessing.collectEventProcessing.spec`:
  `{isPkgInit ∗ pp ↦□ {wc, chQ, …} ∗ kWcCons … ∗ isSpsc γq chQ (kQElem …) True ∗
   spscConsumer γq recv ∗ ⌜recv.length = n⌝ ∗ dghostVar procd (own ½) n ∗
   dghostVar γ.procEx (own 1) false ∗ kResAlive alive q} pp.collectEventProcessing(ctx) {kResAlive alive q}`;
- `watchChan.concurrentProcessEvents.spec`:
  `{isPkgInit ∗ kWcCons … ∗ kProcSt γ procd alive q ∗ rwgAdder rwgN 3 wg n P ∗ ⌜n + 2 ≤ 3⌝}
   wc.concurrentProcessEvents(wg) {rwgAdder rwgN 3 wg (n + 2) (P ∗ kResAlive alive q)}`.

7f-5a step 6 (the specs the 7f-5a Draft §6 names; first statements here):
- `watchChan.serialProcessEvents.spec` (the goroutine's body):
  `{isPkgInit ∗ kWcCons … ∗ kProcSt γ procd alive q ∗ rwgDone rwgN 3 wg (kResAlive alive q)}
   wc.serialProcessEvents(wg) {True}`;
- `watchChan.processEvents.spec`: as `concurrentProcessEvents`' with `watchListOn` (the gate's
  pointer) and `⌜n + 2 ≤ 3⌝`, post `∃ n', rwgAdder rwgN 3 wg n' (P ∗ kResAlive alive q)`; **no
  gate fact on `ConcurrentWatchObjectDecode`**: `Enabled` of a queried feature returns some `b`
  under `featureGateOk` (features' package fact), and both branches are proved;
- `watchChan.run.spec`: startWatching's premises (the five pure ones), `kWcCons …`, `initialRev ↦
  r0 ∗ kStartPre m Q r0 ∗ readAus c γk (Q 0) ∗ (re-arm)`, `kProdSt γ cd [] ∗ dghostVar γ.prodEx (own 1)
  false`, `kProcSt γ procd alive 1` with the full `alive`, `watchListOn ∗ rangeStreamOff`,
  `⌜threadBound GF ≤ 2^30 - 1⌝`, `threadTok`; arguments `#m.bmReq #m.forceInit`; post `threadTok`.
  After `Wait` it holds `kResAlive alive 1`, opens `kResChan`'s invariant (`kResInv` → `kResClosed`,
  the producer token out) and closes `resultChan` (`R := True`);
- `watchChan.Stop.spec`: `{wc.cancel ↦□ cf ∗ cancelSpec cf γc (kCancelPD γ cd) ∗ (kLive γ ∨ kStopped γ)}
  wc.Stop() {kStopped γ}`; `watchChan.ResultChan.spec`: `{wc.resultChan ↦□ ch} wc.ResultChan() {RET ch}`;
- `watcher.createWatchChan.spec`: over `storeWatchOk`, the require-leader context
  (`isContext ci cd ∗ outgoingCtxOkC ci ∗ ctxErrClient ci cd`), `selPredOk c.S pred sel emp`, `kp`
  with `kp ≠ [] ∧ kp.length ≤ opKeyMax`; post `∃ γ procd alive ctx, kWcCons … ∗ initialRev ↦ rev ∗
  kProdSt γ cd [] ∗ dghostVar γ.prodEx (own 1) false ∗ kProcSt γ procd alive 1 ∗ isSpsc γ.res … ∗
  spscConsumer γ.res [] ∗ kLive γ`, the ghost names allocated before `WithCancel`
  (`wp_WithCancel_ctx`, `PDone' := kCancelPD γ cd`);
- `watcher.Watch.spec`: store.Watch's premises over the prepared key and the require-leader context,
  post `⌜err ≠ nil⌝ ∨ (⌜err = nil⌝ ∗ ∃ γ, k8sWatch …)`.

**`store.Watch.spec`**: old → new: the precondition's `watchListOn ∗ rangeStreamOff ∗
concurrentDecodeOff ∗` becomes `watchListOn ∗ rangeStreamOff ∗`. Nothing else. (Ledger entry at the
change; 7f-6 uses the spec as a hypothesis: a weaker premise, so its uses stay valid by dropping the
argument.) `concurrentDecodeOff` is deleted from `WatchDefs.lean` once nothing uses it (the driver's
`Set("ConcurrentWatchObjectDecode=false")` stays harmless; 7f-6 may drop it).

## 5. Form fixes and new pure lemmas

- **`kCdw` takes the child's Done name.** `kCdw γ cd := { cd with PDone := cd.PDone ∨ kCancelPD γ cd }`
  keeps `cd.Done_gn`, but `wp_WithCancel_ctx` gives `{ s with PDone := …, Done_gn := γ' }`, so
  `createWatchChan` cannot produce `kWcProd`'s `isContext ctx (kCdw γ cd)`. New: `kCdw γ cd γc` with
  `Done_gn := γc`, `kWcProd`'s existing `∃ γc` (its `cancelSpec cf γc …`) used for it. Internal:
  `startWatching.spec`'s text is unchanged (it names `kWcProd`); its proof and syncPaginated's
  re-checked.
- `kInElem` refactored as `∃ …, kInElemX …` (same meaning).
- `kInElemX_transformOk` (pure, from `□ Q lb σ`'s `kvWfHist`, the scope inside the store's prefix and
  `kRawStreamSub`): the raw event satisfies `transform`'s premises (`kRawDecOk c.S.dec σ r`, its
  revision non-negative). Needed by both branches.

## 6. Plan, checkpoints, estimate

1. Forms: `kCdw`, `kInElemX`, `kWcCons`, `kProcSt`, `kInElemX_transformOk` (~150).
2. `InvRunWg.lean` (~450, from tokJoinL's proofs).
3. Serial and wiring: `serialProcessEvents`, `processEvents` (concurrentProcessEvents' spec a
   hypothesis), `run`, `Stop`, `ResultChan`, `createWatchChan`, `watcher.Watch`, `store.Watch` without
   `concurrentDecodeOff` (~900-1300). Checkpoint.
4. Concurrent: `WatchConc.lean`, `scheduleEventProcessing`, `collectEventProcessing`,
   `concurrentProcessEvents` (~600-900).
5. Link (`etc/link-lean-first-k8s-etcd3.txt`), `New`'s post if `storeWatchOk` needs more, Results;
   land-stop checks. If step 4 drags, a clean earlier landing: step 3 with `processEvents` proved
   for the serial branch only and `concurrentDecodeOff` kept (02's option), the drop at step 5.

**Estimate: 2100-2800 Lean lines, 2-3 agent contexts.**
