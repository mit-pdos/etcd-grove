# k8s 7f-5 handoff (2026-11-13; branch `k8s-7f5`, worktree `/shared/etcd-grove-k8s7f`)

**Read first:** `notes/k8s-7f5-scope.md` (this stage's Scope, for etcd-grove-81's review),
`notes/k8s-7f-scope.md` (the parent plan; §2, §4, §5.3), `notes/k8s-7f4-freeze.md` (the context-key
refutations T-h..T-k: the lesson for every trusted context text), `/shared/tmp/coord-81/common-rules.md`,
the worktree's untracked `questions.md` (decisions; never re-add it tracked).

## Done
- Branch `k8s-7f5` off lean `222c3fcff7` (k8s-7f4 merged and deleted).
- The Scope (`notes/k8s-7f5-scope.md`), reviewed: 81 decided Q1-Q7 as recommended (§8 there, questions.md).
- S0 (enumeration, Go evidence `examples/premisefix/watcherctx`, Goose dry run, the driver's
  `watchList()`, the no-other-mutator check) and S1 (T5-b in `CtxKeys.lean`, T5-c in `Gate.lean` with
  `watchList`'s spec/proof and the `Main*` proofs; T5-d text only): `notes/k8s-7f5-freeze.md`.

## State
- Dependencies (Scope §2): 7f-3 **missing** (not started); 7c-3 and 7e-1 **landed** (7c-3 folded into
  7e-1, 7e Freeze `8809f94d74`); sweep repairs B5 **landed with `featureOff` only** (`featureOn` is
  this stage's T5-c); 7f-0 partial (records only; the rest goes with 7f-6, Q7).
- No Lean edited. Nothing built on this branch.

## Handoff point (2026-11-14, sixth 7f-5 agent): 7f-3b v3rpc part done on the branch; checkpoint (not landed)

Done (`35fdc186ad` and the commit after it on `k8s-7f5`; questions.md entries of 2026-11-14):
- Steps 1-3, 5, 6 of the list below. `recvLoop` records `prevKV[id] = true` (`swsMu`, the Draft's
  `swsMuP` under the old name, each entry carrying `pkIs γpk id true`); `sendLoop`'s `PrevKv` branch
  (`IsCreateEvent` on `evRd`, the watchable store's `Range` at `ModRevision - 1` through
  `shapes.law`'s `KV.Range.contract` and `v3rpc.range_au`, `r.KVs[0]` written into the copy's owned
  field, the error/empty arms) inside the macro `pk_branch` (the code generator overflowed with one
  macro); `watchReqOk` without `prev_kv = false`; `wrespRO` removed.
- The server's guarantee for the client (7f-3c): `mvccOk` carries `evsSentOk r x m.evs` (`pkWritten`
  per event: mvcc's event, or with `PrevKv := some kv` for a non-create event of a watcher with
  `pkIs … true`, `kv` the key's record at `ModRevision - 1` of a certified log `L` with `L[1] = []`,
  claimed at revisions ≥ 2). The created response's `ctrlWatcher` gives `pkIs r.γpk id c.prevKv`
  (agreement: `pkIs_agree`; the client finds `γpk` through `auxOf_inj_pk`).
- Client adapted minimally (`evRd` readers, `m.evs.length = x.evs.length`); finding
  `nonissues/etcd-watch-prevkv-revision-one.md`.
- **Step 4 moved to 7f-3c** (form decision): `rawRespOkP` swap is client-only.

Next: the checkpoint (full build, tcb --check, gates, interfaces), report to 81, land on its go;
then 7f-3c: `rawRespOkP` (prevKvLogOk from `evsSentOk`: for `prevKV = false`, `pkIs` agreement with the
created response's `pkIs … c.prevKv`; for a written one, `stateAt` transfer between `L` and the
client's log by `histLb` agreement, and `L[1] = []` to exclude revision 1), then `watchGRPCStream`
carrying the pointer, `watcher.Watch.specP`, the users.

Pitfalls: in a `local macro` a `$$ [$H]` is an antiquotation (write `$$ [H]` and `iframe H`); a
`--goal` inside a macro body does not work (use a deliberate `done`); `rw … at H` on an Iris
hypothesis fails (rewrite the goal, or `irevert`).

## Handoff point (2026-11-13, fifth 7f-5 agent, final): 7f-3b mvcc part LANDED (lean `570cea0725`); v3rpc part next

Done (`3e90b6e741` on `k8s-7f5`; full build passes, 17487 jobs; tcb matches 870/4; gates all ok after
the interfaces were regenerated, log `/shared/tmp/k8s7f3b/gates.log`):
- mvcc vocabulary (`InvWatchBatch.lean`): `prevKvIs`, `evRd` (field-wise, persistent: every field but
  `PrevKv`, the key-value `kvPtrFixed`), `evPk e ev q` (the `PrevKv` field owned at a fraction: the
  lock invariant is fractional), `evOwn := evRd ∗ evPk`; laws `evIs_evRd`, `evOwn_intro` (the
  allocated copy), `evOwn_persist`/`evOwns_persist` (give the copies up: back to `evIs`),
  `evOwn_rd`, `evOwns_split`, `evRd_modRev`, `bigSepL_filter_drop`; `evPk_fractional`,
  `evOwn_fractional` (`InvWatchFrac`).
- `ownEventBatch` holds `evOwn`; `eventBatch.add`/`watcherBatch.add` take `evOwn`; `newWatcherBatch`
  makes each copy `evOwn` (`evOwn_intro`); `watcher.send` takes the copies `evOwn` and gives them back
  on `false` (post `if b then ↦*□ else ↦* ∗ [∗list] evOwn`); notify/syncWatchers/moveVictims keep
  them in the victim batches.
- Internally `respIs` keeps `evRd` (persistent); the channel invariant `watchChanInv` gains
  `"Hpk" ∷ respsPk vs (sent.drop recv.length)` (the in-flight responses' `PrevKv` fields);
  `watchRecvResult` carries `respPk v r`; every `imod Hclose` passes `Hpk`.
- API: `mvcc.api.wrespIs` carries `evOwn` (81: D2, wrespIs itself); `respIs_wrespIs` takes
  `respIs ∗ respPk`.
- Readers: `filterSpec`, v3rpc `filterNoPut`/`filterNoDelete` take `evRd`; the examples
  (`mvccfull` `stream__receive`/`stream__watch`, `mvccrand` `watchCheck__receive`) read `evRd`.
- v3rpc stopgap: `WatchApi.wrespIs_persistent` (false now) replaced by `v3rpc.wrespRO` (the old
  read-only form over `mvcc.evIs`) and `wrespIs_ro : wrespIs ⊢ |==> wrespRO`, applied at the send
  loop's two receipts. The v3rpc part of 7f-3b replaces this by the `PrevKv` write.

81 approved the interface diff and accepted `wrespRO` as temporary; landed on lean `570cea0725`
(gates all passed, `/shared/tmp/k8s7f3b/land.log`). **Next, a fresh agent: the v3rpc part of 7f-3b**, in this order (statements in
`Draft7f3a.lean`: `swsMuP`, `watchReqOkP`, `client.rawRespOkP`, `prevKvLogOk`):
1. `recvLoop` records `creq.PrevKv` in the `prevKV` map (`watch.go:342-349`): `swsMu` → `swsMuP`
   (entries allowed in `prevKV`, `fragment` still empty).
2. `sendLoop`'s branch (`watch.go:437-455`): the create check (`IsCreateEvent`), mvcc's `Range` of the
   key at `ModRevision - 1` (`Api/RangeApi.lean`), and `events[i].PrevKv = r.KVs[0]` written into the
   copy's owned field (`evPk`, from `wrespIs`'s `evOwn`), with the `nil`/error arms.
3. `IsCreateEvent`'s spec on `evRd` (today `evIs`).
4. `rawRespOkP` (the client pipeline's server contract: each pointer `prevKvLogOk`), in place of
   `rawRespOk`.
5. `watchReqOkP` in `upOk` (the server's `prev_kv = false` restriction dropped).
6. Remove the stopgap `v3rpc.wrespRO` / `wrespIs_ro` (`WatchApi.lean`) and its two uses in
   `serverWatchStream__sendLoop.lean`.
Then the client part, 7f-3c (`notes/k8s-7f3a-draft.md` §5). Report the v3rpc interface/statement
changes to 81 before landing, as for mvcc.

**Pitfall (wp_join):** after a failing bullet inside `wp_join`, later goals carry unassigned metavariables
and `wp_for`'s clean-up silently fails (`Hif : #(decide …) = #true` undecoded, `word` fails): fix the
FIRST error before reading later ones. `etc/lean-check.py` incremental runs once gave a spurious
`(kernel) application type mismatch` on `moveVictims` that `lake build` did not.

## Handoff point (2026-11-13, fourth 7f-5 agent, final): T5-a LANDED (lean `7112e7c0d6`); 7f-3b next

T5-a landed via `etc/land.sh` (gates all passed, `/shared/tmp/k8s7f3a/land3.log`): the translation of
`WithRequireLeader`/grpc metadata reverted (`WithPrevKV` kept), the restated axiom with its four-part
clause (81 accepted the `Value(&cancelCtxKey)` part), `WithRequireLeader.watchCtx_of_post` proved,
Go tests, STATUS entry. Trust base 870 axioms, 4 sorries (no baseline change).

**Next (a fresh agent): 7f-3b**, from the design section below. 81 approved: `wrespIs` itself
carries `evOwn` (not a second predicate). Order: vocabulary (`evRd`, `evPk`, `evOwn`, laws
`evIs ⊢ evRd`, the recombination to `evIs`), built; mvcc proofs bottom-up (newWatcherBatch,
eventBatch/watcherBatch add, ownEventBatch and victims, watcher.send, the three send sites, Api's
`wrespIs`, WatchLaws); **report the mvcc interface diff (`etc/gen-interface.py` for mvcc's API list)
to 81 before landing 7f-3b**; then v3rpc (`recvLoop` with `swsMuP`, `sendLoop`'s `PrevKv` branch,
`rawRespOkP`, `watchReqOkP`), then the examples/client readers. `Draft7f3a.lean` holds the S1-S9
statements.

## Handoff point (2026-11-13, end of the fourth 7f-5 agent): T5-a decomposed; land after 81 sees the flag

81 decided (a): the axiom's `watchCtx ctx s -∗ watchCtx c s` decomposed (no trunc line). Done in
`873034096c`: `Done()`/`Err()` WP transfers, **plus a `Value(&cancelCtxKey)` WP transfer (not in 81's
list: needed for `#HCC`, whose result predicate `isCancelCtxAny` is not pure, so the pure-`R` `Value`
transfer does not give it; flagged in the freeze note's T5-a review section)**, and
`metadata.outgoingCtxOkC c`; law `WithRequireLeader.watchCtx_of_post`
(`Proof/go_etcd_io/etcd/client/v3/WithRequireLeaderLaws.lean`, proved); `NewLeaseFromLeaseClient`'s
pattern updated. The three holder findings (`backend.txLive/snapRO/rtxStats`) are not from this branch
(it touches no backend file; they did not fail the gate). Build/tcb/axiom-tok results:
`/shared/tmp/k8s7f3a/{full3,tcb3,atok3}.log`: full build passes (17486 jobs), tcb matches (870/4), axiom-tok ok (0 unknown, 0 truncated).

Next, in order: 81's word on the third part; if the axiom-tok log is clean, `etc/land.sh` (with
`LAKE_PACKAGES=/shared/tmp/manifest-ddc.json`, not under GOWORK=off; re-merge lean if refused: the
etcd_auth_safe landing may be ahead); report the lean hash. Then 7f-3b per the design below (81
approved: `wrespIs` itself carries `evOwn`; report the mvcc interface diff before landing 7f-3b).

## Handoff point (2026-11-13, fourth 7f-5 agent, later): T5-a approved; land BLOCKED by the axiom-tok gate

81's review: approved as written (freeze note "T5-a review"); STATUS entry added; lean merged
(`51ee20f154`, clean; the merge adds no trusted text but ours). `etc/land.sh` (log
`/shared/tmp/k8s7f3a/land.log`): build, links, tcb (870/4 after lean's auth-schema-fix), 55 collections
ok, but **axiom-tok FAILED**: `WithRequireLeader.wp_proof`'s walk truncates ("stuck:
Perennial.context.isContextDone", inside `watchCtx`'s `#HDone` over the program-picked `s`), and
`etc/axiom-tok-allow.txt` says no `trunc` line may be added. lean unchanged. STOPPED for 81:
- (recommended) restate the axiom's first clause without `watchCtx`: `□ (∀ Φ, WP ctx.Done() {{Φ}} -∗
  WP c.Done() {{Φ}})`, the same for `Err()`, and `metadata.outgoingCtxOkC c` (the `#HCC` part is
  already the `Value` transfer at `&cancelCtxKey`); `watchCtx ctx s -∗ watchCtx c s` then a proved
  lemma outside the axiom. A trusted-text change (same meaning, more direct): needs 81's review.
- or a `trunc` entry for it (against the ratchet's rule).

7f-3b: design drafted (below), no Lean written.

## 7f-3b design (D2), started 2026-11-13 by the fourth 7f-5 agent; no Lean written yet

Go (fork pin 0b50f0426): `newWatcherBatch` (`watcher_group.go:79-96`) allocates a fresh
`&mvccpb.Event{Type, Kv, PrevKv}` per (watcher, event); the three send sites
(`watchable_store.go:309` moveVictims, `:401` syncWatchers, `:490` notify) send `eb.evs`, the batch's
own copies; v3rpc's `sendWatch` (`watch.go:437-455`) writes `events[i].PrevKv = r.KVs[0]` into
those copies (`events[i] = evs[i]` copies the pointer only). So each event a watcher receives is
owned by that watcher's response, but the Kv it points at is shared.

Proposed vocabulary (mvcc, `InvWatchBatch.lean`, exported through `Spec/.../mvcc/Api.lean`):
- `evRd e ev` (persistent): `e ≠ null`, every field but `PrevKv` `↦□` (state, Type = evType ev,
  Kv = p ≠ null, unknownFields, sizeCache), `kvPtrFixed p ev.kv`. Law `evIs e ev ⊢ evRd e ev`.
- `evPk e ev` (owned): `∃ q, PrevKv-field ↦ q ∗ (match ev.prevKv with none => q = null | some pk => kvPtrFixed q pk)`.
- `evOwn e ev := evRd e ev ∗ evPk e ev`; law: `evOwn e ev` with the field discarded gives back
  `evIs e ev'` (struct recombination: typedPointsto combine), for the send loop's handover to grpc.
The store's shared events (`kvsToEvents`, `rangeEvents`, `End`, the `notify`/`syncWatchers`
arguments) stay `evIs`; `newWatcherBatch`'s post, `eventBatch.add`/`watcherBatch.add`,
`ownEventBatch` (and the victims), `watcher.send`'s pre (events owned; on success handed to the
channel, on failure kept) and `wrespIs` (mvcc API: the channel's responses) take `evOwn`.
Readers of the fields (`IsCreateEvent`, `filterNoPut`/`filterNoDelete`, `eventBatch.add`'s
`Kv.ModRevision`, client `WatchContent.evIs_facts`) move to `evRd`.

Files (from grep of evIs/wrespIs/ownEventBatch/ownWatcherBatch): mvcc `InvWatchBatch`, `InvWatchFrac`,
`InvWatchStore`, `MoveVictimsLemmas`, `WatchSendLemmas`, `eventBatch__add`, `watcherBatch__add`,
`newWatcherBatch`, `watcher__send`, `watchableStore__{notify,syncWatchers,moveVictims,cancelWatcher,watch}`,
`watchableStoreTxnWrite__End`, `kvsToEvents`, `Api/WatchLaws`, `Spec/.../mvcc/Api.lean` (wrespIs: the
API change, interface diff); v3rpc `WatchApi`, `serverWatchStream__sendLoop`, `PerTypeWatch`,
`InvWatchStream`, `WatchLemmas`, `filterNoPut/Delete`, `IsCreateEvent` (specs); examples mvccfull
`stream__receive`/`stream__watch`, mvccrand `watchCheck__receive`; client `WatchContent`, `WatchRun`.

Open question for 81 (recommend (a)): (a) `wrespIs` carries `evOwn` (non-persistent; the channel's
element predicate hands it over), or (b) a second response predicate for the PrevKv fields beside a
persistent `wrespIs`. Order: vocabulary + laws first (built), then mvcc proofs bottom-up, then the
interface diff (STOP before landing per 81), then v3rpc's recvLoop/sendLoop with `swsMuP`.

## Handoff point (2026-11-13, fourth 7f-5 agent): T5-a fallback done; STOPPED for 81's axiom review

Done (on `k8s-7f5`, not landed; lean has moved on, merge it before landing):
- `17c793098e`: translation of `WithRequireLeader` and grpc metadata's helpers
  reverted, `WithPrevKV` kept; `etc/goose.py --project etcd`, `--check` pass; `etc/gen-init.py`
  (`--check` passes; metadata `Init` and the `PkgTable`s back to lean's); metadata's SpecPlan PkgInit
  back. Untracked SpecPlan PkgInit files the generator created (older drift on lean, listed in
  `/shared/tmp/k8s7f3a/specplan-untracked-drift.txt`) are left untracked, not committed.
- `fddf2cdf9b`: `WithRequireLeader.spec` restated (pre `watchCtx ctx s ∨ ⌜ctx = backgroundCtxVal⌝`;
  post `watchCtx ctx s -∗ watchCtx c s`, the WP and chain `Value` transfers for keys not of
  `mdOutgoingKey`'s type, and the old `WithCancel(c)` triple under `⌜ctx = backgroundCtxVal⌝`);
  `NewLeaseFromLeaseClient` adjusted (an arbitrary `s`, the right disjunct); `specGen` removed from
  `Draft7f3a.lean`; Go tests `examples/premisefix/watcherctx/requireleader_spec_test.go` (all pass);
  freeze note "T5-a addendum"; Scope §8 Q2 superseded; questions.md entries.
- Full build passes; `etc/tcb-report.py --check` matches (869/4; the axiom's name unchanged, its text
  changed); details in the freeze note's "T5-a addendum", "Checks". STOPPED for 81's axiom review.

Next: 81's axiom review of the T5-a addendum; apply its fixes; `etc/tcb-report.py --check --update`
only if the text changed the baseline (expected: no line change, the axiom's name is the same);
merge lean; land on 81's go. Then 7f-3b (D2: mvcc's response contract hands over an owned `PrevKv`).

## Handoff point (2026-11-13, end of the third 7f-5 agent): S2 decided; T5-a fallback next

81's S2 decisions (2026-11-13, also in questions.md):
- **D1 fallback.** Restate `WithRequireLeader.wp_proof` (`Proof/go_etcd_io/etcd/client/v3/WithRequireLeader.lean`,
  spec `Spec/.../WithRequireLeader.lean`) to `specGen` (now in `Draft7f3a.lean`; move it into the Spec
  file) in `withVersion.spec`'s pattern. Keep the old `Background()` clauses (`libCtxOk`, `outgoingCtxOkC`
  after `WithCancel`) as a proved corollary, or keep them in the axiom if a corollary is not derivable;
  the lessor's caller must keep working. Go tests in `examples/premisefix/watcherctx` or a sibling:
  every key that is not `mdOutgoingKey` answers as the parent does, through `Value` and the chain;
  Done/Err/Cause are the parent's; same descriptor. Supersede Q2 in questions.md and in
  `notes/k8s-7f5-scope.md` §8 (reason: translation needs 3-4 trusted changes vs 1).
- **Revert the translation** of `WithRequireLeader` and grpc metadata's helpers (`NewOutgoingContext`,
  `Pairs`, `MD.Copy`, `MD.Set`, `copyOf`, `mdOutgoingKey`, `rawMD`, and the imports): restore
  `Code/google_golang_org/grpc/metadata.toml` to lean's, drop `WithRequireLeader` from
  `Code/go_etcd_io/etcd/client/v3.toml`, **keep `WithPrevKV`**; then `etc/goose.py --project etcd`,
  `--check`, `etc/gen-init.py` (metadata Init + PkgTables go back), metadata's SpecPlan PkgInit
  (`etc/gen-specs-pkginit.py`, keep only that file's change). Nothing else needs them (checked: only
  `WithRequireLeader` calls them).
- **D2 yes:** in 7f-3b the mvcc response contract hands over an owned `PrevKv` field per event; list the
  interface diff for review at landing.
- **D3 yes:** `specGen` without the metadata content.
- S1-S9 stay as drafted (`Draft7f3a.lean`, unlinked).

Next, in order: revert the translation as above; the restated axiom with its Go tests (Addendum in
`notes/k8s-7f5-freeze.md`, "T5-a"); build (targeted, then full under flock); `etc/tcb-report.py --check`
(expected: same count, `WithRequireLeader.wp_proof` changed text; collections that reach it);
STOP for 81's axiom review. Then 7f-3b.

## Handoff point (2026-11-13, third 7f-5 agent): 7f-3a at S2 (STOPPED for 81's review)

Done (on `k8s-7f5`, not landed):
- Translation config (Q2) applied: client `WithPrevKV`/`WithRequireLeader`; grpc metadata's
  `NewOutgoingContext`, `Pairs`, `MD.Copy`, `MD.Set`, `copyOf` (imports context/strings/fmt);
  `etc/goose.py --project etcd`, `--check` passes; `etc/gen-init.py` (metadata Init + 17 PkgTables);
  SpecPlan PkgInit for metadata only (the generator's other drift is lean's, ungated, left alone).
  The axiom `WithRequireLeader.wp_proof` still stands over the translated function.
- `EvModel` gains `prevKv : Loc := null` (InvStore.lean; InvWatcher's countable instance updated).
- The statements: `Proof/go_etcd_io/etcd/client/v3/Draft7f3a.lean` (unlinked; `P`-suffixed new
  forms + `WithRequireLeader.specGen`; laws proved, no sorry/axiom), the Draft
  `notes/k8s-7f3a-draft.md` (table old → new, findings, plan, decisions D1-D3).
- Findings: (1) Q2's "no new axiom" is false: translating WithRequireLeader needs WithValue.spec
  at grpc's key (+ valueCtx fields, watchCtx), an intro law for opaque builtRawMD (ToLower too weak
  for its case clause), FromOutgoingContext over a non-isContext parent; recommended the fallback
  (one restated axiom). (2) 7f-3b: the send loop writes `PrevKv` into mvcc's events, which mvcc's
  API gives read-only (`evIs`): an mvcc API ownership change.

Checks: full build passes (16 min, `/shared/tmp/k8s7f3a/full.log`); `etc/tcb-report.py --check`
matches the baseline (869 axioms, 4 sorries); `etc/goose.py --check` passes.

Next (after 81's decisions D1-D3): 7f-3b (mvcc event ownership, v3rpc recvLoop/sendLoop), 7f-3c (client, swap, users).

## Handoff point (2026-11-13, second 7f-5 agent): S1 LANDED (lean `be36a0f818`); 7f-3a next

S1 with the review's fixes landed (`0d873a9ee5`, `be36a0f818`; freeze note "S1 review"; gates all
passed; trust base 869 axioms, 4 sorries). The branch `k8s-7f5` is lean now; continue on it.

**Next: 7f-3a's statements, up to hard stop S2** (Scope §6 row 7f-3a; parent `notes/k8s-7f-scope.md`
§2.3 1-2, §5.1). Nothing of 7f-3a written yet. In order:
1. Translation config (no trust; from `/shared/tmp/k8s7f5/goose-dry-full.patch`):
   - `Code/go_etcd_io/etcd/client/v3.toml`: add `WithPrevKV`, `WithRequireLeader` to `translate`;
   - `Code/google_golang_org/grpc/metadata.toml`: `translate = ["!*", "NewOutgoingContext", "Pairs",
     "MD.Copy", "MD.Set", "mdOutgoingKey", "rawMD", "copyOf"]` (**copyOf**: the S1 review),
     `imports = ["!*", "context", "strings", "fmt"]`;
   - `etc/goose.py --project etcd` (not with GOWORK=off), `--check`.
   - Consequence to handle: `WithRequireLeader` is today names-only with an axiom
     (`Proof/go_etcd_io/etcd/client/v3/WithRequireLeader.lean`, `Background()` only). Translated, that
     axiom becomes a proof over `FromOutgoingContext` (existing spec), `Pairs`/`NewOutgoingContext`
     (translated: `context.WithValue`) and `strings.ToLower` (trusted: some string): the trust base
     loses an axiom (report it; `--check --update` after 81's review). The generalized triple over a
     `watchCtx` parent (T5-a: every other key, Done/Err/Cause the parent's; the metadata "the
     parent's plus one key") is a 7f-3a statement.
2. The statements (Lean text in a Draft note, e.g. `notes/k8s-7f3a-draft.md`, for 81's S2 review;
   no `sorry` under a linked result, so do not change linked definitions before the review):
   - `OpFull.isRangeWatch` (`Proof/go_etcd_io/etcd/cache/v3/InvEtcdTxn.lean:1231`) drops
     `o.base.prevKV = false`; `wrRO`'s `prevKV ↦□ false` (`client/v3/InvWatch.lean:846,859`) becomes
     the model's value;
   - `EvModel` (`cache/v3/InvStore.lean:185`) gains `prevKv : Loc` (null = none); `eventAt`
     (`InvStore.lean:1214`) gains the `PrevKv` field; `eventIs` (`client/v3/WatchStateDefs.lean:102`)
     gains: `prevKV = false → prevKv = null`; else null (always admitted:
     `issues/etcd-watch-prevkv-before-created.md`), or, for a non-create, `kvValAt prevKv` of the
     key's kv at `ev.rev - 1` (`σ.at (r-1)`, as `KVState.revEvents`); a create's is null;
   - `rawRespOk` (`WatchStateDefs.lean:261`) the same at the server's level (`mvcc.stateAt L (r-1)`);
   - the server: `swsMu` allows `prevKV` entries (`v3rpc/InvWatch.lean`), `recvLoop` records
     `creq.PrevKv`, `sendLoop`'s branch `watch.go:442-455` (`watchable.Range` at `ModRevision - 1`).
   - Callers passing `prevKV = false` must see no change (watchkv, cachekv, linkv3p `MainWatch`, the
     compactor, `etcdstart.Collect`).
3. STOP (S2): report the statements and the config's trust-base effect.

## Handoff point (2026-11-13, end of the first 7f-5 agent's context): S1 reviewed; fixes next

S1 (`c46c52934c`) passed 81's axiom review with one MAJOR and minors. **Do these, in order** (81's
decisions, verbatim in the worktree's `questions.md`, last entry; review journal
`/root/.claude-csail/projects/-shared-etcd-grove/c04a65b0-a272-4ae4-94c7-91aa4a20ea30/subagents/workflows/wf_115e23d1-72c/journal.jsonl`):

1. **T5-c (MAJOR).** In `Proof/k8s_io/apiserver/pkg/util/feature/Gate.lean`, do not quantify the `Set`
   triple over every `b`. Add a table in the trusted text giving one fixed value per feature
   (`WatchList ↦ true`, every feature B5 covers ↦ `false`, e.g. `k8sSetValue : GoString → Option Bool`
   or two lists), and specify `Set(setArg s v)` only for `s` with its table value `v`. Then
   `featureOn`/`featureOff` of one feature are unreachable by construction (`featureSet g s v` for the
   one `v`). Restate the header's assumption: no other mutator runs; repeats of the same value are
   harmless. Drop "before any Enabled" if no triple needs it (none should). Callers to adjust:
   `noStreaming.lean`, `watchList.lean` (the side condition becomes the table lookup).
   Add `ResetFeatureValueToDefault` and `AddDependencies` to the mutator lists (Gate.lean header,
   freeze note S0.4, the grep). Make the closure check cover `examples/k8s/daemonset/dsmain` too, or
   state with evidence why it is outside. Turn the check into a script (e.g. `etc/featuregate-check.py`:
   `go list -deps` of the k8s examples, grep the mutators, compare to an allow-list with each hit's
   verdict) and wire it into `etc/gates.sh` (B5 has no gate today, as far as this agent saw; add one
   for both). The S0.4 grep command is in this agent's history: closure via `go list -deps -f` with
   GoFiles, regex over `DefaultMutableFeatureGate\.(Set|SetFromMap|OverrideDefault|SetEmulationVersion|Add)|\.SetFromMap(WithLogger)?\(|OverrideDefault(AtVersion)?\(|SetEmulationVersion|DeepCopyAndReset|featuregatetesting|ReplaceFeatureGates|AddFeaturesToExistingFeatureGates|DefaultMutableFeatureGate *=|DefaultFeatureGate *=`
   (hits saved in `/shared/tmp/k8s7f5/k8s-mutator-hits.txt`).
2. **T5-c docstring (minor 3).** Gate.lean's `Set` error branch says "changes nothing `Enabled`
   reads": inaccurate in Go (a failed `Set` stores the raw pair in `enabledRaw`, poisoning later
   `Set`s: `feature_gate.go:500-504`; `watcherctx` scenario `failed-set`). Reword (what is true: the
   map `Enabled` reads, `enabled`, is not stored; `enabledRaw` is).
3. **T5-a (minor 2).** Add grpc metadata's `copyOf` to the translation config (in the dry-run patch
   `/shared/tmp/k8s7f5/goose-dry-full.patch` for 7f-3a; no new trust). State the Lean result honestly
   ("parent's metadata plus one key": `strings.ToLower` is trusted to return some string), or fix it.
   Strengthen `examples/premisefix/watcherctx/requireleader_test.go`: a non-trivial `Cause` (a parent
   cancelled with `WithCancelCause(errX)`: the child's `Cause` is `errX`), and a NoAlias test that would
   fail without `Copy` (e.g. a parent `MD` whose `hasleader` key exists with another value, or check
   that writing the child's `MD` slice does not change the parent's).
4. **S0.1 (minor 4).** In `notes/k8s-7f5-freeze.md` §S0.1, add the row `getCurrentStorageRV(ctxRL)`
   (`watcher.go:146,193-209`; `store.go:240,735`: with RV 0, WatchList on and SendInitialEvents false,
   `getStartWatchResourceVersion` calls it on `ctxRL` before `createWatchChan`). Say that the strict
   control covers only RV > 0 with a fake watcher, and cite the reviewer's real-member recording test
   `/shared/tmp/coord-81/k8s7f5-review/clientkeys/keys_test.go` (or extend the control).
5. Rebuild (targeted, then the full build under flock and the cap), `etc/tcb-report.py --check
   --update` (one new axiom expected, `k8sfeature.featureOn_persistent`; report if it changes), the
   collections (`--collection etc/tcb-collections/k8setcd3.txt --check --update`; check all 55: the
   loop must not be cut by `head`), gates. Add an "S1 review" section to the freeze note (each finding,
   the fix). Add a STATUS entry (oldest moved to status-history's list, append only, `wc -l` check),
   noting the temporary premise of Q6 is not yet introduced (7f-5a). Merge lean, land via
   `etc/land.sh` on 81's go, report.

## Next, in order
1. DONE (`23af282dca`): S1 built (full build passes), checks in `notes/k8s-7f5-freeze.md` "Checks"
   (tcb: NEW `k8sfeature.featureOn_persistent`, also in collection k8setcd3; not updated). STOPPED for
   81's axiom review of S1.
2. After the review: apply its fixes; `etc/tcb-report.py --check --update` and the k8setcd3
   collection's `--update`; STATUS entry; merge lean; land S1 via etc/land.sh (81's go). Then 7f-3a statements (with T5-a's translation: the dry-run
   patch `/shared/tmp/k8s7f5/goose-dry-full.patch` has the client/metadata toml lines), STOP (S2).
3. 7f-3b/3c, and 7f-5a's Draft in parallel (Q1), STOP (S3) at the Draft.
4. Left from S0: the many-watches check (Scope §5: `isClientWatcher` persistent, repeated `Watch`).

## Pitfalls
- Every trusted text over a context must state every `ctx.Value` key the modelled code reads,
  and the methods called on what it returns (APF's `Signal()`: `apf_context.go:50-51`).
- `prevKv` none is reachable without compaction (`issues/etcd-watch-prevkv-before-created.md`): the
  client spec must admit it.
- `watchGRPCStream.run` (3368 lines): check with `etc/lean-check.py --fast --split`.
- The etcd fork's sources at the pin `0b50f0426` are in the module cache
  (`~/go/pkg/mod/github.com/upamanyus/etcd/{client,server,api}/v3@v3.0.0-20261112123031-0b50f04262d9`);
  `.lake/go-src/etcd` is at another revision.

## Build
Every lake command with `--packages=/shared/tmp/manifest-ddc.json` (scripts: `LAKE_OPTS=...`), under
`systemd-run --scope -q -p MemoryMax=64G`; full builds also under `flock /shared/tmp/etcd-grove-build.lock`.
Go tests under `systemd-run --scope -q -p MemoryMax=32G`, `GOWORK=off`, `PATH=/usr/local/go/bin:$HOME/go/bin:$PATH`.
This worktree's `.lake/build` state: as 7f-4 left it; check `df -h /shared` before any seeding (ask 81).
