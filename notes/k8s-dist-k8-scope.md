# k8s-dist K8: the store over a shared KV (scope, 2026-11-28)

Session K8-0 (etcd-grove-03's brief), branch `k8s-dist-k8/2026-11-28` off `lean` @ `5212560c0d`. Scoping only:
no Lean, no build. Sources: `notes/k8s-dist-lean-plan.md` (row K8, on `k8s-dist-k9/2026-11-28`), `notes/etcd-dist-plan.md`
§23/§26 (`KVPfxDist`), `notes/k8s-dist-k4.md`, `notes/k8s-dist-k9.md` (Handoff K9-20), the K1/K6 packet
`notes/k8s-dist-statement-packet.md` (branch `k8s-dist-stmt/2026-11-28`), the in-process driver
(`Proof/.../examples/k8s/etcd3/Inv.lean`, `realCheck`), Go `examples/k8s/dist/{store,storecodec}.go`.

## 1. The invariant

**In-process today** (`etcd3/Inv.lean`, `kInvBody γ c g0 γk`): one invariant holds etcd's whole client half
`etcdKV γk σ` (the sole writer), the lintest ghost history `ghostVar γ.h ½ h` with `run (k8setcd3S g0).M … h = some S`
(`pM (kSpec g0)`), the pending writes `ghostMapAuth γ.p`, the revisions' states `revOwn` (`γ.r`, `RevOk`,
the changes' mono list `γ.ch`, `KHistI`: no compaction, base fixed, **one change per revision of the whole KV**),
the store's history authority `shistOwn c σ` (`histAuth c.γh σ`, updated at every `KvNext` step), and `KOk c g0 S σ M nx`
(some configuration of `S` relates to `σ` by `KRelH`, `cf.st.hist.length = σ.rev`). Every step of etcd's state
passes through it, which is what keeps `histAuth` and `revOwn` complete.

**Dist (`kInvD`, new `Proof/.../k8s/dist/StoreInv.lean`).** What the driver owns:
- **The `/registry/` prefix share.** The start (K12) allocates `kvPfxH Γ.kv "/registry/" γs okS γhs σ₀` and the
  half `ghostVar γs ½ (view)`; `kInvD` is the owner's invariant `inv (kvClientN.@"k8s") (∃ v, ghostVar γs ½ v ∗ W v)`
  of `KVPfxDist`, `W` = `kInvBody` with `etcdKV γk σ` replaced by "the last state `σl` the store saw, its
  view `v`". The compactor workload owns `/k8sdist-compactor/` (its writer) and `compact_rev_key` (a second prefix,
  or the same owner): apart from `/registry/`, so its writes are `PfxLocal` elsewhere.
- **Foreign revisions** enter only at the store's own firings: `kvPfx_au1H`/`kvPfx_readAuH` hand the callback the
  current full `σ` (with `KVExt σ₀ σ`, a lower bound of `σ.changes`). Between `σl` and `σ` every change is
  foreign (no key under `/registry/`), so `W` catches up in one go: the ghost run takes `σ.rev - σl.rev` foreign
  steps (K4's `foreignL`: items kept, `rv + 1`, the store re-appended to `hist`), `histAuth` gets one entry per
  foreign revision (`histAuth_next` iterated over `σ.at r → σ.at (r+1)`, each a `KvNext` with no `/registry/` change),
  `revOwn`'s map gets those states. **Gap:** today's share proves "no other owner changed my keys" only through the
  current view, which does not exclude a put-then-delete. The ghost variable must carry the prefix's
  revision-indexed changes (`pfxChs p σ : List (Nat × List Change)`), which other owners' `PfxLocal` updates keep;
  equal `pfxChs` then means "no `/registry/` change in between" (K8-2).
- **Compaction** never changes the client `KVState` (`KVExt` keeps `σ.compacted`; `KV_Compact_dist` is a permit,
  `kvCpOk`), so `KHistI`'s `compacted = 0` and base stay. It enters only as error arms: a range at a compacted
  revision fails (a failed read, `errR`, constrains nothing); a watch's compacted end is an Error event, dropped
  by `Model`. The proof obligation is the provenance (§2 K8-5): `StoreOut.Compacted → PastRead in ∨ PinnedRead in`.
- **`KHistI`'s one change per revision** is false of the shared KV in general (it holds of this deployment's
  writers, but no share states it). Weaken it to `/registry/` keys only (what `oneKeyRevs` already says): the
  watch proofs read only prefix events.
- **The linearization ghost** is lintest's, over the semantic model with foreign steps: `kSpecF g0` (`kSpec g0`
  plus `foreignL` as a silent step; K4's `SReach`/`SRun`). linkv's `PendSpec` (`lib/txnwork/PendModel.lean`) has no
  extra silent step: either add one (`silent : St → St → Prop`, default `False`; touches every `PSilent` case split
  in txnwork's users) or define `pMF` beside it in `k8s/dist` with its own `run`/`IsLinearization` lemmas.
  Decide in K8-3's first hour. Its output: `IsLinearization (pMF (kSpecF g0)) (histOf lops) ord` ⇒ `SRun g0 ⟨g0,[]⟩ xs c'`
  in `ord`, what K9's `searchRun_accepts` takes.
- **Several API servers** (`StoreNode` per machine, `NewStoreOnly` each): one `StoreCfg` per store, differing
  in `kc`/`cl`/`mt`/`lt`, all sharing `γh`, `pfx`, `S`. `kInv` reads only those (`kvWf c`, `shistOwn c`,
  `cachedObjOk c`), so `kInvD` is stated over the shared fields (`kInv_same`-style law), one invariant for all.
- **Across machines**: `kInvD`, the share and the lintest half live at the global GS (as `kvPfxShare`,
  `Gg := hG.goose_globalGS`); the linearization update crosses `remote.Do` as kvremote's slot update
  (`kvremote/Node.lean`, `opMaybe_svcOp`). `Record`/the cache are on the orchestrator: `ansOk`/`cachedObjOk` facts
  are persistent and must ride in `Serve`'s post (K10 carries them over the codec).

## 2. Steps, in order

| # | What | Lean targets | Size | Depends | Statement? |
|---|---|---|---|---|---|
| K8-1 | **Foreign erasure** (pure): a run of the semantic model whose history shows no foreign revision is a run of `kSpec`; and the shared seed is `realCheck`'s | `noForeign_erase : SRun g0 c0 xs c' → NoForeignOk g0.st.rv xs m → FailureFreeL xs → ∃ c'', PRun (kSpec g0) … xs c''` (foreign steps after the last write move past every read: K4's `HRel` renaming, `SharedRename.lean`); `runOk_seedShared : 1<r1<r2<2^63 → RunOk (seedSharedL r1 r2)` (`RealB4.RunOk`: `HistSorted`, `HistGood` of the padded history) | 1 | K4 (lean), K9's `NoForeignDefs`/`SeedSharedDefs` (branch `k8s-dist-k9`) | none: now |
| K8-2 | **The share with the prefix's history** | `KVPfxDist`: the ghost variable at `(pfxView p σ, pfxChs p σ)` (or a second one), `kvPfx_au1P`/`kvPfx_readAuP` (the callback also gets "no `p` change after the owner's last"), `pfxLocal_txn`/`pfxLocal_delKey` (the store's compare-put/compare-delete/else-get Txn under `p` is local); N9a/F5 laws kept as corollaries | 0.5-1 | none | none: now |
| K8-3 | **`kInvD` and its laws** | `StoreInv.lean`: `kSpecF`/`pMF` (or the PendSpec field), `kInvD`, `KOkD` (with `KHistI` prefix-only), `kOkD_{ok,list,errW,errR,obs,pend,same}` (the in-process ones over the caught-up state), **`kOkD_foreign`** (catch-up: `histAuth_catchup`, `revOwn_catchup`, ghost run's foreign steps), `kInvD_same` (several stores) | 2 | K8-2 | none: now |
| K8-4 | **The updates the store fires** | the driver-side AUs (`applySpec`'s `k8sAu1`, reads, the `getCall`/`rwCall` call invariants) built from `kvPfx_au1P`/`readAuP` instead of `etcdKV`; the `K8sEtcd.Laws` (K5) are instance-agnostic (`[∧list] γ ∈ K.kvs`), so this is against K5's abstract laws | 1 | K8-3, K5 | none for the AUs; the writes' `unkErr` needs `kvErr` of `Txn_Commit_dist` (GAP-2) end to end |
| K8-5 | **Compacted provenance** (GAP-1's half) | library: `rangeErrSound`'s compacted conjunct (packet §2.4 item 1, in-process, proved: `client/v3/kubernetes/Defs.lean:315`, `Client__{Get,List}`); `listErrF`/`store__GetList`'s error arm: `IsResourceExpired e →` the etcd range was at `withRev > 0`; `store__{Get,Create,Delete,GuaranteedUpdate}`: never Expired; driver: `withRev > 0 → PastRead in ∨ PinnedRead in` (`listOptions`, `pastRead`), so `compacted(raw) → PastRead ∨ PinnedRead` (`storecodec.go:42`; watches are `PinnedRead`) | 1.5-2 (heavy: k8s cone) | K6 §2.4 item 1 (D2) | in-process half now; the dist half needs **D1** (`K.live := True`), **D2**, `KV_GetE_dist` |
| K8-6 | **Watches over the shared KV** | a dist `clientWatchOk` over `Watch_dist` (foreign events filtered out by the `/registry/objs/` range, bookmarks/progress at foreign revisions, a compacted stream as an Error event), `kOkD_obs` | 1-1.5 | K8-3; `Watch_dist`'s compacted arm | if `Watch_dist` lacks a compacted arm: a K6-like axiom change (new doubt) |
| K8-7 | **`Serve` on an API server** | `Serve.spec` (dist): `{isStore c_a ∗ kInvD ∗ slot update} Serve(s, in) {out. Φ out ∗ ansOk ∗ ⌜compacted(raw) → PastRead ∨ PinnedRead⌝}`; `NewStoreOnly`'s spec (`etcd3.New` without seeds) | 1 | K8-4..6 | via K8-5 |
| K8-8 | **The check's argument** | `storeCheck_ok`: lintest's `RunLin2` post (model `AcceptAll`, ghost `pMF`) ⇒ `SRun` ⇒ `searchRun_accepts` ⇒ `CheckShared` not `Illegal`; and `FailureFree ∧ ¬compacted ∧ RawOK ∧ NoForeign` ⇒ K8-1 ⇒ `realCheck.spec`'s premises ⇒ not `Illegal`; `SeedShared`'s `cli.Put` half (`wp_cliPut` of `KVCallsDist.lean` at the `/registry/` share: the two seed puts are owner updates) | 1 | K8-1, K8-3, K9 | none |

**Total: 9-10.5 sessions** (the plan's 4-8 left out K8-2, K8-6 and the library half of K8-5). K8-7 may move to K10.

## 3. Risks, ranked

1. **Compacted provenance is false somewhere in Kubernetes' store** (K8-5). The panic needs: no `ResourceExpired`
   on a Get, a write, or a List read at revision 0. Where it could break: `GuaranteedUpdate`/`Delete` with a cached
   object (`UseCached`) retrying through a path that reads at the object's revision; `GetList`'s legacy
   `rv > 0, Limit > 0` case on a non-recursive key; etcd answering `ErrCompacted` to a range at revision 0 while a
   compaction is applied (`kvstore_txn.go:78-83` says never). **Go test** (`examples/k8s/etcd3`, embedded etcd,
   `TestCompactedProvenance`): a goroutine compacts at the current revision every millisecond while the store
   runs `Gen`'s operations of every kind; assert `compacted(raw)` only when `PastRead(in) || PinnedRead(in)`, and
   count both arms (non-vacuity). One hour.
2. **Foreign revisions change an answer beyond its revisions** (K8-1/K8-3, K4's semantic model). `foreignL` keeps
   the items: true only if no foreign write touches `/registry/` and the store's answers depend on foreign revisions
   only through revision numbers. Where it could break: a watch's progress-notify bookmark or `syncPaginated` at
   a foreign revision; a paged List's continue token or `remainingItemCount`; NoForeign passing while a foreign
   revision was in fact consumed (a Get after it shows only object revisions). **Go test** (`TestForeignHeavy`):
   the in-process driver (one store) with a writer putting `/k8sdist-compactor/w` at 10x the store's rate, no
   compaction: `CheckShared` must be `Ok` in every mode it reaches, and on the histories where `NoForeign` holds
   `RealCheck` must be `Ok` (with K8-1 that is a theorem; the test checks the premise is satisfiable).
3. **`RunOk` of the shifted, padded seed** (K8-1). `realCheck`'s B2/B4 proofs take `RunOk g0`, proved today for
   seeds at 2 and 3; `seedSharedL r1 r2` repeats stores across foreign revisions (`padL`), which `HistGood`/
   `HistSorted` may forbid. **Go test** (`TestRealCheckShifted`): `SeededAt(5, 9)` and `SeededAt(2, 3)` on the same
   no-foreign history renumbered: `RealCheck` must agree. Minutes. If it fails, K8-8 needs a renumbering lemma.
4. **The share cannot see foreign steps** (K8-2/K8-3): `histAuth` and `revOwn` must be complete at every revision,
   and catching up needs per-revision `KvNext` from `σ.changes`; a `/registry/` put-then-delete by "someone else"
   is excluded only with K8-2's history in the ghost variable. Lean-only; settle by writing `kOkD_foreign`'s
   statement first.
5. **`PendSpec` has no foreign step** (K8-3): a field in txnwork rebuilds every linkv user; a copy in `k8s/dist`
   duplicates `run`/`IsLinearization` lemmas. Lean-only.
6. **Statement doubts**: D1 (`K.live := True`) and D2 (`crev ≤ cur` for the compacted half) block K8-5's dist half;
   GAP-2 (`Txn_Commit_dist` `kvErr`) blocks the writes' error arm end to end. If D2 fails, the compacted-at-no-old-
   revision panic is unprovable and the Go check must accept more (a Go change, G-new).
7. **Several stores, one ghost history**: per-store state (lease manager, versioner) is not in `kInv` today; a Go
   test already exists in effect (`TestDist` with `Apiservers ≥ 2`); add `Apiservers = clients` to one `-short` run.

## 4. What can start now on fk-lean2, without the statement approved

In order, each a session's checkpoint; base `k8s-dist-k9/2026-11-28` (for `NoForeignDefs`, `SeedSharedDefs`)
until K9 lands, then `lean`. Builds under `systemd-run --scope -p MemoryMax=56G`, targeted (`etc/importers.py --leaves`).
1. **The three Go tests** (§3 risks 1-3), before any Lean: `TestCompactedProvenance`, `TestForeignHeavy`,
   `TestRealCheckShifted` in `examples/k8s/etcd3` (no translated function changes; test files only).
2. **K8-1** (pure, light build: the `Shared*` cone): `noForeign_erase`, `runOk_seedShared`, in
   `Proof/.../k8s/dist/NoForeignErase.lean` (defs tier; no `Link` root yet).
3. **K8-2** (`KVPfxDist.lean`, etcd dist cone, moderate): the prefix history and `pfxLocal_txn`; check
   putget/durable/compact still build (`KVWorkLinked`, `CompactLinked`).
4. **K8-3's design decision** (PendSpec field vs `pMF`) and `kOkD_foreign`'s statement, then the invariant.
5. **K8-5's in-process half** (packet §2.4 items 1-2): settles D2 for the coordinator; heavy (k8s cone): one
   rebuild at the end, not per edit.

Not now: K8-5's dist half, K8-7 end to end, the `Txn` error arm (wait for D1-D3 and GAP-2's rule-#8 approval).

## Handoff K8-1 (2026-11-28)

Branch `k8s-dist-k8/2026-11-28`: `k8s-dist-k9/2026-11-28` (@ `d0a5e7e1d2`) merged in; the three risk tests of §3
in `examples/k8s/dist/risk_test.go` (test file only; each run a child process with fresh one-member etcds,
`go1.27.3`). All passed, no failure:

- **`TestCompactedProvenance`** (risk 1): 100 runs, 110 s; 168,000 operations (4 clients × 400, 2 watchers × 40),
  8,230 compactions at the current revision (about one per ms of run). 4,871 compacted answers: 4,823 under
  `PastRead`, 48 under `PinnedRead` only, **0 at no old revision**. By kind: list 4,822, watch 49 (no Get or
  write ever answered compacted). Risk 1 not observed.
- **`TestForeignHeavy`** (risk 2): 120 runs, 140 s, cycling modes `throughout` / `tail` (foreign writer from the
  last unary answer on) / `none` (no foreign writer), 40 each; 50,400 store operations, 260,141 foreign
  revisions (≈10 per store operation in the foreign modes). `CheckShared` Ok in all 120 (lazy model).
  `NoForeign` held in 8 `tail` and 4 `none` runs, never in `throughout`; `RealCheck` Ok in all 12. Note:
  `NoForeign` is false in most runs even with no foreign writer (Gen's MinRVs above the last write's
  revision are anchors above `M`), so the RealCheck arm of the dist driver runs rarely.
- **`TestRealCheckShifted`** (risk 3): 10 runs, 329 s; one sequential input sequence (3 clients × 120 + a watch
  every 10) on a cluster seeded at 2, 3 and, renumbered (2→5, 3→9, r≥4 → r+6), on one seeded at 5, 9 (foreign
  revisions 2-4, 6-8, the seeds' bytes copied). Unary answers identical up to the renumbering in all runs;
  `RealCheck` Ok/Ok (seeds 2,3 / 5,9) in all; crossed (history with the other seeds) Illegal/Illegal (non-vacuity);
  `CheckShared(SeededAt(5,9))` Ok. Note: Go's `realCheck` reads only the seeded store `st0`, not the padded
  history; the padding matters only to the Lean `RunOk`.

K8-1's Lean not started on the branch (coordinator, at the context limit). A draft of `runOk_seedShared`
(`seedAt`, `seedSharedL_hist`, `histN_seedShared`, `seedAt_ok`, `seedAt_change`; never checked) is at
`/shared/tmp/k8-1-NoForeignErase.draft.lean`, meant for `Proof/.../k8s/dist/NoForeignErase.lean`.
`noForeign_erase` not drafted: `PRun`/`FailureFreeL` do not exist; its conclusion should be what
`realCheck_pure` takes (`IsLinearization (linkv.pM (kSpec g0) decOp) (histOf lops) (List.range lops.length)`),
probably via a `linkv.PStep` run along the order; the collapse of trailing foreign steps is `SharedRename`'s
renaming (`CutW`, `mstepL_ren`).

## Handoff K8-2 (2026-11-28)

**Why `NoForeign` rarely holds (Go).** Instrumented `TestForeignHeavy` in mode `none` (a temporary diagnostic,
not committed: per run, `M`, the missing revisions in `(floor, M]`, and every revision an input or output names
above `M` with its source field, kind and error), 8 runs: `NoForeign` false in all 8, `CheckShared` Ok, 0 foreign
revisions. In every run the successful writes' revisions are exactly `4..M` (no gap: floor 3, `M` 82-107,
`M - 3` distinct write revisions), and the **only** revisions above `M` are **inputs' `MinRV` of Gets (kind 3) and
Lists (kind 4) answered `ETooLarge`**, 1-5 per run (e.g. `M = 93`: two Lists at MinRV 103; `M = 82`: Lists at
162, a Get at 129; `M = 97`: a List at 238). They are Gen's own draws: `minRV`'s last branch (`m ≥ 98`,
`etcd3/k8setcd3.go`) asks for the cached object's revision **plus** `d`, a future revision, to exercise
`TooLargeResourceVersion`. No compactor, seed, lease or other API server writes in this test (`riskFH` only; in
the dist store workload every API server's writes are in the history, the compactor is another workload).

So it is **by `NoForeign`'s documented definition** ("no revision any input or output names is above `M`"), not
a driver bug, but the definition is **stricter than its purpose**: a `TooLarge` answer to `MinRV > M` shows no
foreign revision. Erasure stays sound without that anchor: answered `TooLarge` at the shared run's revision `s`
means `MinRV > s`, and the erased run's revision is `min(s, M) ≤ s`, so `mgetL`/`mlistL` answer `tooLargeL`
there too (their first test, `uint.nat st.rv < uint.nat req`); and Kubernetes' checker already meets such
inputs in the in-process driver. **Proposed fix (statement-level, coordinator; program not changed):** in
`NoForeign`'s anchor test, leave out the input `MinRV` of an operation answered `ETooLarge` (e.g. a
`HistoryRevs` variant, or `NoForeign` computing its own maximum over the other anchors); the Lean side is
`NoForeignOk`'s `AnchorsOk` with `OpAnchors`' MinRV clause conditioned on the answer not being `tooLargeL`
(`Seeded__NoForeign`'s spec and proof follow). With it, `none` runs should give `NoForeign` true in all runs
(as all 8 had no other anchor above `M`), so D4's `RealCheck` arm runs whenever no foreign writer interleaves.

**Lean.** `Proof/.../k8s/dist/NoForeignErase.lean` (new, builds): K8-1's draft repaired —
`runOk_seedShared (r1 r2) : 1 < r1 → r1 < r2 → r2 < 2^63 → RunOk (seedSharedL r1 r2)` proved (with `seedAt`,
`range'_seedShared`, `seedSharedL_hist`, `histN_seedShared`, `seedAt_ok`, `seedAt_rv`, `seedAt_change`).
**`noForeign_erase` not proved** (budget). Done: `PRun g0 c xs c'` (`SRun` without the `foreign` silent
step: `linkv.PReach` then `PStep`) and `pRun_run` (a `PRun` is a run of `pSeq (kSpec g0)` on
`(x, ansOf y)`, from any closed model state holding its start). Plan, from reading `SharedSem`/`KList`/`KModel`:
1. Left of this step: through `decOp` (`boxIn`/`boxOut`, `plainOut`) to `run (pM (kSpec g0) decOp) init
   (vals (histOf lops) ord)`; the real-time half of `IsLinearization` comes unchanged from the shared
   linearization (same `ord`).
2. `FailureFreeL xs`: no `EOther` answer and no failed watch (Go's `failureFree`); then no `errW` step, so no
   pending write (`PSilent` never fires).
3. Before the last write, no foreign step: each successful bumping write answers `RV` = its new revision
   (`mcreateL`/`mdeleteL`/`mupdateL`, `mstepL_rv`), revisions only grow, so a foreign revision in `(f, M]` is
   one no write answers, against `NoForeignOk`'s first half (counting: `count_cover`).
4. After it, the foreign steps commute past every later operation (reads, no-op updates, watches): their
   answers at `foreignL^k c` equal those at `c` when every anchor is `≤ M = c.rv` (`mgetL`/`mlistL`: TooLarge
   test, `ListRV`, `histAtL` below `M` unchanged by appending; `watchOkL`: no event from a foreign revision,
   bookmarks are anchors). This is the bulk: a per-kind lemma, `mstepL_ren`'s read counterpart.
`realCheck_pure` also takes `GOks` and `hn`; `IsLinearization` there is with `List.range lops.length`, so the
dist linearization ghost must order `lops` as the in-process one does (K8-3's `pMF` decision).

Build of record: `lake build Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.NoForeignErase` at `5349a789f5`,
5270 jobs, OK, on **fk-lean1** (worktree `wt/k8s-dist-k8/2026-11-28`, seeded from `lean-warm`): fk-lean2 has
46 GB free, below `remote-check.sh`'s 65 GB to seed a worktree. The edit loop ran in fk-lean2's K9 worktree
(`rcheck8.sh`: my file copied there, the imports identical; the copy removed after).

## Handoff K8-3 (2026-11-28)

**G15 done** (`d7f986f03b`; recorded in `notes/k8s-dist-k9.md` beside G11-G14). Go: `HistoryRevs` records an
input's `MinRV` only when `in.Kind == KWatch || out.Err != ETooLarge` (`export.go`; `NoForeign`'s doc says so).
Lean: `OpAnchors`' first clause is `(x.Kind' = W64 5 ∨ y.Err' ≠ W64 6) → ∀ r, parseRVD x.MinRV' = some r →
uint.nat r ∈ A` (`SharedSearch.lean`); re-proved `HistoryRevs` (`MinOk`, the new nested `if`),
`SharedComplete` (list case under `Err = 0`), `SharedWatch` (`Or.inl hk`), `SharedModelDefs` (`targetL_lt`,
`sharedBounded_stepIdxOk`), both `opAnchors_mono`. No statement, axiom, premise or sorry changed (the
definition `OpAnchors` is weaker, so `FullComplete`'s premise `AnchorsOk` is weaker: K4 proves more).

**Go tests (go1.27.1)**: `go vet` clean; etcd3 package tests ok (330 s), dist package tests ok;
`TestForeignHeavy -count=24`: mode `none` **8/8 `NoForeign` true, `RealCheck` Ok** (was 0/8 for K8-2, 4/40
for K8-1), `tail` 8/8 true/Ok, `throughout` 0/8 (expected), `CheckShared` Ok in all 24; `-short TestDist` with
`DIST_DUMP` (95 operations), on it `TestReplayHistory` Ok and `TestCrossCheckWatches` pass.
`etc/goose.py --project k8s-apiserver` then `--check`: up to date.

**Build of record**: at `d7f986f03b`, on fk-lean1 (`wt/k8s-dist-k8/2026-11-28`), `lake build` of the leaves of
the changed modules (`k8s.all.TopLevelRobustness`, `k8s.compactor.Results`, `k8s.dist.NoForeignErase`,
`k8s.etcd3.Results`, `k8s.etcd3.SharedAccept`, `k8s_io.apiserver.pkg.storage.etcd3.Results`): 12710 jobs, OK.

**`noForeign_erase`: not proved, nothing new committed.** Unchecked draft lemmas (step 2: `FailureFreeL` =
`∀ p ∈ xs, okOut p.1 p.2`, `pStep_pend_nil`, `pSilent_nil`, `repeat_foreignL_succ`, `sReach_nil` (from no
pending write, silent steps are `Nat.repeat foreignL k`); step 4's bound `targetL_le_anchors` (with
`OpAnchors (range (m+1))`, the target is `≤ m`, so `skipToL` is the identity at `e.rv = m`)) at
`/shared/tmp/k8-3/NoForeignErase.unchecked.lean` (adds `import ...dist.SharedComplete`). Suggested route
for the main proof: reuse K4's `CRel.op`/`CRel.ok` with `A = range (m+1)`, search side = the erased run (no
pending: `SettleL` is `refl`; skip identity by `targetL_le_anchors` or `kstepL_target`), then `stepL_sound`
for `PStep`; invariant `e.rv = g.rv ∨ e.rv = m`. The open point is step 3 (no foreign step below `m`): a
no-op update's answer `RV` counts in `nfWriteRV`, so the cover argument needs "every item's revision is a
bumping write's" (HRel's `stored`/`ρ`), not just revision monotonicity.

## Handoff K8-4 (2026-11-28)

**`noForeign_erase` proved** (`Proof/.../k8s/dist/NoForeignErase.lean`, no `sorry`, no axiom):

```
theorem noForeign_erase (h0 : HSt) (xs) (c' : GCfg) (m : w64)
    (hlen : h0.hist.length = uint.nat h0.st.rv) (hlast : h0.hist.getLast? = some h0.st)
    (hseed : ∀ g ∈ h0.hist, ∀ it ∈ g.items, uint.nat it.obj'.ResourceVersion' ≤ uint.nat h0.st.rv)
    (hnf : NoForeignOk h0.st.rv xs m) (hff : FailureFreeL xs) (hr : SRun h0 ⟨h0, []⟩ xs c') :
    ∃ c'', PRun h0 ⟨h0, []⟩ xs c''
```

The statement had not been written before (only §2's sketch); its three seed premises `hlen`/`hlast`/`hseed`
are `FullComplete`'s (K4's `HRel.init`, needed to reuse `CRel`), true of the seeded store and already
discharged wherever K8-8 calls `fullComplete` on the same `h0`. Nothing else beyond the sketch.

- K8-3's draft lemmas checked (`pStep_pend_nil`, `pSilent_nil`, `sReach_nil`, `targetL_le_anchors`; the last
  needs `1 ≤ m`: a watch-list with `SendInit = 2` has target at least 1). `FailureFreeL` uses
  `k8s_correctness.okOut` (imports `etcd3.RealMS`, `etcd3.NoForeignDefs`; both defs tier).
- **Step 3** (`sRun_jr`): `JR r st` = "`r ≤ st.rv` and no item carries `r`" is kept by every silent and
  operation step, and no successful write answers `r` (`mstepL_items`, `mstepL_bump`: an advancing step is a
  successful write answering the new revision; `mstepL_keep`: a successful non-advancing write, the no-op
  update, answers an item's revision). A foreign step from `rv` makes `JR (rv+1)` hold, so `NoForeignOk`'s cover
  (`CovL`) rules out a foreign step while the store is below `m`. No statement change was needed.
- **Main** (`erase_go`, induction on `SRun`): invariant `CRel A n0 e g`, `e.pend = []`, and either
  `e = g` below `m` with `CovL` of the rest, or `e.rv = m`. Each step: `CRel.op`, `settleL_nil` (no pending:
  settle is `refl`), target `≤ e.rv` (`pStep_target` from the cluster's step, or `targetL_le_anchors` at `m`),
  `skipToL_le`, `stepL_sound`; at `m` no write advances (it would answer `m+1 > m`, against `NoForeignOk`).
  `M = max m h0.rv` handles `m < h0.rv`.

**Build of record**: `lake build ...k8s.dist.NoForeignErase` at `d07756f54b` on fk-lean1 (`wt/k8s-dist-k8/2026-11-28`): 5289 jobs, OK.

**Left for K8**: K8-8 wires `noForeign_erase` + `pRun_run` into `realCheck_pure` (step 1 of Handoff K8-2:
`decOp`, the same `ord`); the `pMF` decision (K8-3 §1) is still open.

## Handoff K8-5 (2026-11-28)

**`pMF` decided (routine, no statement change): a separate model in `k8s/dist`, not a `PendSpec` field.** A
field (a silent step in `PSilent`) changes `linkv.PSilent`/`pM`, which `Spec/.../k8s/etcd3/realCheck.lean`
(`IsLinearization (linkv.pM (kSpec g0) decOp)`) and the other txnwork/linkv specs are written in (25 files):
a spec-vocabulary change and a rebuild of every linkv user. `k8s/dist/SharedSem.lean` already has the
semantic model with foreign steps (`SSilent` = `kSpec`'s `PSilent` or `foreignL`, `SReach`, `SRun`), so `pMF`
is `pSeq`'s construction over `SReach`/`PStep` (sets of `GCfg`), with its `run`/`IsLinearization` lemmas beside it.

**Step "K8-2": `Proof/.../etcd/dist/KVPfxHist.lean`, new, additive** (`KVPfxDist` untouched: its 42 importers,
putget/durable/compact, do not rebuild). The ghost variable holds `pfxVH p σ = (pfxView p σ, pfxChs p σ)`
(`pfxChs` = `chsFrom p σ.compacted σ.changes`: the revisions with a change under `p`, with those changes).
`kvPfxInvP`/`kvPfxHP`/`kvPfxP_au1H`/`kvPfxP_readAuH`/`kvPfxP_alloc`/`kvPfxP_seen` are `KVPfxDist`'s at `pfxVH`;
`kvPfxP_au1H` also takes a lower bound `l0` of the changes (its step gets `l0 <+: σ.changes`, as readAuH's).
Pure: `pfxVH_local` (another owner's update keeps `pfxVH p`), `pfxVH_init`, **`pfxChs_same`/`pfxChs_same_ext`**
(equal `pfxChs`, changes extended ⇒ no change under `p` in between: closes the put-then-delete gap; the owner's
`W v` records `v = pfxVH p σl` with a lower bound of `σl.changes`). Built OK at `1ca71fabf4` (fk-lean1).
Then added (commit `pfxLocal_commit, ...`): `filter_applyChange(s)_other`, `pfxView_commit_other`, `commit_hist`,
`pfxLocal_commit` (an update committing changes under `p`, or nothing, is `PfxLocal p`), `pfxLocal_txn`,
`pfxLocal_deleteRange` (premise: every change of the op is under `p`; the store's Txn's key facts are left to
the caller). **That commit does NOT build** (stopped by the coordinator before fixing): line 199,
`Failed to infer type of binder σ` in `pfxLocal_commit`'s `have hoth : ∀ σ (cs ...` — `σ` is unused; drop it
from `hoth` (and from its two uses `hoth σ cs hcs ...`), then rebuild `...etcd.dist.KVPfxHist` on fk-lean1.

**Next**: fix line 199; the store's Txn premise of `pfxLocal_txn` (keys of `srvRunTxn`'s changes = its ops'
keys, compare-put/compare-delete/else-get under `/registry/`); then step "K8-3" (`pMF` as above, `kInvD` over
`kvPfxHP`, `kOkD_foreign` statement first).

## Handoff K8-6 (2026-11-28)

**Build fixed**: `KVPfxHist.lean:199` (`hoth`'s unused `σ` dropped); `...etcd.dist.KVPfxHist` builds (fk-lean1).

**`pfxLocal_txn`'s premise for the store** (`Proof/.../k8s/dist/PfxTxn.lean`, new): `srvOps_keys` (the server's run of a
model transaction's operations changes only their keys, puts and deletes), `pfxLocal_txnOf` (a `linkv.txnOf cs t e`
whose operations' keys are under `p` is `PfxLocal p`), `pfxLocal_delOp`, and the store's two Txns:
`pfxLocal_putTxn`/`pfxLocal_delTxn` (`opOf lk le (k8s.putTxn k v rev g)`/`(k8s.delTxn k rev g)`, `p <+: k`).

**`pMF`** (`Proof/.../k8s/dist/SharedPend.lean`, new, no sorry): `fpost` (silent `SReach`, a non-wrapping `PStep`,
`SReach`), `fInit h0` (= `SReach h0 ⟨h0, []⟩`, closed), `pSeqF`/`pMF h0 dec` (same state type `linkv.PSet HSt Input`,
so `k8setcd3S`'s `rep`/`ioOk` carry over), `pMF_step`, `pSeqF_step_of` (the owner's step), `pSeqF_step_some`, `FClosed`
(+ `fInit_closed`, `fpost_closed`, `pSeqF_step_closed`, `FClosed.foreign`, `FClosed.pend`), `SRun.reach_pre`,
`pSeqF_run`, `pSeqF_run_nonempty`, and **`pMF_run`**: `List.Forall₂ (fun a p => dec a = some (p.1, ansOf p.2)) l xs →
run (pMF h0 dec) (pMF h0 dec).init l = some S' → ∃ c', SRun h0 ⟨h0, []⟩ xs c'` (K8-8's input to `searchRun_accepts`).

**`kInvD` started** (`Proof/.../k8s/dist/StoreInv.lean`, new, definitions only): `regP = "/registry/"`; `keysOkP`/
`valsOkP` (the workload's keys/values only under `regP`), `OneChangeP`/`KHistID`/`revOwnD` (one change per revision
under `regP` only), `KOkD` (`KOk`'s fields, `closed : FClosed g0 S`, `keys`/`vals` prefix-only), `kInvDW γ c g0 σ₀ σl`
(`kInvBody` without `etcdKV`: lintest ghost over `pMF g0 decOp` from `fInit g0`, `revOwnD`, `shistOwn`, `KVExt σ₀ σl`,
`KOkD`), `kInvDBody` (`∃ σl, ghostVar γs ½ (pfxVH regP σl) ∗ kInvDW … σl`), `kInvD` (`inv (kvClientN .@ "k8s")`).

**`kOkD_foreign`'s statement** (in Lean as `kOkD_foreign.law c g0`, an `abbrev`, to be proved as `kOkD_foreign`):
```
∀ S σl σ M nx m, CfgD c → KOkD c g0 S σl M nx →
  σ.compacted = σl.compacted → σ.base = σl.base → σ.changes = σl.changes ++ m →
  (∀ cs ∈ m, ∀ ch ∈ cs, ¬ regP <+: ch.key) →          -- pfxChs_same_ext of equal pfxVH regP
  kvWf c σ → kvWfHist c σ → σ.rev + 1 < 2 ^ 63 →
  KOkD c g0 S σ M nx
```
Proved toward it (`StoreInv.lean`, pure): `runFrom_append'`, `filter_runFrom_other`, `at_ext_below` (states at or
below `σl.rev` are `σl`'s), `at_ext_foreign` (above it, `σ`'s states equal `σl.kvs` under any prefix the new
revisions do not touch), `regAll_foreign`, **`keysOkP_foreign`, `valsOkP_foreign`** (the `keys`/`vals` fields).
Proof plan for the rest: iterate `FClosed.foreign` `m.length` times from `H.cfg`'s `cf` (NoWrap from `KRelH`'s `σl.rev < 2^63` and the
bound); `KRelH` at each new revision `r` from `filter_applyChanges_other` (changes not under `regP` keep the view under
`kpfxD = "/registry/objs"`, a longer prefix) and `KRelS`'s `absK` reading only keys under `kpfxD`; `keysOkP`/`valsOkP` at
the new revisions: their states agree with `σl.store` under `regP`. Open: `kvWf`/`kvWfHist` of `σ` are premises — the
caller must get them from the share (foreign keys' mod revisions; a structural lemma `kvWfHist` of every `KVExt`
state of a well-formed base, or a field of `kvPfxInvP`).

**Next**: prove `kOkD_foreign`; then `kOkD_{ok,list,errW,errR,obs,pend,same}` (port `kOk_*` to `KOkD`: `keysOk_step`/
`valsOk_step`/`absVals` prefix-only), then `kInvD`'s laws over `kvPfxP_au1H`/`kvPfxP_readAuH` (each firing: catch up
with `kOkD_foreign`, then the in-process step at `σ`).
