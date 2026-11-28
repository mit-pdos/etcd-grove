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
