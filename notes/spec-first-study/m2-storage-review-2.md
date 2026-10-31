# M2, the storage side: review round 2 (2026-10-30)

Reviewed: branch `m2-storage`, commit `e6ed00dee8` (round 1's repair is `5c897670ef`; the internals
switched in `fe466ad8d5`). Targets: the four Draft modules (`mvcc/M2StorageDraft.lean`,
`mvcc/M2StorageDraftSupply.lean`, `etcdserver/M2StorageDraft.lean`, `api/v3rpc/M2StorageDraft.lean`,
`client/v3/M2StorageDraft.lean`), the new laws in `mvcc/InstanceLaws.lean`,
`mvcc.wsOk_M_ne_of_Wu`, and the switched internals (`writerOwn`, `bootBackend_of_newPost`'s `fkV`,
`kbSRM_some`, `kbWTSupplyM_alloc`). Judged by `.claude/skills/spec/PRINCIPLES.md` and
`notes/spec-first-plan.md`'s two tiers, against the Go source in `.lake/go-src/etcd` and the
callers' proofs. I formed my view before reading round 1's report. Nothing was built, and nothing in
the repository changed except this file. No Go bug was found, so nothing goes to `issues/`.

Path abbreviations: `mvcc/` is `Proof/go_etcd_io/etcd/server/v3/storage/mvcc/`, `etcdserver/` is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/`, `v3rpc/` is `etcdserver/api/v3rpc/`, `client/` is
`Proof/go_etcd_io/etcd/client/v3/`, and `examples/` is `Proof/github_com/mit_pdos/etcd_grove/examples/`.

## The questions the brief asks

**Does `Up` of a create request reach `Watch`'s need before it is used?** Yes, it is sound.
- In `watch.go`, `NewWatchStream` runs at `:177`, before any `Recv` (`:251`). The create's
  `sws.watchStream.Watch(...)` runs at `:340`, after the `Recv` that delivers that request.
- In the model, `recvLoop` takes the create arm from `upOk` (`serverWatchStream__recvLoop.lean:207`,
  `:274`) and spends it at `watchStream.Watch` as `P.T`.
- The server fixes `Up` when it registers the method (`v3rpc/Results.lean:1476-1481`,
  `watch_streamHandlerOk` at `watchUp R.γ`). The client must then meet the server's `Up`
  (`isGrpcStream ... (watchUp V.R.γ)`), so the obligation runs the right way.
- Nothing between `NewWatchStream` and the first create needs the fact. `progress`, `progressAll`,
  `cancelWatcher` and `moveVictims` do not read `compactMainRev`. Its only reader is
  `syncWatchers` (`watchable_store.go:374`), and that runs only after `unsynced.size() == 0` exits
  (`:363`).
- `wsOk_M_ne_of_Wu` (`mvcc/M2StorageDraft.lean:207`) is proved, so the invariant's disjunct is
  available exactly where it is needed.

**Can the off server's watch clients get `crevFrozen`?** In principle yes, but the route is not
drafted, and the route the plan gives is incomplete. See N1.

**Is the frozen `E.γbe` share sound at boot and through the apply loop?** Yes.
- `srvBe_allocD` (`etcdserver/M2StorageDraft.lean:240`) discards the apply thread's quarter. Every
  other holder still owns a fraction: `bemuP` ½, `srvWTStock`/`srvWTPool` ¼, and the monitor's `∃ q`
  taken from `bemuP`. Together they stay below 1, so the parts remain valid together.
- Only `srv_be_swap` gathers the whole (`SnapApply.lean:119-156`); this is the one `dghostVar_update`
  on `γbe`.
- `srvWTPool_take_nOn` (`ApplyNormalOn.lean:711-745`) and `srvWTPool_take_{at,extra}_d`
  (`InvApplier.lean:953`, `:1039`) agree at any fraction (`dghostVar_agree … _`).
- The apply-loop rows (`ApplyKVCore.lean:36`, `InvBuild.lean:289`, `InvStart.lean:198`,
  `ServerOn.lean:330`, `StartOn.lean:58`, `AppliedOn.lean:267`) name `srvBeOwn` and follow its
  redefinition in place.
- `createMergedSnapshotMessage` is already generic in `dq`.

**Can the compaction arm meet `kbWTSupplyM`?** Yes. The arm holds `srvWTPool` (persistent, after
`start`) and `srvBeOwn` (via `srvApplyKVOn_beOwn`, as `srvWTPool_take_nOn` does), and
`kbWTSupplyM_of_srvBeOwnD` turns them into `kbWTSupplyM E.γ.kb` without spending the part. The job's
draws come from the same receipt-indexed stock as the apply thread's
(`receiptBound ≤ a + n + 1`). The apply thread's `srvWTTaken`/`srvWTAt` are lower bounds, so the
job's extra takes do not falsify them.

**Do the off-mode laws give back today's statements exactly?**
- For `New`/`newWatchableStore` and `isWatchableStore`: yes, up to a `True` conjunct and a dropped
  `True` premise. `wsFrozenM_off` and `crevRightM_off` give it; `kbWTSupplyM` is `True` off, and
  `New.specD`/`newWatchableStore.specD` diff against `Spec/.../{New,newWatchableStore}.lean` as
  claimed.
- For the create token: no, and the header now says so (S4, resolved). `storeWatchParams.T`,
  `upOk`/`watchUp`, the client's facts and `NewServer.spec`'s post gain `crevFrozen` in every mode.
  No `_off` law can return today's `T`, because the client must still present the fact. That is
  the price of F1's route, and it is correctly documented.

**Is anything vacuous?** No.
- `wsFrozenM` is `True` only in compaction mode, where no create token can exist. `crevFrozen`
  needs `crevUB ½ (-1)`, and the other half is the compaction right's, so the clause is not vacuous
  where it matters.
- `upOkD` is a real obligation.
- `kbWTSupplyM_alloc` has no caller in the repository; its only intended client is
  `mvcc_NewStore_backend_cmp`'s. It is not vacuous, merely unused.

## First tier

### N1 (churn from F1's repair). The off server's `crevFrozen` reaches the watch clients only through undrafted statements, and the plan's route skips the predicate the real callers go through

The repair needs `crevFrozen E.γ` from `NewServer.spec`'s post. The plan (`m2-storage-plan.md:353-357`)
and the client Draft's header (`client/M2StorageDraft.lean:15-17`) say the watching examples "pass
it on" at three sites:
- `examples/watchkv/Served.lean:98`;
- `examples/linkv3p/WatchEnv.lean:82`;
- `cache/v3/Results.lean:269`.

Those are lemmas that take `isWatchServer` as a premise. The real chain from `NewServer` to them goes
through the common example library:
- `common.newServer.spec` returns `memberBuilt` (`Spec/.../examples/common/newServer.lean:73`,
  post `memberBuilt s ρ E₀ lg γn id N false`).
- `common.NewMember` returns `memberBuilt … true`.
- `StartServer`/`Start.lean` turn `memberBuilt` into `memberUp`
  (`Spec/.../common/StartServer.lean:59`, `common/Start.lean:41`).
- The examples unfold `memberUp` (`watchkv/Main.lean:201`), and linkv3p uses `memberWatch`.

`memberBuilt` and `memberUp` (`examples/common/Defs.lean:211-251`) are mentioned in 36 places across
the examples. Two of their properties matter here:
- They are shared by both server specs: `newServer.specCompact`'s post is the same
  `memberBuilt … false`, proved from `NewServer.specCompact`
  (`examples/common/newServer.lean:141-146`; `StartCompactingServer.lean:38`).
- They do not know the mode. Their pure facts give `E.authOn = false` but nothing about `E.γ.kb`.

So the step the plan names ("`NewServer.spec`'s post gains `crevFrozen E.γ`") does not reach the
clients by itself. Adding the conjunct to `memberBuilt` unconditionally breaks
`newServer.specCompact`'s proof, because `NewServer.specCompact` gives none (the plan says so:
"`specCompact`: nothing"). `memberBuilt` would therefore need a mode parameter, or a gated row, plus
the same change in `memberUp`, `StartServer`, `NewMember`, the linkv3p/authkv start lemmas, and the
examples that destructure them. This is the boot-bundle accretion that the "Local" hard rule warns
against. None of it is drafted or listed in "What the switch costs, revised" (`:441-448`).

This is first tier because the hard rule "complete: each caller can establish the precondition" has
not been shown for the real callers of the new premise, and the one route given is wrong for them.
It is fixable, and probably cheaply.

**Fix:** draft the source end to end before Q2 is approved. A cheaper vehicle than a new
`crevFrozen` conjunct in every bundle:
- The fact is already in what the clients hold: `srvWatchBuilt` → `watchSrvOk` → `isWatchServer`
  contain `isWatchableStore`, whose `Hfrz` is `wsFrozenM γ.st` (`v3rpc/InvWatch.lean:147-148`;
  `InvWatchBuilt.lean:39-45`).
- Export one v3rpc law, `isWatchServer p R ∗ ⌜¬ mvcc.kbCmpM R.γ.st.kb⌝ ⊢ mvcc.crevFrozen R.γ.st`
  (from `isWatchableStoreD_frozen`). This is round 1's F1 (a) "from the server facts they already
  read", and it would also retire the examples' `cert0_of_server` unfolds of `isWatchServer`.
- Make the mode a pure fact of the server's state, as auth's is (PRINCIPLES: "a mode is part of the
  state, `E.authMode`"). `NewServer.spec`'s post gets `⌜¬ mvcc.kbCmpM E.γ.kb⌝` (provable: it builds
  at `{ d with cm := false }`), and the merged spec gets `⌜mvcc.kbCmpM E.γ.kb ↔ retention ≠ 0⌝`.
  `memberBuilt`/`memberUp` carry it beside `E.authOn = false`.
- One pure fact then serves every mode-dependent client need (this one, `srvKVCloser`'s gating, D22's
  `srvEnvOk`) instead of one resource per need.

Whichever vehicle is chosen, list the common predicates and specs in the switch's cost.

No other first-tier finding. F2's repair introduces none (see the per-target section).

## Second tier

### S1'. `kbWTSupplyM_of_srvBeOwnD` takes a mode premise it does not need

`etcdserver/M2StorageDraft.lean:227-237` requires `h : mvcc.kbCmpM E.γ.kb`. Off, `kbWTSupplyM E.γ.kb`
is `True`, so the law holds in every mode. The compaction arm, which is one mode-generic spec ("one
spec per function; a mode is state"), would otherwise case-split to call it.

**Fix:** drop `h`. Case on the mode inside the proof, using `srvBeOwnD_frozen` on the on branch and
`itrivial` off.

### S2'. `srvBe_allocD` states the fraction unfolded

`etcdserver/M2StorageDraft.lean:240-244` writes
`if mvcc.kbCmpM (some d) then DFrac.discard else …` in place of `srvBeFrac`. `NewServer`'s proof
then has to re-fold it to build `srvBeOwnD` at `E` with `E.γ.kb = some d`.

**Fix:** state it over a fraction function of the mode (`srvBeFracOf (some d)`, with
`srvBeFrac E := srvBeFracOf E.γ.kb`).

### S3'. The client Draft puts the new conjunct second; positional destructuring in the client's own proofs shifts

`watchMemberFactsD` places `crevFrozen` second (`client/M2StorageDraft.lean:44-46`). The client
package destructures `watchMemberFacts` by position:
- `InvWatch.lean:469-470`, `⟨-, -, %Hst, -⟩`;
- `watcher__Watch.lean:54-55`, `⟨-, -, -, -, #Hkf0⟩`;
- `InvClientNewResult.lean:112`, which unfolds all three;
- outside the package, `examples/linkv3p/WatchEnv.lean:89`, which unfolds it (an existing missing
  law).

The plan's cost list names only the three create sites.

**Fix:** append the conjunct last, or (better) add projection laws (`watchMemberFacts_frozen`,
`_pool`, `_st`) and have these sites use them. Count all of them in the switch cost.

### S4'. Abstraction: the client-facing contract names `mvcc.crevFrozen`

`crevFrozen` is mvcc's invariant over the compaction revision's authority (`InvStore.lean:2025`), an
implementation ghost. It now appears in v3rpc's `upOk`/`watchUp` and in the client's member and
address facts. The client already names mvcc's `watchTokPool`/`watchTok`, so this adds no new
coupling to a package, but it does add an implementation name to an API contract.

**Fix (optional):** an mvcc API name for the fact, e.g. `mvcc.noCompactor γs`, sealed with
`crevFrozen` as its body, with the laws `isWatchableStore… ⊢ noCompactor` (off) and
`crevRightM ={E}=∗ noCompactor`.

### S5'. Two readings of "the mode"

The mvcc side reads the mode from the store's logical names (`wsFrozenM γ.st`, `crevRightM γ.st`;
the plan says "never changes"). `srvBeFrac` reads `E.γ.kb`, and D22's snapshot install replaces it
(`SnapApplyKV.lean:52`, `snapE_kb`), as `withPhys` does for `writerOwn` in `store.Restore`
(`store__Restore.lean:187-190`). The two agree in every reachable state: there is no install in
compaction mode, and received backends have `cm = false`.

**Fix:** state that invariant once, in `srvBeFrac`'s docstring (D22 item 4 in the plan already
needs `d'.cm = false`).

### S6'. Minor

- `v3rpc.createArm_T` (`:74`) and `mvcc.storeWatchParamsD_R` (`:275`) are `rfl` checks that exist
  only for the Draft. Drop them at the switch, as S10 did for `isWatchableStoreD_off`.
- `server_kv_watchable_ofD` still unfolds `backend.wbTok` (`:173`) and `txn.storeWTs` (`:187`). Both
  are inherited from today's lemma. `wbTok` has `ownToks`-level laws available, so use them.
- Uncertain: the plan's D22 item 3 assumes that in the merged no-snapshot configuration
  `applySnapshot`'s walk never reaches `srv_be_swap` (an empty snapshot). I did not find today's fact
  that gives this at `cm = true`. D22's to confirm.

## Round 1's findings at `e6ed00dee8`

| Finding | Status |
|---|---|
| F1 (no enforcement point for "no watchers in compaction mode") | **Resolved** by the per-create token (`storeWatchParamsD.T`, `upOkD`/`watchUpD`, client facts). Sound against the gRPC model (above). Its source for the off server raises **N1 (churn)**. |
| F2 (`kbWTSupplyM_of_srvWTPool`'s discarded part has no source) | **Resolved as a draft**: `srvBeOwnD`/`srvBe_allocD`/`kbWTSupplyM_of_srvBeOwnD`, with the five D22 statements listed. It needs the collaborator's agreement and adds no first-tier problem (S1', S2' second tier). |
| S1 (two glue lemmas by mode) | Resolved (`server_kv_watchable_ofD`). |
| S2 (unfolds in the server's glue) | Resolved (`kbCmpM_some`, `nJobRd_some_on`, `isWatchableStoreD_isStore/_readView`, `storeDlReg_fix`; `newServer_compactRight` dropped). `txn.storeWTs` and `backend.wbTok` remain (S6'). |
| S3 (`crevRightM` took the mode twice) | Resolved. |
| S4 (false "reads as today" claim) | Resolved in the mvcc header and the plan. |
| S5 (`kb = none` loses watchers) | Resolved (`crevFrozen_of_new`). |
| S6 (one fact, two carriers) | Rejected with a recorded decision (`notes/decisions.md`, "M2: the frozen fact stays in `isWatchableStore`"). The reason given (`isWatchableStoreD_frozen` as the off server's source) is the vehicle N1 recommends using. |
| S7 (`watch.spec` premise undrafted) | Superseded: `P.T` carries the fact, and the texts are unchanged. |
| S8, S9 | Resolved (docstrings). |
| S10 | Resolved (`isWatchableStoreD_off` dropped; `writerOwn` kept). |
| Open: `WsOk` gives `Wu ≠ ∅ → M ≠ ∅` | Resolved (`wsOk_M_ne_of_Wu`, proved). |
| Open: the gRPC model | Resolved: `Up` is per request, and the server fixes it at registration. |

## Per target

**mvcc Draft (`wsFrozenM`, `crevRightM`, `isWatchableStoreD` and its laws, `crevFrozen_of_new`, `wsWatchFrozen`, `storeWatchParamsD`, `New.specD`/`newWatchableStore.specD`, `compactRight_of_wsCloser`)**
- Good:
  - small and proved; the off laws are exact;
  - the mode is read from the names alone;
  - the closer is kept until after `tr.Start` (`server.go:376-382`, `:429`), which matches Go's
    deferred `kv.Close()`;
  - the create token is the only place watchers enter, and `wsWatchFrozen` sits in the one invariant
    `syncWatchers` already opens;
  - `NewWatchStream` keeps its text.
- Findings: S4', S6' (minor).

**`M2StorageDraftSupply` (`physCmpD`, `compactJobPreD`, the Compact chain's `specD`s, `NewStore.specD`, the bridges and exports)**
- Good:
  - `store.Compact.specD` carries today's docstring plus the supply paragraph;
  - the supply is persistent and travels in the job's persistent premise;
  - the chain is proved and linked with today's callees (`mvcc_store_CompactD`).
- Findings: none.

**etcdserver Draft (`server_kv_watchable_ofD`, `kbWTSupplyM_of_srvWTPool`, `srvBeFrac`, `srvBeOwnD`, `srvBeOwnD_off/_frozen`, `kbWTSupplyM_of_srvBeOwnD`, `srvBe_allocD`)**
- Good:
  - one glue lemma over `d`;
  - F2's mechanism is minimal: one holder's part is discarded, and every other D22 predicate is
    unchanged;
  - it closes Q1 (a)'s chain to the apply thread.
- Findings: S1', S2', S5', S6'.

**v3rpc Draft (`upOkD`, `watchUpD`, `upOkD_watchUpD`, `createArm_T`)**
- Good: it is a one-arm change; it is sound against `watch.go` and the registration;
  `watchServer.Watch.spec`, `watchSrvOk`, `grpcCfgOk` and `common.Serve` stay mode-free, so a
  compacting server still serves Watch streams (round 1's F1 concern).
- Findings: S4', S6'.

**client Draft (`watchMemberFactsD`, `watchConnFactsD`, `watchAddrFactsD`, `watchUpD_create`)**
- Good: `watchUpD_create` gives the three create sites a law instead of an unfold; `putgetc`'s
  non-watching client owes nothing.
- Findings: N1 (its source), S3', S4'.

**`InstanceLaws` (`kbCmpM_some`, `nJobRd_some_on`, `kbSRM_some`, `kbWTSupplyM_alloc`) and `wsOk_M_ne_of_Wu`**
- Good: all proved and mode-free where they can be. `kbWTSupplyM_alloc`'s margin is documented.
- Findings: none.

**Switched internals (`writerOwn` at `2 + nJobRd`, `bootBackend_of_newPost`'s `fkV`)**
- Good: the off proofs go through `writerOwn_off` (`store__Restore.lean:187-190`, `:390`;
  `NewServer.lean:1844`); `fkV` is persistent and mode-free.
- Findings: none.

## Ranked by need of revision

1. The client Draft together with `NewServer.spec`'s planned post conjunct: N1 (first tier, churn),
   then S3' and S4'.
2. The etcdserver Draft's F2 laws: S1', S2', S5'.
3. The v3rpc Draft: S4', S6' (minor).
4. The mvcc Draft: S6' (minor).
5. `M2StorageDraftSupply`, `InstanceLaws`, `wsOk_M_ne_of_Wu`, the switched internals: no change
   needed.
