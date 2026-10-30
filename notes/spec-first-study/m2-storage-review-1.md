# M2, the storage side: review round 1 (2026-10-30)

Reviewed: branch `m2-storage`, commit `40fb781417` (the Draft of `fe466ad8d5` and Q1 (a)'s
`12343a4cc9`). Targets: `mvcc/M2StorageDraft.lean`, `mvcc/M2StorageDraftSupply.lean`,
`etcdserver/M2StorageDraft.lean`, and the internal changes switched in `fe466ad8d5`. Judged by
`.claude/skills/spec/PRINCIPLES.md` and `notes/spec-first-plan.md`'s two tiers, against the pinned
fork's Go (`.lake/go-src/etcd`, `249d76bea`) and the callers' proofs. Nothing built; nothing in the
repository changed but this file. No Go bug found (nothing for `issues/`).

Paths below are relative to the repository root; `mvcc/` is
`Proof/go_etcd_io/etcd/server/v3/storage/mvcc/`, `etcdserver/` is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/`.

## First tier

### F1. `NewWatchStream.specD`: in compaction mode the real caller cannot meet its premise, and nothing says where "no watchers in compaction mode" is enforced

`mvcc/M2StorageDraft.lean:239-253`. The premise `crevFrozen γ.st` is right for the off server, but
the compacting server serves the Watch handler too, and the draft does not say how that path is
proved.

- Go: `v3rpc.Server` always registers the Watch service
  (`server/etcdserver/api/v3rpc/grpc.go:81`, `pb.RegisterWatchServer(grpcServer, NewWatchServer(s))`),
  and `watchServer.Watch` calls `NewWatchStream` for every incoming Watch stream.
- The proof: the one compacting example, `putgetc`, serves through `common.Serve`
  (`examples/common/common.go:143-151`; `Proof/.../examples/putgetc/Main.lean:133`,
  `MainLinked.lean:63`). `common.Serve`'s proof gets `v3rpc.grpcCfgOk` from `srvWatchReaders`
  (`Proof/.../examples/common/Serve.lean:63`). `grpcCfgOk` holds `v3rpc.watchSrvOk`
  unconditionally (`etcdserver/api/v3rpc/InvGrpcStart.lean:253-254`), and that is where
  `watchServer.Watch` gets its `isWatchableStore` (`etcdserver/api/v3rpc/InvWatch.lean:147-148`) for
  `hNWS` (`watchServer__Watch.lean:84`). `NewServer.specCompact` hands out `srvWatchBuilt` and
  `srvWatchReaders srv E 64` (`Spec/go_etcd_io/etcd/server/v3/etcdserver/NewServer.lean:385,414`).
- The plan's route (`notes/m2-storage-plan.md`, "What the switch costs" and "What the apply-loop
  side will need") has `srvWatchBuilt` carry `crevFrozen` only at `cm = false`. A compacting server
  then has no `crevFrozen` to give, so `v3rpc.Server`'s Watch handler cannot be proved for it, and
  `putgetc`'s `Serve` cannot be either (once `specCompact` is proved and not a `sorry`).
- Failure scenario: the switch is made as listed. `NewServer`'s merged spec at `cm = true` either
  hands out a `srvWatchReaders` without the frozen fact, and `common.Serve` fails at `watchSrvOk`'s
  use in `watchServer.Watch`; or it hands out none, and `common.Serve` cannot be called.

The stated scope ("no watchers in compaction mode", `notes/m2-plan.md:245`, `:301`) can only hold if
nobody opens a Watch stream on a compacting server: a premise on the clients, not on the server.
The draft gives it no place where a caller can discharge it.

**Fix: choose the enforcement point and draft it with this round.** Two options:

- (a) Put the "no compactor" fact in the Watch stream's contract, the client-facing part of
  `watchServer.Watch.spec`'s pre (`v3rpc.upOk`/`watchStreamSpec`, `Spec/.../v3rpc/watchServer__Watch.lean:40-45`),
  so that only a client that can show `crevFrozen` opens a stream. The client's watch proofs get it
  from the server facts they already read (`isWatchServer`, as `WatchLawsHist.lean:41-53` reads
  `isStore` today). `common.Serve` and `v3rpc.Server` then stay mode-free, and `putgetc`'s clients,
  which never watch, owe nothing. This is TaDa-shaped: the fact is the client's to present.
- (b) Make `watchSrvOk` mode-gated, with `v3rpc.Server`'s Watch handler admitted only when it holds.
  This needs the gRPC model to let a handler's obligation depend on the caller (`srvStreamIs ... Up`),
  which I could not verify: uncertain.

Either way, add the v3rpc/`common.Serve`/`NewServer.specCompact` statements to "What the switch
costs".

### F2. The `store.Compact.specD` supply chain is open: `kbWTSupplyM_of_srvWTPool`'s second premise has no source, and the source would be in the collaborator's D22 predicates

`etcdserver/M2StorageDraft.lean:55-65`. Q1 (a) makes the apply thread the only supplier of
`store.Compact`'s new premise `mvcc.kbWTSupplyM γ.kb`
(`mvcc/M2StorageDraftSupply.lean:148-158`). It must be persistent, because the scheduled job keeps a
copy in `compactJobPreD` (`:132-136`) and runs on the FIFO scheduler's goroutine. The only route the
plan gives is `kbWTSupplyM_of_srvWTPool`, which takes `dghostVar E.γbe DFrac.discard d`.

Today every holder of `E.γbe` owns a fixed fraction:
- `srvBeOwn`: a quarter (`etcdserver/InvApplier.lean:555-558`);
- `srvWTPool`'s invariant: a quarter, and the monitor's disjunct (`:818-822`);
- `srvWTStock`: a quarter (`:831-834`);
- the snapshot path: splits and gathers to the whole to update (`SnapApply.lean:126-156`,
  `SnapApplyDefs.lean:135`).

No discarded part exists. Making one means a mode-gated change to one of these D22 predicates
(`srvBeOwn`, `srvWTStock`, or `E.γbe`'s allocation in `NewServer`). That is the collaborator's
snapshot track (`MEMORY.md`, "Collaborator owns snapshots").

The plan files this under "P4" as something later stages will need. But the Draft already switches
the premise from `NewStore`, where any creator could supply it (`True` off, `kbWTSupplyM_alloc`), to
`store.Compact`, where for the server only this unsourced conversion supplies it. So Q1 (a)'s chain
to its one real caller is not closed, and its closing step is undrafted and lives in someone else's
statements.

**Fix:** before Q2 is approved, draft the D22-side statement that makes the persistent anchor, or
pick an anchor in this track's own vocabulary. For example, a compaction-mode-only persistent fact
that `NewServer` allocates at `cm = true` and that `srvWTPool`'s invariant agrees with. Either way,
get the collaborator's agreement on the touched D22 predicate.

Fallback, if no anchor is acceptable: `kbWTSupplyM_alloc`
(`mvcc/InstanceLaws.lean:80`) gives the job a separate stock. That is option (c), and it reverses
R2-7 and roughly doubles the token premise; the user should see this trade-off as part of Q1.

## Second tier

### S1. Two `New` glue lemmas by mode: `server_kv_watchable_ofC` beside `server_kv_watchable_of`

`etcdserver/M2StorageDraft.lean:68-183` beside `etcdserver/BuildLemmas.lean:52-182`.

The off lemma fixes `{ d with cm := false }` (so it ignores `d.cm`), returns `actualMaxReaders - 2`
readers and `retiredAt 0`, and gives `txn.isKV`/`txn.kvWriter`. The on lemma requires
`hcm : d.cm = true`, returns `- 1 - 2` and `retiredAt 1`, and gives `watchWriter`/`writerFrag`.

`NewServer`'s merged spec builds the store at `cm := (retention ≠ 0)`. With two lemmas, its proof
case-splits and carries two posts through the rest of `NewServer`. That is the "mode is state, not a
second spec" rule (PRINCIPLES, hard rule "One spec per function"), applied here to glue.

**Fix:** after the switch, one `server_kv_watchable_of` over `d`:
- `storeBackend` by `d.cm` (`dlNoDel_fix` or `dlReg_fix`);
- `□ (⌜d.cm = true⌝ -∗ fkV)`, as `mvcc_NewStore_backend` takes it (`mvcc/Results.lean:270`);
- `srSlot` through `kbSRM_some` (already mode-free);
- post counts `actualMaxReaders - nJobRd (some d) - 2` and `retiredAt γ (nJobRd (some d))`.

The "Gap" (no `txn.isKV`/`kvWriter`) is only a Draft artifact, as the file header says.

### S2. Unfolds of mvcc definitions in the server's glue (missing laws)

In `server_kv_watchable_ofC`:
- `mvcc.storeDlReg` (`:142`) and `mvcc.nJobRd` (`:148`): new in this draft.
- `mvcc.isWatchableStoreD` (`:165`), `mvcc.isReadView`/`kvOver` (`:177-180`), `txn.storeWTs`
  (`:181`): inherited from today's lemma.

`newServer_compactRight` (`:189-193`) is a wrapper that exists only to unfold `mvcc.kbCmpM`.

**Fix:** add laws in `mvcc/InstanceLaws.lean`:
- `kbCmpM_some : kbCmpM (some d) ↔ d.cm = true`;
- `nJobRd_some_on : d.cm = true → nJobRd (some d) = 1`;
- `isWatchableStore_isStore`, `isWatchableStore_readView`.

Then drop `newServer_compactRight`: `compactRight_of_wsCloser _ _ _ _ (kbCmpM_some.2 hcm)` is one
line at the call.

### S3. `crevRightM kb γs`: the mode is passed twice

`mvcc/M2StorageDraft.lean:75-76` takes `kb` beside `γs`. `wsFrozenM` (`:64`) reads the mode from
`γs.kb`, and every post that uses `crevRightM` also states `γ.st.kb = kb`. As a result:
- `compactRight_of_wsCloser` (`:165-168`) and `newServer_compactRight` take a `kb` that is not tied
  to `γs`;
- `crevRight_split` needs `hk : γs.kb = kb` (`:89`).

**Fix:** `crevRightM γs := if kbCmpM γs.kb then crevUB γs.idx ½ (-1) else True`, as `wsFrozenM`. The
posts read `crevRightM γ.st`, and the laws lose `kb`/`hk`.

### S4. The header's claim "at `cm = false` every statement reads as today" is false for `NewWatchStream.specD`

`mvcc/M2StorageDraft.lean:23-24` (also `notes/STATUS.md:507-511`, `m2-storage-plan.md`'s "every
statement reads as today"). `NewWatchStream.specD` adds `crevFrozen γ.st` in every mode, so at
`cm = false` these change too:
- v3rpc's `watchSrvOk`/`isWatchServer`;
- `srvWatchBuilt` and `srvWatchReaders` (`etcdserver/InvWatchBuilt.lean:39-63`), which are in
  `NewServer.spec`'s post (`Spec/.../NewServer.lean:237,266`);
- `RestorePre.restorePre_of_apply`'s statement, which needs a mode hypothesis to use
  `isWatchableStoreD_frozen` (`etcdserver/RestorePre.lean:54-78`).

The changes only strengthen what the off statements give, so this is a cost, not unsoundness. But it
must be stated, and F1 decides where the fact lives.

**Fix:** correct the claim and list these statements in the switch's cost.

### S5. `kb = none`: mvcc's assumed backend is "compaction mode", so `New` over it loses watchers, with no law to get them back

`kbCmpM none = True` (`mvcc/InvStore.lean:1605-1608`). At `kb = none`, `New.specD` returns an
unfrozen store and hands out the authority's half. Today's `New.spec` freezes it. No client uses `New`
at `none` today (the server uses `some`, `etcdserver/BuildLemmas.lean:136`), so nothing breaks. But a
reader of the interface sees a store that "compacts" whether or not anyone will compact it, and has
no way to choose watchers.

**Fix:** add `crevRightM_freeze : crevRightM γs ={E}=∗ crevFrozen γs` (any mode). A creator that
will not compact then freezes the store and can watch. This makes `NewWatchStream`'s premise a choice
in every mode, not a mode test, and it gives option F1 (a) its law. Also say in `kbCmpM`'s
docstring that `none` counts as compacting for the watch API.

### S6. One fact, two carriers

In off mode the frozen fact is in `isWatchableStoreD` (`Hfrz`, through `wsFrozenM`) and in
`watchStoreInv` (`wsWatchFrozen`, `:149-150`). After the switch `syncWatchers` reads only the
invariant's (`watchableStore__syncWatchers.lean:181,304`). `Hfrz` then serves only
`isWatchableStoreD_frozen`, that is, the off server's source for F1 and `RestorePre`. The plan kept
it so that the predicate reads as today at `cm = false`, but S4 shows the off statements change
anyway.

**Fix (optional):** drop `Hfrz` and `wsFrozenM`. Have `New`'s post give one mode-gated conjunct
(`if kbCmpM γ.st.kb then crevUB ½ (-1) else crevFrozen`), which the server keeps where F1's choice
needs it. This is one carrier and one fewer definition. If `Hfrz` stays, record why in
`notes/decisions.md`.

### S7. Undrafted internal statements that the "post unchanged" relies on

`NewWatchStream.specD`'s post is unchanged only because the stream's `isWatchable` closure
(`mvcc/InvWatchStream.lean:280-303`) captures `crevFrozen`. That requires
`watchableStore.watch.spec` (`Spec/.../watchableStore__watch.lean:39-43`) to gain the premise. This
looks sound, but the drafted text does not show it.

**Fix:** draft `watch.specD`, or note in the plan that it is internal and gains `crevFrozen γ.st`.

### S8. `kbWTSupplyM_alloc`'s docstring is ambiguous

`mvcc/InstanceLaws.lean:76-79`: "For a creator of a compacting store other than the server, whose
supply shares the server's stock". The law allocates a stock of its own, and only the server shares
`srvWTPool`'s.

**Fix:** "For a creator other than the server (whose supply is `srvWTPool`'s, R2-7): a stock of its
own." Also state the margin: the `2^40 - 2` bound against the stores' `2^48`.

### S9. `kbWTSupplyM γ.kb` in `store.Compact.specD`

`mvcc/M2StorageDraftSupply.lean:148-158`. Under `storeCmp γ` the gate is always on, so the `M` adds
nothing. Keeping `kbWTSupplyM` is still right, because both of its sources (`_alloc`,
`_of_srvWTPool`) produce it. At the switch, carry today's full docstring
(`Spec/.../store__Compact.lean:24-65`) plus the planned supply paragraph; the drafted `specD`
docstring is a stub.

### S10. Minor

- `isWatchableStoreD_off` (`:127`) is a Draft-only law: it becomes `Iff.rfl` at the in-place switch.
  Drop it.
- `writerOwn`'s `2 + nJobRd γ.kb` (`mvcc/InvStore.lean:3820`) puts a server-specific count in mvcc.
  The count predates this change (D22 W7) and its reason is documented, so it is acceptable.

## Per target

**`wsFrozenM`, `crevRightM`, `crevRight_split`, `compactRight_of_wsCloser`**
- Good:
  - small, persistent where it should be, proved;
  - true at off (`_off` laws);
  - `compactRight_of_wsCloser`'s timing matches Go. The deferred `newSrv.kv.Close()` is at
    `server.go:376-382`. Every error return before `tr.Start` closes the store, including
    `v3compactor.New` at `:384-386`. After `:429` nothing returns an error (`:432-445`).
- Findings: S3, S5.

**`isWatchableStoreD`, `isWatchableStoreD_frozen`, `wsWatchFrozen`**
- Good:
  - the invariant is establishable (`wsWatchFrozen_init`, M = ∅);
  - `wsWatchFrozen` is stable, because `crevFrozen` is persistent;
  - `Hfrz`'s only use is in `syncWatchers`' non-empty branch, after the `Wu = ∅` exit
    (`watchableStore__syncWatchers.lean:129` before `:181`), so the on-mode predicate is not vacuous;
  - `isWatchableStoreD_frozen` replaces an unfold with a law.
- Findings: S6.

**`New.specD`, `newWatchableStore.specD`**
- Good:
  - exactly today's text, with one conjunct added and `kbWTSupplyM` removed (diffed);
  - at off they are equivalent to today's;
  - at on the post is usable for `store.Compact`: `isStore` inside, then `compactRight` and
    `storeStop` from `compactRight_of_wsCloser`, with `hookIs`, `storeRT` and `idxCert` from the
    server.
- Findings: S3, S5.

**`NewWatchStream.specD`**
- Good: sound (it only strengthens the pre); persistent premise, nothing spent per call.
- Findings: F1, S4, S7.

**`M2StorageDraftSupply` (`physCmpD`, `compactJobPreD`, the Compact chain's `specD`s, `NewStore.specD`, the bridges and exports, `kbWTSupplyM_on`)**
- Good:
  - a one-line move each (diffed against today's `NewStore.spec`);
  - the chain is proved against the drafts and linked (`mvcc_store_CompactD`, `:1493`);
  - the supply is persistent, so it suits the job's goroutine;
  - it also serves a non-server client's writes (`□ (⧗ 1 ={⊤}=∗ wbTok)`).
- Findings: F2 (the server's source), S9.

**`kbWTSupplyM_of_srvWTPool`**
- Good: correct as a law (`srvWTPool_take_extra_d`, already used by the apply path).
- Findings: F2 (premise unsourced).

**`server_kv_watchable_ofC`, `newServer_compactRight`**
- Good: proved; it uses the boot backend's `fkV` and `srSlot`, now kept.
- Findings: S1, S2.

**Switched internals (`writerOwn`, `bootBackend_of_newPost`'s `fkV`, `kbSRM_some`, `kbWTSupplyM_alloc`)**
- Good:
  - every off statement is unchanged (`writerOwn_off`, used at `NewServer.lean:1843-1844`);
  - `fkV` holds in either mode (`bkNoCmp_fkV_of_fkCl`);
  - `kbSRM_some` is mode-free.
- Findings: S8, S10.

## Ranked by need of revision

1. `NewWatchStream.specD`, with the v3rpc and serving statements it implies: F1, S4, S7.
2. `kbWTSupplyM_of_srvWTPool` and the Q1 (a) premise of `store.Compact.specD`: F2.
3. `server_kv_watchable_ofC` / `newServer_compactRight`: S1, S2.
4. `crevRightM` and its laws: S3, S5.
5. `isWatchableStoreD` / `wsFrozenM` / `wsWatchFrozen`: S6.
6. `kbWTSupplyM_alloc` (docstring), `store.Compact.specD` (docstring): S8, S9.
7. `New.specD`, `newWatchableStore.specD`, the Supply module's other specs, `writerOwn`,
   `bootBackend_of_newPost`, `kbSRM_some`: no change needed beyond the above.

Uncertain (not verified):
- whether the gRPC model lets a handler's obligation depend on the client's stream contract (F1 (b));
- whether `WsOk` gives `Wu ≠ ∅ → M ≠ ∅`, as `wsWatchFrozen`'s docstring says (`InvWatchStore.lean:330`;
  not read in full).
