# Status (Lean port)

**Last updated:** 2026-10-09 (`client/v3/concurrency`: the transaction and lease model, `Session` proved; Perennial `56b1b6651`: `fmt.Sprintf` and `strings.Join` proved from Perennial's models, `rand.Int` stays assumed; the cache sorry-free: Perennial `3ae7dc6a4`, see "Sorry-free"; the cache's linearizability as a model fact, `etcdReached`; merged with upstream's server work: the consistent index and the apply thread, the raft predicate refactors and client-facing RawNode specs; Perennial `8c33774d0`: Goose without `-lean`; the whole cache package specified and proved)

Porting the Rocq Raft proof (`new/proof/go_etcd_io/raft/election_proof/`) of
branch `worktree-agent-a22b3746ec9c86178` at `857d09190` (the RawNode branch: it merges
`worktree-raft-replication`'s `feb5c73d4` and adds Ready/Advance/HasReady; the files
were first ported from `main`, then from `feb5c73d4`) to Lean on top of Perennial's Lean
port (mit-pdos/perennial `lean`, pinned at 56b1b6651 (2026-10-09: on 56b1b6651: our 3ae7dc6a4 merged with upstream's `00b3c10ea` (trusted models and proved specs of `fmt.Sprintf`, `strings.Join`, `crypto/rand.Int`; `math/big`'s `ownInt` normalized, its and `crypto/rand`'s `IsPkgInit` instances now Perennial's), see "Perennial `56b1b6651`"; on 68d220ac8: `fmt.wp_Errorf` proved, `map.forRange` with `wp_map_for_range_mut{,_keys}`, `context.wp_WithCancel` proved; on 3ae7dc6a4: `context.isClosedchanInit`, see "Sorry-free"; on 8c33774d0: upstream's `37416dd10` (Rocq code removed) and `cdf8c0f81` (Goose without `-lean` and the ⁱᵐᵖˡ encoding) merged, see below; on f8b35ddbf: `context.wp_Background`, `wp_WithCancel_Background`; on f35530719: Goose prints an axiomatized generic type in Lean; on 8c7000190: `time.NewTimer`, `Timer.Stop`/`Reset` axioms; on 96ec7016d: `fmt.wp_Printf`, `time.Minute`; on 099c2a08b: `fmt.wp_Errorf`'s `Error()`; on 640a605cc: a `select` case on a nil channel is never ready, `chan.wp_select_blocking_nil`; on 48e1192c7: rlocker, `Cond.wp_Wait_with`, `time.wp_Since`) on cbb85c041: upstream's `11fd2db` merged with
`bytes.Compare`, on Lean's module system since 2026-10-09). The Goose translations of
etcd-raft and etcd's `cache` package are this repository's `Code/` and `GeneratedProof/`,
generated and checked by `etc/goose.py`. Files are laid out by kind and Go package path
(`Spec/go_etcd_io/raft/v3/raft__Step.lean`) and every file is a module of Lean's module
system (2026-10-08; decisions.md, "Layout by kind and Go package path" and "Lean's
module system").

## client/v3/concurrency: the transaction and lease model, Session (2026-10-09)

etcd's model now has transactions and leases, `go.etcd.io/etcd/client/v3/concurrency` is
translated with bodies, and `Session` (`session.go`) is proved: 9 of its 10 functions
verified, `Close` unfinished only through Perennial's `wp_WithDeadlineCause` `sorry`. Design:
`decisions.md`, "The transaction model: sequential ops at one revision, per prefix; leases
without liveness; the create-revision persistence law".

- **Translation** (commit "Translate client/v3/concurrency ..."): `etc/goose.py` pins etcd at
  `207c8f747` = `goose-lean` (`6ab61a1c7`) + one **Gooseable** commit (not pushed; push it to
  `upamanyus/etcd`'s `goose-lean` first): concurrency calls the methods it uses of `*Client`'s
  embedded interfaces through the field (`client.Lease.Grant(...)`, `client.KV.Txn(...)`, ...),
  because Goose translates a promoted method as `MethodResolve (*Client) "Grant"` with no
  unfolding for it; and binds `wr.Events` to a `[]*mvccpb.Event` (the alias issue of
  `5ae038f0f`). `client/v3.toml` gained `Client.Ctx`, `Client.GetLogger`, the comparison
  builders, `OpPut`, `OpDelete`, `WithLease`, `WithSort`, `WithFirstCreate`, `WithLastCreate`,
  `withTop`, `WithMaxCreateRev` (and imports proto, fmt); `etcdserverpb.toml` `Compare` and its
  oneof wrappers, `Compare.GetKey`, `TxnResponse`, `ResponseOp` and its wrappers, `PutResponse`,
  `DeleteRangeResponse`, `LeaseRevokeResponse`; `zapcore.toml` imports `time` and `io` (so
  `zap.Logger`'s field types are no longer axiomatized types with `sorry` instances).
- **The model** (`cache/v3/InvEtcdTxn.lean`): `CmpModel` (`client/v3/InvCmp.lean`), `cmpHolds`
  (etcd's `applyCompare`; a value comparison on a missing key **fails**, a correction of the
  plan), `TxnOp` (get/put/delete), `TxnModel`, `applyTxnOp`/`runOps`/`runTxn` (ops in order, each
  on the state the previous left, at one revision), `txnWrote`, `rangeKvsOk` (a get's response:
  sorted, limited, as a relation since etcd's sort is unstable). The client's contracts, as
  definitions: `isEtcdTxnKV kv pfx` (`kv.Txn(ctx)` returns a builder with an abstract state;
  `If`/`Then`/`Else` append; `Commit` returns `txnCommitResult`: an error, or a response at
  `r ≥ lo` reached, with a state `s` such that the response is `runTxn r s t`, and `s` at `r - 1`
  and the result at `r` if it wrote, `s` at `r` otherwise) and `isEtcdLease l` (`Grant`: an ID
  `≠ NoLease`; `KeepAlive`: a channel of which nothing is promised, `isChanAny`; `Revoke`).
  `isEtcdClient` gained `isEtcdTxnKV` and `isEtcdLeaseClient`. `OpFull` gained `val`,
  `rangeEndSet`, the sort option, `ignoreValue`/`ignoreLease` (`InvOp.lean`).
- **New axioms** (`etc/tcb-baseline.txt` after `--update`: 37 axioms, 1 sorry):
  `proto.Clone.wp_proof` (protobuf's deep copy of a `*pb.Compare`, the comparisons' trust
  boundary) and Perennial's `sorry` `context.wp_WithDeadlineCause` (reached by `Session.Close`
  through `WithTimeout`). The two history laws `etcdState_revs` and `etcdState_create_persist`
  are axioms in `InvEtcdTxn.lean` but no result uses them yet (the recipes will), so the
  baseline, which lists what results reach, does not show them.
- **Proved**: the clientv3 builders (`Value`, `Version`, `CreateRevision`, `ModRevision`,
  `LeaseValue`, `Compare`, `Cmp.WithRange`/`WithPrefix`/`Clone`/`ensureCompare`, `cloneCompare`,
  `mustInt64`, `mustInt64orLeaseID`, `OpPut`, `OpDelete`, `WithLease`, `WithMaxCreateRev`,
  `WithSort`, `withTop`, `WithFirstCreate`, `WithLastCreate`, `Client.Ctx`, `Client.GetLogger`,
  `pb.Compare.GetKey`); `Session`: `NewSession`, `Client`, `Lease`, `Ctx`, `Done`, `Orphan`,
  `Close`, `WithTTL`, `WithLease`, `WithContext` (`client/v3/concurrency/InvSession.lean`:
  `isSession s γ client id`, persistent; `sessionDone s γ`, persistent once `donec` is closed).
  `WithSort`/`withTop` take `¬ (target = SortByKey ∧ order = SortAscend)` (decisions.md: the
  closure writes its captured `order` in that case, a race). `NewSession` takes the resulting
  options' context to be a `*cancelCtx` (Perennial's `wp_WithCancel`).
- **Linking**: `etc/gen-link.py --concurrency` writes
  `Proof/go_etcd_io/etcd/client/v3/concurrency/Link.lean` from
  `etc/link-lean-first-concurrency.txt` (results in the namespace `concurrency`, clientv3's with
  `v3.`); `etc/tcb-report.lean`'s default roots, `etc/tcb-report.py` and `etc/verified-code.py`
  include it. The clientv3 specs take clientv3's `Assumptions` (were the cache's), the zap specs
  import the cache's `Base` (were the server's `InvApplier`), and the proto/protoreflect
  package-init instances moved from the server's `BaseApply` to the cache's `Base`.
- **Gates**: `lake build` passes (1740 jobs); `etc/goose.py --check` passes (with
  `ETCD_SRC=/shared/etcd` until `207c8f747` is pushed); `etc/tcb-report.py --check` matches the
  updated baseline; `etc/gen-link.py --cache`/`--server`/`--concurrency` reproduce their
  `Link.lean`; `etc/verified-code.py --reuse` (with `207c8f747` fetched into `.lake/go-src/etcd`
  from `/shared/etcd`): `client/v3/concurrency` 9 verified, 1 unfinished (`Session.Close`) of 62,
  `session.go` 63 of 70 lines; `client/v3` 58 verified of 337; etcd 193 verified of 3599; cache
  107/107 unchanged; Raft 175/323 unchanged.
- **Next**: `Mutex` (`mutex.go`), then `Election`, `STM`, on `isSession` and the transaction
  contract; they will need `etcdState_create_persist`. Push order: the etcd fork's `207c8f747`
  (to `goose-lean`), then etcd-grove (Perennial is unchanged).

## Perennial `56b1b6651`: `fmt.Sprintf`, `strings.Join` proved (2026-10-09)

Perennial's `00b3c10ea` (merged into ours as `56b1b6651`) gives `fmt.Sprintf`,
`strings.Join` and `crypto/rand.Int` trusted models (`Perennial/TrustedCode`) and proved
specs. Two of the raft trust-boundary axioms are now theorems, with their `.spec`s
unchanged (only docstrings), so `Link.lean` is untouched:
- `fmt.Sprintf.wp_proof` from `fmt.wp_Sprintf` (needs only `isPkgInit`; the args slice is framed);
- `strings.Join.wp_proof` from `strings.wp_Join` (stronger: the result is `sep.intercalate xs`;
  Go's panic on a length overflow is not in the model, so the no-panic claim now rests on it).
- `rand.Int.wp_proof` **stays an axiom**: `crypto.rand.wp_Int` has the same pre/postcondition
  (same reader, `math.big.ownInt` = our `ownBigInt`) but needs `mz < 2^63` (the model reads one
  magnitude word and panics beyond); our spec claims every `0 < mz`.

`Proof/go_etcd_io/raft/v3/Base.lean` lost its `math/big` and `crypto/rand` `IsPkgInit`
instances (Perennial now has them; `isRandInitialized` keeps the same body, its
`_access` goes through Perennial's `crypto.rand.isInitialized_access`). Perennial's
`etc/lean-ci.sh`: 369/369 modules ok. Gates: `lake build` passes (1660 jobs);
`etc/goose.py --check` passes (no translation changed); `etc/tcb-report.py --check --update`:
the baseline lost exactly `fmt.Sprintf.wp_proof` and `strings.Join.wp_proof` (36 entries, all
axioms, 0 sorries); `etc/gen-link.py --cache`/`--server` and `etc/gen-btree-link.py`
reproduce their `Link.lean`; `etc/verified-code.py --reuse`: totals unchanged (Raft 175/323,
0 assumed: these are standard-library specs, outside the totals, where `fmt.Sprintf` and
`strings.Join` are now "verified"); cache 107/107 sorry-free. Push Perennial (`56b1b6651`) first.

## Sorry-free (2026-10-09)

Every cache result is `sorry`-free: re-pinned to Perennial `3ae7dc6a4`, which closes the
four Perennial `sorry`s the cache reached:
- `fmt.wp_Errorf` (`4e1bfe544`: `fmt.Errorf` as a trusted model, `wp_Errorf` proved;
  `errors.wp_New`'s `Error()` returns the message);
- `wp_map_for_range_mut_keys` (`6519b44f5`: `map.forRange` no longer holds the map across the
  body; `wp_map_for_range_mut{,_keys}` are now Perennial's, in `Perennial.Golang.Theory.Map`,
  with the statements of our deleted `MapRangeMut.lean`);
- `context.wp_WithCancel` and `context.wp_WithCancel_Background` (the `ctx-withcancel`
  branch: `atomic.Value` trusted model, both proved; `wp_WithCancel` needs its parent to be a
  `*cancelCtx` (`isCancelCtxCtx`), and the cancel function's postcondition gives
  `ContextClosed`);
- and `3ae7dc6a4` (ours): `context`'s `isInit` no longer holds ghost state, so its
  `IsPkgInit` instance (and raft's, the cache's, the client's, the server's) needs no
  `[AllG GF]`; `closedchan`'s closed state is the persistent package-init fact
  `context.isClosedchanInit`, carried by every `*cancelCtx` (`isCancelCtxOf`).

Proof-side changes: `InvCache`'s internal-context fact is `∃ ics, isContext cf.ictx ics ∗
isCancelCtxCtx cf.ictx ics` (`watchEvents` passes it to `wp_WithCancel`); `newCache` gets it
from `wp_WithCancel_Background` and keeps `"#HisStop"`'s old form through
`context.cancel_spec_forget`; **`New` and `newCache` take `context.isClosedchanInit`** (a
package-init fact of `context`, which a program's `main` establishes once `context` is
initialized, as it does `isPkgInit`), for `WithCancel(Background())`; the five
`wp_apply Hcancel` sites drop `ContextClosed` (`as -`). No other statement changed; raft,
btree and server proofs unchanged.

Gates: `lake build` passes (1655 jobs); `etc/goose.py --check` passes (no translation
changed); `etc/tcb-report.py --check --update`: the baseline lost exactly the four sorries
(`Perennial.context.wp_WithCancel`, `Perennial.context.wp_WithCancel_Background`,
`Perennial.fmt.wp_Errorf`, `wp_map_for_range_mut_keys`), 38 entries, all axioms, 0 sorries;
`etc/gen-link.py --cache`/`--server` and `etc/gen-btree-link.py` reproduce their `Link.lean`;
`etc/verified-code.py --reuse`: cache 107 verified, 0 unfinished of 107, 1206 of 1206 lines
(100%), all sorry-free; Raft 175 of 323 (2240 of 3641 lines, 61.5%); etcd 161 verified (all
sorry-free), 13 assumed of 3599 (1560 of 45566 lines, 3.4%), `server/v3` 19 verified, 0
unfinished, 9 assumed (215 lines). `Results.lean`'s `#print axioms` of `cache_New`,
`cache_Get`, `cache_Watch`, `cache_Watch_delivery`: no `sorryAx`. Push Perennial
(`3ae7dc6a4`) first.

## The cache: linearizability as a model fact, `etcdReached` (2026-10-09)

The client assumption no longer mentions caches. "etcd has reached revision `r`"
(`etcdReached r`, `InvEtcd.lean`) is a fact of the model, produced by the client's responses
and carried to every place the store's or the demux's revision moves; `isEtcdKV`'s `Get` triple
is linearizable against it. Design: `decisions.md`, "`New` and the client" (the paragraph
"fixed 2026-10-09").

- **The model**: `axiom etcdReachedAt (r : w64) : IProp GF` and `axiom etcdReachedAt_timeless`
  (an instance); `etcdReached r := ⌜sint.Z r ≤ 0⌝ ∨ ∃ r', ⌜sint.Z r ≤ sint.Z r'⌝ ∗ □
  etcdReachedAt r'`, so persistence, timelessness, downward closure (`etcdReached_mono`) and
  `etcdReached_zero` are instances/lemmas.
- **The client**: `isEtcdKV`'s triple takes any `lo` with `etcdReached lo` and returns
  (`kvGetResult pfx lo`) a header revision `r` with `etcdReached r`, `r < 2^63 - 1`, and `lo ≤ r`
  **unless the request is serializable** (a serializable get may be served by a lagging member);
  `isEtcdKVFrom` and `isEtcdKVLin` are gone. The watch contract (`watchRespOk`) gives
  `etcdReached` of a created notification's and a progress notification's header revision, and
  `etcdStepCertBody` (each batch) of the batch's revision.
- **The store** takes a second parameter `R : w64 → IProp GF` beside `E` (`storeLockInv`,
  `storeReader`, `storeWriter`; not `storeLockedPhys`): the lock invariant and the writer hold
  `□ R latestRev`; `newStore` asks for `□ R 0`, `Restore kvs rev` for `□ R rev`, `Apply` for
  `revCerts R (applyRespRevs st r)` (a progress notification's revision, or each snapshot's it
  appends: `applyResp_latestRev_mem`); `getSnapshot`/`Get`/`LatestRev` return `□ R` of the
  state seen. `applyEventsLocked` and `applyProgressNotifyLocked` are unchanged. The cache's `R`
  is `etcdReached`.
- **The demux**: `DemuxCert` gained `prog : w64 → IProp GF` (timeless, downward closed, `prog 0`,
  and `cert_prog`: a batch's certificate gives `prog` of its revision); the lock (`demuxLockRest`,
  `demuxLocked`) holds `□ C.prog maxRev`; `respCert` of a progress notification adds
  `□ C.prog hdrRev`; `demuxPubBody` adds `□ C.prog v.maxRev`, from which `demuxPubBody_prog`
  gives it of every progress notification of a published log. Every other demux statement
  unchanged (`pub_send`/`pub_close`/`demuxPub_intro` take the extra premise). The cache's `prog`
  is `etcdReached`.
- **The cache**: `get` calls `kv.Get` with the writer's `etcdReached st.latestRev`
  (`storeWriter_rev`), so `get`, `getWatch` and `getWatchLoop` lost their linearizability
  premises; `applyStorage` supplies `Apply`'s `revCerts` from the store watcher's publication
  (`storeW_revCerts`); `watchEvents` supplies `respCert`'s `prog` from the watch receive.
  `isEtcdClient` is the two field points-tos with `isEtcdKV`, `isEtcdWatcher`,
  `isEtcdProgressNotifier`, no quantification over caches. `New.spec` is unchanged.
- **Gates** (2026-10-09): `lake build` passes (1656 jobs); `etc/tcb-report.py --check` (after
  `--update`): 38 axioms (new `etcdReachedAt`, `etcdReachedAt_timeless`), 4 sorries;
  `#print axioms` of `cache_New`, `cache_Get`, `cache_Watch`, `cache_Watch_delivery` now include
  both; `etc/gen-link.py --cache` reproduces `Link.lean`; `etc/goose.py --check` passes;
  `etc/verified-code.py --reuse`: cache 97 verified, 10 unfinished of 107 (unchanged).

## Merged with upstream's server work (2026-10-09)

Our final cache unit (`New`/`newCache`, `Close`, the loops, the clock, the options,
`Results.lean`) and the re-pin to Perennial `8c33774d0` merged with upstream's `aa4020095`
(the consistent index and the apply thread, raft v3.7 in `EtcdDeps/`, the one-record
predicate refactors and `proj_simps`, the client-facing `RawNode` specs). Union everywhere:
`etc/goose.py` takes upstream's structure (`Part`, `owned`, the server's packages and roots)
plus our five names-only packages of `Client`'s field types, without `-lean`; zap is
translated once (upstream's `imports = ["!*", "go.uber.org/zap/zapcore"]`), regenerated by
`etc/goose.py` (only `zap.lean` changed from our side: zap now imports zapcore, so the
cache's `Base.lean` gained `IsPkgInit`/`GetIsPkgInitWf` instances for zapcore; no proof
changed); `etc/tcb-report.{lean,py}` have both the cache's `Results` root and the server's
second run; `etc/verified-code.py` now counts the server's `Link` too (run twice, as
`etc/tcb-report.py`). Gates: `lake build` passes (1656 jobs); `etc/goose.py --check` passes;
`etc/tcb-report.py --check` matches the baseline (the union: 36 axioms, 4 sorries; 389 + 47
root theorems); `etc/gen-link.py --cache`/`--server` and `etc/gen-btree-link.py` reproduce
their `Link.lean`; `etc/verified-code.py --reuse`: Raft 175/323; etcd 150 verified, 11
unfinished, 13 assumed of 3599 (cache 97 verified, 10 unfinished of 107; `server/v3` 18
verified, 1 unfinished, 9 assumed).

## Perennial `8c33774d0`: Goose without `-lean` (2026-10-09)

Perennial's `6fa346618` merges our `f35530719`/`8c7000190`/`f8b35ddbf` with upstream's
`37416dd10` (Rocq code, tooling and prose removed from the `lean` branch) and `cdf8c0f81`:
`goose` and `proofgen` no longer take `-lean` (the output is always Lean), and the names
`Foo.impl`, `T.M.impl` are produced directly instead of through an internal `ⁱᵐᵖˡ` suffix
that the Lean printer decoded. The generated names are the same: regenerating both
translations changed no file. `etc/goose.py` no longer passes `-lean` (it keeps
`-lean-root`). The merge resolved the `goose/glang/coq.go` conflict by deleting the file,
which also deleted the `GenericTypeExpr` type of our `f35530719` (goose did not build);
`8c33774d0` restores it in `goose/glang/syntax.go` (one implementation; its Lean printer is
unchanged). The std-lib translations regenerate byte for byte (Go 1.26.0, no `--lean` flag
now). Gates: Perennial's `lake build` passes; here `lake build` passes (1472 jobs),
`etc/goose.py --check` passes, `etc/tcb-report.py --check` matches the baseline (10 axioms,
4 sorries, unchanged), `etc/gen-link.py --cache` and `etc/gen-btree-link.py` reproduce their
`Link.lean`, `etc/verified-code.py`: Raft 175/323, cache 97 verified and 10 unfinished of 107.
Push Perennial (`8c33774d0`) first.

## Merged with upstream's layout (2026-10-09)

The demux, the `MessageState` translation, the key predicates and request validation and
`verified-code.py`'s cache count (done on the old layout, `EtcdGrove/Cache/`,
`EtcdCache/`) were merged into the layout by kind and Go package path: specs and proofs
under `{Spec,Proof}/go_etcd_io/etcd/cache/v3/`, but the `clientv3` functions translated
for the validation (the 16 `Op` getters, `getPrefix`, `GetPrefixRangeEnd`) under
`{Spec,Proof}/go_etcd_io/etcd/client/v3/` (next to `WatchResponse__IsProgressNotify`);
`InvDemux`, `InvCache` and `MapRangeMut` under `Proof/go_etcd_io/etcd/cache/v3/`; every
file a module (`module`, `public import`, `@[expose] public section`). Perennial is
pinned at `cbb85c041` (upstream's `11fd2db` merged with `bytes.Compare`, which the key
predicates need). `etc/tcb-report.py --check`: 4 axioms (`fmt.Sprintf`,
`rand.Int`, `reflect.DeepEqual`, `strings.Join`) and 2 sorries (Perennial's
`fmt.wp_Errorf`; `wp_map_for_range_mut_keys`, the demux's documented Perennial gap): no
btree, `slices.Sort` or `MessageState` entries, no `newStore_RLocker`. `lake build`
passes (1333 jobs), `etc/goose.py --check` passes, `etc/gen-link.py --cache` reproduces
`Proof/go_etcd_io/etcd/cache/v3/Link.lean`.

## Done (at `857d09190`)

- Lake project depending on Perennial (`lakefile.toml`); `Base.lean`.
- `plog.v`, `protocol.v` (7.1k lines: `Protocol/{Model,Ghost,GhostState,StepGhost,
  LeaderCompleteness,Refinement,Facts}.lean`): **fully proved**. `#print axioms` of
  `ownRaftGhost_step`, `leader_completeness`, `state_machine_safety`,
  `ownRaftGhost_alloc`: only `propext`, `Classical.choice`, `Quot.sound`.
- `defs.v`, `step_lemmas.v`, `inv_*.v` (incl. `inv_memstorage.v`, `inv_readylog.v`,
  `inv_rawnode.v`): no `sorry`.
- The 167 specs and the 167 proofs (`raft.Step`'s branches in `Proof/raft__Step/`,
  one module per Rocq helper file, incl. `MsgStorageAppendResp`/`MsgStorageApplyResp`).
  Trust boundary as in the Rocq at first: the state/logger axioms and nine
  `axiom … .wp_proof` for code outside the scope (since 2026-10-08 only `.wp_proof`
  axioms remain; see below).
- **`RawNode.Ready` is proved here although it is `Admitted` in the Rocq**: the Rocq
  script stops (`Show. Admitted.`) after stepping all the code and closing the struct,
  before the postcondition; `Proof/RawNode__Ready.lean` ports that script and proves the
  postcondition from the Rocq file's own (Qed) helper lemmas. Its spec was checked
  clause by clause against `spec_RawNode__Ready.v`.
- `memstorage_instance.v` (`MemstorageInstance.lean`) and `election.v` (the links:
  `Link.lean`, generated by `etc/gen-link.py` from the 857d09190 Rocq; the
  results: `Results.lean`, which `#print axioms` the top-level results): no `sorry` of
  their own. **no `sorry` at all since 2026-10-08**: `raftLog.slice`'s one `sorry` (Rocq's deliberate
  `admit`, "the log fits in memory") is gone, see below.

- **`confchange.Restore` is proved (2026-10-08)**, no longer an axiom. The package is
  now translated in full (Perennial's `confchange.toml`), and `Restore` is proved from
  `toConfChangeSingle`, `chain` and `Changer.Simple` (itself from `checkAndCopy`,
  `Config.Clone`, `apply`, `makeVoter`, `initProgress`, `symdiff`, `checkAndReturn`,
  `checkInvariants`, `joint`/`incoming`/`outgoing`, `nilAwareDelete`): 16 new
  spec/proof pairs, Lean-first (no Rocq counterpart), listed in
  `etc/link-lean-first.txt` for `etc/gen-link.py`; shared vocabulary in
  `InvConfchange.lean`. `Restore.spec` is unchanged. `JointConfig.IDs.spec` was
  generalized (any `JointConfig` cell, any fractions) with the old tracker form derived
  (`IDs.spec_tracker`); `apply`/`Simple` take a `size vm < 2^63` premise (their
  `len == 0` test is a 64-bit comparison). The translation needed a Goose fix: `cc := cc`
  (the loop-local-copy idiom in `Restore`) read the *new* cell; see notes/decisions.md.
- **`raftpb.ConfState.Equivalent` is proved (2026-10-08)**, no longer an axiom: `raftpb`'s
  translation includes it (`Code/go_etcd_io/raft/v3/raftpb.toml`: `ConfState.Equivalent`, imports
  `fmt`/`reflect`/`slices`). What it calls that Goose cannot model is
  `reflect.DeepEqual`; that is the new axiom, stated on two `ConfState` values as Go's
  `DeepEqual` reads on this struct (`Spec/reflect_DeepEqual.lean`, `confStateDeepEq` in
  `InvRaftpb.lean`, which also has `sorted_perm_eq` and `wp_slice_append_nil_empty`:
  `append` of nothing onto `nil` is `nil`, with no ownership of the empty source,
  which the callers do not have). So the two axioms about core raft code are gone;
  the 13 that remain are all outside raft (`reflect`, `math/big`, `fmt`, `strings`,
  `slices`, `rand`, the `Logger` and `Storage` interfaces, protobuf's `Entry.Size`).
- **The last `sorry` is gone (2026-10-08).** `raftLog.slice` admitted
  `|ents| + |unstable| < 2^63`, the bound `extend.spec` asked for and nothing could
  supply (Rocq: `Admitted. (* Trusted *)`). `extend.spec` no longer asks for it: past
  `2^63` the Go `int` `need` wraps negative, the code runs `append(dst, vals...)`, and
  Perennial's `append` model assumes no length overflow (`sumAssumeNoOverflowSigned`,
  Goose's standing treatment of Go's `growslice` panic) -- the admission restated. So
  the proof takes it from the model (`Proof/extend.lean`), and what is trusted is
  unchanged. Every result is now `sorry`-free; `etc/tcb-report.py --check`: 13 axioms,
  0 sorries.
- **`big.NewInt` and `big.Int.Int64` are proved (2026-10-08)**, in Perennial
  (`Proof/math/big.lean`; `math/big.toml` translates `NewInt`, `Int.Int64` and `low64`):
  `ownBigInt` is Perennial's `math.big.ownInt` (sign and little-endian word slice) instead
  of an abstract axiom, the two specs are unchanged, and `crypto/rand.Int` (still assumed)
  is stated over the concrete predicate. Perennial's Go semantics gained unary minus on
  unsigned integers (`neg_uint64` & co., `Golang/Defn/Predeclared.lean`), which `NewInt`
  uses. Perennial pinned at 584b17c54: `lake build` passes, `etc/goose.py --check`
  passes, `etc/tcb-report.py --check`: 10 axioms, 0 sorries. `slices.Sort` and `strings.Join` stay assumed, and both specs
  claim more than Go's code does in the model: `Sort` overflows `2*root+1` in its
  heapsort fallback past 2^62 elements, `Join` panics if the total length overflows
  `int` (and cannot be translated: `strings.Builder` uses `unsafe.String`).
- **`ownInflightsRaw` is indexed by one pure record (2026-10-08)**, `InflightsRing`
  (window, `start`, buffer length), instead of the Goose value and the buffer's
  contents; `grow`'s spec is now deterministic and the public `Inflights` specs are
  unchanged. The rule (one record, as small as the specs allow) is in decisions.md,
  "Predicate indices", with what else it was applied to and what is left as is.
- **`ownUnstable` is indexed by one pure record (2026-10-08)**, `UnstableSt` (entries,
  `offset`, `offsetInProgress`, pending snapshot), instead of the Goose value and the
  entries; the predicate carries the snapshot's `ownSnap` and the logger, so the
  `unstable` specs lost those premises and their "unchanged" facts.
- **The same rule, applied to the rest (2026-10-08)**: the storage's `prev`/`ents`/`ss`
  are one `StorState` (`StorageModel.ownStorage`, `isStorageWith`, the
  `MemoryStorage` predicates); `ownProgressMap`'s pointer map is existential; `Progress.recentActive`
  and `ReadOnly.safe`, which no spec reads, are gone.
- **The `raftLog` layer follows it too (2026-10-08)**: `ownRaftLogCore` is inlined into
  `ownRaftLog l ls` (storage `∃ σ : StorState`), the proofs keep `ls` a variable, and
  `newLogWithSize` lends the storage with a wand back to `ownRaftLog`. `proj_simps`
  (`ProjSimps.lean`) generates `@[simp, word_unfold]` projection lemmas for 31
  record-building functions; `CLAUDE.md` ("Proof writing", "Records") says how proofs
  handle records (keep them variables, `word` over `omega`). The `ownRawNode` fold into one
  record was reverted, then superseded by the client-facing `RawNode` specs below.
- **The `Logger` and `Storage` interfaces assume nothing (2026-10-08).** `isLogger`
  (`InvLogger.lean`) is a definition, the formatting methods' triples bundled as
  `isStorageWith` bundles `Storage`'s, so `isLogger_persistent` is an instance and
  `Logger.wp_logf` a theorem: a client supplies the triples with its `Logger`.
  `ownStorage` (`InvStorage.lean`) is the field of `class StorageModel GF`, a
  parameter every section that reaches it carries (`[StorageModel GF]`, also in
  `etc/gen-link.py`'s template), with deliberately no global instance; it stays
  abstract (not specialised to `ownMemoryStorage`), but the results now hold for
  *every* storage predicate instead of one unknown one, which no client could have
  established (`newRaft`'s precondition asks for it, and `ownRawNode_persist` hands it
  to the application to `Append`). Four axioms gone (`isLogger`,
  `isLogger_persistent`, `Logger.wp_logf`, `ownStorage`); `etc/tcb-report.py
  --check`: 6 axioms (`reflect.DeepEqual`, `fmt.Sprintf`, `strings.Join`,
  `slices.Sort`, `rand.Int`, `raftpb.Entry.Size`), 0 sorries. `RawNode.wp_Ready` rests
  on `Entry.Size` alone, `RawNode.wp_Propose` on `Entry.Size`, `rand.Int`,
  `slices.Sort` and `reflect.DeepEqual`.
- **`raftpb.Entry.Size` is proved (2026-10-08)**, no longer an axiom: `raftpb.toml`
  translates `Entry.Size` and `sovRaft` (gogoproto, `raft.pb.go`) and imports
  `math/bits`; `Proof/Entry__Size.lean` proves the triple from the body, with
  `sovRaft` a Lean-first spec/proof pair (`etc/link-lean-first.txt`). The triple gained
  only an `isPkgInit raftpb` conjunct (for `bits.Len64`), which `limitSize`/`entsSize`
  discharge from `isPkgInit raft.v3`; no caller's spec changed. `etc/tcb-report.py
  --check`: 5 axioms, 0 sorries; `RawNode.wp_Ready` and `wp_HasReady` now rest on none
  of this repository's axioms, `RawNode.wp_Propose` on `rand.Int`, `slices.Sort`,
  `reflect.DeepEqual`.
- **`slices.Sort` is proved (2026-10-09)**, no longer an axiom: Perennial (pinned at
  c061d3b22) translates `Sort` and the `*Ordered` pdqsort and proves
  `slices.wp_Sort_uint64` (`Proof/slices_proof/sort.lean`), which
  `Proof/slices/Sort.lean` is. Its spec gained the premise `len ≤ 2^62` (past it the
  heapsort fallback's `2*root+1` overflows `int`, so the old spec was false in the
  model), and the bound is carried as follows:
  - `ownTracker`'s `Hcfg_size` and `ownConfig`'s `Hcsz` are tightened from
    `size cfg < 2^63` to `≤ 2^62`. Nothing in the heap bounds a voter set, so this
    is still a property of the configuration.
  - The bound enters at `newRaft`, whose spec has a new premise that the storage's
    initial `ConfState` has at most `2^62` voters. This is the only new assumption.
  - `raft.restore` takes the bound from the old tracker (`ownTracker_size`): the
    snapshot's voters are a permutation of the current configuration.
  - The tighter premise replaces `< 2^63` on `MajorityConfig.CommittedIndex`,
    `JointConfig.CommittedIndex` and `readOnly.maybeAdvance` (an exported result with
    no callers).
  - It is a new premise on `MajorityConfig.Slice`, `ConfState.Equivalent` and
    `assertConfStatesEquivalent`, whose callers discharge it from the tracker or the
    configuration.

  `lake build` passes; `etc/tcb-baseline.txt` lost exactly `slices.Sort`: the Raft proof's own axioms are now
  `reflect.DeepEqual`, `fmt.Sprintf`, `strings.Join` and `rand.Int`.
  Since Perennial `56b1b6651` (2026-10-09) `fmt.Sprintf` and `strings.Join` are theorems
  from Perennial's trusted models; the Raft proof's own axioms are `reflect.DeepEqual` and
  `rand.Int` (Perennial's `wp_Int` covers only `mz < 2^63`).
- **What the four remaining axioms would take** (checked 2026-10-08, with "no
  higher-level spec changes" as the constraint):
  - `fmt.Sprintf`, `strings.Join`: not translatable (`fmt`'s printer reaches
    `reflect`; `strings.Builder.String` is `unsafe.String`), and `Join`'s no-panic claim
    needs a bound on the strings' total length that `Sprintf`'s "some string" cannot
    give.
  - `reflect.DeepEqual`: reflection, outside Goose.
  - `rand.Int`: `crypto/rand.Reader` reads the OS RNG (a syscall), outside GooseLang.
  The last four can only go by changing the Go code (the `upamanyus/etcd-raft`
  `goose` fork) or by trusted models (`Perennial/TrustedCode`), which move the
  trust rather than remove it.
- **`RawNode` specs are client-facing (2026-10-09)**: `ownRawNode γ rn id rs` hides the
  node state, the ghost state and `NStateRel`; `RNState` is what a client observes
  (delivered committed log, entries to persist, queued steps, `advanceable`); `Ready`'s
  committed entries come with `isCommitted γ (rs.delivered ++ ce)`, no `applying`.
  `PstepCommitMono` and `ready_stable_ok` are proved; `raft.Step`'s spec gained a frame
  for local messages. Known gap: `advanceable` -- a client can call `Ready` once, then
  neither `Advance` nor `Ready` (see Next).
- Trust base: `etc/tcb-report.py` (gate: `--check` against `etc/tcb-baseline.txt`).
- **Build checked 2026-10-08** at Perennial c35b7710d (a `--packages` override pointing
  at a checkout of the pinned commit): `lake build` completes (977 jobs, 0 errors); `etc/tcb-report.py --check`
  passes (13 axioms, 0 sorries). Perennial's own `sorry`s (`Proof/errors.lean`,
  `GeneratedProof/{os,strings,sync,fmt}.lean`, `Proof/context.lean`) are not reached by
  any result.

- Build timing: `etc/build-report.py build` (parallelism over time, critical path;
  design in `decisions.md`); CI: `.github/workflows/lean.yml` (self-hosted runner
  `coqdev`, as in mit-pdos/xv6iris; build with the report on the summary page,
  `tcb-report.py --check`). First full build of this
  repository's modules (dependencies built, 24 cores, 2026-10-08): 402 modules,
  3m48s wall, 40m35s CPU; the import chain bounds it at 3m02s, of which
  `Proof/stepLeader.lean` is 1m08s (the slowest module, and last on the path before
  `Link`); the Protocol chain (`Plog` … `Facts`) ran one compile at a time for the
  first 1m10s. Since `Protocol.lean` imports only `Model`/`Ghost`/`GhostState` (what
  `Defs` and `Inv*` use), `Defs` starts at 0:29 and the build takes 3m01s (bound
  2m19s); what limits it now, and two measured upstream options (precompiled
  Perennial: −11% CPU; the module system for faster imports), are in
  `decisions.md` ("Build speed"). With every file (here and in Perennial) a module, a
  compile's peak memory is 1.8 GiB instead of 2.8 GiB and a spec module (almost all
  import) takes 2.1s of CPU instead of 2.6s; whole-build times on a quiet machine
  are still to be measured (the 2026-10-08 runs shared the machine).
- Verified code: `etc/verified-code.py` (since 2026-10-09 it takes the forks and pins
  from `etc/goose.py`, reads the translations in `Code/` and counts the linked results of
  both `Link.lean`s, raft's and the cache's). After the merge (2026-10-09; `upamanyus/etcd-raft`
  `531b20c`, `upamanyus/etcd` `48fd5a5`): raft 175 of 323 functions verified, 2240 of
  3641 Go code lines (61.5%, all sorry-free); etcd 80 of 3599 functions (76 sorry-free),
  584 of 45564 lines (1.3%): the cache package 61 of 107 functions verified, 8 unfinished
  (their proofs use a `sorry`: the demux's three loops over a map they write,
  `wp_map_for_range_mut_keys`, and five error paths through Perennial's `fmt.wp_Errorf`), 550 of 1204
  lines (45.7%), and 19 `clientv3` functions (the `Op` getters, `getPrefix`,
  `GetPrefixRangeEnd`, `WatchResponse.IsProgressNotify`). The btree (not etcd's code) is
  not counted.

## etcd `cache`: the `EtcdCache` library (2026-10-08; translation only, no proofs)

Preparation for verifying etcd's `cache` package (`go.etcd.io/etcd/cache/v3`) here, set
up like the raft translation (in `{Code,GeneratedProof}/{go_etcd_io/etcd,k8s_io,
google_golang_org}/` since the layout by Go package path; it was the library `EtcdCache`),
generated and checked by `etc/goose.py` (now two projects, `etcd-raft` and `etcd`).

- **Source**: fork `upamanyus/etcd`, branch `goose-lean`, pinned at `48fd5a507`: branch
  `goose` rebased onto upstream `main` (`f061acd09`; it was on `3efe157f6`, 2026-03-29) without
  conflicts ("Avoid fallthrough", in `client/v3/leasing`, is now `b6b069ede`), plus two
  new commits that change `cache/` only, both behavior-preserving workarounds for Goose
  bugs: `5ae038f0f` names `mvccpb.Event` instead of its alias `clientv3.Event`
  (Goose's `getStructInfo` does not `Unalias`, so `ev.Kv` on an alias-typed pointer is
  rejected), `48fd5a507` selects `entry[T].revision` from a variable instead of from
  `r.at(mid)` (Goose's `StructFieldGet` on a generic struct value omits the type
  argument: `entry.ty`, not `entry.ty T`). It is a *new* branch because the Rocq
  translations (etcd-grove `main`, Perennial `master`: `etc/ci-goose-check.py`) are
  regenerated from branch `goose` by name, so `goose` must stay at the March upstream.
  Pushed 2026-10-08, so `etc/goose.py` fetches it from GitHub (`--src etcd=<checkout>` or
  `$ETCD_SRC` only for an unpushed revision). CI's Go is now 1.27 (etcd's `go.mod`).
  **Since 2026-10-09 pinned at `6ab61a1c7`**: `48fd5a507` merged with the fork's branch
  `cache-ready-after-retry` (three fixes of `cache.go`, see "The watch loop and Cache.Watch"),
  pushed as `goose-lean` the same day (`etc/goose.py --check` fetches it from GitHub).
- **With bodies**: all of `cache/v3` (every function and method, non-test files;
  `cache/v3.toml`: `translate = ["*"]`).
- **Types and names only** (`translate = ["!*"]`, `translate_types = true`, a few
  imports kept so their types translate): `client/v3`, `api/v3/etcdserverpb`,
  `api/v3/mvccpb`, `api/v3/v3rpc/rpctypes`, `k8s.io/utils/third_party/forked/golang/btree`
  (with `sync` imported so that the generic `FreeList[T]` is translated: an
  axiomatized generic type comes out as `∀ (T : go.type), go.type`, which is not Lean).
- **The protobuf messages the cache reads are real structs** (2026-10-08, second
  commit): `mvccpb.KeyValue`, `mvccpb.Event`, `etcdserverpb.{ResponseHeader,
  RangeResponse,WatchResponse}` are listed in their package's `translate` (type only,
  no methods). `translate_types` alone never translates them: every protobuf-go v2
  message has `state protoimpl.MessageState`, `unknownFields protoimpl.UnknownFields`,
  `sizeCache protoimpl.SizeCache`, and Goose's `translate_types` refuses any type
  mentioning another package's alias. Those three aliases come from two more
  packages: `google.golang.org/protobuf/runtime/protoimpl` (just the three aliases;
  `SizeCache`/`UnknownFields` translate to `int32`/`[]byte`; protoimpl's other aliases
  must not be left to `translate_types`, which axiomatizes an alias-of-an-alias as
  `axiom SizeCache`, not `SizeCache.ty`, a name the users do not find) and
  `google.golang.org/protobuf/internal/impl` (names only, but for the struct
  `impl.MessageState`, translated since 2026-10-09; its pointer field's `*MessageInfo`
  stays axiomatized), and `google.golang.org/protobuf/internal/pragma` (types only, all
  four translated: `NoUnkeyedLiterals`, `DoNotCompare` (`[0]func()`) and `DoNotCopy`
  (`[0]sync.Mutex`, so `sync` is imported), which `MessageState` embeds, and
  `DoNotImplement`).
  `clientv3.GetResponse` (`type GetResponse pb.RangeResponse`), `clientv3.WatchResponse`,
  `Op`, `OpOption`, `KV`, `Watcher`, `WatchChan` were already translated.
  `clientv3.Client` is translated since 2026-10-09 (the cache reads its `KV` and
  `Watcher` fields in `newCache`), with the packages of its other fields' types names-only
  (`google.golang.org/grpc`, `grpc/credentials`, `client/v3/credentials`,
  `client/v3/internal/resolver`, `go.uber.org/zap`; "The whole package" below).
- Nothing else (grpc, zap, ...) is reached; types that would need it are axiomatized
  (212 `axiom X.underlying`, by `grep '^axiom .*\.underlying'` in `Code/`), and their
  generated instances are `sorry -- axiomatized type` (424, in `GeneratedProof/`: 150
  in the protobuf packages, 236 in
  `etcdserverpb`, 36 in `client/v3`, 2 in `rpctypes`; no proof uses them, and the raft
  trust base is unaffected). Standard-library packages are Perennial's.
- **`impl.MessageState` is a real struct** (2026-10-09): its generated `TypedPointsto` and
  `IntoValTyped` instances are proved (`solve_into_val_typed_struct`), so the two
  `sorry -- axiomatized type` instances the cache proofs reached (allocating
  `&pb.ResponseHeader{}`) are gone from the trust base. `Proof/go_etcd_io/etcd/cache/v3/Base.lean`
  gained a `True` package instance for `internal/pragma` (translated names-only,
  `Code/google_golang_org/protobuf/internal/pragma.toml`). The field-only message
  predicates and `InvStore.lean`'s high-priority `TypeRepr` instances (`decisions.md`) were
  kept: they still work, and no longer guard against a `sorry`.
- `-lean-root` maps `go.etcd.io/etcd`, `k8s.io` and `google.golang.org` to the empty root
  (modules `Code.go_etcd_io.etcd.cache.v3`, ...).
- The two Goose bugs above belong fixed in Perennial's `goose/types.go`: `types.Unalias`
  in `getStructInfo` (tried: two lines, and the alias errors go away), the type arguments
  in `structInfoToGlangType` (not tried); with them the two fork commits could be dropped.
  The `go.type` in axiomatized generic types is a third (Lean backend).

## The cache's btree: verified (`Proof/k8s_io/utils/third_party/forked/golang/btree/`)

The B-tree etcd's cache uses, `k8s.io/utils/third_party/forked/golang/btree` (the fork
of google/btree's generic `BTreeG`, renamed, without the non-generic `Item` API), is
translated with bodies (part of the `etcd` project of `etc/goose.py`; its `.toml` no
longer restricts it) and proved. The proof was first done on google/btree `aeba20f`
(2026-10-08) and moved onto the fork with the layout by package path (2026-10-09):
every proof carried over unchanged but for the renames (the fork's `freeNode` and
`ReplaceOrInsert` are restructured but equivalent). Design in `decisions.md`
("google/btree: a second proof tree").

- **Every function is proved**: 51 specs, 51 linked results (`Link.lean`, generated by
  `etc/gen-btree-link.py`), no `sorry` and no axiom of this repository; `Results.lean`
  prints every result's axioms: `propext`, `Classical.choice`, `Quot.sound` and
  Perennial's names-only Go declarations (no `sorryAx`). The API (`New`,
  `NewWithFreeList`, `NewOrdered`, `Less`, `NewFreeList`; `BTree`'s `Clone`,
  `ReplaceOrInsert`, `Delete`/`DeleteMin`/`DeleteMax`, `Get`, `Has`, `Min`, `Max`,
  `Len`, `Clear`, the eight `Ascend*`/`Descend*`), its internals (the `items` methods,
  the free list under its mutex, copy-on-write contexts, `mutableFor`/`mutableChild`,
  `split`/`maybeSplitChild`, `insert`, `get`, `min`/`max`,
  `remove`/`growChildAndRemove` (one joint Löb induction), `iterate`, `reset`), and
  package initialization.
- The top-level predicate `ownBTree o t dq s` (`Defs.lean`): the tree at `t` holds the
  entries `s` (Go item, key), keys strictly increasing under `o`; `ownBTree_split`
  (`Fractional.lean`) divides it between readers.
- **No bug found.** Restrictions the specs carry: `1 < degree <= 2^62` (`New` panics
  below; above, `maxItems()` overflows and the second insert panics), `less` deciding
  a strict total order on keys, `Len()` modulo `2^64`. `iterate`'s
  `includeStart`/`hit` skip branches are dead for every caller.
- **The cache uses it** (`InvBtree.lean`): the cache's seven btree specs (its trust
  boundary until now) are the proved ones; its `ownBTree` (models under a strict weak
  order) is defined over the btree's, with the classes of the order as keys, and the
  store's proofs derive their model-level triples from the proved specs
  (`*.modelSpec_of`, all proved; the cache's `ownBTree` keeps the list of (Go item,
  model) pairs, and `ownBTree_persist` rests on `btree.ownBTree_persist`,
  `Fractional.lean`). `btree.New` and `newStore` (and `isStore`) now require
  `degree <= 2^62`.
- **Needs Perennial `11fd2db`** (its `lean` since 2026-10-09, pinned here): three
  commits on top of `2b8cb96`: (1) `copy` as a memmove -- the old model copied in place
  front to back, which is not Go's `copy` for overlapping slices and made `insertAt`'s
  `copy(s[i+1:], s[i:])` corrupt the tree (`decisions.md`); (2) a step rule for
  converting between pointer types with the same underlying type; (3)
  `sort.wp_initialize'`. Raft needed one change for (1)
  (`Proof/go_etcd_io/raft/v3/InvRaftpb.lean`).
- Regenerating the `etcd` project needs Go 1.27 for goose (the fork requires it):
  `GOTOOLCHAIN=go1.27.1 etc/goose.py --project etcd`.
- Cost of the proof (time, tokens, build time, size): `COST.md` in the proof directory.

## Next

- **Close the `Advance` gap** (decisions.md, "RawNode: client-facing specs"): `Advance`
  is proved only when `Ready` queued no self-addressed response, which the specs expose
  as `RNState.advanceable`; since `Ready` does not say when that holds, no client can call
  `Advance` (nor a second `Ready`) yet.
- Follow the Rocq RawNode branch past 857d09190 (its worktree has an uncommitted
  edit to `proof_RawNode__Ready.v`, not ported).

## Differences from the Rocq besides the language

- No axiom for the `Logger` and `Storage` interfaces (Rocq: `is_Logger` and
  `own_Storage` are `Axiom`s, with `wp_logf` a third): `isLogger` is a definition and
  `ownStorage` a typeclass parameter (`StorageModel`), see "Done".
- Names follow Perennial's Lean conventions (`raft.wp_Step`, `own_raft_phys` →
  `ownRaftPhys`, …); see Perennial's `etc/lean-rename/renames.tsv` for the
  framework's Rocq → Lean names.
- The framework changes `main` made to Perennial's Rocq framework
  (`new/golang/theory/*.v`) are ported to Perennial's Lean framework where a proof
  here needs them, not to this repository.

### The ring buffer (`cache/ringbuffer.go`): proved (2026-10-08)

`ringBuffer[T]` is specified and proved in full, Lean-first, for any Go type argument `T`
with Lean representation `T'` (Perennial's `atomic.Pointer[T]` instance assumptions):
`newRingBuffer` and the 13 methods (`Append`, `full`, the four iterations, `PeekLatest`,
`PeekOldest`, `RebaseHistory`, `moduloIndex`, `at`, the two binary searches), one
`{Spec,Proof}/go_etcd_io/etcd/cache/v3/<fn>.lean` pair each, linked in `Proof/go_etcd_io/etcd/cache/v3/Link.lean`
(generated: `etc/gen-link.py --cache`, from `etc/link-lean-first-cache.txt`). Package
instances in `Proof/go_etcd_io/etcd/cache/v3/Base.lean` (`True` for the cache and the etcd, k8s and protobuf packages
it imports). No `sorry`, no axiom: `etc/tcb-report.py --check` now also takes
`Proof.go_etcd_io.etcd.cache.v3.Link`'s 14 results as roots (200 roots) and the baseline is unchanged.

- **The predicate** (`InvRingBuffer.lean`): `ownRingBuffer r cap isItem revOf items`, the
  model a list of abstract values `items : List V`, oldest first. `r ↦ rb`, `rb.buffer' ↦*
  ents`, `RingOk` (`0 < cap ≤ 2^61`, `len(buffer) = cap`, `size = |items|`, `tail < cap`,
  `head = (tail + size) % cap`), item `i` in slot `(tail + i) % cap` with `revision =
  revOf items[i]` (pure) and `isItem item items[i]` (under `□`), revisions strictly
  increasing (`RevSorted`), and the stored `revisionOf` closure's triple
  (`revisionOfSpec`). `cap` is a parameter.
- **Specs**: `Append` takes `isItem item v` (persistent) and `RevAbove` (revision above the
  newest), and leaves `ringAppend cap items v`; the searches return `ltCount` /
  `leCount - 1`; the iterations are loop-invariant style (`iterSpec`, `P : Nat → IProp`,
  `Q` on early stop) over the exact visited sublists (`ascendGeVisited`, ...).
- `newRingBuffer` asks for `capacity ≤ 2^61`: `at` computes `tail + i + len(buffer)`, up
  to `3·cap`, which overflows a Go `int` past that, and Goose's `make` does not bound the
  length. The demux's caller (`historyWindowSize`, unbounded in `Config`) will have to
  supply it. See `decisions.md`.
- No Goose or proofgen problem with the generic structs: `ringBuffer T'`/`entry T'`
  points-tos, field access and the `[]entry[T]` slice all worked as generated.

### The store (`cache/store.go`, `cache/snapshot.go`): proved (2026-10-08)

`newStore` and `store`'s `Get`, `getSnapshot`, `Restore`, `Apply`,
`applyProgressNotifyLocked`, `applyEventsLocked`, `LatestRev`, with `validateRevisions`,
`newKVItem`, `kvItemLess`, `newClonedSnapshot`, `snapshot.Range`, `isPrefixScan`,
`probeItemFromKey`, and two methods of other packages translated for the store
(`clientv3.WatchResponse.IsProgressNotify`, `etcdserverpb.ResponseHeader.GetRevision`;
`client/v3.toml` also translates the constants `EventTypeDelete`/`EventTypePut`): one
`Spec`/`Proof` pair each, linked in `Proof/go_etcd_io/etcd/cache/v3/Link.lean`. Design and rejected alternatives:
`decisions.md`, "store: btree as the trust boundary, ghost state under the RWMutex".

- **State model** (`InvStore.lean`): `StoreState` = latest revision, latest map, history of
  `(rev, map)` snapshots, oldest first; a map (`KvMap`) is the btree's item list, entries
  `(key, *KeyValue)` strictly sorted by Go's `<` on strings (`kvLess`, `go.GoStringLt`).
  `StoreInv cap st`: `latest.rev ≥ 0`, maps sorted, at most `cap` snapshots with strictly
  increasing revisions none above `latest.rev`. `StoreState.Synced` (newest snapshot =
  latest map) holds after `Restore` and a successful `Apply` (`applyResp_synced`), not after a
  failed one. Models: `snapModel` (`getSnapshot`), `kvRange` (`Range`), `applyEvents`/`applyResp`
  (`Apply`, with the exact partial state of a failed delete), `restoreState` (`Restore`).
- **Ghost shape**: `storeLockInv s γ cap q` is the `RWMutex`'s fractional `P q` (Perennial's
  `ownRWMutex`): `q` of `latest.rev`, of the history ring (`ownRingBuffer` is now fractional) and
  of a `monoNat` on `latest.rev`, and `q/2` of a `ghostVar` with the `StoreState`.
  `storeWriter s γ cap st` (the other half, a mutex token, the latest tree, a lower bound);
  `storeReader s γ cap` (a reader token: `RWMutex` bounds the readers; `newStore` returns
  `actualMaxReaders - 1`); `storeRevLb γ r` (persistent); `isStore s γ cap` (persistent:
  `revCond`'s `isCond`, `degree > 1`, `0 < cap ≤ 2^61`). Readers (`Get`, `getSnapshot`,
  `LatestRev`) return facts about *some* state at least their lower bound (`storeSeen`);
  `Apply`/`Restore` take and return `storeWriter` with the exact transition.
- **Errors** are package variables (`Base.lean`: the cache's `ErrNotReady`, `rpctypes`'
  `ErrFutureRev`/`ErrCompacted` point to fixed non-nil errors); specs return "the value of
  that variable" (`snapErr`).
- **Axioms (trust boundary)**: none of the store's own since 2026-10-09: the btree is
  proved (`Proof/k8s_io/.../btree/`, see above), and its seven specs and `ownBTree` are
  the proved ones (`InvBtree.lean`).
- **`sorry`**: none of the store's own since 2026-10-09: `newStore_RLocker`
  (`RWMutex.RLocker()`'s conversion `*RWMutex → *rlocker`) steps by Perennial's new
  `convert_pointer_same_underlying` (Perennial `11fd2db`). `fmt.Errorf` (the error paths)
  is Perennial's own `sorry` (`Proof/fmt.lean`), reached.
- **Perennial gaps found**: the pointer-to-pointer conversion above (closed in
  `11fd2db`); no `isLocker` for
  `rlocker` (the cache's `revCond.Wait` will need it); `wp_load` through a fractional or
  persistent struct points-to fails (the Access search takes the field-store instance, which
  needs `DFrac.own 1`, and does not backtrack), worked around per proof with
  `attribute [-instance] …_access_store_…`; a struct field access finds `TypeRepr` through
  the struct's `IntoValTyped` (for protobuf messages a `sorry` until `MessageState` was
  translated), worked around with direct `TypeRepr` instances in `InvStore.lean`.
- `etc/tcb-report.py --check` (2026-10-09, roots now including the btree's `Link`): 4 axioms (`fmt.Sprintf`, `rand.Int`, `reflect.DeepEqual`, `strings.Join`) and 3 sorries, all outside this repository's proofs (Perennial's `fmt.wp_Errorf`, two generated protobuf instances); the nine btree axioms and `newStore_RLocker` are gone. `etc/goose.py --check` passes (fetching the fork from GitHub; Go 1.27 for the etcd fork). Since the merge with the demux and `MessageState` work: 4 axioms, 2 sorries ("Merged with upstream's layout" above).

### watcher, notifier, ready (`cache/watcher.go`, `cache/demux.go`, `cache/ready.go`): proved (2026-10-09)

Three small concurrent components, Lean-first like the store, one `Spec`/`Proof` pair per
Go function, linked in `Proof/go_etcd_io/etcd/cache/v3/Link.lean` (the 15 new specs are stated at
`HeapGS HasLC.hasLC GF`, as Perennial's channel, `Once` and `context` specs are;
`etc/gen-link.py --cache` now emits them in a second section, as the raft side does).
Design and rejected alternatives: `decisions.md`, "watcher, notifier, ready".

- **watcher** (`InvWatcher.lean`, `OnceFrame.lean`): `newWatcher`, `enqueueResponse`,
  `Compact`, `Stop`. Predicates `isWatcher w γ pred` (persistent; `pred :
  Option (GoString → Bool)`, the `keyPred` closure's triple `keyPredSpec`, nil iff `none`),
  `watcherOpen γ sent` (the producer's), `watcherClosed γ sent c` (persistent; `c = none`
  from `Stop`, `some rev` from `Compact rev`), `watcherConsumer γ received` (the
  consumer's); the invariant `watcherInv` ties the two logs to the channel state (any
  capacity `≥ 0`, unbuffered included). `enqueueResponse` returns `ok` with
  `enqueueResult pred r sent ok sent'` (the pure model `filterResp`: dropped responses are
  reported delivered; otherwise `ok → sent' = sent ++ [r']`, `!ok → sent' = sent`); the sent
  values are `respSent` (`respAt` and a non-nil `Header`). `Stop`/`Compact` take
  `watcherAt γ sent ph` (open or already closed) and give `watcherClosed γ sent
  (ph.cancelAfter c)`. Consumer side, as lemmas: `watcher_recv_au` (the `recvAu` of
  `<-w.respCh`, for `Cache.Watch`'s `select`), `wp_watcher_receive`, `isWatcher_isChan`,
  `wp_watcher_cancelResp` (`w.cancelResp` after `watcherClosed`: `cancelAt p c`),
  `watcher_received_prefix(_closed)`.
- **notifier** (`InvNotifier.lean`): `newNotifier`, `notify`, `wait`. A notification counter
  (`notifierLb γ k`); `notify` takes a `notifierHandle` (an `RWMutex` token; `newNotifier`
  returns `actualMaxReaders` of them) and gives `notifierLb γ (k0 + 1)`; `wait ctx` returns
  `nil` with `notifierLb γ (k0 + 1)` (a `notify` after the read) or a non-nil error with the
  context done (`notifierWaitResult`).
- **ready** (`InvReady.lean`): `newReady`, `Ready`, `Set`, `Reset`, `waitForState`,
  `WaitReady`, `WaitNotReady`. An epoch counter (`readyEpochLb γ e`), the state in epoch `e`
  being `readyParity e`; `Ready`/`Set`/`Reset` return `readySeen γ e0 b` (state `b` in an
  epoch `≥ e0`; `true` after `Set`, `false` after `Reset`); `waitForState ctx pred` is
  higher-order (`readyPredSpec r pred P`, `P : Bool → Bool`), instantiated with `id` and
  `not`, returning `readyWaitResult` (`nil` with a seen state satisfying `P`, or a non-nil
  error with the context done).
- **`Base.lean`**: `rpctypes`' package facts gained `errorStringSpec` for `ErrCompacted`
  (its `Error()` returns some string), which `Compact` calls; the two store proofs that
  destructure `rpctypesInit` were adjusted (patterns only).
- **New `sorry`s in the trust base** (`etc/tcb-report.py --check --update`: 14 axioms, 4
  sorries): `impl.MessageState`'s generated `MessageState_typed_pointsto` and
  `MessageState_into_val_typed` ("axiomatized type"), reached by `&pb.ResponseHeader{}` in
  `enqueueResponse` (a nil header) and `Compact`: allocating a protobuf message needs the
  message's `IntoValTyped`, which contains its opaque `state` field. They go once
  `protobuf/internal/impl.MessageState` (and the `internal/pragma` types it embeds) are
  translated rather than axiomatized (done 2026-10-09: both gone, see the `EtcdCache`
  section). `Stop`, `newWatcher`, the consumer lemmas, the
  notifier and ready rest on no `sorry`; Perennial's `context` `sorry`s (`WithCancel`, ...)
  are not reached (only `isContext`'s `Done`/`Err` are used).
- **Perennial gaps found**: `Once.wp_Do` takes a persistent closure triple, so a closure
  cannot use the caller's resources; `OnceFrame.lean` proves `Once.wp_Do_frame` (the caller
  lends `R`, gets `R'` back if its closure ran, `R` otherwise) from `isOnce`'s definition.
  `RWMutex` (both specs) needs a token for `RLock`, so there is no persistent `isNotifier`.
  `init_RWMutex`'s `List.replicate (Int.toNat actualMaxReaders)` is unfolded by the kernel
  (deep recursion) unless the count is first abstracted with an equation and `rw`
  (`generalize` is not enough; `Proof/newNotifier.lean`). `wp_start` on the closure's triple
  in `Compact` failed looking for a `MethodUnfold` of the `Error` method named by a
  persistent hypothesis (`errorStringSpec`) still in context; clearing it fixed that
  (`Proof/watcher__Compact.lean`).


### The demux (`cache/demux.go`): proved, modulo one Perennial gap (2026-10-09; gap closed, see "Sorry-free")

`newDemux` and `demux`'s `Register`, `Unregister`, `Init`, `Broadcast`, `LatestRev`,
`BroadcastProgress`, `BroadcastProgressTo`, `updateStoreLocked`, `broadcastLocked`,
`broadcastProgressLocked`, `broadcastEventsLocked`, `Purge`, `purge`, `Compact`,
`resyncLaggingWatchers`: one `Spec`/`Proof` pair each, linked in `Proof/go_etcd_io/etcd/cache/v3/Link.lean` (all at
`HeapGS HasLC.hasLC`). Out of scope (the Cache stage): `NewDemux`, `resyncLoop`,
`WaitForNextResync`. Vocabulary and every shared lemma in `InvDemux.lean` (no `sorry`);
design and rejected alternatives: `decisions.md`, "demux: the delivery invariant under the
lock".

- **State.** The writer's `DemuxCore` (`minRev`, `maxRev`, the history's batches, the ghost
  `stream` of every batch since the last purge; a `Batch` is the events of one revision,
  `batchRev` the ring's `revOf`), invariant `DemuxInv`; the watcher maps, the registrations
  (ghost map `w ↦ RegInfo`: names, resolved start `s`, filter agreement) and their `View`s
  (stream, `maxRev`, next revision `n`, phase active/lagging/closed) live in the lock
  (`RegsOk`; the Go maps are `actOf views`/`lagOf views`).
- **The delivery theorem** (`Unregister`'s postcondition, `DeliveredLog`): when a registrant
  unregisters its watcher, the watcher is closed after a log `sent` such that the events sent
  are exactly the events of the stream batches with `s ≤ revision < n` (for the watcher's
  last `n`), filtered by its key predicate, in stream order (so no gap and no duplicate); the
  log is in order (responses' events strictly increasing from one response to the next, and a
  progress notification at `p` is at or above every earlier event and below every later one);
  and a compaction cancel is at `n`. `demux_watcher_delivered` gives the same at any time under
  a read lock, combined with the consumer: what it received is a prefix of such a log.
- **Overflow premise.** `DemuxInv` has `maxRev < 2^63 - 1` (so `maxRev + 1`, `lastRev + 1`,
  `PeekOldest() + 1` do not wrap); `Broadcast` takes it of the response
  (`RespRevsBounded`: header and event revisions below `2^63 - 1`). Also: events sorted
  (`EvRevSorted`, as for the store), `newDemux`'s capacity in `(0, 2^61]`.
- **`Register`'s premise `watcherUnique w γ`** (`w` has no other ghost name): needed to know
  `w` is not registered yet; not derivable from `isWatcher`. The Cache stage has to get it
  from `newWatcher` (e.g. a registry of `respCh` points-tos), which today does not provide it.
- **Findings against the design:** (1) `minRev` is not a lower bound of the history's
  revisions: `Broadcast` checks events against `maxRev` only, so `Init(100)` then an event at
  5 keeps a batch below `minRev` (etcd's watch from 100 never sends it). `DemuxInv` keeps only
  "every stream batch at or above `minRev` is in the history", which is what resync needs; the
  delivery invariant is unaffected. (2) `resyncLaggingWatchers`'s outcome is not observable
  outside the lock: its postcondition `∃ c views views', ResyncStep c views views'` is proved
  with the lock's real views (the loop tracks `ResyncOutcome` per key) but is satisfiable
  trivially as a statement. No case where the delivery invariant breaks.
- **`sorry`** (closed 2026-10-09: Perennial's `6519b44f5` proves it, `MapRangeMut.lean` is
  gone; see "Sorry-free"): one, `wp_map_for_range_mut_keys` (`MapRangeMut.lean`), a **Perennial gap**:
  `broadcastProgressLocked`, `broadcastEventsLocked` and `resyncLaggingWatchers` write the map
  they range over (current key only, which Go allows), and Perennial's `map.forRange` keeps the
  map `StartRead`-locked for the whole loop, so a write in the body is stuck: the lemma is what
  Go guarantees and is false in Perennial's present model. Fix in Perennial: read the domain
  once, then look each key up when it is visited (skipping deleted keys). Also reached: the two
  known `impl.MessageState` sorries (`&ResponseHeader{}` in the progress responses; gone
  2026-10-09, `MessageState` is now translated).
  `etc/tcb-report.py --check --update`: 14 axioms, 5 sorries (the baseline gained
  `wp_map_for_range_mut_keys`). `lake build` passes; `etc/gen-link.py --cache` reproduces
  `Proof/go_etcd_io/etcd/cache/v3/Link.lean`.

### Key predicates and request validation (`cache/predicate.go`, `cache/cache.go`): proved (2026-10-09)

`ExactKey`, `FromKey`, `Range`, `KeyPredForRange`, and `Cache`'s `validateRange`,
`validateGet`, `validateWatch`, `Ready`, `WaitReady`, `RequestProgress`: one `Spec`/`Proof`
pair each, linked in `Proof/go_etcd_io/etcd/cache/v3/Link.lean`; vocabulary in `InvCache.lean`. No `sorry`, no axiom
(`etc/tcb-report.py --check` unchanged: 14 axioms, 3 sorries; the unsupported-option errors
reach Perennial's `fmt.wp_Errorf` `sorry`, already in the baseline).

- **Newly translated** (`client/v3.toml`, with bodies): the 16 `Op` getters the cache reads
  (`IsCountOnly`, `IsPrevKV`, `IsSortSet`, `Limit`, `Min/MaxModRev`, `Min/MaxCreateRev`,
  `IsFragment`, `IsCreatedNotify`, `IsFilterPut`, `IsFilterDelete`, `RangeBytes`, `Rev`,
  `IsSerializable`, `IsProgressNotify`), `GetPrefixRangeEnd`, `getPrefix` and the variable
  `noPrefixEnd`; each proved (`Spec/go_etcd_io/etcd/client/v3/Op__*.lean`, `getPrefix`, `GetPrefixRangeEnd`).
  `OpOption`s, `OpGet`/`OpWatch` are not (the `Get`/`Watch` stage decides how to model them).
- **`bytes.Compare` is now in Perennial** (Perennial `d292dc284`, pinned here): it calls
  `internal/bytealg` (assembly), so `bytes.toml` marks it trusted, with a model in
  `TrustedCode/bytes.lean` (compare the contents as strings) and `bytes.wp_Compare` proved
  from it (`compareResult`). Push Perennial before this repository.
- **Keys** are `GoString`s (a `[]byte`'s contents); the predicates are `exactKeyPred`,
  `fromKeyPred`, `rangePred` and `keyPredForRange start end` (`GoString → Bool`, in
  `go.GoStringLt`), and `mem_kvRange` says `kvRange`'s entries are exactly the map's entries
  whose key satisfies `keyPredForRange` (for `Get`/`Watch` to agree). The closures keep the
  key slices: the specs take them read-only (`↦*□`) and return `keyPredSpec f p`
  (`InvWatcher.lean`) with `f ≠ nil`, i.e. `keyPredOk f (some p)` for `newWatcher`.
- **`validateRange`** returns `rangeErr`: `nil` iff `validRange prefix start end`, else the
  value of `ErrKeyRangeInvalid`; `prefixRangeEnd` is `GetPrefixRangeEnd` as a function.
  **`validateGet`/`validateWatch`** return `validateResult`: some non-nil error (the
  `fmt.Errorf` wrapping of `ErrUnsupportedRequest` is not modelled) if the `Op` asks for an
  unsupported option (`OpModel.getUnsupported`/`watchUnsupported`), else `rangeErr`'s
  outcome with a nil predicate, else `nil` and the `KeyPredForRange` closure for
  `[key, op.RangeBytes())`. `Base.lean`'s package facts gained `ErrUnsupportedRequest`,
  `ErrKeyRangeInvalid` (cache) and `noPrefixEnd` (`clientv3`).
- **`isCacheFields c cf γr γd cap`** is a partial, persistent `Cache` predicate (fields
  `prefix`, `cfg`, `ready`, `demux`, with `isReady`/`isDemux`); the `Cache` stage extends it.
  `Ready`/`WaitReady`/`RequestProgress` are the `ready`/`demux` specs through it.
- `lake build` passes; `etc/goose.py --check` passes; `etc/gen-link.py --cache` reproduces
  `Proof/go_etcd_io/etcd/cache/v3/Link.lean`.

### Cache.Get and the etcd model (2026-10-09)

`Cache.Get` is proved end to end, with `Cache.serverRevision`, `Cache.waitTillRevision`,
`conditionalProgressRequestor.add`/`remove`, and the `clientv3` functions that build a `Get`'s
`Op` (`OpGet`, `NewOp`, `Op.applyOpts`, `IsOptsWithPrefix`, `IsOptsWithFromKey`, `WithLimit`,
`WithRev`, `WithPrefix`, `WithRange`, `WithFromKey`, `WithSerializable`, `WithCountOnly`,
translated with bodies in `client/v3.toml`): one `Spec`/`Proof` pair each, linked in
`Proof/go_etcd_io/etcd/cache/v3/Link.lean`. No `sorry`. Design: `decisions.md`, "The etcd
model".

- **The model** (`InvEtcd.lean`): `axiom etcdState rev pfx s` (etcd's state at `rev`, keys with
  prefix `pfx`, as `EtcdKv` contents) and `axiom etcdState_agree` (one state per revision).
  `isEtcdKvs rev pfx m` (a definition, persistent): the map `m`'s `*KeyValue`s hold, in order,
  such a state (`kvValAt`, read-only fields), keys sorted with prefix `pfx`;
  `isEtcdKvs_agree`: same revision, same keys and contents. Contents rather than pointers,
  because each response allocates fresh `KeyValue`s (pointer agreement would be false of the
  real client).
- **The client**: `isEtcdKV kv pfx` is a definition, the triple of `kv.Get(ctx, key, opts...)`
  for options with model transformers `gs` (`optsAt`, `optSpec`, `OpFull` in
  `client/v3/InvOp.lean`, covering every field `toRangeRequest` sends): any error; or a header
  revision `r` with `isEtcdKvs r pfx m` for some `m`, and, for a prefix get
  (`OpFull.isPrefixGet`), `resp.Kvs` lists exactly `m`. It is a premise (`isCacheFields`), not
  an axiom: the Cache stage will assume it of `client.KV` (the axiom about the client). Since the
  `etcdReached` change (top section) the triple is also linearizable: it takes `etcdReached lo`
  and returns `etcdReached r` with `lo ≤ r` for a non-serializable request.
- **The Get theorem in words** (`Spec/go_etcd_io/etcd/cache/v3/Cache__Get.lean`,
  `cacheGetResult`): for a reader of the store (with a lower bound `r0`), options that do not
  make `OpGet` panic, and `o` the request's `Op`, `c.Get(ctx, key, opts...)` returns either
  `nil` and an error — the context done, an unsupported option, a range outside the prefix
  (`ErrKeyRangeInvalid`), and for a linearizable request the client's error, a revision above
  etcd's (`ErrFutureRev`, with the etcd revision it saw), or `ErrCacheTimeout`; or the store's
  `getSnapshot` error — or a fresh response, owned by the caller, whose header revision is the
  store's latest revision in some state `st` (at least `r0`) and whose `Kvs`/`Count` are the
  key-values in `[key, o.rangeEnd)` of the snapshot `(r, m)` that `snapModel st o.rev` picks
  (the greatest cached revision at most `o.rev`, or at most the latest for `0`;
  `snapModel_ok_spec`: `r ≤` the latest revision), where **`m` is etcd's state at `r`**
  (`isEtcdKvs r prefix m`); and, unless the request is serializable, etcd had a state at a
  revision `serverRev` with `o.rev ≤ serverRev ≤` the latest revision of `st` (the answer is at
  least as fresh as etcd when the call started). Note: for `rev = 0`, `r` need not be the latest
  revision (a progress notification moves it without a snapshot); the header still reports it.
- **Store generalization**: the store's lock-protected predicates take a certificate
  `E : w64 → KvMap → IProp GF` (`storeLockInv`, `storeReader`, `storeWriter`,
  `storeLockedPhys`); every history snapshot carries `□ E r m` (ring item `snapCert E`);
  `newStore` takes `E`; `Restore` asks for `□ E rev (restoreMap kvs)`; `Apply`/
  `applyEventsLocked` ask for `snapCerts E` of every snapshot they append (`applyRespSnaps`,
  `applyEventsSnaps`); `getSnapshot` returns `snapCert E p (r, m)`, `Get` `□ E r m`. Other store
  statements unchanged; `isStore` now fixes `revCond`'s locker to `sync.rlockerOf (s.mu)`. The
  cache's `E` is `etcdCert prefix`.
- **`isCacheFields`** gained `store` (`isStore`, with `cf.γs`, `cf.scap`), `kv` (`isEtcdKV`),
  `progressRequestor` (an interface holding `*conditionalProgressRequestor`,
  `isProgressRequestor`: `mux` guards the waiter count, `cond` a `Cond`). Readers of the
  store use `cacheReader cf` (a store reader token): `Get` and `waitTillRevision` take it and
  give it back; where clients get them from is the Cache stage's.
- **`waitTillRevision`**: `nil` only with `storeRevLb γs rev`, else `ErrCacheTimeout` or the
  context's error (`waitResult`). Proved, including the goroutine (`select` on the
  `time.After` channel and `ctx.Done()`, then `revCond.Broadcast()`) and `revCond.Wait()` under
  the read lock.
- **Perennial (`48e1192c7`, pinned)**: `sync.toml` translates `rlocker.*`;
  `sync_proof/rlocker.lean` proves `RWMutex.wp_RLocker`, `rlocker.wp_Lock`/`wp_Unlock`,
  `rlocker_isLockerWith`; `isLockerWith` (a locker whose `Lock` needs a resource that `Unlock`
  gives back) and `Cond.wp_Wait_with`; `time.wp_Since` is a new Perennial axiom (like
  `wp_Now`/`wp_Until`: `time.Since` is not translated). Push Perennial first.
- **Trust base**: new axioms of this repository `etcdState`, `etcdState_agree` (see the
  `tcb-baseline.txt` diff in the commit); `isEtcdKV` is a premise, to become the client axiom
  at the Cache stage.
- **Remaining gaps**: the client axiom itself (where `client.KV` enters, `New`); the `Watch`
  side of the model (the watch loop must produce `isEtcdKvs` for every snapshot it appends,
  `applyEventsSnaps`); `conditionalProgressRequestor.run`; `WaitForRevision`.
- **Gates** (2026-10-09, Perennial `48e1192c7`): `lake build` passes (1370 jobs);
  `etc/tcb-report.py --check`: 5 axioms (`etcdState` new; `etcdState_agree` is not reached by
  any linked result, only by the lemma `isEtcdKvs_agree`), 2 sorries (unchanged);
  `etc/goose.py --check` passes; `etc/gen-link.py --cache` reproduces `Link.lean`;
  `etc/verified-code.py --reuse`: the cache package 66 of 107 functions verified (636 of 1204
  lines), `clientv3` 31 functions.

### The watch loop and Cache.Watch (2026-10-09)

`Cache.Watch` is proved end to end, with `Cache.watchEvents`, `Cache.applyStorage`,
`Cache.get`, `Cache.WaitForRevision`, and the `clientv3` functions `OpWatch`,
`WithProgressNotify`, `WithCreatedNotify`, `WatchResponse.Err` (translated with bodies), and
(since the fixes below) `Cache.watch`, `getWatch`, `getWatchLoop`; out of scope as planned:
`New`/`newCache`, `Close`, `NewDemux`/`resyncLoop`/`WaitForNextResync`,
`progressRequestor.run`, `realClock`/`realTimer`. Design: `decisions.md`, "The stream model:
`EtcdStep`, certificates through the demux".

- **Verified against the fixed code (2026-10-09).** The verified code is `goose-lean` at
  `6ab61a1c7` (pushed; see the EtcdCache section): `48fd5a507`
  merged with the fork's branch `cache-ready-after-retry` (for an upstream PR), whose three
  commits fix findings 1 and 2: `64313a1f8` `Init(rev)` once before the loop, the `Once` only
  setting `ready` (finding 2; `watch_retry_test.go`); `21ac13e0d` each upstream watch in a child
  context canceled when `watchEvents` returns; `a7de41a72` `watch` waits for `applyStorage` after
  `Unregister` (a receive from `applyErr`), returns its error if `watchEvents` did not, and the
  goroutine leaves `c.waitGroup` (finding 1; `TestCacheWatchWaitsForStoreWriter`). Design:
  `decisions.md`, "The watch loop is verified against the fixed code".
  - `Cache.watch` (`Spec/.../Cache__watch.lean`): with the demux's writer and the store's writer
    (synced, latest map etcd's state at `R ≤` latest revision, `0 < rev ≤ R + 1`), returns a
    non-nil error and both writers. `applyErr` is a **handoff** channel (`Handoff.lean`, a new
    generic idiom): the goroutine hands the store's writer back with its error or, with the close,
    the writer and its certificate; the loop takes it at its first receive (in `watchEvents` or
    in the wait), so `Restore`/`Register` of the next round never run beside an old `Apply`.
  - `Cache.getWatch`: `get` then `watch(R + 1)`; returns a non-nil error and both writers.
  - `Cache.getWatchLoop`: with both writers (etcd's linearizability for `get` was the premise
    `isEtcdKVLin cf`; since the `etcdReached` change, the writer's certificate and `isEtcdKV`
    give it, no premise), returns `()` once the
    internal context is done, **with both writers** (returned, not dropped). `defaultConfig` is
    proved (needs Perennial's `time.Minute`).
  - Changed statements: `applyStorage` takes a store watcher from any `0 < s ≤ R + 1` (it was
    `s = R + 1`) when `R` is at most the latest revision, and on `nil` returns the store's
    certificate; `watchEvents` takes the demux initialized at `rev` (`CursorOk`), a `Once` with
    trivial resources, and returns what it took from `applyErr`; `isEtcdKVFrom` (so `get`) also
    bounds the revision below `2 ^ 63 - 1`. `initCore_ok`, `demuxWriter_inv` moved to
    `InvCache.lean`.
  - Perennial (`96ec7016d`, on `099c2a08b`; push Perennial first): `fmt.Printf`'s trusted model
    (it panicked) returns `(0, nil)`, `fmt.wp_Printf` proved; `time.Minute`/`time.Hour`
    translated (were axioms). Trust base: `context.wp_WithCancel` (a Perennial `sorry`) is now
    reached (`watchEvents`); `etc/tcb-baseline.txt` updated: 10 axioms, 3 sorries.
  - Gates: `lake build` passes (1406 jobs); `etc/tcb-report.py --check` passes (after
    `--update`, above); `etc/goose.py --check` passes (fetching the fork); `etc/gen-link.py
    --cache` reproduces `Link.lean`; `etc/verified-code.py --reuse` (with `6ab61a1c7` fetched
    into `.lake/go-src/etcd` from `/shared/etcd`, until pushed): the cache package 74 of 107
    functions verified, 9 unfinished (`watchEvents` now among them: it uses the
    `wp_WithCancel` sorry), 803 of 1206 lines (66.6%); `cache.go` 14 of 21.
- **The stream model** (`InvEtcd.lean`). One new axiomatized proposition, `EtcdStep r0 r1 pfx
  evs`: etcd had no event under `pfx` strictly between `r0` and `r1`, and its events at `r1` are
  `evs` (etcd's contents, `EtcdEv`); `r0 ≤ r1`, `r0 < r1` for events. Two property axioms:
  `etcdStep_transfer` (`etcdState a pfx s` for `r0 ≤ a < r1` gives `etcdState r1 pfx
  (applyEvsState s evs)`) and `etcdStep_compose` (a step without events then a step is a step).
  The bridge `isEtcdKvs_step` (proved) turns a map that is etcd's state at `Y` and a step from
  `p ≤ Y` whose events the store's batch matches (`evsMatch`) into etcd's state at the batch's
  revision: what certifies the store's snapshots from the watch stream.
- **The client's watch** (`isEtcdWatcher`, a definition like `isEtcdKV`): a prefix watch from
  `rev > 0` returns an SPSC channel whose responses satisfy etcd's watch contract from the
  position before to the one after (`watchRespOk`: an error, the created notification, a progress
  notification with its step, or sorted events above the position, below `2^63 - 1`, in batches
  each the step after the previous one); `etcdWatch_recv_au` is the receive.
- **Certificates through the demux**: `isDemux d γd cap C`, `demuxWriter … C`, …, for a
  certificate `C : DemuxCert GF` (the cache's: `etcdStepCert pfx`). The lock holds the stream's
  certificate chain from `DemuxCore.base` (the revision before `Init`'s); `Broadcast` takes, for
  an accepted response, `respCert` (its batches chained from the stream's last batch; a progress
  notification at or above `base`). A watcher publishes, for each log its producer had, the
  delivery facts and the delivered batches' chain (`demuxPub`, `WatcherPub`; the consumer learns
  it at each receive, `watcher_recv_au`), from a revision below its start (`RegsStart`). The
  demux's other statements are unchanged but for the `C` argument; `Register` takes the
  watcher's publication and `watcherUnique w` (now an exclusive half of `w.keyPred`'s points-to,
  produced by `newWatcher`).
- **The Watch theorem in words** (`Spec/go_etcd_io/etcd/cache/v3/Cache__Watch.lean`,
  `cacheWatch_delivery`): for a context, options (`OpWatch` must not panic) and a demux token
  and wait-group slot (`cacheWatchSlot`), `c.Watch(ctx, key, opts...)` returns a channel; if
  `WaitReady` fails it is closed and empty; if the request is rejected (`validateWatch`) it holds
  one canceled response and is closed; otherwise, with `o` the request's `Op`, the responses the
  caller receives, in order, are a prefix of the responses the demux sent the watch's watcher,
  possibly followed by the compaction's cancel response, and for every prefix received:
  the events received are exactly the events of a list of etcd's batches `b_1 … b_k` (each the
  events of one revision, increasing) whose keys are in `[key, o.rangeEnd)`, in order, with no gap
  and no duplicate; each `b_i` is certified by etcd's step from at most `b_{i-1}`'s revision
  (`EtcdStep`: its events are etcd's events at that revision, and nothing under the prefix
  changed in between), `b_1` from a revision `p₀` below the start revision `o.rev` when it is not
  `0`, and every `b_i` is at or above it: nothing etcd did under the prefix from `o.rev` on is
  missing; the responses are in order (`SentOrdered`: events increase from response to response,
  and a progress notification is at or above every earlier event and below every later one); a
  compaction cancel at `n` comes after every batch below `n` was sent.
- **The loop's pieces**: `watchEvents` (the demux's writer, `cacheWriter`: certifies every batch
  it broadcasts from the watch's steps, through its knowledge `TailOk`/`CursorOk` of where the
  stream is; `readyOnce.Do(Init; Set)` with the framed `Once`), `applyStorage` (the store's writer:
  every snapshot `Apply` appends is etcd's state at its revision, from the store watcher's
  publication and the bridge), `get` (`Restore` of etcd's state at the response's revision; it
  needs etcd's linearizability: finding 4; now from `etcdReached`), `WaitForRevision`.
- **`Cache.Watch`'s premises and costs**: `cacheWatchSlot` (a demux token and a wait-group
  budget token, both kept by the goroutine: each `Watch` spends one of the `2^31 - 1` slots of
  `cacheWgInv`, which keeps the `int32` counter from overflowing); `isCacheFields` gained the
  watcher, internal context, clock (`isClock`/`isTimer`, definitions: the clock's trust boundary,
  to be met by `realClock`), the wait group (Perennial's `isWaitGroup`, no waiters: `Close` is out
  of scope) and `0 ≤ PerWatcherBufferSize` (finding 5). The rejected request's cancel reason is
  `err.Error()`: Perennial's `fmt.wp_Errorf` (still a `sorry`) now says `Error()` returns some
  string (Perennial `099c2a08b`), and the package facts say so of `ErrKeyRangeInvalid`.
- **Perennial** (pinned at `099c2a08b`, on `640a605cc`, on `48e1192c7`; push Perennial first):
  `640a605cc`: the channel model's `TrySend`/`TryReceive` return "not ready" on a nil channel
  (they dereferenced it, so a `select` with a nil-channel case was stuck: `Watch`'s
  `case <-progressChan` without `WithProgressNotify`), with `wp_TryReceive_nil`,
  `wp_TrySend_nil`, `nilClausePre`, `chan.wp_select_blocking_nil`/`_nonblocking_nil`;
  `099c2a08b`: `fmt.wp_Errorf`'s error has an `Error()` spec.
- **Findings** (about etcd's cache, `upamanyus/etcd` `48fd5a507`, `cache/cache.go` unless noted;
  1 and 2 are fixed on the fork, `6ab61a1c7`, and the verified code has the fixes):
  1. *Two writers of the store.* `watch` (348-370) does not wait for an iteration's
     `applyStorage` goroutine (355-361) before the next iteration, when `watchEvents` returns
     `nil` (the watch channel closed, 402-403, or `applyErr` closed, 418-420), nor does
     `getWatchLoop` (316-328) before the next `get`'s `store.Restore` (344): after `Unregister`
     closes the store watcher, the old goroutine keeps draining its buffered responses into
     `store.Apply` (377-382). The two writers serialize on `store.mu`; the result is right only
     because `validateRevisions` (`store.go:126`) rejects the stale events, which needs etcd's
     linearizable `Get` to return a revision at least the old stream's. So `applyStorage`'s spec
     (one writer, `storeWriter`) is true, but `watch`, `getWatch`, `getWatchLoop` cannot be
     proved against the store's single-writer specs: that needs a multi-writer store (the
     writer's state and latest tree inside `store.mu`'s invariant, `Apply`/`Restore` specified
     for the current state, with a cache-level invariant on it) and etcd's linearizability in the
     client model. Not done: fixed instead (`a7de41a72`), and the three functions are proved
     against the fixed code with the single-writer specs.
  2. *The cache can stay not ready after a retry.* `watch` registers the store watcher (352)
     before `Init` (406); on a retry whose `Get` revision `R'` differs from the demux's `maxRev`
     (or with `maxRev = 0`), `Init(R'+1)` purges (`demux.go:131-135`, `141-143`), stopping the
     store watcher; `applyStorage` returns `nil` (378-379) and closes `applyErr` (360);
     `watchEvents` receives `nil`, resets `ready` (418-420) and returns `nil`; `watch` loops
     (366-369) with the same `readyOnce` (349), so `Init`/`ready.Set` (405-408, the only `Set`)
     never run again: `Get`/`Watch` block in `WaitReady` until `watch` fails. The first
     iteration's client watch is never canceled (it runs on `internalCtx`), and the next
     iteration re-watches from the original `rev`, whose replayed events `Broadcast` rejects once
     the stream has events (another round of the retry loop). Liveness, not safety: the specs
     are unaffected. **Confirmed in Go (2026-10-09)**: `cache/ready_liveness_test.go` in the
     fork's working tree (not committed; its own per-stream fake watcher, since the tests'
     `mockWatcher` feeds every stream from one channel) drives exactly this: first `Get` at 9,
     event at 10, stream canceled, retry `Get` at 12 → `watch(13)`, `Init(13)` purges (the
     `141-143` branch), `ready` set then reset, a second upstream stream opens (the first is
     never canceled), the event at 13 reaches the store, and `Ready()` stays false:
     `WaitReady` and `Cache.Watch` time out (5 of 5 runs under `-race`, no data race). The
     control with the retry `Get` at 10 (`Init(11)`, no purge) recovers. The retry backoff is
     `defaultConfig().InitialBackoff`, real time, not the cache's clock or `Config`.
  3. *The store watcher starts lagging.* On a fresh demux (`maxRev = 0`), `Register(storeW,
     rev)` with `rev ≠ 0` makes it lagging (`demux.go:89-95`): it gets the stream only at the
     first resync, so the store, and linearizable `Get`s, lag by up to `ResyncInterval` at
     start. Performance only.
  4. *`get` needs linearizability.* `store.Restore` (`store.go:105-117`) does not check that the
     revision does not go back, and the store's readers' lower bounds (`storeRevLb`) need it;
     `isEtcdKV` related no two calls, so `Cache.get`'s spec took `isEtcdKVFrom kv pfx
     st.latestRev` (a prefix get returns at least the store's revision) as a premise. Now
     (`etcdReached`, top section) the writer knows etcd reached its latest revision and the
     client's get is linearizable: no premise.
  5. *`PerWatcherBufferSize` is not validated.* `newCache` (72-77) checks `HistoryWindowSize`
     and `BTreeDegree` only; `WithPerWatcherBufferSize(-1)` makes `newWatcher`'s
     `make(chan, -1)` panic in `Watch` (138) and in the watch loop's goroutine (351), which
     crashes the process. The proofs take `0 ≤ PerWatcherBufferSize` (`isCacheFields`).
  6. The demux's earlier finding, that `validateRevisions` alone accepts after `Init(m)` events
     below `m - 1` when `maxRev = 0`, is now excluded by the certificates (`respCert`): an
     accepted batch is above the stream's last batch, hence above `base`.
- **Not reached**: no `sorry` of this work; the observed flakiness: `Proof/go_etcd_io/raft/
  v3/stepLeader.lean` failed twice in full rebuilds after a Perennial re-pin ("not pure" at
  239, "ambiguous `decide_true`" at 277) and built alone, unchanged, right after; not
  investigated.
- **Gates** (2026-10-09, Perennial `099c2a08b`): `lake build` passes (1397 jobs);
  `etc/tcb-report.py --check` (after `--update`): 10 axioms, 2 sorries — new `EtcdStep`,
  `etcdStep_transfer`, `etcdStep_compose`, and (the `clientv3` commit) `rpctypes.Error.wp_proof`,
  `status.Error.wp_proof` (grpc is not translated); `etc/goose.py --check` passes;
  `etc/gen-link.py --cache` reproduces `Link.lean`; `etc/verified-code.py --reuse`: the cache
  package 71 of 107 functions verified (8 unfinished: the documented `sorry`s), 776 of 1204
  lines (64.5%); `clientv3` 35 functions.

### The whole package (2026-10-09)

Every function of etcd's `cache` package has a `Spec`/`Proof` pair and a linked result: 107 of
107 (`etc/verified-code.py --reuse`: 97 verified, 10 unfinished, 943 of 1206 Go lines verified,
78.2%). This stage added the rest: the ten `Config` options (`InvConfig.lean`), `Prefix.Match`,
the real clock (`realClock.NewTimer`, `realTimer.Chan/Stop/Reset`), the progress requestor
(`newConditionalProgressRequestor`, `run`), the demux's `NewDemux`, `resyncLoop` and
`WaitForNextResync`, and `Cache`'s `WaitForNextResync`, `Close`, `newCache` and `New`
(`InvNew.lean`). `Results.lean` restates the exported results and prints their trust base.
Design: `decisions.md`, "`New` and the client: translating `Client`, timers as the trust
boundary".

- **The client is translated** (Perennial's Goose, no fork change): `clientv3.Client` is listed
  in `client/v3.toml`, and the packages of its fields' types are names-only (`.toml`s with
  `translate = ["!*"]`, `translate_types`): `google.golang.org/grpc`, `grpc/credentials`,
  `client/v3/credentials`, `client/v3/internal/resolver`, `go.uber.org/zap` (five packages;
  `-lean-root go.uber.org=` in `etc/goose.py`). zap's two axiomatized generic types hit a Lean
  backend bug of Goose (Rocq's `∀ (T : go.type), go.type` printed verbatim), fixed in Perennial
  `f35530719` (`GenericTypeExpr`; Rocq output and Perennial's std-lib translations unchanged).
  `Client.cfg` (`clientv3.Config`, with a `*tls.Config`) and four other field types stay
  axiomatized; their `sorry -- axiomatized type` instances are kept out of the trust base by
  high-priority `TypeRepr` instances for `Client` (`InvNew.lean`, as `InvStore.lean` does for
  the protobuf messages).
- **The client's assumption** `isEtcdClient client pfx` (`InvNew.lean`, a definition): the
  `KV` and `Watcher` fields point for good to a `KV` with `isEtcdKV` and a `Watcher` with
  `isEtcdWatcher` and `isEtcdProgressNotifier` (`RequestProgress` returns some error, no
  logical effect; new in `InvEtcd.lean`). Nothing about caches: etcd's linearizability is a
  property of the client's `Get` against the model fact `etcdReached` (what a caller knows etcd
  has reached), which the client's responses produce and the store and demux carry (top
  section; it replaced the quantification over every cache built over the client).
- **Timers are the trust boundary** (Perennial `8c7000190`, axioms like `wp_Now`):
  `time.wp_NewTimer` returns a `*Timer` with `time.isTimer t ch γ` (its `C` field holds for
  good a channel on which a receive yields some time, `isChanBag`, no logical content);
  `Timer.wp_Stop` and `Timer.wp_Reset` (for such a timer) return some `bool`. `realClock`'s
  `NewTimer` proves the cache's `isTimer` from them, so the real clock is an `isClock`
  (`isClock_realClock`, `Proof/.../New.lean`). `resyncLoop` uses `time.NewTimer` directly.
- **`New`'s theorem in words** (`Spec/go_etcd_io/etcd/cache/v3/New.lean`, `newCacheResult`):
  for a client of etcd for the prefix `pfx` (`isEtcdClient`) and options with model
  transformers `gs` (`cfgOptsAt`), the configuration is `defaultConfig()` with the options
  applied in order; if it has `HistoryWindowSize ≤ 0` or `BTreeDegree < 2`, `New` returns `nil`
  and a non-nil error; otherwise, provided the configuration is `CfgBounded`
  (`HistoryWindowSize ≤ 2^61`, `BTreeDegree ≤ 2^62`, `PerWatcherBufferSize ≥ 0`: finding 5's
  premise and two overflow bounds the code does not check), it returns a cache `c` with
  `isCacheFields` (every field, for that prefix and configuration) and its handles: `2^30 - 2`
  readers of the store (`Get`, `WaitForRevision`), `2^30 - 3` watch slots (a demux token and a
  wait-group slot each, `Watch`), `2^30 - 2` handles on the demux's resync notifier
  (`WaitForNextResync`) with its lower bound `0`, and the whole "open" token (`cacheOpen`,
  `Watch` takes a fraction, `Close` all of it); its resync loop, watch loop (with both writers)
  and progress requestor run on its wait group.
- **The other new specs**: `NewDemux` takes the caller's wait group as `wgSlotProtocol` (the
  triples of its `Add(1)`/`Done()`), returns `newDemux`'s resources less the resync loop's demux
  token and notifier handle; `resyncLoop` returns its two tokens once the context is done;
  `WaitForNextResync` (demux's and `Cache`'s) is the notifier's `wait`: `nil` only after a
  notification beyond the caller's lower bound, or the context's error; `run` returns `()`
  (everything it uses is persistent; `isProgressRequestor` now fixes the `cond`'s locker to
  `&p.mux`, `isPrRun` its other fields); `Close` takes `cacheOpen cf 1` and gives it back
  (nothing comes back through the wait group); each `With*` returns a closure with
  `cfgOptSpec f (fun c => {c with X := n})`; `defaultConfig` now returns `defaultConfigVal`.
- **Changed statements**: `isCacheFields` gained `stop` (the cancel function, with its triple);
  `cacheWgInv` admits one waiter, which has deposited `cacheOpen cf 1`, so `Cache.Watch` takes
  and gives back `cacheOpen cf q` (its `Add(1)` must not happen while `Close` waits:
  Perennial's `WaitGroup.Add` from zero needs no registered waiter); `newDemux` returns the
  notifier's handles (`demuxResyncHandle`) and its lower bound.
- **Perennial** (`f8b35ddbf`, on `f35530719`, on `8c7000190`; push Perennial first):
  `context.wp_Background` (proved: `backgroundCtxVal`) and `context.wp_WithCancel_Background`
  (a `sorry`, as `wp_WithCancel`: `Background()`'s `Done()` is `nil`, so it is not an
  `isContext` and `wp_WithCancel` does not apply); the timer axioms; the Goose fix.
- **Perennial gaps found**: `wp_apply` loses track of an `IProp`-typed variable introduced
  by `intro` inside the proof when the applied spec mentions it (here `NewDemux`'s `Pslot`,
  `Prun`): "unknown free variable", or a silent stop reported as unsolved goals at `by`; a
  workaround is to bind the spec's variables with `fun … => by`. A side goal of `wp_apply` (a
  pure premise) may lack the Lean hypotheses `wp_start` introduced (`%H`): frame them from an
  Iris pure hypothesis instead. `wp_for`'s `cleanup_bool_decide` (`try simp`) can silently
  fail on a large context (`Cache.Watch` after `isCacheFields` grew): clearing two unused
  hypotheses fixed it.
- **What the cache's results rest on** (closed 2026-10-09: the four `sorry`s below are gone,
  see "Sorry-free"; `Results.lean`'s `#print axioms`, by `etc/tcb-report.py`;
  besides Lean's `propext`, `Classical.choice`, `Quot.sound` and Perennial's names-only Go
  declarations, about 855 opaque types of the translation):
  - (since the `etcdReached` change, all of these also rest on `etcdReachedAt` and
    `etcdReachedAt_timeless`, `cache_Watch_delivery` included: the cache's demux certificate
    mentions `etcdReached`.)
  - `cache_New`: the model axioms `etcdState`, `EtcdStep`, `etcdStep_compose`,
    `etcdStep_transfer`; this repository's `rpctypes.Error.wp_proof`, `status.Error.wp_proof`
    (grpc's `status` is not translated); Perennial's `time.wp_NewTimer`, `Timer.wp_Stop`,
    `Timer.wp_Reset`; the `sorry`s `wp_map_for_range_mut_keys` (the demux's map iteration,
    Perennial gap), `fmt.wp_Errorf`, `context.wp_WithCancel`, `context.wp_WithCancel_Background`.
  - `cache_Get`: `etcdState`, `EtcdStep`; Perennial's `time.wp_Now`, `time.wp_Since`; the
    `sorry` `fmt.wp_Errorf`.
  - `cache_Watch`: `etcdState`, `EtcdStep`; the `sorry` `fmt.wp_Errorf`.
  - `cache_Watch_delivery` (the delivery theorem for a received log): `EtcdStep` only.
  - `cache_WaitForRevision`, `cache_WaitForNextResync`, `cache_Close`: `etcdState`,
    `EtcdStep`, no `sorry`.
  The 10 unfinished functions are those whose own proof reaches a `sorry`: `newCache`
  (`wp_WithCancel_Background`, `fmt.wp_Errorf`), `watchEvents` (`wp_WithCancel`),
  `validateGet`, `validateWatch`, `validateRevisions`, `store.applyEventsLocked`,
  `store.getSnapshot` (`fmt.wp_Errorf`), `demux.broadcastEventsLocked`,
  `broadcastProgressLocked`, `resyncLaggingWatchers` (`wp_map_for_range_mut_keys`).
- **Gates** (2026-10-09, Perennial `f8b35ddbf`): `lake build` passes (1472 jobs);
  `etc/tcb-report.py --check` (after `--update`): 10 axioms, 4 sorries (new:
  `sorry Perennial.context.wp_WithCancel_Background`; the roots now include
  `Proof.go_etcd_io.etcd.cache.v3.Results`, 389 root theorems); `etc/goose.py --check` passes;
  `etc/gen-link.py --cache` reproduces `Link.lean`.

## etcd's server: the consistent index and the apply thread (`server/v3/etcdserver`): proved (2026-10-09)

Toward ruling out etcd's consistent-index bugs (manual-notes.txt bullets 3-4). Lean-first; the
shared definitions (`Base`, `BaseApply`, `InvCindex`, `InvApply`, `InvServer`, `InvApplier`,
`InvRaftpb`) and `Link.lean` in `Proof/go_etcd_io/etcd/server/v3/etcdserver/`, every spec and
proof in its package (`.../etcdserver/cindex/`, `storage/schema/`, `go_uber_org/zap/`,
`encoding/binary/`, ...), raft v3.7's getters in `EtcdDeps/{Spec,Proof}/go_etcd_io/raft/v3/raftpb/`;
linked by `etc/gen-link.py --server` (`etc/link-lean-first-server.txt`, 47 results). Design
and rejected alternatives: `decisions.md`, "The consistent index and the apply thread".
Done on branch `apply-thread` on the old layout (`EtcdGrove/Server/`, `EtcdCache/`), and
merged into the layout by kind and Go package path (2026-10-09): every file a module, nothing
in the proofs changed but deprecated `if_pos`/`if_neg`.

- **Translation** (`etc/goose.py`'s etcd project): `etcdserver/cindex` in full;
  `storage/schema`'s `cindex.go`; in `etcdserver` the post-lock hook, `apply`,
  `applyEntryNormal`, `applyEntries`, `setAppliedIndex`, `setTerm` and the types they use
  (`EtcdServer`, `raftNode`, `etcdProgress`, `toApply`). The packages their types name are
  translated names-only or types-only (zap, `net/http`, bbolt, config, membership, apply,
  lease, ...). **etcd's own raft dependency, v3.7** (protobuf-go v2 raftpb: pointer fields,
  getters with bodies) is translated into `EtcdDeps/` (a `Part` of the etcd project). It is not
  the gogoproto fork in `Code/go_etcd_io/raft/`, and both define
  `Perennial.go_etcd_io.raft.v3.*`, so no module imports both, and `etc/tcb-report.py` runs
  `tcb-report.lean` twice. The etcd pin (`6ab61a1c7`) needs Go 1.27 (`GOTOOLCHAIN=go1.27.1`
  where the default Go is older).
- **cindex** (`InvCindex.lean`): `NewConsistentIndex` and the 7 methods of
  `*consistentIndex`, plus schema's `UnsafeReadConsistentIndex`, `ReadConsistentIndex`,
  `unsafeUpdateConsistentIndex` and its two wrappers. The index is mirrored by a ghost
  variable; the specs that read or store it are logically atomic, and the backend's meta keys
  are a client-chosen view, read and written through client-supplied triples.
  `unsafeUpdateConsistentIndex`'s `verify.Verify` assertion is proved never to fire.
- **The protocol** (`InvApply.lean`): ghost `(ci, processed-through p, last entry with writes
  eff, pending)`, with `eff ≤ ci ≤ p` out of flight; a commit saves `ci`, so it persists no
  effects above the saved index and no unprocessed entry at or below it (`commit_save_au`).
- **The apply thread** (`InvServer.lean`, `InvApplier.lean`), proved:
  - the post-lock hook (`getTxPostLockInsideApplyHook`, server.go:2448): under the batch lock,
    `ci := i` for the entry `i = p + 1`;
  - `applyEntryNormal`: the applier's contract with the hook, the writes update; a no-write
    entry gets the deferred `ci` update;
  - `apply`: the loop; entries at or below `ci` are replayed with no backend writes, those above
    are applied in order;
  - `applyEntries`: keeps `loopOk` (processed through the larger of `ci` and `ep.appliedi`)
    and advances `appliedi`; the "unexpected committed entry index" panic is ruled out.
- **Trust boundary** (`etc/tcb-report.py --check`, whole repository: 36 axioms, 3 sorries;
  the server adds the 26 axioms below and no sorry):
  - the applier's contracts `apply.Apply` and `applyConfChange`, with `applierFor` (and
    `applierFor_persistent`): one locked critical section with the hook first, or no writes;
  - `pbutil.MustUnmarshalMessage`;
  - names-only callees: zap (`Error`, `Int'`, `Int64`, `String`, `Stringer`, `Uint64`,
    `Logger.Debug`, `Logger.Warn`), `isLeader`, `Logger`, `GoAttach`, `stopWithDelay`,
    `Notify`, `ElectionTimeout`, `AlarmStore.Get`, `Members`, `errors.Is`, `humanize.Bytes`;
  - `BigEndian.Uint64`/`PutUint64` (Perennial translates only `LittleEndian`) and
    `verify.Verify`.

  The only `sorry` the server's results reach is Perennial's `fmt.wp_Errorf`
  (`applyEntries`): with `MessageState` translated as a struct, the `impl.MessageState`
  sorries that `var cc raftpb.ConfChange` reached before the merge are gone.
- **Findings**: `SetConsistentIndex` stores index then term, so a commit concurrent with
  `applyEntryNormal`'s deferred update (outside the lock) can persist the new index with the
  previous entry's term. That entry is a term's first, empty entry, so it is the previous term.
  The term is only read for schema detection and `verify`. Details in `decisions.md`.
- **Not done**: `applyAll`/`applySnapshot` (the snapshot path: `SetBackend` before the lessor's
  `Recover`, the comment at server.go:1055) and the backend side (`BackendHooks.
  OnPreCommitUnsafe`, the commit that calls `UnsafeSave`), whose specs would close the loop
  from the commit's side; establishing the protocol at bootstrap; `applyConfChange` itself.
- **Build** (at the merge): `lake build` passes (1591 jobs); `etc/goose.py --check` passes;
  `etc/gen-link.py --cache` and `--server` reproduce the two `Link.lean`s. One full build
  failed in `Proof/go_etcd_io/etcd/cache/v3/InvDemux.lean:1911` (`slots_take_all`: the
  `iframe` closing `IH`'s premise left `Hrest`, unfolded by `unfold slotRes`, unsolved); the
  unchanged file then built alone and in the next full build. Not understood: watch for it.
