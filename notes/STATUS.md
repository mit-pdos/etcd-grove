# Status (Lean port)

**Last updated:** 2026-10-12 (the apply package's unit 1 on branch `apply-u1`: every function of `backend.go` (but `Compaction`), `quota.go`, `capped.go`, `corrupt.go`, `auth.go` specified and proved, the constructors packaging the layers into `applierSpec`, `chainStep` over `backendStep`, `chain_put`/`_deleteRange`/`_range`/`_txn`; `auth.AuthStore` translated as an interface; a finding (a lease checkpoint entry's several critical sections; fix branch `lease-checkpoint-one-section`); gates 82 axioms, 1 sorry, apply 35/0, apply 63 of 73 functions verified, etcd 557 of 3599, see "Unit 1: the layers"; the apply package's units 0 and A merged into `lean` (the context premise `txnCtx` and the hook premise `csContract ∗ hookIs` both on txn's write path; one `csContract`, mvcc's; `store.Rev` under the hook's `End`; the server's `Link` reuses mvcc's zap results; gates 82 axioms, 1 sorry, apply 17/0, txn 22/0, mvcc 17/0, server 26/0, etcd 494 verified of 3599 functions), see "Merge 0/A"; the apply package's unit A: the backend's post-lock hook in mvcc's contract (`hookIs`, `csContract`), threaded through `store.Write`/`End` and txn's `Put`/`DeleteRange`/`Txn`, see "Unit A: the hook through mvcc"; the server's apply package, unit 0 on branch `apply-u0`: translated with bodies, scaffolding, 12 trust-boundary axioms, the txn functions at `context.TODO()` (`txnCtx`), `store.Rev`, `gen-link.py --apply` and the reuse rule; gates 81 axioms, 1 sorry; a finding (the alarm gauge), see "The server's apply package; a closed theorem about the register's driver in the operational semantics, `register_adequate`, from Perennial's adequacy; package initialization proved for raft, its subpackages, `context` and the register; the account of every axiom and `sorry` it rests on, see "Adequacy of the register's driver"; `origin/lean` merged into `mvcc` (the txn package, units 0–4, and its mvcc changes: the read-only write transaction, `metricsTxnWrite.Rev`/`Changes` of either kind, `idxLogAuth`, reads pinned by tokens; our `zap.Logger.Panic` kept), see "Merge: lean into mvcc (2026-10-12)"; mvcc: the watchable store, unit 2 complete: the batches (`ebAdd`, `batchOf`) and `choose`/`chooseAll` over the members' states, 23 functions of `watcher_group.go`/`watcher.go`; unit 3's design (the store's invariant, the channel protocol of the watch guarantee, three parts), see "The watchable store" and decisions.md "The watchable store's concurrency (unit 3)"; unit 2, first half: the watcher group's sets and structure (11 functions over the tree's contract, 5 of them conditional on it) and the client's watch stream (7 functions over the `watchable` contract; `trace.SpanFromContext` axiom), see "The watchable store"; 2026-10-11: unit 1b: the interval tree's contract (string-affine intervals over the opaque `ownIvt`, seven pending specs, `gen-link.py --adt`) and four pure functions proved, see "The watchable store"; unit 1a: `pkg/v3/adt` (the interval tree) and `watchable_store.go`/`watchable_store_txn.go`/`watcher.go`/`watcher_group.go` translated with bodies, the plan (contract first, the tree's proof last), see "The watchable store"; mvcc: `zap.Logger.Panic`/`Fatal` specified (a panic with the message; an exit, never returning), the key index's `put`/`tombstone`/`get` specified over all inputs (a bad input is the panic, the key index unchanged), `isTreeIndex` with a non-nil logger, see "`key_index.go`'s panics"; the txn units 3 (`Txn`) and 4 (the history laws of the log) merged into `lean` (`2175453f0`; notes-only conflicts, no proof changed; the whole package verified: every translated function of `txn.go`/`put.go`/`range.go`/`delete.go`, txn 39 of 48 functions, 570 of 653 lines; gates 69 axioms, 1 sorry, txn 20/0, etcd 474 verified of 3599 functions, 4943 of 45570 lines), see "Merge 3/4" and "The whole package"; the txn units 1 (`Put`, `DeleteRange`) and 2 (`range.go`) merged into `lean` (`mkGteRange` proved by both: unit 1's kept, `executeRange` adapted, one `wp_slice_literal_nn`; `gen-link.py` every mode reproduces; txn 27 of 48 functions verified, 274 of 653 lines; gates 69 axioms, 1 sorry, txn 20/0, etcd 462 verified of 3599 functions, 4647 of 45570 lines), see "Merge of units 1 and 2"; 2026-10-11: the txn units 0, 0b and 0c merged into `lean` (notes-only conflicts, no proof changed, both `Link.lean`s reproduce; gates 69 axioms, 1 sorry, txn 17/0, mvcc 13/0, etcd 435 verified of 3599 functions, 4373 of 45570 lines), see "Merge of units 0, 0b and 0c"; the server's `txn` package unit 0 on branch `txn-u0`: translated (`txn.toml`, Goose accepts it
as pinned), the requests and responses as the client model's values (`Requests.lean`), `isKV`,
`isTxnLessor`, 13 trust-boundary axioms (`sort.Sort`/`Reverse`, traceutil, `proto.Size`,
`zap.Logger.Panic`, ...), mvcc's read-only write transaction proved, `gen-link.py --txn`, a
finding (`Txn` panics on an empty `RequestOp`, rejected by the gRPC layer), gates 69 axioms, 1
sorry, etcd 435 verified of 3599, see "The server's txn package"; branch `mvcc` merged into `lean`: Perennial `e4e126e46` (one `AllG`: the `[AllG GF]` section variable dropped from the mvcc files), both sides' `gen-link.py` modes and notes kept, the etcd pin `bc8b52a50` (no change to the mvcc sources), see "Merge: mvcc into lean"; mvcc: `index.go` complete: `treeIndex.KeyIndex`/`Insert` proved under the index's history invariant (a reader's pointer lookup; the writer swaps a key's index for an equal one), see "`index.go`, the point operations"; mvcc: `NewStore` proved on a fresh backend: the ghost state allocated, the batch lock's resource deposited at its first `Unlock`, five new trust-boundary axioms, see "The store's constructor"; mvcc: `storeTxnWrite.Range` proved: the bucket view split between `s.revMu` and the batch lock, the batch transaction reads its own puts, `rangeKeys` over an owned reader capability and the index knowledge, see "The writer's range read"; the write transactions proved: `store.Write`, `storeTxnWrite.put`/`Put`/`delete`/`deleteRange`/`DeleteRange`/`End`/`Rev`/`Changes`, the wrappers over a `TxnKind`, `writeView.Put`/`DeleteRange`; the batch transaction's and the lessor's contracts, the revision budget; `proto.Marshal`, `zap.Error`, `zap.Logger.Error` axioms, see "The write transactions"; mvcc: the KV core, phase one: the key index, `index.go` over the verified B-tree, the range reads, the revision encoding, the read transactions opened and closed (`InvStore.lean`: the backend's Key-bucket contract, the store's locks) and the read transaction's `Range` (`rangeOutcome`: the key-values of the certified log at the requested revision, read from the index then the bucket; `traceutil.Trace.Step` and `proto.Unmarshal` axioms) and the wrappers (`metricsTxnWrite.Range`/`End`, `readView`; `traceutil.TODO` axiom) proved on branch `mvcc`, Perennial `bf935cbd5`: Goose ranges over an integer, `float64` of an integer, merged `lean` (panics and `recover`, `client/v3/leasing`), see "mvcc: the KV core, phase one"; Perennial's panics and `recover` adopted (Perennial branch `panic`, not yet pinned: needs `7cea8cc26`), the STM's two panic axioms gone, `lockerMutex.Lock`/`Unlock` specified, four standard-library axioms of `client/v3/leasing` replaced by Perennial's specs, see "Panic and recover"; `client/v3/leasing` unit 5: the monitors, `NewKV` and `Close` proved, every leasing result unconditional, 66 of 67 functions verified; two findings reproduced (`waitRescind`'s `nil` without a delete lets a range delete through another client's lease; a session reset between `acquire` and `Add` leaves a stale entry), see "Unit 5: the monitors; the package"; `client/v3/leasing` units 3 and 4: `txn.go` and `kv.go` but the monitors specified and proved, nested transactions and owned responses in the contract, two new findings (a write of an uncached key applied twice, a failed acquisition ignores the get's options), see "Units 3 and 4"; `client/v3/leasing` units 1 and 2: translated, the protocol as a premise on etcd's history with `leased_value_stable`, the lease cache specified and proved, findings in `EvictRange` and `evalCmp`, see "client/v3/leasing: the protocol premise and the lease cache"; merged upstream's register example, `node.go`, raft from upstream etcd-io/raft and thread tokens into the Mutex/Election/STM line, Perennial `7c93f27aa`, see "Merge: the register, `node.go` and thread tokens"; `STM`: all of `stm.go` specified and proved, atomicity of the serializable levels, Perennial `9276bd1ed`: a map has fewer than `2^63` keys, two trust-boundary axioms for the STM's panic and `recover`, a new history law, the serializable snapshot broken after a retry (a finding, reproduced and fixed on a fork branch), see "STM"; `Election`: all of `election.go` specified and proved, election exclusion, only the leader proclaims, `Campaign` may return `nil` without its key (a finding), see "Election"; `Mutex`: mutual exclusion, Perennial `d240c1732`: `fmt.Sprintf` formats `%s`, `strings.HasPrefix`, see "Mutex: mutual exclusion"; the register example verified over raft: logically atomic `Put`/`Get`, raft proposals over a client log, see "The register example"; the cache's wait-group counter bounded by thread tokens, Perennial `105fb79f5`: the `WaitGroup.Add` overflow assumption reverted, `New` assumes fewer than `2^31 - 3` live threads, see "The wait-group counter and thread tokens"; `node.go` proved: `RestartNode`, `run`, `Propose`, `Step`, `Tick`, `Ready`, `Advance`, see "`node.go`: the concurrent `Node`"; groundwork for `node.go`: a computed `Ready` can be abandoned, Perennial's `wp_slice_append_undo`; pre-vote out of scope at the RawNode level; `Ready`'s messages carry terms at most the node's, see "`node.go` groundwork"; `RawNode.Ready` split into `readyWithoutAccept` and `acceptReady`, for `node.go`; the storage contract has a pending append, for `node.go`; `MemoryStorage.Append` and `NewMemoryStorage` proved; merged upstream's RawNode work into the cache-as-shipped and concurrency line, Perennial `7d0b56b07`, see "Merge: upstream's RawNode work"; `RawNode.Step` takes a `MsgApp` between `Ready` and `Advance`; the `Advance` gap closed; Perennial `f52ce33dc`: Goose with Go 1.22 loop variables, range over arrays, `fallthrough`, `break` in `switch`/`select`, local types; the raft retarget to upstream parked, see "Retargeting raft to upstream"; the TCB and verified-code scripts generic, `--roots`/collections; Perennial `79adaac01`: models of `fmt.Sprintf`, `strings.Join`, `crypto/rand.Int`, three raft axioms gone; Perennial `7d0b56b07`: Goose with per-iteration loop variables, `break` out of `select`, see "Perennial `7d0b56b07`"; merged `cache-as-shipped` into the concurrency work, see "Merge: the cache as shipped and client/v3/concurrency"; the cache as shipped: the verified code is upstream main plus the one real fix, the store has shared writers, Perennial `9092f8eaa`: `WaitGroup.Add`'s overflow a model assumption, see "The cache as shipped"; `client/v3/concurrency`: the transaction and lease model, `Session` proved; the cache sorry-free: Perennial `3ae7dc6a4`, see "Sorry-free"; the cache's linearizability as a model fact, `etcdReached`; merged with upstream's server work: the consistent index and the apply thread, the raft predicate refactors and client-facing RawNode specs; Perennial `8c33774d0`: Goose without `-lean`; the whole cache package specified and proved; `etcdState_modrev_persist`: the owner promoted `queue_fifo_before_claim`'s hypothesis `EtcdModRevPersist` (a key-value lives unchanged from its mod revision while present) to the model's seventh history axiom, the result unconditional, gates 46 axioms, 1 sorry, see "The whole package"; `client/v3/experimental/recipes` unit 2 merged: the whole package verified, 38 of 38 functions, 401 of 401 lines, sorry-free, `pqueue_order` (least priority, then earliest, under `PQKeysWf`), `PriorityQueue.Enqueue` returns `seqKeyPutAt`, the token in `txnCommitErrTodo`, gates 45 axioms, 1 sorry, etcd 373 verified of 3599, see "Merge of unit 2" and "The whole package"; `client/v3/experimental/recipes` units 1b and 3 merged: no proof changes needed, the recipes 28 of 38 functions verified, all sorry-free, 300 of 401 lines, etcd 363 verified of 3599, gates 43 axioms, 1 sorry, see "Merge of units 1b and 3"; `client/v3/experimental/recipes` unit 3: the RWMutex and the double barrier specified and proved, exclusion under unmodified keys, see "Unit 3"; `client/v3/experimental/recipes` unit 1b: `newUniqueKV`, `newUniqueEphemeralKV`, `newSequentialKV` proved, `fmt.Sscanf` an etcd-grove axiom, the client's transaction errors `clientErrIs` (for `errors.Is`), `newSequentialKV` puts but does not create its key, its order under `SeqKeysBelow`, gates 43 axioms, 1 sorry, etcd 353 verified of 3599, see "Unit 1b"; Perennial `e4e126e46` pinned (`cb6a5921e` plus `strings.Split`, `errors.Is`, `fmt.Sprintf`'s integer directives under `ArgsWf`), merged with the one-`AllG` bump and the register's cluster driver, the recipes files without `[AllG GF]` (`waitEvents`' spec names `isSpsc (GF := GF)`), the gates unchanged (42 axioms, 4 sorries; etcd 350 verified of 3599); `client/v3/experimental/recipes` unit 1: the client bundle under the premise that a watch channel is never closed, the client's contracts at `context.TODO()` and its puts, `WithFirstKey`'s options needing a resource, `key.go`/`client.go`/`watch.go` specified and proved but three helpers left to unit 1b, the claim happens at one revision, see "Unit 1"; `client/v3/experimental/recipes` unit 0: translated (a Gooseable commit `bc8b52a50` pinned), the clientv3 option bodies, `gen-link.py --recipes`, the collection, two findings reproduced and fixed on a fork branch (`waitEvents` returns `nil` on a closed watch channel: `Dequeue` panics, `Barrier.Wait` returns released), see "Recipes"; Perennial `cb6a5921e` pinned: one `AllG GF`, provided by `HeapGS`; the `[AllG GF]` section variable dropped from 654 files, see "Perennial `cb6a5921e`: one `AllG`"; the register's cluster driver `Main` proved safe from package initialization, everything allocated in the proof; raft's `isLogger` was unsatisfiable, fixed, see "The register's cluster driver"; 2026-10-10: Perennial's panics and `recover` adopted (Perennial branch `panic`, not yet pinned: needs `7cea8cc26`), the STM's two panic axioms gone, `lockerMutex.Lock`/`Unlock` specified, four standard-library axioms of `client/v3/leasing` replaced by Perennial's specs, see "Panic and recover"; `client/v3/leasing` unit 5: the monitors, `NewKV` and `Close` proved, every leasing result unconditional, 66 of 67 functions verified; two findings reproduced (`waitRescind`'s `nil` without a delete lets a range delete through another client's lease; a session reset between `acquire` and `Add` leaves a stale entry), see "Unit 5: the monitors; the package"; `client/v3/leasing` units 3 and 4: `txn.go` and `kv.go` but the monitors specified and proved, nested transactions and owned responses in the contract, two new findings (a write of an uncached key applied twice, a failed acquisition ignores the get's options), see "Units 3 and 4"; `client/v3/leasing` units 1 and 2: translated, the protocol as a premise on etcd's history with `leased_value_stable`, the lease cache specified and proved, findings in `EvictRange` and `evalCmp`, see "client/v3/leasing: the protocol premise and the lease cache"; merged upstream's register example, `node.go`, raft from upstream etcd-io/raft and thread tokens into the Mutex/Election/STM line, Perennial `7c93f27aa`, see "Merge: the register, `node.go` and thread tokens"; `STM`: all of `stm.go` specified and proved, atomicity of the serializable levels, Perennial `9276bd1ed`: a map has fewer than `2^63` keys, two trust-boundary axioms for the STM's panic and `recover`, a new history law, the serializable snapshot broken after a retry (a finding, reproduced and fixed on a fork branch), see "STM"; `Election`: all of `election.go` specified and proved, election exclusion, only the leader proclaims, `Campaign` may return `nil` without its key (a finding), see "Election"; `Mutex`: mutual exclusion, Perennial `d240c1732`: `fmt.Sprintf` formats `%s`, `strings.HasPrefix`, see "Mutex: mutual exclusion"; the register example verified over raft: logically atomic `Put`/`Get`, raft proposals over a client log, see "The register example"; the cache's wait-group counter bounded by thread tokens, Perennial `105fb79f5`: the `WaitGroup.Add` overflow assumption reverted, `New` assumes fewer than `2^31 - 3` live threads, see "The wait-group counter and thread tokens"; `node.go` proved: `RestartNode`, `run`, `Propose`, `Step`, `Tick`, `Ready`, `Advance`, see "`node.go`: the concurrent `Node`"; groundwork for `node.go`: a computed `Ready` can be abandoned, Perennial's `wp_slice_append_undo`; pre-vote out of scope at the RawNode level; `Ready`'s messages carry terms at most the node's, see "`node.go` groundwork"; `RawNode.Ready` split into `readyWithoutAccept` and `acceptReady`, for `node.go`; the storage contract has a pending append, for `node.go`; `MemoryStorage.Append` and `NewMemoryStorage` proved; merged upstream's RawNode work into the cache-as-shipped and concurrency line, Perennial `7d0b56b07`, see "Merge: upstream's RawNode work"; `RawNode.Step` takes a `MsgApp` between `Ready` and `Advance`; the `Advance` gap closed; Perennial `f52ce33dc`: Goose with Go 1.22 loop variables, range over arrays, `fallthrough`, `break` in `switch`/`select`, local types; the raft retarget to upstream parked, see "Retargeting raft to upstream"; the TCB and verified-code scripts generic, `--roots`/collections; Perennial `79adaac01`: models of `fmt.Sprintf`, `strings.Join`, `crypto/rand.Int`, three raft axioms gone; Perennial `7d0b56b07`: Goose with per-iteration loop variables, `break` out of `select`, see "Perennial `7d0b56b07`"; merged `cache-as-shipped` into the concurrency work, see "Merge: the cache as shipped and client/v3/concurrency"; the cache as shipped: the verified code is upstream main plus the one real fix, the store has shared writers, Perennial `9092f8eaa`: `WaitGroup.Add`'s overflow a model assumption, see "The cache as shipped"; `client/v3/concurrency`: the transaction and lease model, `Session` proved; the cache sorry-free: Perennial `3ae7dc6a4`, see "Sorry-free"; the cache's linearizability as a model fact, `etcdReached`; merged with upstream's server work: the consistent index and the apply thread, the raft predicate refactors and client-facing RawNode specs; Perennial `8c33774d0`: Goose without `-lean`; the whole cache package specified and proved)

Porting the Rocq Raft proof (`new/proof/go_etcd_io/raft/election_proof/`) of
branch `worktree-agent-a22b3746ec9c86178` at `857d09190` (the RawNode branch: it merges
`worktree-raft-replication`'s `feb5c73d4` and adds Ready/Advance/HasReady; the files
were first ported from `main`, then from `feb5c73d4`) to Lean on top of Perennial's Lean
port (mit-pdos/perennial `lean`, pinned at cb6a5921e (2026-10-11: on cb6a5921e: the one `AllG GF` is `GooseGlobalGS.gooseAllG`, provided by `HeapGS`, `ThreadGS`/`ReceiptGS` without their own, see "Perennial `cb6a5921e`: one `AllG`"; on bf935cbd5: Goose ranges over an integer (`for i := range n`, as the three-clause loop) and `float64(n)` of an integer as an uninterpreted function, for mvcc, on upstream's 7cea8cc26 (panics and `recover`, `strings.Compare`/`TrimPrefix`, `(*Time).Add`, `errors.As`), see "mvcc: the KV core, phase one" and "Panic and recover"; on 7cea8cc26 (the `panic` branch merged): the panic outcome, `Catch`, `recover`, standard-library models, see "Panic and recover"; 2026-10-10: on 7c93f27aa: our 9276bd1ed merged with upstream's 105fb79f5 (thread tokens, `wp_fork_tok_*`, the revert of the `WaitGroup.Add` assumption, `wp_slice_append_undo`, the iframe heartbeat option), see "Merge: the register, `node.go` and thread tokens"; on 9276bd1ed: a map has fewer than `2^63` keys, `wp_map_len_lt`, see "STM"; on d240c1732: models of `fmt.Sprintf` formatting `%s` and of `strings.HasPrefix`, see "Mutex: mutual exclusion"; on 7d0b56b07: our `9092f8eaa` merged with upstream's Goose changes (per-iteration loop variables, array ranges, `fallthrough`, `break` out of `switch`/`select`, local types) and `context.wp_WithCancel` building again, see "Perennial `7d0b56b07`"; on f52ce33dc (upstream's, in 7d0b56b07): the Goose features for upstream raft, see "Perennial `f52ce33dc`"; on 79adaac01 (upstream's, in 7d0b56b07): `context.wp_withCancel` builds again; on 9092f8eaa: `WaitGroup.Add`'s overflow a model assumption, the `RWMutex` writer guard, see "The cache as shipped"; on 56b1b6651: our 3ae7dc6a4 merged with upstream's `00b3c10ea` (trusted models and proved specs of `fmt.Sprintf`, `strings.Join`, `crypto/rand.Int`; `math/big`'s `ownInt` normalized, its and `crypto/rand`'s `IsPkgInit` instances now Perennial's), see "Perennial `56b1b6651`"; on 68d220ac8: `fmt.wp_Errorf` proved, `map.forRange` with `wp_map_for_range_mut{,_keys}`, `context.wp_WithCancel` proved; on 3ae7dc6a4: `context.isClosedchanInit`, see "Sorry-free"; on 8c33774d0: upstream's `37416dd10` (Rocq code removed) and `cdf8c0f81` (Goose without `-lean` and the ⁱᵐᵖˡ encoding) merged, see below; on f8b35ddbf: `context.wp_Background`, `wp_WithCancel_Background`; on f35530719: Goose prints an axiomatized generic type in Lean; on 8c7000190: `time.NewTimer`, `Timer.Stop`/`Reset` axioms; on 96ec7016d: `fmt.wp_Printf`, `time.Minute`; on 099c2a08b: `fmt.wp_Errorf`'s `Error()`; on 640a605cc: a `select` case on a nil channel is never ready, `chan.wp_select_blocking_nil`; on 48e1192c7: rlocker, `Cond.wp_Wait_with`, `time.wp_Since`) on cbb85c041: upstream's `11fd2db` merged with
`bytes.Compare`, on Lean's module system since 2026-10-09). The Goose translations of
etcd-raft and etcd's `cache` package are this repository's `Code/` and `GeneratedProof/`,
generated and checked by `etc/goose.py`. Files are laid out by kind and Go package path
(`Spec/go_etcd_io/raft/v3/raft__Step.lean`) and every file is a module of Lean's module
system (2026-10-08; decisions.md, "Layout by kind and Go package path" and "Lean's
module system").

## The server's apply package (`server/v3/etcdserver/apply`)

Plan: `decisions.md`, "The server's apply: the hook through mvcc, the chain as triples, compaction
out of the model" (units 0 and A in parallel, then 1, 2, 3).

### Unit 0: translation and scaffolding (2026-10-12)

Branch `apply-u0` (worktree `/shared/etcd-grove-apply0`, off `lean` at `436f363c4`; Perennial
`e4e126e46` as a path dependency, `.lake/manifest-merge.json`).
- **Translation**: `apply.toml` translates everything but `metrics.go` (`alarms`, `init`: names
  only); the pin (`bc8b52a50`) translates as is: goose promotes the methods of the wrappers'
  embedded `applierV3` *interface* as `MethodUnfold` wrappers (`applierV3Capped.Range` is
  `MethodResolve applierV3.ty "Range"` on the field), the gap the plan expected does not exist.
  `etcdserverpb.toml` adds `InternalRaftRequest`, `RequestHeader`, `InternalRaftStringer`, the
  requests read and responses built (compaction, lease, alarm, auth), the alarm actions and
  types; `membershippb.toml` (the three cluster requests, `Member`, `RaftAttributes`,
  `Attributes`); names-only `authpb` (a goose gap: a struct listed by name whose field names a
  type of a package not imported, `AuthRoleGetResponse.Perm`, is emitted with a dangling
  reference), `semver/v3`, `etcdserver/api`, `etcdserver/version`; `lease.Lease` and
  `storage.BackendQuota` become translated structs (`lease.toml` imports `sync`,
  `storage.toml` `backend`). `etc/goose.py` lists the new packages (`github.com/Masterminds/
  semver=` root). The other names-only packages (`types`, `wait`, `pbutil`, `auth`, `v3alarm`,
  `membership`, `storage`, `traceutil`, `lease`) existed.
- **Base** (`apply/Base.lean`): `applyInit` (`alarms` holds a `*GaugeVec`; `ErrCorrupt` a fixed
  non-nil error) and the instances of the packages the apply package reaches, moved from the
  server's `BaseApply.lean` (which imports it): the apply package must not import the server's
  translation (unit 3 imports the other way). `InvRaftpb.lean` imports it instead of
  `BaseApply`; the cache's `Base` gains `membershippb`'s and `authpb`'s instances.
- **Scaffolding**: `InvRequest.lean` (`IRRModel`, `HeaderModel`, `irrDecode` (opaque; a decoder,
  not the plan's encoder: decisions), `irrId`, `dispatchKind`, `noSideEffect`,
  `needAdminPermission`, `semverValid`, `internalRaftRequestIs p rq`, persistent, the KV four
  as the txn package's `rangeRequestIs`/`putRequestIs`/`deleteRangeRequestIs`/`txnRequestIs`);
  `Contracts.lean` (`csContract P f Pre Q Post`, `isAuthStore`, `isApplyLessor` over
  `isTxnLessor` with `Grant`/`Revoke` (at the sole writer: deletions committed)/`Checkpoint`/
  `Lookup` (`leaseIs`: `ID`, `TTL()`, `Keys()`), `isAlarmStore`, `isCluster`, `isRaftStatus`,
  `isSnapshotServer`, `isConsistentIndexer`, `isQuota`, `isApplyKV` (txn's `isKV` and the
  store's `ReadView`)); `Wait.lean` (`waitOk`, moved from the server's `InvApplier.lean`, with
  `IsRegistered`; two server proofs take the new conjunct); `Chain.lean` (`Chain`, `baseChain`,
  `alarmChain`, `Outcome`, `chainStep` over the backend's relation, `applierSpec` with the
  layers' structs only: the method triples are unit 1's). `csContract` is defined here in the
  `apply` namespace; unit A's (mvcc/txn) should replace it at the merge.
- **Axioms** (12 new, each `Spec/`+`Proof/`): `semver.MustParse` (a version, or a panic, by
  `semverValid`), `semver.Version.LessThan`/`String` (non-nil versions), `types.ID.String`,
  `etcdserverpb.AlarmType.String` (through the field's address), `zap.Logger.Info`,
  `txn.WarnOfExpensiveRequest`/`WarnOfFailedRequest` (return), `prometheus.GaugeVec.
  WithLabelValues` (a gauge with mvcc's `gaugeSpec`: `Inc`/`Dec` are its contract),
  `context.WithValue` (Perennial translates `context` without its body; restricted to the auth
  store's two key types), `storage.NewBackendQuota` (an `isQuota`), `storage.BackendQuota.Cost`
  (the capped applier's, on the three request types). `pbutil.MustUnmarshalMessage` is
  generalized to a case per message type (`ConfChange` verbatim; `InternalRaftRequest`:
  `{p ↦ x ∗ d ↦* bs ∗ ⌜irrDecode bs = some rq⌝} … {internalRaftRequestIs p rq ∗ d ↦* bs}`),
  stated over raftpb's and etcdserverpb's assumptions; the server's `EtcdServer.apply` takes
  `hMU.1`. Not axioms: `time.Now`/`Since` (Perennial's), `context.Background` (Perennial's),
  the components (contracts). `errors.Is` (`dispatch`'s metrics) is the server's axiom, stated
  under the server's assumptions: unit 2 restates it or uses Perennial's `errors.wp_Is`.
- **The context** (`txnCtx`): the plan's "the proofs change little" assumed only the four entry
  points take the context; it flows to `txn`, `executeTxn`, `put`, `executeRange`,
  `deleteRange`, `traceutil.Get`. mvcc's `TxnRange.lean` gains `doneNil ctx` (`Done()` is `nil`:
  `context.TODO()`'s, `doneNil_todo`, and `WithValue`'s over it), `txnCtx ctx cd := doneNil ctx
  ∨ isContext ctx cd` (`txnCtx_todo`), `neverCd` (`neverDone_neverCd`, for `Txn` at `TODO()`)
  and `txnCtx_rangeCtx`; `rangeCtx true` takes `doneNil` in place of `TODO()`'s value. Every
  txn spec with a context (and `Results.lean`) says `mvcc.txnCtx ctx cd` for `context.isContext
  ctx cd`; `EnsureTrace`'s and `Get`'s axioms take and return a `txnCtx`. Proof changes:
  `executeRange`, `deleteRange` (the range read's `todo` from `txnCtx_rangeCtx`, 3 lines each),
  `applyCompare`, `getPrevKV` (one line). Unit A touches `deleteRange`, `put`, `txn`,
  `executeTxn`, `Put`, `DeleteRange`, `Txn` specs for the hook: their context lines are one-word
  changes.
- **`mvcc.store.Rev`** specified and proved (`store__Rev.lean`): the store's `ReadView`'s
  `Rev`, with the caller's tokens and certificate passed to `store.Read` (`log₀ <+: log`, `v =
  len log - 1`); in mvcc's link list and `Results.lean`.
- **Links**: `gen-link.py --apply` (namespace `apply`), `etc/link-lean-first-apply.txt` (the
  axioms; the txn package's `Put`/`DeleteRange`/`Range`/`Txn`/`ApplySecObserve` and mvcc's
  `store.Rev` as `@`; the package's 72 functions commented out with a first guess of their
  callees), `apply/Link.lean`, `apply/Results.lean` (skeleton), `etc/tcb-collections/apply.txt`.
  **Reuse rule**: a callee whose result a Link this one imports already defines (same full name)
  is imported, not redefined; searched: the `@` callees' Links and `REUSES` (the server's
  imports mvcc's). The server's Link drops `binary.bigEndian.wp_PutUint64`/`wp_Uint64` and
  `zap.wp_Error` and imports mvcc's Link; the trust report groups the server's Link with the
  apply package's (`61 root theorems in [server Link, apply Link, apply Results]`), which import
  mvcc's. `--leasing` did not reproduce on `lean` (txn's `compareInt64` made the bare name
  ambiguous): its list says `leasing_compareInt64` (its Link: one theorem moved).
- **A finding** (`issues/etcd-apply-alarm-gauge-reactivate.md`, reproduced): `Alarm` increments
  the alarm gauge for an alarm already active (`AlarmStore.Activate` returns the existing
  member): the gauge reads 2 for one alarm and 1 after it is disarmed. The plan's suspects:
  (1) `Apply` panics on `ID == 0` with no header: a precondition (pre-3.0 entries), `irrId`;
  (2) `dispatch`'s `Panic` default: every proposal site sets one field (`grep` of
  `InternalRaftRequest{` in `server/`), only a crafted WAL entry reaches it; (3)-(6) as the
  plan says, for units 1-2.
- **Notes on this repository**: `Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseCacheWrite`
  failed once in a full build (an `iframe` not seeing through a literal record's projection)
  and passed on the rebuild: a flaky elaboration, as `InvSTMRun` before.
- **Gates**: full `lake build` passes (2645 jobs); `ETCD_SRC=/shared/etcd etc/goose.py --check
  --perennial /shared/perennial-merge` passes; `gen-link.py` reproduces every Lean-first Link
  (`--cache/--server/--concurrency/--leasing/--recipes/--register/--mvcc/--txn/--apply`);
  `etc/tcb-report.py --check --update`: 81 axioms, 1 sorry (was 69, 1: the 12 above); every
  collection unchanged (server 26, mvcc 13, txn 20, cache 10, concurrency 12/1, recipes 11,
  leasing 8, btree 0, raft 1, register 1); apply 17 axioms, 0 sorries;
  `etc/verified-code.py --reuse --package go.etcd.io/etcd/server/v3/etcdserver/apply`: 73
  functions, 684 lines, 0 verified, 1 assumed (`Apply`, the server's axiom), 71 translated,
  1 not translated (`metrics.go`'s `init`); etcd 474 verified of 3599, 4943 of 45570 lines
  (unchanged: `store.Rev` is a promoted method, not a Go function).

### Unit A: the hook through mvcc (2026-10-12)

Branch `apply-uA` (worktree `/shared/etcd-grove-applyA`, off `lean` at `436f363c4`), in
parallel with unit 0. The backend's post-lock hook is in mvcc's contract and threaded through
the write path, in the shape of the server's `apply.Apply.spec`, so that the applier's contract
can be proved of the real write path (decisions.md, "mvcc: the batch lock runs the hook").

- **mvcc** (`InvStore.lean`): `batchTxSpec … Locked P f`/`isBatchTx … P f`/`isKeyBackend b View W
  P f`: `LockInsideApply : ∀ Pre Q, {Pre ∗ □ {P ∗ Pre} f() {Q}} … {Locked [] ∗ W ∗ Q}`, both
  `Unlock`s take `∗ P`, `LockOutsideApply` returns `Locked [] ∗ P`. `StoreNames.hook`/`hookFn`,
  `hookIs γ P f` (saved proposition and read-only ghost variable; `hookIs_agree`,
  `hookIs_agree_lc`), `isStore` holds `∃ P f, hookIs γ P f ∗ isKeyBackend … P f` (arity
  unchanged), `storeTxnWriteIs` the same `∃ Pw fw`. `csContract P f Pre Q Post`,
  `csContract_noHook`, `txnEndPre`/`txnEndPre_write`. Specs changed: `NewStore` (any `P f` in,
  `hookIs γ P f` out), `store.restore` (`isKeyBackend … P f`), `store.Write` (`hookIs ∗ Pre ∗ □
  {P ∗ Pre} f() {Q}` in, `Q` out), `storeTxnWrite.End` (`hookIs γ P f ∗ P` in),
  `metricsTxnWrite.End` (`txnEndPre γ kind` in), `writeView.Put`/`DeleteRange` (`hookIs ∗
  csContract` in, `Post` out). The read path is unchanged (its callers of `metricsTxnWrite.End`
  give `txnEndPre` of a read, `True`).
- **txn**: `Put` (`Pre` if the lease check fails, else `Post`), `DeleteRange` (`Post`), `Txn`
  (`Pre` on a failed check, `if txnReadonly t then Pre else Post` on success) take `csContract P
  f Pre Q Post ∗ hookIs γ P f`; the rest of their statements is unchanged. `put`/`deleteRange`/
  `txn`/`executeTxn` (inside an open transaction) are unchanged. The sole-writer results
  (`put_soleWriter`, `deleteRange_soleWriter`, `txn_runTxn`, `txn_readonly_no_revision`,
  `txn_check_error_no_write`) are restated at any `P f Pre Q Post`; the old statements are the
  instance `csContract_noHook`.
- **What the server bridge (unit 3) does with it**: `applierFor ua P f` becomes a definition
  whose store is `isStore s γ ∗ hookIs γ P f` (the backend's `P f` the server's `batchLockInv γ
  TM` and hook); the applier's KV calls pass the apply thread's `Pre`, hook triple
  (`hook_set_au`) and update (`writes_done`) to txn as one `csContract`, and get `Post` (a
  write) or `Pre` (no lock) back, exactly `apply.Apply.spec`'s `Post ∨ Pre`.
- Gates: full build clean (2600 jobs, no new `sorry`); `gen-link.py --mvcc/--txn/--server`
  reproduce (no Link change); `tcb-report.py --check`: baseline unchanged (69 axioms, 1 sorry;
  no new axiom), every collection unchanged (mvcc 13/0, txn 20/0, server 26/0, ...); `goose.py`
  untouched. (The base's first full build here once failed in
  `leasing/InvLeaseCacheWrite.lean:485`, an unsolved goal; the rebuild passed it unchanged:
  nondeterministic, not this unit's.)
- **Plan corrections**: `LockOutsideApply` cannot keep `{True} … {Locked []}`: `NewStore`'s first
  `Unlock` (now taking `P`) needs `P`, so it hands `P` out (the lock's invariant from the
  backend's creation). `StoreNames` gets two names (`hook`, `hookFn`), not one. The `P` agreement
  is under a later (saved propositions): `store.Write` and `End` spend a later credit.
  `writeView.Put`/`DeleteRange` open write transactions too and take `csContract`.

### Merge 0/A (2026-10-12)

`apply-u0` then `apply-uA` merged into `lean` (`--no-ff`). `lean` was at `d059a80ad`, not the
units' base `436f363c4`: the `mvcc` branch (the watchable store, units 1a to 2, and `zap.Logger.
Panic`/the key index's total specs) had been merged into it, so the merge also met mvcc's new
work. Perennial `e4e126e46` and the etcd pin `bc8b52a50` unchanged.
- **Conflicts** (all resolved by keeping both sides): `etc/tcb-baseline.txt` (the union: unit
  0's twelve and `lean`'s `trace.SpanFromContext`), `notes/STATUS.md` (one apply section, "Unit
  0" then "Unit A"), `notes/decisions.md` (both entries); txn's specs `DeleteRange`, `Txn` and
  `Results.lean`'s five sole-writer results (unit 0's `mvcc.txnCtx ctx cd` in place of
  `context.isContext ctx cd`, with unit A's `csContract P f Pre Q Post ∗ hookIs γ P f`; `Put`
  merged without conflict, both premises). No statement weakened.
- **`csContract` deduplicated**: unit 0's copy in `apply/Contracts.lean` (the same definition)
  removed; `Contracts.lean` imports mvcc's `InvStore` and uses `mvcc.csContract`;
  `csContract_pre` kept, of `mvcc.csContract`.
- **Fixes from the merge**: `store.Rev` (unit 0) calls `metricsTxnWrite.End`, which unit A gave
  the premise `txnEndPre γ kind`: of a read, `True` (as `readView.FirstRev`); `Rev` is read-only,
  no hook. The server's `Link.lean` regenerated: `lean`'s mvcc `Link` now links `zap.String`/
  `Int64` (the key index's callees), so by unit 0's reuse rule the server's imports them from
  mvcc's instead of redefining them (the build failed on the duplicates). No other proof changed.
- **Gates**: full build clean (2728 jobs); `gen-link.py` `--apply/--mvcc/--txn/--server/
  --leasing` (and `--adt/--cache/--recipes/--concurrency/--register`, `gen-btree-link.py`)
  reproduce; `etc/goose.py --check --perennial /shared/perennial-merge` (`ETCD_SRC=/shared/etcd`)
  passes; `etc/tcb-report.py --check`: 82 axioms, 1 sorry (the textual union: `lean`'s 70 and
  unit 0's 12; no `--update`); every collection matches (apply 17/0, txn 22/0, mvcc 17/0, server
  26/0, cache 10/0, concurrency 12/1, recipes 11/0, leasing 8/0, adt 0, btree 0, raft 1,
  register 1). Verified code: apply 73 functions, 0 verified, 1 assumed (`Apply`), 71
  translated, 684 lines (681 translated); etcd 494 verified of 3599 functions, 5149 of 45570
  lines (unchanged: `store.Rev` is a promoted method).

### Unit 1: the layers (2026-10-12)

Branch `apply-u1` (worktree `/shared/etcd-grove-apply1`, off `lean` at `504afa17e`). Every
function of `backend.go`, `quota.go`, `capped.go`, `corrupt.go` and `auth.go` is specified and
proved but the backend's `Compaction` (out of the model), the constructors package each layer,
`chainStep` is closed over the backend's relation (`Chain.lean`; decisions.md, the apply entry's
unit 1 bullets).
- **A translation fix** (`auth.toml`): `auth.AuthStore` was an axiomatized type (its methods'
  signatures name `context`, `etcdserverpb`, `authpb`, not imported), so its typed points-to was
  `sorry -- axiomatized type`, reached by `ApplierOptions` and the auth applier's `as` field;
  importing the three packages translates it (and `AuthBackend`, `AuthReadTx`, `AuthBatchTx`,
  `TokenProvider`) as interfaces, as `lease.toml` does for `Lessor`. Nothing else generated
  changed; `goose.py` itself untouched.
- **The triples** (`applierTriples E c ai`, `applierSpec E c a := ∃ ai, a = ok ai ∗ applierTriples
  E c ai`, persistent): one per `applierV3` method but `Compaction`, in the environment `E : AEnv`
  (the store `s`, its ghost names `γ`, the batch lock's `P` and hook `f`). Every method takes the
  apply thread's KV resources `kvOwn E log` (the store's reader slots, the sole writer of `log`,
  the state's leases known) and the chain's thread-owned resources `chainRes c a`, and returns
  them. The KV methods (`Put`, `DeleteRange`, `Range`, `Txn`) and `LeaseRevoke` (whose lessor
  deletes through the store) run the request `rq` `dispatch` passes on (`dispatchKind rq`, the
  field `some o`, the per-request premise) and return `∃ oc, ⌜chainStep backendStep c rq log oc⌝
  ∗ <answer> ∗ kvOwn E (oc.logAfter log) ∗ chainRes c a ∗ (Post ∨ Pre)` (`kvPost`; `Range` without
  the contract); the answers (`putOutcomeIs`, `deleteOutcomeIs`, `rangeOutcomeIs`,
  `txnOutcomeIs`, `revokeOutcomeIs`) carry the txn package's response predicates at their exact
  model values for an applied outcome, the error of a rejection (`rejErrIs`: `ErrCorrupt`,
  `ErrNoSpace`, the auth store's, the backend's), the quota's `ErrNoSpace` after a write
  (`noSpaceErrIs`). The other methods (`mPre`/`mPost`) take `csContract P f Pre Q Post` where
  they may write and return `Post ∨ Pre`, the log as it is; one triple per shape, over the
  method name (`respMethods`, `resp0Methods`, `clusterMethods`, the request facts the layers
  read: `reqFacts`). `Apply` is higher-order: `{irrWrapperIs r rq skip ∗ A ∗ {chainRes c a ∗ A}
  af(r, v3) {ar; chainRes c a ∗ B ar}} a.Apply(r, v3, af) {ar; B ar ∨ (⌜needAdminPermission rq⌝ ∗
  A ∗ rejectResultIs ar)}`.
- **`backendStep rq log o`**: by `dispatchKind rq`: a put is `put_soleWriter`'s three cases (the
  lease not found, the ignore flag's key missing: `.rejected .backend`; else `log ++
  [[putChangeOf …]]`); a delete the filter (`commitLog log delChanges`) or the range read's error;
  a range `.applied log false`; a transaction `checkTxn`'s error or `srvRunTxn` committed (none
  for a read-only one); a revocation the lessor's deletions (`commitLog log pend`, all
  deletions); compaction and an empty request `False`; the others the log as it is or the
  component's error.
- **`chainRes`, the auth mutex**: `chainRes (.auth c) a` owns the auth layer's `authInfo`
  (`authInfoOwn p`) beside the inner's; the other layers own nothing. `aa.mu` is a Perennial
  mutex whose resource is `authInfoOwn p` (`authIs`, made by `newAuthApplierV3` with
  `init_Mutex`): `Apply` locks it, owns `authInfo`, hands it to the `applyFunc` through the
  inner's `Apply` (whose `A`/`B` frame it), resets it, unlocks. So `Apply`'s caller owns
  nothing of the chain (its triple has no `chainRes`), and `dispatch` gets `chainRes` from the
  `applyFunc`'s precondition. Rejected: `authInfo` thread-owned with a trivial mutex resource
  (`Apply`'s statement would carry `chainRes`, and unit 2's `uberOwn` with it).
- **The constructors** package the layers: `{backendOptsOk E opts} newApplierV3Backend(opts)
  {a; applierSpec E .backend a}`, `{applierSpec E c app} newQuotaApplierV3(lg, cfg, be, app) {a;
  applierSpec E (.quota c) a}`, `newApplierV3Capped`, `newApplierV3Corrupt` (a pointer `p`,
  `applierSpec E (.corrupt c) (mkOk (*applierV3Corrupt) p)`), `newAuthApplierV3(as, base, lessor)`
  (with `isAuthStore`, `isApplyLessor`). A constructor's proof takes its layer's method specs as
  hypotheses (the link) and proves the promoted methods through the inner's triples
  (`chainRes_<layer>_out`/`_in`, `Packaging.lean`). No thread-owned part is returned: the auth
  layer's resource is in its mutex.
- **Lemmas**: `txn/SoleWriterKV.lean` (`put_soleWriter_of`, `deleteRange_soleWriter_of`,
  `range_soleWriter_of`: the txn results over their callee's spec, moved from txn's
  `Results.lean`, which restates them unchanged); `apply/KVLemmas.lean` (the leases known across
  a put, a delete, a revocation's deletions); `apply/Packaging.lean`; `WrapLemmas.lean` (an `err = nil` answer is an applied outcome: the quota layer), `AuthLemmas.lean` (`checkTxnPermission`'s Löb proof over `checkTxnReqsPermission`'s body, the auth layer's rejection/pass lemmas), `BackendLemmas2.lean` (`go.NotInterface go.uint64`, a missing Perennial instance: `types.ID.String`'s method resolution stalls without it; belongs in Perennial's `PostLifting.lean`).
- **Contracts**: unit 0's contracts used as stated, none changed (the lessor's `Checkpoint` is one critical section per call: the finding below). Not in the contracts: `cappedIs`/`corruptIs` have no `Persistent` instance (the proofs `ipersist`; harmless).
- **`Compaction`**: no triple in `applierSpec`, `backendStep` is `False` of a compaction; the
  corrupt applier's `Compaction` (`ErrCorrupt`) is proved, the backend's is not specified.
  Unit 2's `dispatch` takes `dispatchKind rq ≠ .compaction` and never calls a `Compaction`.
- **A finding** (`issues/etcd-apply-lease-checkpoint-sections.md`, reproduced): a lease checkpoint
  entry with several checkpoints writes the backend in one critical section per checkpoint
  (`lessor.Checkpoint` persists each lease in its own `LockInsideApply`), so a backend commit
  between two persists the entry's consistent index with part of its writes; the backend's
  `LeaseCheckpoint` triple takes a request with at most one checkpoint (the premise, in its
  request facts and `rqOk`; not a weaker contract). A fix exists on the fork branch
  `lease-checkpoint-one-section` (2a163496c: `Lessor.Checkpoint` takes the whole batch and
  persists it in one critical section); the issue file is the upstream draft.
- **The plan's suspects**: (3) `quotaApplierV3.Put`/`Txn`/`LeaseGrant` apply, then answer
  `ErrNoSpace` if the quota said no: by design, the apply loop raises the `NOSPACE` alarm on that
  error (`server.go:1976`); the client gets an error for a committed write; the spec says so
  (`chainStep`'s quota case, `.applied log' true`); not a bug. (5) `authApplierV3.UserGet`/
  `RoleGet` reset `authInfo` and return an empty response with the error, so `dispatch`'s result
  has both `Resp` (not nil) and `Err`, unlike the other rejections (`Resp` nil): harmless
  (`raftRequest` reads `Err` first; `Apply` resets `authInfo` again); the triples say nothing of
  the response. (6) the corrupt applier blocks the KV requests, compactions and lease grants and
  revocations only; alarms (so that the alarm can be disarmed), auth, cluster requests and lease
  checkpoints go through: by design (`corruptRejects`).
- **Results** (`apply/Results.lean`, unit 1's section): `chain_put`, `chain_deleteRange`,
  `chain_range`, `chain_txn` at `alarmChain ns cr` (`baseChain` at `false false`), the outcome in
  the txn package's terms (`putModel`, `deleteModel`, `txnModel`, `quotaAfter`; `alarmPut`, ...),
  with `#print axioms`.
- **Gates**: full `lake build` clean (2860 jobs, no `sorry`); `gen-link.py --apply` reproduces `Link.lean`
  (81 results; `gen-link.py` learned that an `@` callee's result taking the cache's assumptions is
  named in its own Link without the namespace prefix: txn's `wp_Txn`), `--txn/--mvcc/--server/
  --leasing/--cache/--recipes/--concurrency/--register/--adt` unchanged; `etc/goose.py --check
  --perennial /shared/perennial-merge` (`ETCD_SRC=/shared/etcd`) passes with the `auth.toml`
  change; `tcb-report.py --check`: 82 axioms, 1 sorry (unchanged: no new axiom); every collection
  matches but apply's, updated: 35 axioms, 0 sorries (was 17: its results now reach the txn
  package's and mvcc's trust base through `txn.Put`/...`/store.Rev`, and `context.TODO`'s proof
  is linked); `verified-code.py --reuse --package go.etcd.io/etcd/server/v3/etcdserver/apply`: 73
  functions, 63 verified (all sorry-free), 1 assumed (`Apply`, the server's axiom), 8 translated
  (the backend's `Compaction`, `uber_applier.go`'s 6, `noSideEffect`), 486 of 684 lines verified;
  backend.go 31 of 32, auth.go 16/16, quota.go 4/4, capped.go 4/4, corrupt.go 8/8; etcd 557
  verified of 3599 functions, 5635 of 45570 lines (was 494, 5149)..
## Adequacy of the register's driver: the closed theorem and its trust base (2026-10-12)

`register_adequate` (`Proof/github_com/mit_pdos/etcd_grove/examples/register/Adequacy.lean`,
restated as `register_cluster_safe` in `Results.lean`) is a theorem about the operational
semantics, with no Iris in its statement. Take `registerProgram`, which is
`initialize'(); Main()` for the register package. Start it from any state with no package
initialized (`IsInit σ`) and one live thread (`g.threads = 1`). Then for every real
execution of any length `n` (`RealNsteps n`): if the main thread has finished, its value is
`#()`; every thread is a value or can step; no thread has ended in a panic. Client B's check
of its `Get` is one such panic, so it never fires.

- **Proof.** Perennial's `goose_adequacy_nopanic` is used at the disk FFI, whose
  initial-state conditions are trivial. The register's proofs are generic over the FFI.
  - Bounds: `N = n + 1`. `T = n + 2` comes from `threads_le_steps`: one step forks at most
    one thread. The WP uses neither receipts nor thread tokens, so neither bound costs
    anything.
  - Ghost state: a concrete bundle `registerGF` (`AllG` at slot 0, then invariants, credits,
    heap, prophecies, package state, the disk heap) with its `GooseGpreS` instance.
  - From `ownGoState ∅` to `ownInitializing getIsPkgInit`: `getIsPkgInit` is a lookup table
    over the 29 packages the register reaches, transitively. Its `GetIsPkgInitWf` is proved
    by `repeat' (first | exact True.intro | apply And.intro | rfl)`.
  - Then `register.wp_initialize'` (`Init.lean`), then `register.wp_Main`.
- **Initialization, proved.**
  - raft (`Proof/go_etcd_io/raft/v3/Init.lean`): the initializer establishes
    `isInitialized`, which until now was only assumed (`Base.lean`). That covers the error
    variables (`errors.New`; `IsNewError` from Perennial's new `errors.wp_New_ptr`),
    `globalRand`'s mutex (`init_Mutex`), `emptyState` and the two message tables. Nothing in
    `isInitialized` was false.
  - `quorum`, `tracker`, `confchange` and the register.
  - Perennial's `context` (`Perennial/Proof/context_proof/context_init.lean`, new).
  - Changed instances:
    - Perennial's `io`: `isPkgInit` now gives `Discard ↦□ _`, because raft's initializer
      loads it.
    - etcd-grove's `os`: `isPkgInit` gives `Stderr ↦□ _`, for the same reason.
- **Perennial**: branch `register-adequacy` (`15ef44029`, one commit on `lean`'s
  `e4e126e46`, not pushed; the pin here is that commit): `Proof/io.lean` (the `isPkgInit`
  above), `Proof/context_proof/context_init.lean` (new, with `wp_New_errorString`, `errors.New`
  at its concrete type, which `isTypedErr` needs), and `Proof/math/big.lean`,
  `Proof/crypto/rand.lean` (`wp_initialize'`, `sorry`, marked unprovable). raft's
  `IsNewError` now comes from upstream's `errors.wp_New_ptr` (`IsPointerError`,
  `isNewError_of_ptr`). Merged with `lean` (one `AllG`: `registerGF_allG` is
  `GooseGpreS.goosePreGAllG`, no `[AllG GF]` next to `HeapGS`); full build 2514 jobs, axiom
  account unchanged. **Push order**: Perennial `register-adequacy` first, then etcd-grove.
- **The theorem's hypotheses.** Perennial's Go semantics is a parameter, as in every result:
  - `GoGlobalContext`, `GoLocalContext`, `go.Semantics`;
  - `register.Assumptions`, which includes every imported package's `Assumptions`: each Go
    name stands for its Goose-translated body or for Perennial's trusted model (in
    `TrustedCode`: `sync.Mutex`, `sync/atomic`, the runtime semaphores, `fmt.Sprintf`/`Printf`
    (no formatting), `strings.Join`, `crypto/rand.Int`, `time.Sleep`, ...), plus the struct
    layouts;
  - two new classes of the same kind:
    - `log.NewModel`: the name `log.New` stands for a model returning a fresh pointer.
      Perennial translates `log` without `New`.
    - `context.ErrorStringIsError`: `*errors.errorString` is in `error`'s type set, a
      method-set fact. `methodSet` is uninterpreted, so `context`'s `isInit`, which asks for
      `isTypedErr Canceled`, cannot be established otherwise.

  No instance of `go.Semantics` has been constructed anywhere. The theorem is non-vacuous
  only if these classes are jointly satisfiable, which is believed but not proved.
- **`#print axioms register_cluster_safe`** lists 302 axioms. A Lean classifier
  (`isProp` of each axiom's type) splits them as follows:
  - **Lean's**: `propext`, `Quot.sound`, `Classical.choice`.
  - **297 data axioms, no logical content.** These are Goose's declarations of what it does
    not translate, all in `Code/`: opaque types (`reflect.Value`, `os.file`,
    `sync.Map`, ...), their `underlying` and `zero_val`, constants, and 135 package-variable
    initializers (`X.init : val`). They are 5 in `raftpb`, 53 in `math`, 25 in `os`, 17 each
    in `time` and `math/big`, 7 each in `strconv` and `reflect`, 2 in `log`, 1 each in
    `errors` and `crypto/rand`. Every type is inhabited, so they are consistent: read each
    type as `Unit`.
  - **One propositional axiom**: raft's `reflect.DeepEqual.wp_proof`, Go reflection on two
    `ConfState`s (`ConfState.Equivalent`, reached from `RestartNode`).
  - **`sorryAx`**, from 9 `sorry` declarations, all package initializers that cannot be
    proved because they run opaque initializers:
    - Perennial: `errors.wp_errorType_init` (the `reflectlite` initializer of
      `errorType`), `time.wp_initialize'`, `math.wp_initialize'`, `log.wp_initialize'`,
      `math.big.wp_initialize'`, `crypto.rand.wp_initialize'`;
    - etcd-grove (`Proof/go_etcd_io/raft/v3/Init.lean`): `os.wp_initialize'`,
      `strconv.wp_initialize'`, `raftpb.wp_initialize'` (gogoproto's registration and the
      `fmt.Errorf` error variables that `raftpb.toml` does not translate).

    `reflect.wp_initialize'` is also a `sorry` but is not reached, because `raftpb`'s
    initializer is the only caller.
- **A soundness caveat about trust-boundary axioms.** Axioms like
  `reflect.DeepEqual.wp_proof` quantify over every semantics instance. The `Assumptions`
  classes do not constrain `functions reflect.DeepEqual`, so the axiom asserts the spec for
  every function table, including ones where `DeepEqual` returns a wrong answer. Together
  with adequacy, a constructed model of `go.Semantics` with such a table would refute it.
  The axiom is consistent only as long as no such model is built. The sound form is a
  hypothesis class naming a trusted model, as `log.NewModel` does, with the spec proved from
  it. The same applies to every `*.wp_proof` axiom in `etc/tcb-baseline.txt` and to
  Perennial's spec axioms for names without `FuncUnfold` (`time.wp_Now`, `errors.wp_As`).
- **Is raft's proof complete (outside reconfiguration and read-only requests)?** Judged by
  this list, nearly, but not totally. Nothing about raft's algorithm or its Go code is
  assumed: every raft function `Main` reaches is verified, and raft's package state is now
  proved from its initializer. Two raft-repository items remain:
  - `reflect.DeepEqual.wp_proof` (Go reflection, a standard-library function, with the
    caveat above);
  - `raftpb.wp_initialize'` (generated protobuf registration, outside raft's logic).

  Everything else is the standard library (8 initializers whose variable initializers are
  opaque, `log.New`'s model, the method-set fact, Perennial's trusted models) or Perennial's
  framework: GooseLang's semantics and the Goose translator; `go.Semantics`, not shown
  satisfiable; `AngelicExit`, under which global variables land at `globalAddr` and the
  overflow `assume`s hold; a 64-bit platform. The statement is safety only: no stuck
  thread, no panic, B reads A's write. It says nothing about liveness.
- **Build.** A full `lake build` passes (2202 jobs). One unrelated proof had to be
  repaired: `lcOwn_emap_revokes_acc` (`leasing/InvLeaseCacheWrite.lean`) needed a
  `dsimp only` before its `iframe` (a projection of a literal record).
- **TCB collection.** See the dated line in `etc/tcb-collections/register.txt`.

## Merge: lean into mvcc (2026-10-12)

`origin/lean` (`436f363c4`: the server's `txn` package, units 0–4, and its changes to mvcc's
files: the read-only write transaction `NewReadOnlyTxnWrite`/`txnReadWrite.*` (`InvRoTxn.lean`),
`metricsTxnWrite.Rev`/`FirstRev`/`Range` of either transaction kind and `Changes`, `idxLogAuth`,
reads pinned by the caller's tokens, `NewStore` returning the initial log's certificate)
merged into `mvcc` (base `e3effe933`). The Perennial and etcd pins did not move.
- **Conflicts**, all resolved by keeping both sides: `etc/gen-link.py` (our `--adt` mode and
  theirs `--txn`, with its `NAMESPACED` entry), `etc/goose.py` (`pkg/v3/adt` and
  `etcdserver/txn` both translated with bodies), `etc/link-lean-first-mvcc.txt` (our adt,
  watcher-group, batch and stream lines and their read-only transaction lines; the lines both
  changed merged without conflict: our key index's `zap_*` callees, their
  `metricsTxnWrite__*` callees), `etc/tcb-baseline.txt` (the union: `trace.SpanFromContext`
  and their `traceutil`/`sort`/`txn` axioms), `notes/STATUS.md` (both sides' sections).
  `zap.Logger.Panic` (added by both): ours kept (`⌜r = PanicV #msg⌝`); no `txn` proof
  destructures its postcondition (`sortRangeResults`' panic branch is unreachable), so nothing
  needed adapting. `newTreeIndex` (spec and proof): our `⌜lg ≠ null⌝` premise and `%Hlgnn` in
  `isTreeIndex` with their `idxLogAuth γ ½ []` in the postcondition; `NewStore`: the
  call to `newTreeIndex` discharges our premise and destructures their `idxLogAuth` (`Hil`).
- **Link.lean** regenerated for mvcc (their eleven functions added); `--txn` and `--adt`
  regenerate unchanged.
- **The build** (2683 jobs) needed no further change: no semantic conflict between our
  `isTreeIndex`, total key-index specs and watch files and their `InvStore`/`InvIndex` changes.
- **Checked**: `etc/goose.py --check` passes at the unchanged pins with no regeneration;
  `etc/tcb-report.py --check` matches the textual union (70 axioms, 1 sorry; ours 58, theirs
  69); every collection matches but `txn`, which now reaches our `zap.Int64`/`zap.String`
  (through the key index's total specs under `treeIndex.Put`/`Tombstone`): updated, 20 to 22
  axioms. Verified code: etcd 494 of 3599 functions (5149 of 45570 lines); mvcc 78 of 155 (7
  conditional on the tree's contract), 829 of 2073 lines; adt 4 of 42; txn 39 of 48, 570 of
  653 lines.

## The watchable store (2026-10-11, branch `mvcc`)

The next target after the KV core: etcd's watchers (`watchable_store.go`, the sync loops and
`notify`; `watchable_store_txn.go`, the write transaction's `End` notifies; `watcher.go`, the
client's stream; `watcher_group.go`, the synced and unsynced groups: key watchers in a map,
range watchers in the interval tree of `pkg/v3/adt`, a red-black tree with a `max`
augmentation). The result to reach: the watch guarantee — a watcher on `[key, end)` from
`startRev` receives every change of a key in its range at a revision at or above `startRev`,
once, in revision order, until cancelled, the events being the store's log of changes
(`Log`); compaction and `Restore` out of scope, as for the store. The plan (decisions.md,
"The watchable store: the plan, the interval tree's contract"): contract first, the tree's
proof last — unit 1a the translation (done), 1b the interval tree's contract (its model
specs, pending: `?` in the link list, hypotheses of what reaches them, as the recipes did),
unit 2 `watcher_group.go` and `watcher.go` over the contract, unit 3 the store's concurrency
and the guarantee, unit 4 the tree's proof (red-black insert/delete fixups), discharging the
hypotheses.
- **Unit 1a, the translation** (2026-10-11): `pkg/v3/adt` with bodies
  (`Code/go_etcd_io/etcd/pkg/v3/adt.toml`: everything but `MaxHeight` (floating point),
  the two `String`s (`fmt`) and `visitLevel` (debugging); 38 of its 42 functions, 495 of 548
  lines) and the four watchable-store files in the mvcc toml (all 46 of their functions;
  the promoted wrappers of `watchableStore` over `*store` and of `watchableStoreTxnWrite`
  over `TxnWrite`, which `End` needs for `Changes`/`Rev`); `go.opentelemetry.io/otel/trace`
  names-only (new; `watcher.go`'s `trace.SpanFromContext`), `client/v3` and `verify` already
  were; `Base.lean` gets the package-init instances of `adt` and `otel/trace`. Goose took
  the type assertions `.(watcherSet)`, the maps keyed by `*watcher`, five `select`s (two with
  `default`, one on a nil-able `time.After` channel, one on a ticker), `time.NewTicker`/
  `Ticker.Reset`/`time.Since`, the builtin `max`, `float64(n)` for the gauges, `verify.Verify`
  with a closure, the variadic `fcs ...FilterFunc`, and `Stab`'s closure over its named
  result (heap-allocated). `etc/goose.py --check` passes; the build, the baselines (57 axioms,
  1 sorry; mvcc 16, 0) and the verified-code figures are unchanged, with the package now
  1348 of 2073 lines translated (65%). A remark for unit 2: `watcherSetByKey`'s second
  `switch` case (`len(wranges) == 0 && len(wkeys) == 0`) is unreachable after the first
  (harmless dead code).
- **Unit 1b, the interval tree's contract** (2026-10-11): `Proof/go_etcd_io/etcd/pkg/v3/adt/`
  (`Base`: the package's init instance, moved out of mvcc's; `Model`: `IvlS`, `affCmp`
  (`StringAffineComparable.Compare`), `ivlCmp` (`Interval.Compare`: left, right, or overlap),
  `ivlLt` (the tree's order: begin, then end), `ivtInsert`, `stab`, the orders' lemmas and
  `ivtInsert_sorted`/`mem_ivtInsert`; `Defs`: `affIvl b e` (the Go `Interval` of two
  `StringAffineComparable` interface values) and the `opaque ownIvt t L`, its body naming the
  heap, semantics and package instances so that unit 4's definition changes no statement).
  **Pending** (`?` in `etc/link-lean-first-adt.txt`; hypotheses of what reaches them):
  `NewIntervalTree` (`ownIvt t []`), `intervalTree.Insert` (a new interval: `ivtInsert`),
  `Delete` (`eraseP`, returns membership), `Find` (the entry's pair, a read-only pointer for
  good, or `nil`), `Intersects` (`stab ≠ []`), `Stab` (the overlapping entries' pairs as a
  slice of pointers, read-only for good, in the tree's order), `Len`. **Proved**:
  `StringAffineComparable.Compare` (`affCmp`), `NewStringAffineInterval`,
  `NewStringAffinePoint` (`s ++ "\x00"`), `Interval.Compare` (`ivlCmp`; the type assertion
  and the dynamic `Compare` calls step under `wp_auto`, the interface call reducing to the
  value-receiver method; the struct is split into its fields for the loads, `ivl_split`/
  `ivl_combine`). `Link.lean` by `etc/gen-link.py --adt`, `Results.lean`, collection
  `etc/tcb-collections/adt.txt` (0 axioms); the baselines unchanged; verified-code: adt 4 of
  42 functions. Unit 2's design is in decisions.md, "The watcher group and the stream".
- **Unit 2, first half** (2026-10-12; design: decisions.md, "The watcher group and the stream
  (unit 2)"). **The group's sets and structure** (`InvWatchGroup.lean`): `WatchRange` (a key, or
  `[key, end)` affine) with `covers`, `watcherFixed w r fcs` (the never-written fields,
  persistent), `WatcherSt`/`watcherOwn` (the mutable fields, for the store), `ownWatcherSet`
  (a `map[*watcher]struct{}` as a `GMap Loc Unit`; `ownWatcherSetOpt` for a possibly nil map,
  which Perennial gives no ownership: lookups, `len` and `range` on it are pure),
  `ownKeyMap`, `ownWatcherGroup wg W` (the all-watchers set, the key map, the tree through
  `ownIvt` with `RangesOk`: sorted by `ivlLt`, one interval per distinct range), the lemmas
  `ownWatcherGroup_fixed`/`_member`/`_not_null`/`_intro`, `ivlCmp_point_iff` (the stab of the
  point `[k, k\x00)` is the overlap `b ≤ k < e`: `strLt_succ_le`). Proved: `watcherSet.add`/
  `delete`/`union` (disjoint, the argument possibly nil), `watcherSetByKey.add`/`delete`,
  `newWatcherGroup` (a value; a wand from the location), `watcherGroup.add` (a non-member),
  `contains` (a decidable existence over `W`), `size` (with the bound), `delete` (returns
  membership; two `watcherFixed` of a pointer agree, `watcherFixed_agree`),
  `watcherSetByKey` (the covering members, lent by a wand, by alias when the code can; its
  unreachable second `switch` case falls through). The five that reach the tree's pending
  contract are linked with its specs as hypotheses (`?` lines in the mvcc link list;
  `adt_NewStringAffine*: @`). Map notes: `make`/`delete` on a named map type need
  `go.make1_underlying`/`go.delete_underlying` first; a pointer-receiver call on a named map
  needs `wp_method_call; wp_call` then a load; `Convert watcherSet.ty go.any` is
  `interface.mkOk watcherSet.ty #m` and the assertion back steps under `wp_auto`.
  **The stream** (`InvWatchStream.lean`): the `watchable` contract `isWatchable wa P` over the
  store's choice `P : WatchParams` (`IW w` a watcher of the store, `WC w` cancelled, `C ch`
  what it needs of the channel, `F f` of a filter, all persistent; `CR ch L` the right to
  close `ch` with the watchers `L` registered on it, owned): `watch` registers (returning
  `IW`, the cancel closure's spec `cancelSpec` yielding `WC`, `CR` grown), `progress`/
  `progressAll` take `IW` only, `rev`; `isWatchStream ws wa P γ` (the fields, `C ch`, the
  store's close triple for `ch` once every registered watcher is cancelled, the `sync.Mutex`
  guarding `watchStreamInv`: the id maps with their watchers' `IW` and closures' specs, `CR`
  or, once closed, the token `watchStreamOpen γ`). Proved: `Watch` (the empty-range and
  closed cases both `ErrEmptyWatcherRange`, duplicate id, else `nil` with the id), `Chan`,
  `Cancel` (`nil` or `ErrWatcherNotExist`), `Close` (consumes `watchStreamOpen γ`: the
  double close excluded), `Rev`, `RequestProgress`, `RequestProgressAll`. `clientv3.AutoWatchID`
  /`InvalidWatchID` translated as values (`client/v3.toml`); `trace.SpanFromContext` an
  axiom (`trace.isSpan`: `End` returns), with `otel/trace/embedded`, `otel/codes`,
  `otel/attribute` types-only so that `trace.Span` is an interface, not an axiomatized type
  (`Watch` stores the span); the package facts `ErrWatcherNotExist`/`ErrEmptyWatcherRange`/
  `ErrWatcherDuplicateID`/`watchStreamGauge`. A translator remark: Goose emits the deferred
  variadic `span.End()` with no arguments as a call on `()` (elsewhere a deferred call passes
  its argument): to check in Perennial. Proof notes: `wp_apply` of a closure's spec inside the
  stored closure's proof failed with "unknown free variable" (again: `wp_bind` + `iapply`); a
  local named `end` needs `irename`. Baselines: 58 axioms, 1 sorry; mvcc 17. Verified-code:
  mvcc 71 of 155 functions (5 conditional), `watcher.go` all 7, `watcher_group.go` 6 + 5
  conditional of 16; 771 of 2073 lines.
- **Unit 2, second half** (2026-10-12): `InvWatchBatch.lean`: `EvM` (an `mvccpb.Event`: put or
  delete, the key-value, the previous one), `kvPtrFixed`/`evIs` (persistent: events are shared),
  `EventBatch`/`ebAdd` (`eventBatch.add` exactly, over `getLast?`; the cap
  `watchBatchMaxRevsV = 1000`, a package fact `globalAddr watchBatchMaxRevs ↦□`), `batchOf W ST
  evs` (per member, the fold of the covering events at or above its `minRev`; `batchOf_snoc`:
  any nodup listing of the covering members gives the same step, so the map's iteration order
  does not matter), `minRevOf`, `takeMembers` (`choose`'s prefix of the iteration),
  `ownEventBatch`, `ownWatcherBatch` (a map of pointer-and-model pairs), `ownStates ST`, the
  borrow `ownWatcherGroup_watchers` (the all-watchers set out of the group and back, for the
  loops over `wg.watchers`). Proved: `eventBatch.add`, `watcherBatch.add` (a fresh batch when
  absent), `newWatcherBatch` (`nil` for an empty group, else `batchOf`), `chooseAll` (the
  minimum `minRev`; premises: every member's state given, none below `compactRev`, none above
  `curRev`, none restoring — the store's invariant, unit 3 — excluding the compaction response
  and the panic), `choose` (the group itself below `maxWatchers`, else a fresh group of a
  nondeterministic subset of `max 0 maxWatchers` members). Notes: `BigSepM.bigSepM_lookup_acc`/
  `_insert_acc` for the states; a struct allocated by `wp_auto` is persisted by `ipersist`
  after `typedPointsto_not_null`; `&eventBatch{}` arrives as `zero_val`, rewritten to the
  literal by `rfl`; `math.MaxInt64` reduces under `wp_auto`; a map `range` with `break` under
  `wp_wand_r`. Baselines unchanged (58 axioms, 1 sorry; mvcc 17); verified-code: mvcc 74 of 155
  functions (7 conditional on the tree's contract), 823 of 2073 lines; `watcher_group.go` 9 + 7
  conditional of 16, `watcher.go` all 7. Unit 2 is complete; unit 3 follows.


## The server's txn package (`server/v3/etcdserver/txn`)

Plan: `decisions.md`, "The server's txn: the two models meet, the sole writer as tokens" (units 0
to 4; unit 0b, the index answering the state, in parallel with unit 0, in the main tree).

### Unit 0: translation and scaffolding (2026-10-11)

Branch `txn-u0` (worktree `/shared/etcd-grove-txn0`, off `lean` at `e3effe933`).
- **Translation**: `Code/go_etcd_io/etcd/server/v3/etcdserver/txn.toml`, bodies for every
  function of `txn.go`, `put.go`, `range.go` (with `kvSort`, the five `kvSortBy*` and their
  promoted `Swap`/`Len`) and `delete.go`; `util.go` (`WarnOf*`, `isNil`: reflect) and
  `metrics.go` (`ApplySecObserve`, `RangeSecObserve`, the metrics, `init`: prometheus, a float
  division) names only; listed in `etc/goose.py`. `etcdserverpb.toml` adds the requests
  (`TxnRequest`, `RequestOp` and its four oneof wrappers, `RangeRequest`, `PutRequest`,
  `DeleteRangeRequest`; until now axiomatized types), the eight sort constants and
  `RequestOp.GetRequestRange` with its body. Every other package the code names was already
  translated (`sort`, `bytes`, `math`, `fmt`, `time`, `context` Perennial's; `proto`, `zap`,
  `traceutil`, `lease`, `etcdserver/errors`, `mvcc` names-only or the mvcc core). Goose (Perennial
  `e4e126e46`) accepts the package as pinned (`bc8b52a50`): no Gooseable change. The
  translation, for the proof writers: package `go_etcd_io.etcd.server.v3.etcdserver.txn`, its
  `Assumptions` include mvcc's, `sort`'s, `context`'s, ...; `trace.StepWithFunction(func() {...},
  msg)` passes a `FuncLit`; `lg.Panic` is `MethodResolve (*zap.Logger) "Panic"`; `sort.Sort`
  is `sort.«Sort»`; `mkGteRange`'s `[]byte{}` is a slice composite literal.
- **Base** (`Proof/.../etcdserver/txn/Base.lean`): `txnInit` states the two foreign error
  variables the code returns, `lease.ErrLeaseNotFound` and `etcdserver/errors.ErrKeyNotFound`
  (their packages' facts are mvcc's `True` and the server's `ErrNoSpace`, left unchanged); no
  fact of the package's own (its metrics are read only by names-only code).
- **Requests** (`Requests.lean`, persistent predicates): `rangeRequestIs r o`,
  `putRequestIs p o`, `deleteRangeRequestIs d o` denote the client model's `OpFull`
  (`rangeOpOf`, `putOpOf`, `deleteOpOf`, with `proj_simps`; decision: reuse `OpFull`, not a record
  of the fields); `rangeEndOf` reads a range end as mvcc does (`nil`: the key; empty non-nil:
  from the key on, `[0]`); `putTxnOp` is the server's total put; `compareIs c cm` (`CmpModel`,
  the client's `compareAt` with the server's range end), `comparesIs`; `requestOpIs`/
  `requestOpsIs` (mutual, structural through nested transactions) and `txnFieldsIs`,
  `txnRequestIs rt t`; responses `kvIs`/`kvsIs` (the cache's `kvValAt` without the cache's
  assumptions), `rangeResponseIs resp rev kvs more count`, `putResponseIs resp rev prev`,
  `deleteRangeResponseIs resp rev n prevs`, `responseOpIs`/`responseOpsIs` (mirroring
  `TxnOpResult`, nested responses with header revision `0`), `txnRespFieldsIs`,
  `txnResponseIs resp rev t ok rs`. The put request's size cache is in an invariant (`proto.Size`
  stores it atomically). **`Defs.lean`**: `isKV kv s γ`, `isTxnLessor le γl` (mvcc's `isLessor`
  plus `Lookup`: `nil` or `leaseKnown`). No `soleWriter` (unit 0b's).
- **Axioms** (trust boundary, each `Spec/<pkg>/<fn>.lean` + `Proof/<pkg>/<fn>.lean`):
  `sort.Sort` (over `sorterSpec x R lt`, the `Len`/`Less`/`Swap` triples on a model list: a
  permutation sorted by a strict weak order `lt`, at most `2^62` elements; Perennial translates
  `sort` without it) and `sort.Reverse` (`Less` flipped); traceutil (names-only)
  `EnsureTrace` (a context with the input's deadline and `Done`, `{ cd with Values := vs }`, and
  a non-nil trace; decision: the derived context's descriptor, since `EnsureTrace` returns
  `context.WithValue(ctx, ...)` when `ctx` has no trace, and Perennial has no `WithValue`),
  `Get` (a non-nil trace), `Trace.StepWithFunction` (`WP f() {{Q}}` in, `Q` out: it runs the
  closure, a panic propagating), `Trace.AddField`, `StartSubTrace`, `StopSubTrace` (return; all
  on a non-nil trace); `proto.Size` of a `*pb.PutRequest` (an `int ≥ 0`); `zap.Logger.Panic`
  (a panic outcome `PanicV p`: zap writes then panics); `zap.Int32`; `txn.RangeSecObserve`,
  `txn.ApplySecObserve` (metrics: return). Existing ones reused: `traceutil.TODO`,
  `Trace.Step`, `zap.Error`, `zap.Logger.Error`, `context.TODO`; Perennial's `fmt.wp_Errorf`,
  `bytes.wp_Compare`, `time.wp_Now`/`wp_Since`. `zap.Duration` is not needed (only `util.go`).
- **mvcc's read-only write transaction** (additive, `InvRoTxn.lean`: `isRoTxnWrite trw s γ log
  rev`): `NewReadOnlyTxnWrite`, `txnReadWrite.FirstRev`/`Rev` (through the promoted methods down
  to `storeTxnCommon`'s), `Range`/`End` (to `metricsTxnWrite`'s), `Changes` (`nil`), `Put`/
  `DeleteRange` (a panic outcome): specified and proved, sorry-free, in
  `etc/link-lean-first-mvcc.txt`, mvcc's `Link.lean` regenerated (additions only).
- **Linking**: `etc/gen-link.py --txn` (namespace `txn`, the txn package's assumptions),
  `etc/link-lean-first-txn.txt` (the 18 trust-boundary functions; mvcc's wrappers as `@`; the
  package's 38 functions and `RequestOp.GetRequestRange` commented out with a first guess of
  their callees),
  `Proof/.../txn/Link.lean`, `Results.lean` (prints the mvcc wrappers' axioms),
  `etc/tcb-collections/txn.txt`. `etc/proof_roots.py` picks them up by directory.
- **A finding** (`issues/etcd-txn-empty-requestop.md`, reproduced): `Txn` panics on a
  `RequestOp` whose oneof is empty (`executeTxn` reads the `nil` response `newTxnResp` left for
  it), inside the write transaction (the batch lock stays held); the gRPC layer rejects such
  requests, so it is an unstated precondition. The request predicates give it no denotation.
- **For the next units**: (1) `mkGteRange("\x00")` returns `[]byte{}`, which Go makes
  non-nil, and mvcc's spec (`decide (endk = slice.nil)`, `rangeAnswers`' `endNil`, `inRange`'s
  `e = []` as no bound) reads a non-nil empty end as no upper bound, as the index does
  (`end == nil`, then `len(end) > 0`): consistent. But Perennial's `wp_slice_literal` quantifies
  over the literal's pointer, so a proof cannot tell `[]byte{}` from `slice.nil` through it; the
  allocation's typed points-to gives `ptr ≠ null` (`typedPointsto_not_null`), so units 1 and 2
  need a literal lemma that keeps it. (2) A range inside a transaction with `Revision ≠ 0` reads
  another revision, which the model's `TxnOp.get` does not (it reads the transaction's state):
  `txn_runTxn` needs a premise on nested ranges' revisions. (3) A range answered header-only
  (`skipRangeExecution`) is not described by `responseOpIs`. (4) Comparisons and sort targets
  outside the protobuf enumerations denote nothing (`compareIs`, the client's codes).
- **Notes on existing specs** (this repository's, not etcd's): `traceutil.Trace.Step`'s axiom
  (mvcc's, `Spec/go_etcd_io/etcd/pkg/v3/traceutil/Trace__Step.lean`) says `Step` returns on any
  trace, `nil` included, where Go dereferences it (`t.stepDisabled`): unfaithful for `nil`,
  harmless while every trace passed is non-nil (the txn package's come from `EnsureTrace`/`Get`);
  the new trace axioms require a non-nil trace. `InvSTMRun.lean` (concurrency) failed once in a
  full build under load (an `iframe` not framing `STMSt.empty.reads` against `∅`) and passed on
  the rebuild and with `lake env lean`: a flaky elaboration, not a change of this unit.
- **Gates**: full `lake build` passes (2503 jobs; the etcdserverpb change rebuilds the cache, concurrency,
  leasing and recipes proofs unchanged); `ETCD_SRC=/shared/etcd etc/goose.py --check` passes at
  the pins; `etc/tcb-report.py --check --update`: 13 new axioms (the list above), baseline 69
  axioms and 1 sorry (was 56 and 1); `--collection etc/tcb-collections/txn.txt`: 17 axioms (the
  13 and `traceutil.TODO`, `Trace.Step`, `zap.Error`, `zap.Logger.Error`), 0 sorries; every other
  collection unchanged (mvcc 13 axioms: the wrappers rest on mvcc's existing ones);
  `etc/verified-code.py --reuse`: the txn package 48 functions, 653 lines, 39 translated with
  bodies (570 lines: `txn.go` 12/296, `range.go` 18/164, `put.go` 6/77, `delete.go` 3/33), 2
  assumed (`metrics.go`), 0 verified; mvcc 62 of 155 functions verified (was 58: the four
  read-only wrapper functions; the promoted `FirstRev`/`Rev`/`Range`/`End` are not Go
  functions), 661 lines; etcd 435 verified of 3599, 4373 of 45570 lines (was 431, 4367).
- **The trust report's grouping**: `etc/tcb-report.py` runs Lean once per set of part roots the
  roots reach; the server's `Link.lean` reaches `EtcdDeps` and clashes with mvcc's
  (`binary.bigEndian.wp_PutUint64` is in both). txn's `Base` first imported the server's
  `BaseApply.lean` for `etcdserver/errors`' instance, which put txn's roots (whose `Link`
  imports mvcc's) with the server's: the instance moved, unchanged, to
  `etcdserver/errors/Base.lean` (imported by `BaseApply`). When the apply package links txn's
  results, mvcc's and the server's Links will have to coexist (rename one side's `binary` results
  or put mvcc's in a namespace).

### Unit 0b: the index answers the state; the sole writer (2026-10-11)

Branch `txn-u0b` (from `e3effe933`), two new files in
`Proof/go_etcd_io/etcd/server/v3/etcdserver/txn/`, sorry-free; built with
`--packages=.lake/manifest-merge.json` (Perennial `e4e126e46`).

- **`Lemmas.lean`** (pure; standard axioms only). Hypotheses: `LogOk log` (`LogWf`, length and
  every revision's change count below `2^63`; `LogOk.of_cert` from `idxCert`'s pure part for a
  non-empty log), a revision `r < 2^63` (any: past the log's end the state is `stateAfter`).
  The server's range is `srvInRange endNil k e key` (`endNil`: `key = k`; else mvcc's
  `inRange`: `k ≤ key` and `key < e` unless `e = []`, no upper bound), `srvSel s endNil k e` the
  state's key-values in it. Results: `rangeAnswers_stateAt` (`List.Forall₂ (AnsKv log
  (stateAt log r))` between `rangeAnswers log endNil k e (W64 r)` and `srvSel (stateAt log r)
  endNil k e`: one for one, in key order; `AnsKv`: `findKey` of the answer's key is the
  key-value, its mod revision/create revision mains and version are the answer's, `BucketHas`
  at the mod revision; the created revision's sub-revision is not characterized), via
  `forall2_filterMap_keys` (answers by sorted keys against a sorted state); `rangeAnswers_keys`,
  `rangeAnswers_findKey`, `rangeAnswers_length`, `rangeAnswers_stateAt_w` (at a word revision,
  `sint.nat`); `rangeTaken_eq` (`takeLimit (limitOf limit)` of the answers for both kinds of
  read), `rangeTaken_nonpos`, `rangeTaken_pos`, `rangeTaken_stateAt`, `rangeTotal_stateAt`
  (`totalOf (limitOf limit) withTotal` of the selection's length); `delKeys_eq` (the keys of the
  pending state in the range, needs `LogOk (ilog ++ [pend])`, `ilog ≠ []`), `delKeys_length`,
  `applyChanges_delKeys` (the pending changes then the deletes: the pending state without the
  range); `applyChange_put` (`putKv`, `rfl`), `applyChange_del`, `applyChanges_append`,
  `applyChanges_dels`, `applyChanges_dels_sel`, `stateAfter_snoc`; `lastRev_sint`,
  `lastRev_nat`, `stateAt_lastRev` (a read transaction's `rev`).
- **The end key.** `srvEnd rangeEnd`: `[]` is `(true, [])` (a `nil` end: the one key), `[0]` is
  `(false, [])` (`mkGteRange` makes it `[]byte{}`, non-nil and empty: mvcc's `end == nil` test
  fails and `unsafeVisit`'s `len(end) > 0` test makes it unbounded), anything else
  `(false, rangeEnd)`. `srvInRange_srvEnd`: exactly the client's `inRange k rangeEnd key`
  (`InvEtcd.lean`); `srvSel_srvEnd` (= `rangeIn`), `applyChanges_delKeys_client` (a range
  delete is the client's `.delete` filter). Unit 0's request predicates must give mvcc
  `endNil := (RangeEnd = nil)` after `mkGteRange`, and an empty `RangeEnd` decodes to `nil`.
- **Shapes.** The index's history records events (revision, key, delete or not) and commit
  markers, not values: `histOf_prefix_logShape`/`histOf_prefix_shape_logShape` (a history
  prefix is a `logShape` prefix), `logShape_eq_of_prefix`. Two certificates `idxCert a`,
  `idxCert b` give `logShape a`, `logShape b` comparable (`idxCert_logShape`), not `a`, `b`.
- **`SoleWriter.lean`** (Iris). `soleWriter γ log := idxCert γ.idx log ∗ ownToks γ.revs
  (soleBudget log)`, `soleBudget log = 2^63 - 3 - log.length` (timeless, not persistent);
  `soleWriterOpen` with one token fewer. `soleWriter_of_NewStore` (`[[], []]`: `2^63 - 5`
  tokens, as `NewStore` returns), `soleWriter_split` (one `revToken`, needs
  `log.length + 4 ≤ 2^63`), `soleWriter_close` (`soleWriterOpen log ∗ idxCert (commitLog log
  pend) ∗ (if pend = [] then revToken else True) ⊢ soleWriter (commitLog log pend)`),
  `soleWriter_pins_write` (`soleWriterOpen γ log ∗ storeTxnWriteIs tw s γ ilog pend ⊢
  ⌜ilog.length = log.length ∧ logShape ilog = logShape log⌝`: the auth's count covers the
  caller's tokens and the transaction's, the writer's history authority is above the caller's
  certificate), `soleWriter_pins_write'` (keeping the resources), `stateAfter_commitLog`,
  `soleWriter_read_shape` (a read transaction's log and the sole writer's: shapes comparable).
- **Not provable from unit 0b's mvcc specs** (proposed mvcc changes, one each; all resolved by
  unit 0c, below):
  1. *Values*: the pins give the log's length and shape, not `ilog = log`; make the index
     history's commit marker carry the revision's changes (`HistItem.commit cs`, so `histOf`
     is injective and `idxCert` certifies the log itself), or add a monotone list of committed
     logs whose lower bound `idxCert` includes.
  2. *The empty `End`*: `storeTxnWrite.End` (and `txnEndPost`) with `pend = []` drops the
     `revToken` (the proof keeps `ownTokAuth`'s count): return it (`… ∗ if pend = [] then
     revToken γ else True`; the token is in `storeTxnWriteIs`). Without it a `Put`/`DeleteRange`
     that changes nothing loses the exact count, and no bookkeeping recovers the pin (each lost
     token lets an unseen writer commit a revision): `soleWriter_close` takes it as a premise.
  3. *`NewStore`* does not return `idxCert γ.idx [[], []]`; `soleWriter_of_NewStore` takes it.
  4. *The read pin* (`log' = log` for `store.Read`'s `∃ log' rev`): the read transaction holds
     no token authority and its certificate is only comparable with the caller's. `store.Read`
     must take the caller's `idxCert γ.idx log₀` and `ownToks γ.revs m` (unchanged) and return
     `histOf log₀ <+: histOf log'` and `log'.length + m + 3 ≤ 2^63` — provable if `revMuInv`
     kept a fraction of `ownTokAuth γ.revs` with the budget (`End` changes the count under
     `s.revMu` held exclusively). Until then, unit 3 can use only the write pin and the
     certificates' order.

### Unit 0c: the mvcc changes for the sole writer (2026-10-11)

Branch `txn-mvcc` (from `txn-u0b`), four commits, sorry-free, no new axiom; built with
`--packages=.lake/manifest-merge.json`. Unit 0b's "not provable" list is closed: the sole writer
pins both its transactions' logs to its own. Design and rejected options: `notes/decisions.md`,
"mvcc: the certificate carries the log, the token count is exact, a read is pinned by tokens".

1. *The certificate carries the log*: `IdxNames.log`, a monotone list of the committed log,
   half its authority in `idxWriter`, half `idxLogAuth` (under `s.revMu`); `idxCert` holds its
   lower bound. `idxCert_prefix`, `idxCert_agree_len`, `idxWriter_cert_prefix`,
   `idxLogAuth_cert_prefix`, `idxCert_nil`; `idxWriter_commit` takes and returns the other half.
2. *An empty `End` keeps its token*: `storeTxnWrite.End`'s post and `txnEndPost` add
   `if pend = [] then revToken γ else True`.
3. *`NewStore`* returns `idxCert γ.idx [[], []]`.
4. *The read pin*: the budget's authority is split in halves (`ownTokAuth_halves`), one under
   `s.revMu` with `log.length + ntok + 3 ≤ 2^63`; `store.Read` takes `ownToks γ.revs m` and
   `idxCert γ.idx log₀` and returns them with `log₀ <+: log ∧ log.length + m + 3 ≤ 2^63`
   (`m = 0`, `log₀ = []` give the old spec: the `readView` proofs). The certificate is needed
   too: the tokens bound the log read from above only.

`SoleWriter.lean`: `soleWriter_pins_write` gives `ilog = log`; `soleWriter_pins_read` (pure:
from `store.Read`'s post at the sole writer, `log' = log`) and `soleWriter_Read` (`store.Read`
at `soleWriter γ log` returns `isTxnRead mw s γ log rev ∗ soleWriter γ log`, needs
`log.length + 3 ≤ 2^63`); `soleWriter_close` is fed by `End`'s post, `soleWriter_close_end` by
`txnEndPost`; `soleWriter_of_NewStore` takes `NewStore`'s post (`ownToks ∗ idxCert`).
`Lemmas.lean` untouched. Files: mvcc's `InvIndex`, `InvStore`, `newTreeIndex`, `NewStore`,
`store__Read`, `storeTxnWrite__End`, `metricsTxnWrite__End`, `readView__{Rev,Range,FirstRev}`,
`writeView__{Put,DeleteRange}`, `storeTxnCommon__Range`, `treeIndex__{Put,Tombstone,Insert}`
(proofs, a few lines each), the specs `store__Read`, `storeTxnWrite__End`, `NewStore`,
`newTreeIndex`; `txn/SoleWriter.lean`.

### Merge of units 0, 0b and 0c (2026-10-11)

`txn-mvcc` (unit 0b and unit 0c) fast-forwarded `lean` (`e3effe933`), then `txn-u0` (unit 0)
merged into it. Conflicts only in the notes: this section's heading (one kept, the units in
order 0, 0b, 0c) and `decisions.md` (both entries kept, unit 0's plan first). Everything else
merged cleanly: unit 0c changed no `Link.lean`, link list or baseline, so mvcc's `Link.lean`,
`etc/link-lean-first-mvcc.txt`, `etc/tcb-baseline.txt` and the collections are unit 0's. No
proof needed a change: unit 0's `txnReadWrite.*`/`InvRoTxn.lean` (a read transaction, whose
`txnEndPost` case unit 0c left alone) and `Requests`/`Defs` (over `isStore`, `isLessor`,
`leaseKnown`) elaborate over unit 0c's mvcc. `gen-link.py --mvcc` and `--txn` reproduce both
`Link.lean`s (`store.Read`'s new binders do not reach the generated text). Gates (Perennial
`e4e126e46`, `--packages=.lake/manifest-merge.json`): `lake build` clean (2505 jobs);
`tcb-report.py --check --update` 69 axioms, 1 sorry, the baseline unchanged from unit 0's (13
axioms more than unit 0c's: `sort.Sort`/`Reverse`, traceutil, `proto.Size`, `zap.Int32`,
`zap.Logger.Panic`, the two txn metrics); every collection matches (txn 17/0, mvcc 13/0,
server 26/0, concurrency 12/1, recipes 11/0, cache 10/0, leasing 8/0, raft 1/0, register 1/0,
btree 0/0); `goose.py --check` up to date; `verified-code.py`: etcd 435 verified of 3599
functions (4373 of 45570 lines), txn 0 of 48 (2 assumed, 39 translated; 570 of 653 lines
translated).

### Unit 1: Put and DeleteRange (2026-10-11)

Branch `txn-u1` (main tree, off `lean` at `5e3fc3803`), sorry-free, no new axiom; built with
`--packages=.lake/manifest-merge.json` (Perennial `e4e126e46`). Every function of `put.go` and
`delete.go` is specified (`Spec/go_etcd_io/etcd/server/v3/etcdserver/txn/`) and proved, each proof
importing only its callees' specs, linked (`etc/link-lean-first-txn.txt`, `Link.lean`).

- **The specs**, one line each:
  - `mkGteRange(e)`: `[0]` becomes a slice holding `[]` and not `nil`; anything else is returned
    as it is.
  - `checkLease(lessor, p)`: `nil` with `leaseOk γl o.leaseID` (no lease, or `Lookup` found it:
    `leaseKnown`), or `lease.ErrLeaseNotFound` with the lease nonzero (`errVarIs`: the package
    variable's error).
  - `getPrevKV(trace, tw, p)`, on a transaction of either kind (`isTxn mw s γ kind`; `checkPut`
    reads at `Txn`'s read transaction): if `readsPrev o` (`IgnoreValue`, `IgnoreLease` or
    `PrevKv`), `prevKvIs r (kindState kind) o.key` (the `RangeResult`'s `KVs` hold the key's
    key-value at the state read, if any), else `nil`; the error is always `nil` (`context.TODO()`).
  - `checkAndGetPrevKV`: `getPrevKV`'s answer, with `needsPrev o → findKey` some; or
    `errors.ErrKeyNotFound` when an ignore flag finds no key-value.
  - `checkPut(trace, tw, lessor, p)`: `nil` (with `leaseOk` and the previous key-value present if
    needed), `ErrLeaseNotFound` (checked first) or `ErrKeyNotFound`.
  - `put(ctx, tw, p, prevKV)` at a write transaction `isTxnWrite mw s γ ilog pend ...` with
    `getPrevKV`'s answer at `pendState ilog pend`, the previous key-value there if needed and the
    lease written `leaseOk`: the change `putChangeOf o pv` pending, and `putResponseIs resp
    (W64 ilog.length) (if o.base.prevKV then pv else none)` (the answer's own `*KeyValue` made
    read-only).
  - `deleteRange(ctx, tw, dr)` at a write transaction: `delChanges (pendState ilog pend) o`
    pending (the range's keys deleted) and `deleteRangeResponseIs resp (W64 writeRev …)
    |rangeIn …| (if PrevKv then rangeIn … else [])`; or, with `PrevKv`, the range read's context
    error (`ctx` done), nothing changed.
  - `Put(ctx, lg, lessor, kv, p)`: pre `isKV ∗ storeReader ∗ revToken ∗ ownToks γ.revs m ∗ idxCert
    γ.idx log₀ ∗ isTxnLessor le γ.leases ∗ putRequestIs p o ∗ isContext ctx cd ∗ □ (∀ ilog,
    Pinned log₀ m ilog ∧ IgnoreLease -∗ leaseOk (the previous lease at ilog))`; post `storeReader ∗
    ownToks m ∗ trace ≠ nil ∗` either `ErrLeaseNotFound` (lease nonzero, `resp = nil`, the token
    back) or `∃ ilog, Pinned log₀ m ilog ∧ ilog ≠ []` and either `ErrKeyNotFound` (ignore flag, no
    key-value at `ilog`, token and `idxCert ilog` back) or `err = nil ∗ putResponseIs resp
    (W64 ilog.length) prev ∗ idxCert (ilog ++ [[putChangeOf o pv]]) ∗ leaseOk γ.leases (putLeaseOf
    o pv)`, `pv = findKey o.key (stateAfter ilog)`.
  - `DeleteRange(ctx, lg, kv, dr)`: the same pin, fewer than `2^63` keys at the pinned `ilog`;
    post `∃ ilog` pinned, either `err = nil ∗ deleteRangeResponseIs resp (W64 (writeRev ilog dels))
    |rangeIn (stateAfter ilog) o| prevs ∗ idxCert (commitLog ilog dels) ∗ (if dels = [] then
    revToken else True)` (`dels = delChanges (stateAfter ilog) o`), or with `PrevKv` the context
    error, `resp = nil`, the token and `idxCert ilog` back.
- **The pin, as `store.Read`'s** (decision: `decisions.md`, txn entry, "Unit 1"): `Put`'s and
  `DeleteRange`'s specs take the revision token for their transaction and, beside it, any `m`
  tokens and certificate of `log₀` (`m = 0`, `log₀ = []`: the plain token spec), and return
  `Pinned log₀ m ilog` (`log₀ <+: ilog ∧ ilog.length + m + 4 ≤ 2^63`), read inside the open
  transaction (`isTxnWrite_pinned`: `soleWriter_pins_write` for any caller). After `End` nothing
  pins `ilog` any more (the token is spent), so the sole writer's statements could not be derived
  from a spec with the token alone. At the sole writer (`m = soleBudget log - 1`) `Pinned` is
  `ilog = log` (`pinned_sole`).
- **Two premises the code needs** (stated on the specs, not findings): (1) with `IgnoreLease`, the
  lease `put` writes is the previous key-value's, which mvcc's `Put` attaches (`Attach` needs
  `leaseKnown`; Go panics on an unknown lease): `Put` takes `leaseOk` of the previous lease at the
  pinned log (the sole writer: at its own log), and returns `leaseOk` of the lease it wrote, so a
  sole writer can keep "every lease in the state is known" by itself (not proved here: mvcc has
  no invariant on the leases in its state). (2) `DeleteRange` needs fewer than `2^63` keys
  (mvcc's `DeleteRange` premise).
- **`metricsTxnWrite.Range` of either kind; a range read at `context.TODO()`** (mvcc change,
  minimal, `decisions.md`): `getPrevKV` calls `Range` on the *write* transaction, through
  `mvcc.ReadView`, at `context.TODO()`. mvcc's `metricsTxnWrite.Range` spec was for a read
  transaction and an `isContext` only, and `context.TODO()`'s `todoCtx{}` is not an `isContext`
  (its `Done()` is `nil`). Now `metricsTxnWrite.Range` is over `isTxn mw s γ kind` (as `End`; a
  write transaction's range is `storeTxnWrite.Range`'s: `ilog ++ [pend]` at `writeRev`,
  `TxnKind.readLog`/`readRev`), and `rangeKeys`, `storeTxnCommon.Range`, `storeTxnWrite.Range`
  and `metricsTxnWrite.Range` take the context as `rangeCtx todo ctx cd` (`isContext ctx cd`, or
  `ctx = todoCtxV` when `todo`) and return `todo = true → r ≠ null` (at `context.TODO()` the
  `select` on `Done()` takes its default: `wp_select_nonblocking_nil`; no context error). New
  file `mvcc/TxnRange.lean` (`rangeCtx`, `rangeDone`, `rangeCtx_Done`, `wp_todoCtx_Done`,
  `wp_select1_alt_or_nil`, `readLog`/`readRev`). The old statement is the instance `kind :=
  .read log rev`, `todo := false` (`readView.Range` and `txnReadWrite.Range` use it, their specs
  unchanged). mvcc's link list: `metricsTxnWrite__Range: storeTxnCommon__Range
  storeTxnWrite__Range`. So `Put`'s spec has no context-error case; unit 3 (`applyCompare` reads
  at `context.TODO()` too) can use the same.
- **`Write.lean`** (shared, pure and Iris): `putChangeOf`/`putValOf`/`putLeaseOf`,
  `applyChange_putChangeOf`/`stateAfter_put` (the server's put is the client's `putTxnOp`),
  `delChanges`, `delKeys_client`, `stateAfter_commit_delete` (the delete is the client's filter),
  `srvEnd_mkGte` (`mkGteRange`'s slice is `srvEnd (rangeEndOf …)`), `pendState`, `kindState`,
  `KindOk`, `isTxn_kindOk`, `isTxnWrite_facts`, `Pinned`, `isTxnWrite_pinned`, `pinned_sole`,
  `rangeAnswers_one`, `prevKvIs`, `prevKvIs_of_outcome`, `rangeOutcome_sel`, `zip_kvsIs`,
  `kvPtrIs_kvIs`/`kvPtrIs_not_null` (a range result's fresh `*KeyValue` made `kvIs`),
  `errVarIs`, `leaseOk`, `todoCd`, and `wp_slice_literal_nn` (Perennial's `wp_slice_literal`
  keeping `typedPointsto_not_null`: `[]byte{}` is not `nil`, so mvcc's `decide (end = nil)` is
  `false` for `mkGteRange("\x00")`).
- **Responses**: `putResponseIs`'s `PrevKv` is the range result's own pointer; the result is
  dropped, so its `*KeyValue` is made read-only (`kvIs`) and shared, no change to unit 0's
  predicates. The responses' fields are persisted after their last store (`wp_fupd` in
  `deleteRange`, where the stores are the last steps).
- **Results** (`Results.lean`, `#print axioms` of each, no `sorryAx`): `put_putKv` and
  `deleteRange_filter` (the specs restated; the committed states `stateAfter_put`,
  `stateAfter_commit_delete`), `put_put`, `deleteRange_deleteRange`, `put_checkPut` (for unit 3),
  `put_soleWriter` and `deleteRange_soleWriter`: derived triples with `soleWriter γ log` for the
  token: the commit is at `log`, `soleWriter γ (log ++ [[c]])` (or `soleWriter γ (commitLog log
  dels)`, or `soleWriter γ log` on an error) comes back, and the committed state is the client's
  `applyTxnOp`.
- **`gen-link.py`**: an `@` callee's result takes `[go_etcd_io.etcd.cache.v3.Assumptions]` when
  its own package's `Link.lean` gives it them (mvcc's write path reaches the index's btree); so
  do the txn results that reach one. Every mode's `Link.lean` reproduces.
- **Findings**: none in the Go code. The ignore flags' `prevKV.KVs[0]` in `put` is safe in `Put`
  (`checkAndGetPrevKV` found the key in the same write transaction); `checkLease` checks `Lease`
  even with `IgnoreLease` (the client rejects that combination; a behavior, not a bug).
- **Gates**: full `lake build --packages=.lake/manifest-merge.json` clean (2525 jobs); `gen-link.py` reproduces
  every mode's `Link.lean` (`--txn`, `--mvcc` regenerated: mvcc's adds `storeTxnWrite.wp_Range` as a
  callee of `metricsTxnWrite.wp_Range`); `tcb-report.py --check`: the baseline matches (69
  axioms, 1 sorry: no axiom added or removed); `--collection txn.txt --check --update`: 20 axioms,
  0 sorries (was 17: `proto.Marshal`, `proto.Unmarshal`, `binary.bigEndian.PutUint64`, mvcc's
  existing axioms, now reached through mvcc's write path by the package's own results); every
  other collection unchanged (mvcc 13/0, server 26/0, concurrency 12/1, recipes 11/0, cache 10/0,
  leasing 8/0, raft 1/0, register 1/0, btree 0/0); `verified-code.py --reuse`: txn 9 of 48
  functions verified (18.8%; 2 assumed, 30 translated), 110 of 653 lines (16.8%); mvcc unchanged
  (62 of 155, 661 lines); etcd 444 verified of 3599 functions (was 435), 4483 of 45570 lines (was
  4373).

### Unit 2: Range (2026-10-11)

Branch `txn-u2` (worktree `/shared/etcd-grove-txn2`, off `lean` at `5e3fc3803`), sorry-free;
Perennial `e4e126e46` (`--packages=.lake/manifest-merge.json`). Every function of `range.go`
(18) and `mkGteRange` (`delete.go`) specified (`Spec/.../txn/`) and proved (`Proof/.../txn/`),
linked (`etc/link-lean-first-txn.txt`, `Link.lean`). Decisions: `decisions.md`, the txn entry's
"Unit 2" bullet.

- **The model** (`RangeModel.lean`, pure, standard axioms only): the server's range as the code
  computes it: `rangeLimitOf` (`rangeLimit`), `fastKeysOnly`/`kvRead` (mvcc's `FastKeysOnly`
  read: no value and lease `0`), `srvPre` (the state's key-values in the range, at most the limit
  read with, as read, filtered by `kvFilterOk`; none if count-only), `srvSorted` (a permutation
  of `srvPre` sorted by `kvLeBy target`, ascending or descending, when `effSortOrder` is `1`/`2`:
  `sort.Sort` is not stable, ties in any order; `srvPre` itself otherwise), `srvTrunc`/`srvMore`
  (the first `limit`, `More`), `respKv` (keys-only drops the value), `srvRangeOk o s kvs more`,
  `srvCount` (count-only: the range's size; else `totalOf` of mvcc's limit and `withTotal`).
  The comparators `kvLtBy` (`kvLtBy_swo`: strict weak orders; `kvLtBy_false_iff`: not-less is the
  client's `kvLeBy`); `sub_neg_iff` (Go's `(a - b) < 0` is `a < b` on non-negative values: no
  overflow). **The bridge** `srvRangeOk_rangeKvsOk`: `srvRangeOk` gives the client's
  `rangeKvsOk o (rangeSel s o)` up to `leaseZ (fastKeysOnly o)`, and `More` is the client's below
  `MaxInt64`, unless `cutEarly o`. The sort's premises: `validSortTarget` (else `lg.Panic`),
  `sortOk o log` (a sorting request reads a log of at most `2^62` changes, `LogSmall`;
  `stateAt_small`: then at most `2^62` keys, revisions and versions in `[0, 2^62]`).
- **The heap** (`InvRange.lean`): `kvAt` (mvcc's owned `kvPtrIs true`; `kvPtrIs_false`: a fast
  read's is `kvAt` of `kvRead true`), `kvsAt` (a list of (pointer, key-value)), `kvsOwnAt`,
  `rangeResultIs rr rev count vs` (the `*RangeResult`, its key-values owned), `rangeResult`
  (`executeRange`/`Range`'s three outcomes: `ErrFutureRev`, a context error on a full read
  (mvcc's `rangeOutcome`, kept), or the response with `srvRangeOk` of `stateAt log (rangeRev rev
  o.base.rev)` and `srvCount`), `checkRangeErr`. `RangeLemmas.lean`: mvcc's read to the model
  (`rangeKvs_kvsAt`, `taken_stateAt`, `total_stateAt`, `srvPre_small`, `isTxnRead_pure`/`_cert`),
  `rangeResultClient`, `rangeResult_client`.
- **The specs** (one line each): `kvSort.Len` (`len(s.kvs)`); `kvSort.Swap` (the slice's `i`-th
  and `j`-th pointers exchanged); `kvSortBy{Key,Version,Create,Mod,Value}.Less` (`kvLtBy t` of the
  two owned key-values; the integer targets need `kvOk`); `IsDefaultOrdering` (`order = 0 ∨
  (target = 0 ∧ order = 1)` on the `int32`s); `HasRevisionFilters` (`hasRevFilters o`);
  `rangeLimit` (`rangeLimitOf o`); `mkGteRange` (`srvEnd (rangeEndOf sl e) = (decide (sl' = nil),
  e')`: `[]byte{0}` becomes a non-`nil` empty slice); `pruneKVs` (with an `isPrunable` closure
  deciding `P` of an owned key-value: the key-values `P` rejects, in order; the pruned ones and
  the slice's tail no longer owned); `filterRangeResults` (`filter (kvFilterOk o)`);
  `sortRangeResults` (`srvSorted o vs vs'`, premises `validSortTarget` and, when sorting, at most
  `2^62` key-values with `kvOk`); `asembleRangeResponse` (`rangeResponseIs resp rev ((srvTrunc o
  vs).map (respKv o)) (srvMore o vs) count`, the result's key-values persisted into the
  response); `checkRange` (on a read transaction: `checkRangeErr rev o err`: `nil` for revision
  `0` or in `[-1, rev]`, `ErrFutureRev` above, `ErrCompacted` below `-1`); `executeRange` (on
  `isTxnRead mw s γ log rev`, premises `validSortTarget o ∧ sortOk o log`: `rangeResult`);
  `Range` (`store.Read` with the caller's `ownToks m` and `idxCert log₀`, premise `sortOk` on
  every log the read may see: `rangeResult` at the log read, `log₀ <+: log`, `log.length + m + 3
  ≤ 2^63`, the trace non-`nil`); `Count` (the count-only `countOp`: `rangeIn` length of the state
  read, or `ErrFutureRev` and `0`). mvcc: `metricsTxnWrite.Rev`/`FirstRev` of a read
  transaction (`rev`, `-1`), additive (`etc/link-lean-first-mvcc.txt`).
- **Results** (`Results.lean`, `#print axioms`: no `sorryAx`): `range_rangeSel` (`Range` with
  `rangeResultClient`: the client's `rangeKvsOk` of `rangeSel`, premise `¬ cutEarly o`);
  `range_soleWriter` (at `soleWriter γ log`, `log.length + 3 ≤ 2^63`: the read is at `log`,
  revision `log.length - 1`, `soleWriter` returned); `count_result` (`Count` at the sole writer).
- **Where the server and the client model differ** (both in `issues/`, with Go tests):
  `etcd-range-sort-none-limit.md` (a non-key target with `SortOrder: NONE` and a positive limit:
  only the first `limit + 1` keys are sorted, a wrong result reachable with `etcdctl get
  --sort-by=VERSION --limit=1`; `cutEarly`), `etcd-range-keys-only-lease.md` (keys-only ranges
  have lease `0` unless sorted by value, since 7624a8a2e; `leaseZ`). The client's `rangeKvsOk`
  already allows any order of ties, so a non-stable sort is no difference. The comparators'
  subtraction cannot overflow on a small log (`sub_neg_iff`, `kvOk`): not a finding.
- **For the merge with unit 1**: `mkGteRange`'s spec and proof (with `wp_slice_literal_nn`) are
  here; if unit 1 has its own, keep one and adapt `executeRange`'s call (one `wp_apply`). The
  `metricsTxnWrite.Range` call in `executeRange` is in one place for unit 1's `isTxn`
  generalization. `etc/gen-link.py`: an `@` callee whose result takes the cache's assumptions
  (mvcc's `metricsTxnWrite.Range`, through the btree) now passes them on (`[go_etcd_io.etcd.
  cache.v3.Assumptions]` on `wp_executeRange`, `wp_Range`, `wp_Count`); the cache's link list
  names its `Range` `v3_Range` (the txn package's `Range` made the bare name ambiguous), its
  `Link.lean` regenerated (one import moved).
- **Gates**: `lake build` clean (2550 jobs); `gen-link.py --txn`, `--mvcc` and every other mode
  reproduce their `Link.lean`; `tcb-report.py --check`: 69 axioms, 1 sorry (baseline unchanged);
  `--collection txn.txt --check --update`: 19 axioms, 0 sorries (was 17: mvcc's
  `binary.bigEndian.PutUint64` and `proto.Unmarshal`, reached through `store.Read`/`Range`; no
  axiom added); every other collection unchanged (mvcc 13/0, server 26/0, cache 10/0, ...);
  `ETCD_SRC=/shared/etcd goose.py --check --perennial /shared/perennial-merge` up to date;
  `verified-code.py --reuse`: txn 19 of 48 functions verified (range.go 18/18, 164 lines; delete.go
  1/3), 170 of 653 lines; etcd 454 of 3599 functions, 4543 of 45570 lines (was 435, 4373).

### Merge of units 1 and 2 (2026-10-12)

`txn-u1` (unit 1, with the stray `issues/recipes-pqueue-dequeue-order.md` commit `8eb95dacb`)
fast-forwarded `lean` (`b3c219f87`), then `txn-u2` (unit 2) merged into it. Conflicts and their
resolutions:

- **`mkGteRange`** (`Spec/.../txn/mkGteRange.lean`, `Proof/.../txn/mkGteRange.lean`): both units
  specified and proved it. Unit 1's spec is kept, being the stronger: the result holds `[]` and
  is not `nil` for `[0]`, and is `rangeEnd` itself otherwise; unit 2's (`srvEnd (rangeEndOf sl e)
  = (decide (sl' = nil), e')`) follows from it by unit 1's `srvEnd_mkGte` (`Write.lean`). With
  unit 2's proof went its copy of `wp_slice_literal_nn` (it was in unit 2's `mkGteRange.lean`);
  the one left is unit 1's, in `Write.lean`.
- **`executeRange`'s proof** (the one proof changed): its `mkGteRange` call now gets the slice's
  `ownSlice_len` first (a `nil` slice holds `[]`), then `srvEnd_mkGte` for unit 2's equation,
  generalizing the result's contents to `e'` (the rest of the proof unchanged); its
  `metricsTxnWrite.Range` call is unit 1's generalized spec at `kind := .read log rev`, `todo :=
  false` (`rangeCtx false ctx cd` from `isContext`, as `readView.Range`). One unused `simp`
  argument (`hcoB`) dropped.
- **`etc/gen-link.py`**: both units added the same rule (an `@` callee whose result in its own
  package's `Link.lean` takes the cache's assumptions passes them on); unit 1's version kept (the
  `theorem` anchored at a line start), one comment for both. Every mode (`--cache`,
  `--concurrency`, `--server`, `--register`, `--leasing`, `--recipes`, `--mvcc`, `--txn`)
  reproduces its `Link.lean`; the cache's `v3_Range` rename (unit 2) merged cleanly.
- **`etc/link-lean-first-txn.txt`**: one list of mvcc's `@` callees (`store.Write`/`Read`,
  `metricsTxnWrite.Range`/`Put`/`DeleteRange`/`End`/`Rev`/`FirstRev`), then unit 1's functions
  (one `mkGteRange`), then unit 2's; txn and mvcc `Link.lean` regenerated
  (`etc/link-lean-first-mvcc.txt` merged cleanly: unit 1's `storeTxnWrite__Range` callee and unit
  2's `Rev`/`FirstRev`).
- **`Results.lean`**: unit 1's section, then unit 2's (`section unit2`, the opens of both), each
  with its `#print axioms`; unit 0's mvcc prints last. **Notes**: this section's units in order;
  `decisions.md` both bullets (unit 1's first); `issues/README.md` merged cleanly.

The issues from the txn work, now all in `issues/`: `etcd-txn-empty-requestop` (`Txn` panics on
a `RequestOp` with an empty oneof; unit 0), `etcd-range-sort-none-limit` (a sort by a non-key
target with order `NONE` and a limit is cut short by the limit; unit 2),
`etcd-range-keys-only-lease` (keys-only ranges drop the lease unless sorted by value; unit 2).

Gates (Perennial `e4e126e46`, `--packages=.lake/manifest-merge.json`): `lake build` clean (2568
jobs), no `sorry`, no new axiom; `gen-link.py` reproduces every mode; `tcb-report.py --check`:
69 axioms, 1 sorry (baseline unchanged); `--collection txn.txt --check --update`: 20 axioms, 0
sorries (unit 1's list exactly, the union of both units': unit 2's 19 and `proto.Marshal`);
every other collection unchanged (mvcc 13/0, server 26/0, concurrency 12/1, recipes 11/0, cache
10/0, leasing 8/0, raft 1/0, register 1/0, btree 0/0); `ETCD_SRC=/shared/etcd goose.py --check
--perennial /shared/perennial-merge` up to date; `verified-code.py --reuse`: txn 27 of 48
functions verified (56.2%; `range.go` 18/18, `put.go` 6/6, `delete.go` 3/3; 2 assumed, 12
translated), 274 of 653 lines (42.0%); mvcc unchanged (62 of 155, 661 lines); etcd 462 of 3599
functions, 4647 of 45570 lines (was 435, 4373 before the units).

### Unit 3: Txn (2026-10-12)

Branch `txn-u3` (worktree `/shared/etcd-grove-txn3`, off `lean` at `10cc14b29`), sorry-free;
Perennial `e4e126e46` (`--packages=.lake/manifest-merge.json`). Every function of `txn.go` (12)
and `etcdserverpb.RequestOp.GetRequestRange` specified (`Spec/.../txn/`, `Spec/go_etcd_io/etcd/
api/v3/etcdserverpb/`) and proved, linked (`etc/link-lean-first-txn.txt`, `Link.lean`; the
package's `compareInt64` is `txn_compareInt64` there, leasing has one too). Decisions:
`decisions.md`, the txn entry's "Unit 3" bullet.

- **The pure model** (`TxnRun.lean`, standard axioms only): the path `txnPath s t` (`opPath`,
  `opsPath`: the verdict of `t`, then the paths of the chosen branch's nested transactions, in
  pre-order, every comparison at the read state `s`; `txnPath_length`: one plus `nestedCount`, the
  number of nested transactions, what `newTxnResp`/`checkTxn`/`executeTxn` return; the slicing
  `path[1:]`, `path[n+1:]` keeps `x :: opsPath s (rest of the branch) ++ rest`). **The server's run**
  `srvOp`/`srvOps`/`srvRunTxn`: the client's `applyTxnOp`/`runOps` but a nested transaction's
  branch is its verdict at the read state, and the run returns the mvcc changes (a put's
  `putChangeOf`, a delete's keys; `srvOp_putTxnOp`, `srvOp_delete`) with the results; the state
  is `applyChanges` of them (`srvOp_state`). `srvRunTxn_runTxn`: the server's run is the client's
  `runTxn` when every nested verdict is stable (`OpsStable`), always without nested transactions
  (`opsStable_flat`). The premises `OpsOk weak` (below), `PathsIgnOk` (what `checkTxn` checks),
  `opsOk_strong`, `opsLeases`, `TxnPre`, `txnReadonly`/`txnSerializable` (`serializable_linearizable`:
  `txnSerializable t = !t.linearizable`, the client's).
- **The heap** (`InvTxn.lean`): `txnViewIs tw s γ kind ro` (a `*metricsTxnWrite` of either kind,
  or the read-only wrapper of a read transaction), `txnWriteIs tw s γ ro ilog pend`
  (`executeTxn`'s); the transaction responses (moved from `Requests.lean`, `responseOpIs skip`:
  a range's key-values the client's `rangeKvsOk` of the selection up to `leaseZ`, its count the
  range's; `skip`: header-only, no key-values, `More` false, count `0`), `txnRespFieldsIs`,
  `respsIs`, `txnResponseIs skip`; the skeleton `opSkel`/`opsSkel`/`respsSkel`/`txnSkel`
  (`newTxnResp`'s: each wrapper's response field `nil` and owned; a nested transaction's response
  complete but for its operations'); `leasesOk`, `leasesKnown`; `checkErrIs`. `TxnLemmas.lean`:
  the run split at an index, the requests/responses element by element, `Rev`/`Changes` of
  `executeTxn`'s transaction, `txnWriteIs_kind`, `rangeResult_txn` (a range at revision `0` at a
  context never canceled: no error, the client's selection).
- **The specs** (one line each): `compareInt64` (`int64Cmp`); `compareKV(c, ckv)` (`cmpKv cm v`);
  `applyCompare(rv, c)` on a read transaction of `log` (`cmpHolds (stateAfter log) cm`; the range
  at `context.TODO()`, no error); `applyCompares` (`cms.all (cmpHolds …)`); `compareToPath(rv, rt)`
  (a fresh slice of `txnPath (stateAfter log) t`); `GetRequestRange` (the range request of a
  range op, else `nil`); `IsTxnReadonly` (`txnReadonly t`), `IsTxnSerializable`
  (`txnSerializable t`); `checkTxn(trace, rv, rt, lessor, path)` (nil, `nestedCount`,
  `PathsIgnOk` and `leasesOk` of the path's puts' leases; or `checkErrIs` and `0`; nothing
  written); `newTxnResp(rt, path)` (`txnSkel` of the branch the path chooses, `nestedCount`; any
  `s0`); `executeTxn(ctx, lg, tw, rt, path, tresp, skip)` (on `txnWriteIs tw s γ ro ilog pend`,
  path at `stateAfter ilog`, at a context never canceled: nil, `nestedCount`, `srvOps` of the
  branch at the pending state, its changes pending, `respsIs skip`, the state's leases known);
  `txn(ctx, lg, tw, rt, isWrite, path, skip)` (`srvRunTxn` at `ilog`, the header revision
  `writeRev ilog chs`, nil); `Txn` (at the sole writer: `checkErrIs` with `resp`, `trace` `nil` and
  the sole writer unchanged; or `srvRunTxn` committed, `soleWriter γ (commitLog log chs)`, the
  response at `writeRev log chs`, `chs = []` for a read-only request, the leases known).
- **The premises of `Txn`**, in one list: `soleWriter γ log` (the apply thread); `isKV`,
  `storeReader`; `isTxnLessor lessor γ.leases`; `txnRequestIs rt t` (no empty oneof, unit 0's; a
  comparison's operand wrapper not a typed `nil`, new: `compareKV`'s `tv != nil`); the context
  an `isContext` that is never canceled (`neverDone`: its Done proposition never holds; the
  apply thread passes `context.TODO()`, whose `EnsureTrace` derivative has `nil` `Done`, see
  below); `leasesKnown γ.leases (stateAfter log)` (every lease of the state granted: an
  `IgnoreLease` put attaches the previous key's lease; `Txn` returns it for the new state);
  `TxnPre log t`: `log.length + 4 ≤ 2^63`; `OpsOk true` on the chosen branch's run: every range
  at revision `0` (the transaction's state, the client's `txnOpOf`), a valid sort target, not
  `cutEarly`, a small sorted selection (`sortSmall`, `sortRangeResults`' premise at the state
  read); every `IgnoreValue`/`IgnoreLease` put finds its key at the state it runs at unless it is
  missing at `log` (`IgnOk`; `checkTxn` fails then); fewer than `2^63` changes.
- **Changes to units 0–2's and mvcc's files**: mvcc (`TxnRange.lean`): `rangeCtx true` also takes
  an `isContext` with `neverDone` (`rangeDone` likewise; `rangeKeys`' proof: the `select`'s case
  would give `□ PDone`), `TxnKind.beginRev`/`pend`; `metricsTxnWrite.Rev` of either kind (was a
  read transaction's; `checkRange` adapted); `metricsTxnWrite.Changes` (new: the length, non-
  negative); `txnReadWrite.Range` at `rangeCtx`. `executeRange` on `txnViewIs` (either kind or the
  wrapper), at `nd` a context never canceled with no context error, premise `sortSmall` at the
  state read (was `sortOk` of the log; `Range` adapted through `sortSmall_of_sortOk`);
  `deleteRange` at `nd` with no error (`DeleteRange` passes `false`); `Requests.lean`: the
  transaction responses moved to `InvTxn.lean` (they name `leaseZ`, `RangeModel.lean`), `compareIs`
  gains the typed-`nil` conjunct; `getPrevKV`'s proof one line.
- **Results** (`Results.lean`, `#print axioms`: no `sorryAx`): `txn_srvRunTxn` (the spec),
  `txn_runTxn` (under `OpsStable`: the committed state, the verdict and the results are the
  client's `runTxn` at the sole writer's log), `txn_readonly_no_revision`,
  `txn_check_error_no_write`, `compareToPath_txnPath`, `txn_serializable_iff`
  (`IsTxnSerializable` returns `!t.linearizable`), `srvRunTxn_runTxn_flat`.
- **Findings** (both in `issues/`, with Go tests): `etcd-txn-delete-then-ignore-put.md` (a
  reachable panic: a from-key delete then an `IgnoreValue`/`IgnoreLease` put of a deleted key in
  one transaction passes `checkIntervals`, whose interval for a `"\x00"` range end is empty, and
  `checkTxn`, which checks at the read state, and `put` indexes an empty `KVs` in the apply loop);
  `etcd-txn-nested-compare-snapshot.md` (nested comparisons are evaluated before the outer
  operations run: undocumented). **This repository's client model is wrong there**:
  `applyTxnOp (.txn …)` (`cache/v3/InvEtcdTxn.lean`) evaluates a nested transaction's comparisons
  on the state the operations before it left; etcd on the state before the transaction. The
  client contracts that use nested transactions (leasing's) inherit that; not changed here
  (another package's proofs), `txn_runTxn` carries the agreement as `OpsStable`.
- **The plan's suspects**: (1) the re-read of `prevKV` in the write transaction after `checkTxn`
  checked it at the read: with a concurrent writer committing in between it could panic, but under
  the sole writer the write transaction's log is the read's (`soleWriter_pins_write`): not
  reachable, a design note; the reachable case is within one transaction (finding above). (2) the
  comparisons at an earlier snapshot: under the sole writer the snapshot is the write
  transaction's committed log, so the top-level comparisons see exactly the state the branch runs
  on; only the nested ones are early (finding above). `checkTxn`'s error case returns `0`: Go's
  `txnCount += txns + 1; txnPath = txnPath[txns+1:]` runs before the error test, so a nested
  call's count must be bounded on an error too (the spec says `0`, as Go returns).
- **The context**: `EnsureTrace`'s axiom takes an `isContext`, which `context.TODO()` (the apply
  thread's) is not; `Txn`'s spec is for an `isContext` never canceled. The apply package will need
  `EnsureTrace` of `TODO()` (a derived context whose `Done` is `nil`) or a `neverDone` descriptor
  for it.
- **Gates**: full `lake build --packages=.lake/manifest-merge.json` clean (2599 jobs), no `sorry`;
  `gen-link.py --txn` and `--mvcc` reproduce their `Link.lean` (mvcc's: `metricsTxnWrite.Changes`,
  `Rev`'s new callee; txn's: unit 3's functions, `executeRange`'s new callee);
  `tcb-report.py --check`: 69 axioms, 1 sorry (the baseline unchanged: no axiom added);
  `--collection txn.txt --check --update`: 20 axioms, 0 sorries (unchanged); every other
  collection unchanged (mvcc 13/0, server 26/0, concurrency 12/1, recipes 11/0, cache 10/0,
  leasing 8/0, raft 1/0, register 1/0, btree 0/0); `ETCD_SRC=/shared/etcd goose.py --check
  --perennial /shared/perennial-merge` up to date; `verified-code.py --reuse --package
  go.etcd.io/etcd/server/v3/etcdserver/txn`: txn 39 of 48 functions verified (81.2%: every
  function Goose translates with a body: `txn.go` 12/12, `range.go` 18/18, `put.go` 6/6,
  `delete.go` 3/3; 2 assumed, `metrics.go`), 570 of 653 lines (87.3%); mvcc 62 of 155 (661
  lines; `metricsTxnWrite.Changes`/`Rev` are promoted methods, outside the totals); etcd 474 of
  3599 functions, 4943 of 45570 lines (was 462, 4647).

### Unit 4: the history laws of the log (2026-10-12)

Branch `txn-u4` (main tree, off `lean` at `10cc14b29`). `Proof/.../etcdserver/txn/HistoryLaws.lean`
(pure Lean, standard axioms only; `#print axioms` in `Results.lean`, `section unit4`). The client's
history axioms (`etcdState_*`, `InvEtcd.lean`/`InvEtcdTxn.lean`) are stated over the abstract
`etcdState`; these theorems show that each law holds of the server's log model (`stateAt log r`,
for `r < log.length`; per prefix `stateAtPfx log r pfx`, the filter by `pfx <+: key`). They
**validate** the axioms against the server model, they do not discharge them (nothing links
`etcdState` to a log yet). Each law and what it needs:

- **`revs`** (`stateAt_revs`): positive create revision, create ≤ mod ≤ `r`, positive version.
  Needs `LogOk` (revision 0 empty, `log[0]? = some []`, for a positive create revision; the word
  bound) and **`NoDupKeysPerRev log`** (each revision's changes have distinct keys) for the
  version only. *Counterexample without it:* a revision may put one key many times (`LogOk` bounds
  only each revision's change count, below `2^63`): two revisions of `2^62` puts of `k` each give
  `k` version `2^63`, whose signed value is negative. With it, a record created at `c` and
  modified last at `m` has version at most `m - c + 1` (`KvInv`). The revision parts alone need
  only `log.length < 2^63` (`stateAt_revInv`). (Unit 2 met the same unbounded version in the
  sort's comparators: its `LogSmall`.)
- **`create_persist`** (`stateAt_create_persist`): only `log.length < 2^63`. A record whose
  create revision is not the current revision's had its key, with that create revision, before
  it (`mem_applyChanges_createRev`); a delete-and-recreate in one revision gives the new record
  that revision as its create revision, so no counterexample.
- **`modrev_persist`** (`stateAt_modrev_persist`): only `log.length < 2^63` (a record whose mod
  revision is not the revision's was there before it, `mem_applyChanges_modRev`).
- **`modrev_det`** (`stateAt_modrev_det`): only `log.length < 2^63`, **not** `NoDupKeysPerRev`:
  the expected counterexample (`[.put k v1 l, .put k v2 l']` in one revision: one mod revision,
  two records) is not one, since only the later record survives the revision; by
  `modrev_persist` both records of the law are in the state at their mod revision, which holds
  one record per key (sorted). No other counterexample found (delete-and-recreate within a
  revision: the same argument).
- **`agree`** (`stateAtPfx_agree`): `stateAtPfx` is a function. `stateAtPfx_wf`: its states are
  `EtcdStateWf` (keys strictly increasing, under the prefix). The four laws per prefix
  (`stateAtPfx_revs`, `_create_persist`, `_modrev_det`, `_modrev_persist`) follow.
- **`etcdReachedAt`** has no pure law (its only axiom is `Timeless`). The log analogue of what it
  is used for: a revision's state is fixed once the log has it (`stateAt_of_prefix`,
  `stateAtPfx_of_prefix`: a longer log has the same state at every revision of the shorter one).
- **A commit keeps the hypotheses.** `LogOk.snoc`: `LogOk (log ++ [pend])` from `LogOk log`, the
  word bounds, and `DelsPresent` (the commit's deletes are of keys present when they run:
  `LogWf`'s condition for the one revision). `NoDupKeysPerRev.snoc_iff`: kept iff the commit's
  keys are distinct; `keys_nodup_iff_check`: for a revision with `DelsPresent`, its keys are
  distinct **iff its put keys are distinct and none of them is also deleted** — etcd's
  `checkIntervals` (v3rpc, "duplicate key given in txn request": distinct put keys, no put key in
  a delete's range); two deletes of one key need a put between them, which the check excludes.
  `NoDupKeysPerRev.snoc` packages it; `sel_keys_nodup`: a range delete's keys (`delKeys_eq`'s
  `(srvSel s …).map key`) are distinct. Unit 3 instantiates it with `runOps`' changes (a put
  `.put k v l`, a delete `(delKeys …).map .del`): its premise is the client's transaction passing
  that check (the check is in the gRPC layer, not in the apply path the proof covers).

**What the client axioms assume of the server**, beyond `LogOk`: `NoDupKeysPerRev` (a revision
writes a key at most once), for `etcdState_revs`'s positive version only.

Gates: `lake build --packages=.lake/manifest-merge.json` of `HistoryLaws` and `Results` clean, no
`sorry`, `#print axioms` standard only (`propext`, `Classical.choice`, `Quot.sound`). The
`tcb-report.py --collection txn.txt --check` not run (`.lake/tcb.json` not current; the merge runs
it); no new axiom.

### Merge 3/4 (2026-10-12)

`txn-u3` (unit 3, six commits) merged into `lean` (`e099df5ea`), then `txn-u4` (unit 4)
(`2175453f0`). Conflicts in the notes only (this section's "Unit 3" and "Unit 4" subsections,
`decisions.md`'s two bullets, both kept in unit order); `Results.lean` merged cleanly (unit 3's
section, then unit 4's `section unit4` and its `public import ...txn.HistoryLaws`). Unit 3's
changes (the responses moved to `InvTxn.lean`, `executeRange`/`deleteRange` generalized, mvcc's
`TxnRange.lean`) touch nothing `HistoryLaws.lean` uses (`Lemmas.lean` and mvcc's model): no
proof changed.

Gates (Perennial `e4e126e46`, `--packages=.lake/manifest-merge.json`): `lake build` clean (2600
jobs), no `sorry` of this repository's, `HistoryLaws`' results on the standard axioms only;
`gen-link.py --txn` and `--mvcc` reproduce their `Link.lean`; `ETCD_SRC=/shared/etcd goose.py
--check --perennial /shared/perennial-merge` up to date; `tcb-report.py --check`: 69 axioms, 1
sorry (baseline unchanged); every collection unchanged (txn 20/0, mvcc 13/0, server 26/0,
concurrency 12/1, recipes 11/0, cache 10/0, leasing 8/0, raft 1/0, register 1/0, btree 0/0);
`verified-code.py --reuse`: txn 39 of 48 functions verified (81.2%), 570 of 653 lines (87.3%);
etcd 474 of 3599 functions (13.2%), 4943 of 45570 lines (10.8%), as after unit 3 (unit 4 is pure).

### The whole package (2026-10-12)

**Verified**: every function of `txn.go`, `put.go`, `range.go` and `delete.go` that Goose
translates with a body (39: `txn.go` 12, `range.go` 18, `put.go` 6, `delete.go` 3), and
`etcdserverpb.RequestOp.GetRequestRange`, sorry-free; `metrics.go`'s two observers are assumed,
`util.go` names-only. mvcc gained the read-only write transaction (`txnReadWrite`,
`NewReadOnlyTxnWrite`) and `metricsTxnWrite.Rev`/`FirstRev`/`Changes`.

**Exported results** (`Results.lean`, each with `#print axioms`): unit 1 `put_putKv`,
`deleteRange_filter`, `put_put`, `deleteRange_deleteRange`, `put_checkPut`, `put_soleWriter`,
`deleteRange_soleWriter`; unit 2 `range_rangeSel`, `range_soleWriter`, `count_result`,
`srvRangeOk_rangeKvsOk`; unit 3 `txn_srvRunTxn`, `txn_runTxn`, `txn_readonly_no_revision`,
`txn_check_error_no_write`, `compareToPath_txnPath`, `txn_serializable_iff`,
`srvRunTxn_runTxn_flat`; unit 4 (pure) `stateAt_revs`, `stateAt_create_persist`,
`stateAt_modrev_persist`, `stateAt_modrev_det`, `stateAtPfx_agree` and the `stateAtPfx_*`
versions, `stateAt_of_prefix`, `LogOk.snoc`, `NoDupKeysPerRev.snoc`(`_iff`),
`keys_nodup_iff_check`, `sel_keys_nodup`; unit 0 mvcc's `txnReadWrite.wp_*`.

**The premises of the results**, in one list: the sole writer (`soleWriter γ log`: every
revision token is the apply thread's); the context `context.TODO()` or an `isContext` that is
never done (`neverDone`); no compaction (mvcc's `isStore` fixes `compactMainRev = -1`); leases as
the lessor's `Lookup` says (`isTxnLessor`), and for `Txn` every lease of the state known
(`leasesKnown`); `LogOk` (the log well formed, its length and every revision's change count below
`2^63`); for a range a valid sort target (`validSortTarget`), a small sorted selection
(`sortSmall`; `LogSmall` of the log for `Range`), well-formed key-values (`kvOk`), not
`cutEarly`; a `DeleteRange` of fewer than `2^63` keys; `NoDupKeysPerRev` (a revision writes a key
at most once), which a commit keeps exactly when the transaction passes etcd's `checkIntervals`;
`DelsPresent` (a commit's deletes name present keys, for `LogOk.snoc`); `OpsStable` for `txn_runTxn` with nested transactions
(every nested verdict the same before and after the operations preceding it); `TxnPre` (the
log's room for the commit, `OpsOk` of the chosen branch: ranges at revision `0`, ignore-flag
puts whose key exists where they run).

**Open ends**: the client model's `applyTxnOp (.txn …)` (`cache/v3/InvEtcdTxn.lean`) is wrong for
nested transactions (it evaluates a nested comparison after the operations before it; etcd
before the transaction), kept because leasing's proofs use it (`txn_runTxn` carries the
agreement as `OpsStable`); traceutil's `EnsureTrace` axiom needs an `isContext`, so `Txn` is not
stated at the literal `context.TODO()` (the apply package needs `EnsureTrace` of `TODO()` or a
`neverDone` descriptor for it); the server's `Link.lean` and mvcc's both define
`binary.bigEndian.wp_PutUint64`, a clash once the apply package links both; mvcc's
`traceutil.Trace.Step` axiom claims a return on a `nil` trace (Go dereferences it), harmless while
every trace passed is non-nil.

**Issues found** (`issues/`, all in `issues/README.md`): `etcd-txn-empty-requestop` (`Txn`
panics on a `RequestOp` with an empty oneof; unit 0), `etcd-range-sort-none-limit` (a sort by a
non-key target with order `NONE` and a limit is cut by the limit; unit 2),
`etcd-range-keys-only-lease` (keys-only ranges drop the lease unless sorted by value; unit 2),
`etcd-txn-delete-then-ignore-put` (a from-key delete then an ignore-flag put of a deleted key
panics in the apply loop; unit 3), `etcd-txn-nested-compare-snapshot` (nested comparisons see the
state before the transaction, undocumented; unit 3).

**Fix branches (2026-10-12).** Three of them are bugs with fix branches on the fork, one
signed-off commit each off upstream `main` (f061acd09), with tests, and their drafts rewritten
for etcd-io/etcd: `txn-delete-then-ignore-put` (d9ba0e03c: `checkIntervals` reads a `"\x00"`
range end as the affine infinity, as `mkGteRange` does, so the transaction is rejected as a
duplicate key; restart runs with the real binaries show the crash is permanent: the entry is in
every member's WAL beyond the stored consistent index and replays on every restart, with a fixed
binary too, so one write-permitted request takes the whole cluster down for good),
`range-sort-none-limit` (7362d4129: a `rangeSortOrder` shared by `rangeLimit` and
`sortRangeResults`, so the limit is dropped exactly when the results are re-sorted;
`IsDefaultOrdering` unchanged, since `RangeStream` relies on it) and `range-keys-only-lease`
(01e522548: the server no longer requests mvcc's index-only read, since the lessor's item map
holds a key's lease now, not at the revision read; this reverts the speedup of upstream PR
#21791, which upstream may prefer to keep by documenting the omission instead). Found while
fixing the sort cut: `etcd-rangestream-sort-none` (`RangeStream` with a non-key sort target and
order `NONE` returns duplicated and missing keys; outside the verified code, no fix branch).

## Merge: mvcc into lean (2026-10-11)

Branch `mvcc` (25 commits: the KV core's translation, model, key index, tree index, read and
write transactions, `NewStore`) merged with `origin/lean` (`672501acc`: the recipes package,
the register's cluster driver, Perennial `e4e126e46`), in the `mvcc` worktree, then fast-forwarded
onto `lean`.
- **Conflicts**: five files, all bookkeeping: the Perennial pin (`lakefile.toml`,
  `lake-manifest.json`: `lean`'s `e4e126e46` contains mvcc's `bf935cbd5`, so it wins),
  `etc/gen-link.py` (both sides' modes kept: `--mvcc`, `--recipes`, `--register`,
  `--skip-unproved`; the `[StorageModel GF]` and the cache-assumptions binders both emitted),
  the two notes (both sides' sections kept; the pin history spliced).
- **One `AllG`** (Perennial `cb6a5921e`, in `lean`'s pin; see "Perennial `cb6a5921e`: one
  `AllG`"): the `[AllG GF]` section variable next to `[hG : HeapGS …]` dropped from the 88
  files mvcc had added with it (a `sed`), and from `muInv`'s binders (`InvStore.lean`);
  `Link.lean` regenerated (its results no longer take `[AllG GF]`). No proof changed.
- **The etcd pin** moved on `lean` from `0fc6f23b1` to `bc8b52a50` (one commit, names only in
  the recipes package): the packages mvcc translates are identical, `etc/goose.py --check`
  passes at the merged pins with no regeneration.
- **Two fixes the one-`AllG` bump needed** (as on `lean`, "Perennial `cb6a5921e`: one `AllG`"):
  `leaseKnown_persistent` and `isLessor_persistent` state their predicate with `(GF := GF)` (the
  `[AllG GF]` local instance used to fix `GF`; `HeapGS ?hlc ?GF` is not tried), and
  `mkOk_loc_inj` (`InvStore.lean`), whose statement mentions no `GF`, gets its own binders
  (`[FfiSyntax] [GoLocalContext] [GoGlobalContext] [go.Semantics]`) outside the section: as a
  section theorem its `HeapGS`/`Assumptions` binders were undetermined at every use.
- **Checked** (after a full build, 2450 jobs): `etc/goose.py --check` at the merged pins;
  `etc/tcb-report.py --check` matches (56 axioms, 1 sorry: the two sides' lists merged
  textually, disjoint); every collection matches (btree 0, cache 10, concurrency 12 and the
  sorry, leasing 8, mvcc 13, raft 1, recipes 11, register 1, server 26 axioms);
  `etc/verified-code.py`: etcd 431 of 3599 functions verified, 4367 of 45570 lines (mvcc 58 of
  155, 655 of 2073).

## mvcc: the KV core, phase one (2026-10-10)

Started the verification of etcd's `server/v3/storage/mvcc` KV core (`notes/decisions.md`,
"mvcc: the log of changes as the model"), on branch `mvcc` (worktree `/shared/etcd-grove-mvcc`;
another session was committing `client/v3/leasing` to the main checkout at the time).

- **Translation**: the KV core with bodies (`Code/go_etcd_io/etcd/server/v3/storage/mvcc.toml`:
  `revision.go`, `key_index.go`, `index.go`, `kv.go`, `kv_view.go`, `kvstore_txn.go`,
  `metrics_txn.go`, the promoted methods of embedded fields), `pkg/v3/schedule` and prometheus's
  `client_golang/prometheus` names-only (`etc/goose.py`). It needs Goose's range over an
  integer and `float64(n)` of an integer as an uninterpreted function, written in
  `/shared/perennial-mvcc` on Perennial `7c93f27aa`, rebased on upstream's `7cea8cc26` (the
  panic branch) when it landed, pushed as `114b847ff` and `bf935cbd5` (2026-10-10 evening) and
  pinned here as `bf935cbd5`; `lean` (panics and `recover`, `client/v3/leasing`) merged at the
  same time, so `etc/goose.py --check` passes with the pinned translator (the etcd pin
  `0fc6f23b1` is upstream's `goose-lean`).
- **Model** (`Proof/go_etcd_io/etcd/server/v3/storage/mvcc/Model.lean`): the log of changes,
  `stateAt` through the client model's `putKv`, the key index `indexOf (evsOf log)` with
  `kiPut`/`kiTombstone`/`kiGet`/`kiFindGen`/`genWalk` mirroring the code, the key bucket
  `bucketOf log` with the opaque `kvEncode`, `revBytes`, `LogWf`; the pure lemmas the proofs use.
- **Proved** (specs in `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/`, proofs beside the shared
  `Base`/`Model`/`Defs`; `Link.lean` by `etc/gen-link.py --mvcc` from
  `etc/link-lean-first-mvcc.txt`; `Results.lean` prints the axioms; collection
  `etc/tcb-collections/mvcc.txt`): `Revision.GreaterThan`, `generation.isEmpty`,
  `generation.walk`, `keyIndex.Less`, `keyIndex.isEmpty`, `keyIndex.findGeneration`,
  `keyIndex.get`, `keyIndex.put`, `keyIndex.tombstone`: 9 of the core's 72 functions, all
  sorry-free, resting on no axiom of this repository (the error and metrics variables are
  package facts, `Base.lean`).
- **The model's main theorem** (`LogLemmas.lean`, `kiGet_indexOf`, sorry-free, standard axioms
  only): for a well-formed log (`LogWf`, length and every revision's change count below 2^63),
  what the index built from the log's events answers of a key at a revision (`idxGet` then
  `kiGet`) matches the key-value of the state at that revision (`KvMatch`): both absent, or the
  key-value's mod revision, create revision and version are the answer's, and the bucket holds
  the key-value at the answer's revision (`BucketHas`: `changeKv` of that change). Proved
  key by key (`kiOfKey`, the key's events folded; `indexOf_rep` links it to the btree-model
  index), by induction over the log's revisions and, within one, over its changes
  (`rev_step`), with `Lemmas.lean` (what `kiGet` answers after `kiPut`/`kiTombstone`, below
  and at or above the new revision, under `KiWf`/`KiAbove`; `kiGet_top`).
- **`index.go`, the point operations** (2026-10-10, branch `mvcc`): the btree's
  `ownBTree_combine` (`btree/Combine.lean`, keys determined by items) and the cache wrapper's, so
  a tree can be a `RWMutex` resource; `Hist.lean` (the index's history with commit markers,
  `kiGet_reader`, the writer's facts, finding/inserting entries by key, `kiLastEmpty_false_of_del`);
  `InvIndex.lean` (`ownTree`, fractional; `idxLockInv`, `isTreeIndex`, `idxReader`, `idxWriter`,
  `idxCert`, `idxWriter_commit`, `reader_answer`). **Proved and linked** (sorry-free):
  `newTreeIndex`, `treeIndex.keyIndex`, `unsafeGet`, `Get` (a reader with the certificate of a
  committed log reads what it determines), `Put` and `Tombstone` (the writer, for the pending
  revision's next change). The specs of `Get`/`Put`/`Tombstone` are stated at
  `HeapGS HasLC.hasLC` (later credits) with the cache's btree interface assumptions
  (`etc/gen-link.py` adds `[go_etcd_io.etcd.cache.v3.Assumptions]` when a spec has it).
  **`KeyIndex` and `Insert`** (2026-10-11, the last of `index.go`; `restore` and the tests are
  their only callers, on a private index): under the live index's invariant, the history fixes
  the tree's keys and their indexes, so `KeyIndex` (a reader with `idxKnows`) returns the key's
  pointer (`kiKey`, persistent) or `nil`, present whenever the reader's log gives the key an
  index (`kiOfKey … ≠ kiEmpty`), and exactly then for the writer's knowledge; `Insert` (the
  writer, an owned key index holding the key's `kiOfKey`, not empty) always *replaces* the key's
  entry and returns the old one, owned: inserting a new key is not a step of the live index
  (decisions.md, "`KeyIndex` and `Insert` under the history"). Lemmas:
  `idxGet_indexOf_eq_none_iff` (a key has an entry iff its `kiOfKey` is not `kiEmpty`),
  `ownTree_entry` (an entry's pointer is not `nil` and carries its key), `idxKnows_writer_events`.
- **`index.go`, the range reads** (2026-10-10, branch `mvcc`): `unsafeVisit` (the entries in
  `[key, end)` in key order, `rangeEntries`, through the btree's `AscendGreaterOrEqual` model
  spec and a visitor triple `visitSpec`, the visited entries lent to the caller's closure by
  index), `Revisions`, `CountRevisions`, `Range`: a reader with the certificate of a committed
  `log` and `atRev` below its length gets the keys of the range with a revision at `atRev` in
  `log`, in key order (`rangeAnswers`; the one key if `end == nil`), at most `limit` of them if
  positive (`rangeTaken`), and the count (`rangeTotal`: all of them if `withTotalCount`, else at
  most `limit`); `Range`'s `keys` are the key indexes' own key slices, read-only (`ownKeys`).
  The model: `rangeAt` (the index's answers in a range), `reader_range` (a reader's range
  answer is its certified log's: the certified keys stay, `kiOfKey_ne_mono`, sorted subsets
  are sublists, the later keys answer nothing below the certified length), the visiting
  (`fromKey`, `belowEnd`, `filter` as `takeWhile` on sorted entries) and the visitors'
  accumulation (`entryAnswers` of a prefix, `takeLimit`/`totalOf`/`reached` and the limit's
  arithmetic), in `Hist.lean`; the proofs share `ReadLemmas.lean` (`kiGetVal_pairs`,
  `entries_not_empty`, and the two Boolean conditions of the visitors as triples on the Goose
  expressions, `wp_reachedLimit`, `wp_stopCond`, so each visitor has one continuation per
  outcome). All four sorry-free and linked; `Results.lean` prints 20 results and the two model
  theorems; the collection's baseline is still empty (no axiom, no sorry).
- **`revision.go`, the encoding** (2026-10-10 evening, branch `mvcc`): the eight functions
  proved (`RevBytes.lean`, shared: the model's `revBytes r tomb` split as the encoder leaves it,
  `bucketKeyBytes`, `isTomb`, the list lemmas of each step). `newBucketKey`, `NewRevBytes` (17
  zero bytes, capacity 18), `isTombstone`/`IsTombstone` (`isTomb`: 18 bytes, the last `'t'`),
  `BucketKeyToBytes` (into a buffer of 17 or 18 bytes with its capacity: the 17 bytes of the
  revision, then for a tombstone the mark appended or written over the 18th; a non-tombstone
  keeps the 18th), `RevToBytes` (the same, no mark), `BytesToBucketKey`/`BytesToRev` (the 17
  bytes of a nonnegative revision and at most one byte after them, as the model's `revBytes`
  values are; a tombstone iff that byte is the mark; any other input panics, outside the spec).
  The callees are encoding/binary's `BigEndian.PutUint64`/`Uint64`, the server's trust-boundary
  axioms (`Spec/encoding/binary/`, `u64Be` of `InvCindex.lean`), now also in the mvcc list:
  the encoders and decoders rest on those two axioms, the rest of mvcc on none. Proof notes:
  a slice expression `b[i:j]` evaluates to `slice.slice b V i j` behind a bounds `if`
  (`simp only [Hb, _root_.and_self, ite_true]`), the parts come from `ownSlice_slice ... .1`
  and go back by `ownSlice_combine` and `ownSlice_trivial_slice` (as the register's
  `encode`); `wp_if_destruct` wants a `decide` or a Boolean variable, a field such as
  `bk.tombstone'` needs `cases h : bk.tombstone'`; a closed `decide` of a word equality
  reduces by `simp (config := { decide := true }) only [hl]` after `hl : s.len = W64 17`.
- **The read transactions, opened and closed** (2026-10-11, branch `mvcc`): `InvStore.lean`
  (design: decisions.md, "The transactions: the store's locks and the backend contract"): the
  backend's contract for the `Key` bucket (`keyReadSnap rt m`: a `ReadTx` over a snapshot `m`,
  `UnsafeRange(Key, k, nil, 0)` reads `m`'s entry; `isKeyBackend b View`:
  `ConcurrentReadTx()`/`ReadTx()` return a snapshot of the caller's `View q m`), the locks
  (`s.mu` holds nothing, `muInv`; `s.revMu` holds `currentRev = log.length - 1`,
  `compactMainRev = -1`, `idxCert γ.idx log` and the bucket's ghost-map authority
  `bucketView γ q (bucketMap log)`, `revMuInv`), `isStore` (persistent: backend, index as the
  `index` interface over `isTreeIndex`, logger, the two guards), `storeReader` (a reader slot
  of each lock and the index's), `storeTxnReadIs` (the `storeTxnRead`'s fields, read-only) and
  `isTxnRead mw s γ log rev` (the `metricsTxnWrite` wrapper, owned, around `txnReadWrite`
  around the `storeTxnRead`, with `s.mu` held shared). Proved: `store.Read` (under `s.revMu`
  shared: the snapshot of the committed log's bucket, `rev` its last revision; both modes),
  `storeTxnRead.End` (the tokens back), `storeTxnCommon.FirstRev`/`Rev` (the fields; the
  promoted calls load through `txCommon tr`), `newMetricsTxnRead`. Trust-boundary axioms (not
  yet linked): `traceutil.Trace.Step` returns; `proto.Unmarshal` of `kvEncode kv` into a
  `*mvccpb.KeyValue` sets its fields to `kv`'s and returns `nil`. Proof notes: a nested
  struct's points-to cannot be made persistent as a whole (`ipersist` wants a `DFractional`
  points-to: split it with `iStructNamedPrefix` and persist the fields), and only while the
  goal is a `WP` (a basic update needs a modality to eliminate into); an Iris hypothesis with
  `∀`s is instantiated by `ihave H' := H $$ %x %y` before `wp_apply H'`; a persistent
  predicate about to be destructed is kept with `ihave #H0 : P $$ []` then `· iexact H`; an
  abbreviation of an address (`structFieldRef`) must live in a section with
  `[GoSemanticsFunctions]` (as `idxMuAddr`), else its uses leave the lock lemmas' instances
  undetermined; a lock resource with no content takes the semantics' instances explicitly.
- **The read transaction's range** (2026-10-11, branch `mvcc`): `storeTxnCommon.rangeKeys` and
  `Range` proved and linked. The spec (`rangeOutcome`, `InvStore.lean`): with the store, the
  transaction's read-only fields (`storeTxnReadIs`: the snapshot `m ⊇ bucketMap log`, the
  certificate, `rev = log.length - 1`), a reader slot of the index, a context and the two key
  slices, a range at `ro.Rev` (`rangeRev`: `rev` if at most 0) returns either the future-revision
  error (`rev < ro.Rev`: `ErrFutureRev`, a result with `Count = -1`), or, for a full read, `nil`
  and an error once the context is done (the `select` on `ctx.Done()` in the loop), or `nil`
  error and the result: `CountOnly` the count of `rangeAnswers`, else `Rev = rev`,
  `Count = rangeTotal` and `KVs` the `rangeTaken` answers in key order (`rangeKvs`: each
  `*mvccpb.KeyValue` is the key-value `findKey` gives in `stateAt log` at that revision, with
  `kvPtrIs`: a fast-keys-only read fills the key, create/mod revision and version, a full read
  also the value and lease, read from the bucket). The model lemma `rangeAnswers_kv`
  (`BucketLemmas.lean`): every answer of `rangeAnswers` at a revision of a well-formed log has
  its key-value in `stateAt`, with the answer's revisions and version, and the bucket maps the
  answer's revision's bytes to its encoding (from `kiGet_indexOf`'s `KvMatch` and `BucketHas`;
  the bucket's functionality from `revBytes_inj`). Callees: `treeIndex.CountRevisions`/`Range`/
  `Revisions`, `sliceCapWithLimit` (proved, `capWithLimit`), `NewRevBytes`, `RevToBytes`, the
  backend's `UnsafeRange` by the contract `keyRangeSpec` in `storeTxnReadIs`, and the two
  trust-boundary axioms now linked: `traceutil.Trace.Step` and `proto.Unmarshal` (the mvcc
  collection's baseline has them with the two BigEndian axioms). Proof notes: the Go `range`
  over an integer and over the slice are `wp_for` loops whose invariant names every conjunct
  (an unnamed invariant lets `wp_if_destruct` pick a `decide` inside the postcondition); the
  non-blocking `select` is `chan.wp_select_nonblocking_alt` with
  `context.isContextDone_nonblocking_receive` (as `Election.Campaign`), the loop's resources
  passed through its `P`; the fixed hypotheses are framed by name after `wp_for_post` (a bare
  `iframe` instantiates the invariant's existential wrongly); `hif` from `wp_if_destruct` is
  sometimes `#(decide c) = #true`, sometimes `c` (`first | exact Hif | …`); the long proof needs
  `set_option maxHeartbeats 4000000 in`.
- **The wrappers** (2026-10-11, branch `mvcc`): `metricsTxnWrite.Range` (counts, forwards:
  `isTxnRead` kept, `rangeOutcome`) and `End` (the counters and the gauge of `metrics.go` by
  the package facts `counterSpec`/`gaugeSpec`, then the deferred `storeTxnRead.End`: the
  reader's tokens back, `storeReader`); `readView.FirstRev`/`Rev`/`Range` (`isReadView rv s γ`:
  the view's `kv` is the store; a transaction opened by `store.Read` around the read and
  closed by the deferred `metricsTxnWrite.End`; `Rev` and `Range` return with the certificate
  `idxCert γ.idx log` of the log they read, `rev = log.length - 1`). `traceutil.TODO` is a new
  trust-boundary axiom (returns a trace). The promoted methods (`txnReadWrite`'s from its
  `TxnRead`, `storeTxnRead`'s from `storeTxnCommon`, `metricsTxnWrite`'s from its `TxnWrite`)
  are `MethodUnfold` lambdas in the translation, not functions: the proofs unfold them in
  place, `rw [method_unfold (t := go.GoType.PointerType T.ty) (m := go!"M")]; wp_call`, naming
  the type and method because a bare `wp_method_call` rewrites the first `methods` term it
  finds, which may be the one stored in the `defer` cell or a counter's in a hypothesis.
- **The write transactions** (2026-10-11, branch `mvcc`; the design: decisions.md, "The write
  transactions: the batch lock's resources, the backend's write path, the lessor"). Specified
  at the checkpoint `628f69632` (`InvStore.lean`: `batchTxSpec`/`isBatchTx` and `BatchTx()` in
  `isKeyBackend`, `isLessor`/`leaseKnown`, `writerRes` under the batch lock, `revToken` and the
  budget `ownTokAuth γ.revs`, `revMuInv` with halves of `currentRev` and `γ.clog`,
  `storeTxnWriteIs`/`isTxnWrite`, `changesAre`, `TxnKind`/`isTxn`/`txnEndPost`, `commitLog`,
  `isWriteView`; `InvIndex.lean`: `IdxKnow`/`idxKnows` for the index readers, `idxKnows_facts`,
  `idxWriter_wf`; `BucketLemmas.lean`: `writeRev`, `delKeys`, `pendPuts`, `bucketMap_append`,
  `changeKv_put`, `LogWf'.append_change`, ...), then proved and linked: `store.Write` (a token
  for the batch lock's resources), `storeTxnWrite.put` (the index read by the writer, the
  bucket's `UnsafeSeqPut`, the index's `Put`, the `changes` append, the lease detached and
  attached), `Put`, `delete`, `deleteRange` (the keys at `writeRev`, each deleted in a loop),
  `DeleteRange`, `End` (the commit under `s.revMu`: both halves of `currentRev`, the ghost
  log, the index writer's commit, the token back, the batch `Unlock`'s write-back), `Rev`,
  `Changes`; `metricsTxnWrite.Put`/`DeleteRange`/`End` (over `TxnKind`), `writeView.Put`/
  `DeleteRange`; `readView.*` and `treeIndex.Get`/`Range` reproved for the changed specs. Three
  new trust-boundary axioms: `proto.Marshal` (the converse of `Unmarshal`), `zap.Error`,
  `zap.Logger.Error`; the mvcc collection's baseline updated. `changesAre_snoc` (`InvStore.lean`)
  is the shared lemma of `put` and `delete`. Proof notes: a spec held as an Iris hypothesis with
  `∀`s is applied as `wp_apply H $$ %x %y [$H1 $H2]` (the `%_` left to unification by the framed
  hypotheses; an argument nothing determines, `GetLease`'s item, given explicitly); an `if
  err != nil` after a call whose spec returns `nil` is resolved by `wp_auto` (no
  `wp_if_destruct`), an unknown error is `cases err with | nil => … | ok e => …`; a `&T{...}`
  literal is allocated by `wp_auto` (`«$r0_ptr»`, no `wp_alloc`), and the key-value a spec
  takes for it is a literal record with the Goose literal's fields (`createRev := 0`, not
  `W64 0`, not `zeroKv k`: the frame does not unfold a definition or convert the literals); a
  record literal continued on a second line must not contain a type ascription `(x : Int)` (it
  does not parse: `W64 ilog.length`); a predicate packaged before the code's last reads of the
  struct (`tw.s` for the lessor) is built as a wand over the struct's points-to and applied at
  each return (`iapply HΦ; iapply Hpack; iexact Htw`); `rw … at H` on an Iris hypothesis is
  `rw` on the goal (the context is part of it); two halves of a points-to join by
  `((typedPointsto_dfractional _ _).dfractional _ _).2` and split by `.1` after `own_half_half`
  rewrites `DFrac.own 1` (an `icombine … as` leaves a plain conjunction); `icombine … gives`
  of the token authority and a token needs `revToken` unfolded; `isStore`'s `ti` shadows the
  transaction's after `iNamedSuffix` (`icombine Hidx HidxS gives %h; mkOk_loc_inj; subst`); a
  range loop's index is `i_ptr`/`i`, its loop variable's cell is in the invariant (the body
  stores it), and after `wp_for_post` the goal is the fixed resources then the invariant:
  `iframe` the fixed ones by name, then `iexists`; `word` failed with "unknown free variable"
  on `0 ≤ sint.Z (W64 n) ∧ sint.Z (W64 n) < (l ++ [x]).length` (an `sint.Z (W64 n) = n` step
  by `BitVec.toInt_ofInt_eq_self`, then `omega`); `trace_state`'s output in a `lake env lean`
  log has no header (it reads as a second goal of the preceding error).
- **The writer's range read** (2026-10-11, branch `mvcc`; design: decisions.md, "The writer's
  range read"): `storeTxnWrite.Range` proved and linked (an Opus subagent's work). The bucket view
  is split (`revMuInv` half, `writerRes`/`storeTxnWriteIs` half, `bucketView_halves`; `End`
  joins them), `batchTxSpec` reads under the lock (`UnsafeRange` sees the pending puts) and its
  `Unlock` with puts takes a wand building `W` from the written-back view; `rangeKeys`'s spec
  is over the `storeTxnCommon` fields at a fraction, `keyReader rt m R` (`keyReadSnap_reader`,
  `batchTx_reader`), `idxKnows` and `0 ≤ rev < log.length`; `treeIndex.Revisions`/
  `CountRevisions` take `idxKnows` as `Get`/`Range` do; `txCommonW`, `idxKnows_wf`,
  `writeRev_commitLog`. The result: `rangeOutcome` at `ilog ++ [pend]` and `writeRev ilog pend`.
  No new axiom (the mvcc collection: 8 axioms, 0 sorries). Proof notes: the whole-struct
  points-to of `storeTxnWriteIs` is split with `iStructNamedPrefix` for the promoted
  `rangeKeys` and joined back with `typedPointsto_combine`.
- **The store's constructor** (2026-10-11, branch `mvcc`): `NewStore` translated (`kvstore.go`;
  `restore` and everything else it calls untranslated) and proved and linked, on a fresh backend.
  The spec: the caller gives the empty bucket view `ghostMapAuth γb 1 ∅` (the fresh-backend
  assumption), the backend's contract for every store location and names with that bucket name
  (`writerRes s γ` is the store's choice), and the lessor at its own ghost name `γl`; it returns
  `isStore s γ` at the initial log `[[], []]` (`currentRev = 1`), the two views, every reader slot
  (`storeReader`) and `2 ^ 63 - 5` revision tokens. A `nil` logger is replaced by `zap.NewNop()`'s;
  `cfg` is not modelled. Contract changes (`InvStore.lean`): `batchTxSpec` gains
  `LockOutsideApply()` (`Locked []`, **no** resource: the batch lock holds `writerRes` from
  `NewStore`'s first `Unlock`, the no-puts triple, on) and `UnsafeCreateBucket(b)` (keeps the
  puts); `isKeyBackend` gains `ForceCommit()`; `isLessor le γl` is over the lessor's own `GName`
  (`leaseKnown γl id`, the specs of `put`/`Put` take `leaseKnown γ.leases`) and gains
  `SetRangeDeleter(f)` (the closure over `store.Write` is opaque; the lessor's later calls of it
  are outside the model); `revMuInv` is `Fractional` (for `sync.init_RWMutex`);
  `idxWriter_commit` no longer needs `ilog ≠ []` (the first two commits). `mvccInit` gains the two
  configuration defaults `NewStore` reads (package variables, any values). Five new axioms:
  `zap.NewNop` (non-nil), `schedule.NewFIFOScheduler`, `NewHashStorage`,
  `schema.UnsafeCreateMetaBucket` and `store.restore` on a fresh backend (the identity on the
  verified state; its store of `1` into `currentRev` is modelled as no write, since `NewStore`
  holds only half of `currentRev` then: the other half is the batch lock's; in the code that
  write is protected by `s.mu` held exclusively, which `muInv = True` does not express). Proof
  notes: `wp_join` for the `lg == nil` and `cfg` defaults (the cases join at the logger's and the
  config's points-to); `wp_apply` of the batch transaction's triples (its token `Locked` a
  variable from an existential) failed with "unknown free variable" here (not in `store.Write`):
  `wp_bind (App (Val #(methods bt.ty _ bt.v)) (Val #()))` then `iapply` (cause not found); the
  store's names are an `obtain`ed variable with equations, rewritten into the context
  (`rw [← hγi, …]`), not a `let`.
- **`key_index.go`'s panics** (2026-10-11): `zap.Logger.Panic` is an axiom panicking with its
  message (`RET r; ⌜r = PanicV #msg⌝`, Perennial's panic outcome; a nop logger panics too:
  `Panic`/`Fatal` entries are always written) and `zap.Logger.Fatal` an axiom that never
  returns (`os.Exit(1)`; as Perennial's `AngelicExit`, divergence: postcondition `False`); no
  verified function reaches `Fatal` (the protobuf axioms never fail), so it is not linked and
  in no baseline. `keyIndex.put`, `tombstone` and `get` are now specified over all inputs
  (decisions.md, "`key_index.go`'s panics as outcomes"): the former precondition is the normal
  case, and otherwise the result is the panic with zap's message and the key index unchanged
  (`tombstone`, in the code's order: empty → its panic; last generation empty →
  `ErrRevisionNotFound`; revision not above `modified` → `put`'s panic; `ki.gens ≠ []` stays a
  premise, an index out of range being stuck). They take `⌜lg ≠ null⌝` (so does
  `treeIndex.unsafeGet`; `isTreeIndex` records it, `newTreeIndex` requires it, `NewStore` has
  it) and `kiKey p k` where the panic reads the key. The callers (`treeIndex.Put`/`Tombstone`/
  `unsafeGet`, the range reads' visitors) discharge the case (`simp only [h, ↓reduceIte]` on
  the `if` under the result's binder, then `subst`); the panic unwinds through `wp_auto` with
  nothing special. Baselines: 57 axioms (`zap.Logger.Panic`), the mvcc collection 16
  (`zap.Int64`, `zap.String`, `zap.Logger.Panic`); verified-code figures unchanged.
- **Not yet**: the restore and the compaction (out of scope).
  `etc/verified-code.py` (2026-10-11, after `treeIndex.KeyIndex`/`Insert`): 58 of the package's
  155 functions verified, 655 of 2073 lines; of the KV core translated with bodies (661 lines),
  99% of the lines; `NewHashStorage` and `restore` count as assumed (`kvstore_txn.go` all 17
  functions, `index.go` 12 of 15 (the rest is the compaction), `key_index.go` 8 of 18,
  `revision.go` all 9, `kvstore.go` `NewStore`).
- **Perennial `bf935cbd5` pinned, `lean` merged** (2026-10-10 evening): the two Goose/semantics
  commits were rebased on upstream's `7cea8cc26` (panics and `recover`; no conflict; goose's
  tests, Perennial's build and the examples' regeneration checked) and pushed; the pin moved
  from `7c93f27aa` (via `lean`'s `7cea8cc26`) and `lean` (`client/v3/leasing`, the panic
  adoption, 15 commits) was merged (`fb427fb05`: both sides' `gen-link.py` modes and notes
  kept). `etc/goose.py --check` passes; the only translation that differed was `lean`'s
  regenerated `client/v3/concurrency` (`with_defer_recover:`). Two fixes for the new Perennial:
  `treeIndex.Get`'s proof stalled at the function's `return` (every pure `let` step now needs
  its value not to be a panic, `v.isPanic = false`, proved automatically for `#x` and
  constructors but not for an opaque `val`), so `ReadLemmas.kiGetVal_pairs` gives the
  4-tuple's components typed (`#m`, `#c`, `#v`, `#i`); and `etcdserver/BaseApply.lean`'s
  `storage/mvcc` instance, `True` from the names-only translation, failed once the
  translation had bodies (`define_is_pkg_init` wants prometheus's instance; the whole-repo
  build had not been run on this branch), so `BaseApply` now imports mvcc's `Base.lean`
  (which has `mvccInit` and the instances of traceutil, lease, schedule, prometheus) and its
  three duplicates (mvcc, traceutil, lease) are gone.
- **Incident**: a `lake env` call in the worktree, whose `.lake/packages` was then a symlink to
  the main checkout's, found the main checkout's manifest pointing at a Perennial revision
  (`1eabc2c47`, the other session's unpushed commit, with a non-GitHub remote) and re-cloned
  `.lake/packages/perennial`, deleting that clone and its build cache. Restored at the pinned
  `7c93f27aa` with the cache copied earlier; `1eabc2c47` exists in no local repository. The
  worktree now has its own `.lake/packages` (copies; `perennial` a clone of
  `/shared/perennial-mvcc` with the GitHub remote URL).
- **Environment**: this machine had no Lean or Go; elan (`~/.elan`, toolchain `v4.34.1`) and Go
  1.27.1 (`~/.local/go`) were installed user-locally, not on `PATH`.
## Recipes (`client/v3/experimental/recipes`)

Plan: `decisions.md`, "Recipes: the client contracts reused, the queue's claim, two prefixes as
one". Units 0 to 4; unit 0 (translation, scaffolding, the reproductions), unit 1 (the bundle,
`key.go`, `client.go`, `watch.go`), unit 1b (the three key helpers unit 1 left), unit 2 (the barrier,
the queue, the priority queue, the revision token) and unit 3 (the RWMutex, the double barrier)
are done and merged; the package is verified ("The whole package").

### Unit 0: translation and scaffolding (2026-10-11)

- **The Gooseable commit** `bc8b52a50` on the fork's `goose` branch (pinned in `etc/goose.py`),
  as concurrency's `207c8f747` and leasing's `0fc6f23b1`: Goose as pinned (Perennial
  `7cea8cc26`) rejects the package with 3 errors, all the known alias issue (`[impossible(go)]:
  expected (pointer to) struct type for base of selector, got *go.etcd.io/etcd/client/v3.Event`
  at `watch.go:49` (`ev.Type`), `queue.go:76` and `priority_queue.go:79` (`ev.Kv`)), and the
  calls of methods promoted from `*clientv3.Client`'s embedded interfaces (`c.Watch`,
  `client.Get/Put/Delete`) translate to `MethodResolve (*Client) "Get"`, which has no
  unfolding; a `*Client` passed as a `clientv3.KV` (`newKey(b.client, ...)`,
  `claimFirstKey(q.client, ...)`) dispatches to the same. The commit (7 files, +31/-22) binds
  `*clientv3.Event`s to `*mvccpb.Event`, calls through the fields (`c.Watcher.Watch`,
  `client.KV.Get/Put/Delete`) and passes `client.KV` where a `KV` is expected. One behavior
  difference, for a `Client` whose `KV` field is nil (no real client): `RemoteKV.Delete` returns
  `nil` where the original panics.
- **Configuration**: `Code/go_etcd_io/etcd/client/v3/experimental/recipes.toml` translates
  the package in full (`translate = ["*"]`, `imports = ["*"]`), listed in `etc/goose.py`;
  `client/v3.toml`: bodies for `WithFirstRev`, `WithFirstKey`, `WithLastKey`, `WithMaxModRev`,
  `WithMinModRev` (the recipes' get options; `WithMinModRev` is not called by the recipes but
  came with the batch); `Code/go_etcd_io/etcd/client/v3.lean` regenerated (+79 lines, bodies
  and unfoldings only). Everything else the plan suspected translates: `fmt.Sscanf(..., "%d",
  &newSeqNum)` (a call of Perennial's names-only `fmt.Sscanf` with `[]any{&newSeqNum}`), `for
  wresp := range wc` (`chan.forRange WatchResponse.ty`), `EphemeralKV{RemoteKV}` (below),
  `append(WithLastRev(), WithMaxModRev(...))` (`go.append` of a slice literal), the `...`
  spreads, `errors.Is` (`FuncResolve errors.Is`), `strings.Split`.
- **The translation, for the proof writers**: package namespace
  `go_etcd_io.etcd.client.v3.experimental.recipes`, assumptions class `...recipes.Assumptions`
  (imports context, mvccpb, clientv3, errors, concurrency, fmt, strings, time). `EphemeralKV`
  is a struct with one field `RemoteKV` (a `RemoteKV` value, not a pointer); `&EphemeralKV{*k}`
  is a `GoAlloc` of a composite literal of the loaded `*k`; its promoted methods
  `(*EphemeralKV).Delete/Key/Put/Revision/Value` have `MethodUnfold` instances
  (`EphemeralKV.TypeAssumptions.ptr_Revision_unfold`, ...) to `(*RemoteKV).M` applied to
  `StructFieldRef EphemeralKV.ty "RemoteKV" r`; `ek.rev` is `StructFieldRef RemoteKV.ty "rev"`
  of `StructFieldRef EphemeralKV.ty "RemoteKV"`. `waitEvents`'s loop is `chan.forRange
  WatchResponse.ty` over the `WatchChan`, the inner one `slice.forRange`; its `return ev` is
  `doReturn` out of both. `WaitEvents`/`WaitPrefixEvents` `defer cancel()`. The functions
  are `newKey`, `newKV`, `newUniqueKV`, `putNewKV`, `newSequentialKV`, `newEphemeralKV`,
  `newUniqueEphemeralKey`, `newUniqueEphemeralKV`, `deleteRevKey`, `claimFirstKey`,
  `WaitEvents`, `WaitPrefixEvents`, `waitEvents`, `NewBarrier`, `NewQueue`,
  `NewPriorityQueue`, `NewRWMutex`, `NewDoubleBarrier` and the methods `RemoteKV.{Key,
  Revision, Value, Delete, Put}`, `Barrier.{Hold, Release, Wait}`, `Queue.{Enqueue, Dequeue}`,
  `PriorityQueue.{Enqueue, Dequeue}`, `RWMutex.{RLock, Lock, waitOnLastRev, RUnlock, Unlock}`,
  `DoubleBarrier.{Enter, enteredClients, Leave}`; the errors are global variables
  (`ErrKeyExists`, ...: `GlobalVarAddr`).
- **Scaffolding**: `etc/gen-link.py --recipes` (namespace `recipes`; a clientv3 function's
  result `recipes.v3.wp_F`, concurrency's `recipes.concurrency.Session.wp_Client`, from their
  specs' own namespace, no change to the script needed) reading
  `etc/link-lean-first-recipes.txt` (every function of the package, 38, with its callees in Go
  order as a first guess, and the clientv3, concurrency and `fmt_Sscanf` lines they reach;
  self-calls, interface calls and Perennial-specified standard-library calls not listed). It
  fails now only on the missing specs (the 38, the four new clientv3 options, `fmt_Sscanf`).
  `etc/tcb-collections/recipes.txt`: the `roots` line, no baseline yet. `etc/proof_roots.py`
  and `etc/verified-code.py` need nothing (they find a package's `Link.lean`/`Results.lean` by
  directory).
- **Two findings, reproduced before any Lean** (`issues/recipes-dequeue-closed-watch.md`,
  `recipes-barrier-wait-closed-watch.md`; fix branch `recipes-closed-watch-channel`
  `0aa6c6af8`, one commit off upstream `main`, worktree `/shared/etcd-recipes-repro`; tests
  `tests/integration/clientv3/experimental/recipes/v3_closed_watch_test.go`): `waitEvents`
  returns `nil` when the watch channel closes (the client closed, or etcd cancels the watch
  for a compaction past the start revision), so `WaitEvents`/`WaitPrefixEvents` return `(nil,
  nil)`; `Queue.Dequeue`/`PriorityQueue.Dequeue` then dereference `ev.Kv` and panic (closing
  the client, or a compaction racing the watch's registration, 5 of 5 attempts), and
  `Barrier.Wait` returns `nil` while the barrier is held, `DoubleBarrier.Enter` `nil` with fewer
  than `count` entrants (`RWMutex.waitOnLastRev` and `Leave` only retry). The fix: `waitEvents`
  returns the canceled response's `Err()` or a new `ErrWatchClosed`, which the callers already
  propagate. For the proofs as shipped, `WaitEvents`'s spec takes the premise that the channel
  delivers the events before it closes (a nil dereference is stuck in GooseLang), stated on the
  watch channel.
- **Numbers** (`etc/verified-code.py --reuse`): the recipes 38 functions, 401 Go lines (at `bc8b52a50`), all
  translated, 0 verified (`double_barrier.go` 4/101 lines, `key.go` 13/98, `rwmutex.go` 6/46,
  `priority_queue.go` 3/37, `queue.go` 3/36, `watch.go` 3/32, `barrier.go` 4/26, `client.go`
  2/22); etcd 330 verified of 3599.
- **Gates**: `lake build` passes with the translation (the recipes' `Code` and
  `GeneratedProof` modules included); `etc/tcb-report.py --check` matches the baseline (42
  axioms, 1 sorry); `ETCD_SRC=/shared/etcd etc/goose.py --check` passes at the new pin.

### Unit 1: the base, the client bundle, `key.go`, `client.go`, `watch.go` (2026-10-11)

Files: `Proof/go_etcd_io/etcd/client/v3/experimental/recipes/` (`Base`, `InvRecipesClient`,
`InvRecipesLemmas`, `InvRecipesClaim`, one proof per function, `Link`) and
`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/`; deviations from the plan:
`decisions.md`, "Recipes", "Unit 1".

- **The bundle** `isEtcdRecipesClient client pfx` (persistent): the `KV` field with the
  contracts at `context.TODO()` (`isRecipesKV`: `isEtcdKVTodo`, `isEtcdTxnKVTodo`,
  `isEtcdDeleteKVTodo`, `isEtcdPutKVTodo`, `InvEtcdTxn.lean`; the recipes pass `TODO()` to every
  `KV` call, and `TODO()`'s context, never done, is not an `isContext`), and the `Watcher` field
  with `isEtcdRangeWatcherOpen` (`InvEtcdTxn.lean`): `isEtcdRangeWatcher` with the SPSC close
  predicate `False`. **The premise**: a watch channel is never closed (no compaction past a
  watched revision, the client not closed while a recipe waits); every recipes result rests on
  it, which the fixed code would not need (the two findings). No `ctx` field (unused).
- **Puts** (`InvEtcdTxn.lean`, the recipes' addition): `putTxn op` (the one-operation transaction
  `Then(OpPut(...))`), `putResult` (as `deleteResult`, through `runTxn`: no new etcd semantics),
  `isEtcdPutKV` (any `isContext`) and `isEtcdPutKVTodo`. `context.TODO()` specified and proved
  (`Spec/context/TODO.lean`: `todoCtxVal`).
- **Options** (`InvOp.lean`): `withMaxModRevM`, `withMinModRevM`; `WithFirstRev`, `WithLastKey`,
  `WithMaxModRev`, `WithMinModRev` specified and proved as the existing ones; **`WithFirstKey`**
  (`withTop(SortByKey, SortAscend)`, whose `WithSort` closure rewrites its captured `order`,
  which `WithSort.spec`/`withTop.spec` exclude) returns options needing a resource
  (`optsAtRes sl gs R`, `optSpecRes`, `optsAt_res`: the closures are called one at a time),
  proved by stepping into `withTop` and `WithSort`; `isEtcdKVTodo` takes such options.
- **Keys** (`key.go`): `RemoteKVSt` (`kv`, `key`, `rev`, `val`) behind `ownRemoteKV` (exclusive),
  `ownEphemeralKV` (the embedded field); `RemoteKV.Key/Revision/Value`, `Delete` (nil `kv`: `nil`;
  otherwise `deleteResult`; `kv` becomes nil), `Put` (needs a `kv`: `putResult` of
  `.put key val 0`). `putNewKV`: `(r, nil)` with `keyCreatedAt pfx key val lease r` (absent at
  `r - 1`, at `r` created with create/mod revision `r`, version 1, the value, the lease),
  `(0, ErrKeyExists)` with the key present at some `r ≥ lo`, or another error; `newKV`,
  `newKey`, `newEphemeralKV` (the session's client's `KV`, its lease `id`).
- **The claim** (`client.go`): `deleteRevKey kv key rev` (`rev > 0`): `(true, nil)` with
  `revKeyDeleted pfx key rev r` (mod revision `rev` at `r - 1`, absent at `r`), `(false, nil)`
  with `revKeyGone` (no `key` with mod revision `rev` at `r`), or an error; `claimFirstKey`: the
  first claimed `*KeyValue` with its `revKeyDeleted`, each before it gone (`claimedBefore`), or
  `nil` with all gone. **At most once** (`InvRecipesClaim.lean`, `revKeyDeleted_same_rev`): two
  claims of `(key, rev)` are at the same revision (history laws only).
- **Events** (`watch.go`): `waitEvents` (loop invariant: the consumer's received list and
  `0 ≤ i < len(evs)`; the close branch is `False`) returns an `*Event` with `waitedEvent pfx o
  rev typ ev` (`eventAt`, of the last awaited type, `rangeWatchEvOk`); `WaitEvents` /
  `WaitPrefixEvents` (`WithCancel(Background())`, deferred `cancel()`, `c.Watcher.Watch`):
  always `err = nil` (never `ErrNoWatcher`: the channel is not nil, `isChan_not_null`);
  `waitedEvent_key_delete`, `waitedEvent_put`, `waitedEvent_key` for the callers.
- **Deferred to unit 1b** (specs written, proofs `sorry`): `newUniqueKV`, `newSequentialKV`,
  `newUniqueEphemeralKV` (Perennial's `strings.Split`, `errors.Is`, `Sprintf` integer models;
  `fmt.Sscanf` an axiom then). `newUniqueEphemeralKey` is proved (a call of
  `newUniqueEphemeralKV`). The specs state the key's prefix `kp ++ "/"` and its creation; the
  decimal shape and `newSequentialKV`'s order are unit 1b's (the order needs a premise on the
  keys under the prefix, see `decisions.md`).
- **Link**: `etc/gen-link.py --recipes --skip-unproved` (new flag: leaves out the listed
  functions with no proof file and those reaching one, named in the header);
  `etc/link-lean-first-recipes.txt`: unit 1's lines in hypothesis order, `context_TODO`,
  `WithMinModRev`; `fmt_Sscanf` off `newSequentialKV`'s line until 1b.
- **Numbers** (`etc/verified-code.py --reuse`): the recipes 15 of 38 functions verified (14
  sorry-free: `newUniqueEphemeralKey` reaches a unit-1b `sorry`), 3 unfinished, 102 of 401 Go
  lines (`key.go` 47/98, `client.go` 22/22, `watch.go` 33/33); etcd 350 verified of 3599.
- **Gates**: `lake build` passes; `etc/tcb-report.py --collection etc/tcb-collections/recipes.txt`:
  the first baseline, the axioms `etcdReachedAt`, `etcdState`, `etcdState_revs`,
  `proto.Clone.wp_proof` and the three unit-1b `sorry`s; `etc/tcb-report.py --check`: the three
  `sorry`s are new, the repository baseline updated (`--check --update`: 42 axioms, 4 sorries).

### Unit 1b: `newUniqueKV`, `newUniqueEphemeralKV`, `newSequentialKV` (2026-10-11)

The three `sorry`s of unit 1 proved; decisions: `decisions.md`, "Recipes", "Units 1b, 2 and 3"
(the `Sscanf` axiom, `clientErrIs`, `newSequentialKV` not creating its key, `SeqKeysWf`).

- **`newUniqueKV`, `newUniqueEphemeralKV`**: the loop (`wp_for`, the variables as invariant)
  over `time.Now().UnixNano()`, `Sprintf("%s/%v")` (`str_slash_v_int64`: the key is
  `kp/<decimal of an int64>`, now in both specs) and `putNewKV`/`newEphemeralKV`; `errors.Is` on
  `ErrKeyExists` (`wp_Is_leaf`, from `errNewLeaf` in the package facts, `Base.lean`) retries; on
  the client's error (`wp_Is` with `clientErrIs`) either answer is fine (retry, or return the
  error). `newUniqueEphemeralKey`'s spec unchanged (its proof drops the decimal).
- **`clientErrIs`** (`InvEtcdTxn.lean`): `isEtcdTxnKVTodo`'s builder also gives
  `txnCommitErrTodo` (its `Commit` with `clientErrIs` on an error); threaded through the third
  case of `putNewKV`, `newKV`, `newEphemeralKV` (`newKey`'s spec unchanged). `deleteRevKey`'s
  proof adapted (one pattern).
- **`newSequentialKV`** (Löb induction for the retry; `wp_join` with a general postcondition
  for the `if len(resp.Kvs) != 0` block, which may return `Sscanf`'s error): the spec
  takes `pfx <+: __kp` and returns `seqKeyPutAt pfx kp key val g r` (the key made from the
  get's state at `g ≥ lo`, `SeqNext`; the state at `r ≥ g` the puts of `__kp` and the key on
  the state at `r - 1`, `__kp` unmodified since `g`), not `keyCreatedAt`: the transaction does
  not check the key's absence. `InvRecipesSeq.lean`: `lastKeyOp` (`WithLastKey()`'s get) and
  `lastKeyOp_kvs` (its one key-value is the greatest of the range), `lastField`
  (`strings.split`'s last field, `lastField_slash`), `scanInt_fixedDigits`, `seqTxn` and its
  lemmas, `sprintf_slash_016d` (any sign), the order: `seqNext_order` / `seqKeyPutAt_order`
  (under `SeqKeysBelow kp (10^16 - 1)` at `g`: the key is `seqKey kp m`, `m` one past the
  greatest, `m < 10^16`, above every key with prefix `kp` then), `seqNext_absent`,
  `seqKeyPutAt_created` (fresh, given also no new key under `kp` between `g` and `r - 1`).
- **`fmt.Sscanf`**: an etcd-grove axiom (`Spec/fmt/Sscanf.lean`, `fmt.scanInt`), linked
  (`fmt_Sscanf` on `newSequentialKV`'s line).
- **Spec changes the units 2 and 3 meet**: `newSequentialKV`'s (new premise, new success
  case; `PriorityQueue.Enqueue`), `newUniqueKV`'s and `newUniqueEphemeralKV`'s pure success
  facts have a fourth conjunct (the decimal), `putNewKV`/`newKV`/`newEphemeralKV`'s third case
  is `⌜..⌝ ∗ clientErrIs err`, `recipesInit`'s first conjunct has `⌜errNewLeaf e⌝`,
  `isEtcdTxnKVTodo`'s builder a third conjunct (`txnCommitErrTodo`).
- **Numbers** (`etc/verified-code.py --reuse`): the recipes 18 of 38 functions verified, none
  unfinished, 153 of 401 Go lines (`key.go` 98/98, `client.go` 22/22, `watch.go` 33/33); etcd
  353 verified of 3599.
- **Gates**: `lake build` passes (the full build); `etc/tcb-report.py --collection
  etc/tcb-collections/recipes.txt --check --update`: the three `sorry`s gone, the axiom
  `fmt.Sscanf.wp_proof` added (Perennial's `errors.wp_Is` and `time.wp_Now` are not listed:
  the report lists this repository's); `etc/tcb-report.py --check --update`: the same change to
  the repository baseline (43 axioms, 1 sorry).
### Unit 2: the barrier, the queue, the priority queue (2026-10-11)

Files: `Proof/go_etcd_io/etcd/client/v3/experimental/recipes/` (`InvRecipesBarrier`,
`InvRecipesQueue`, one proof per function, `Results`, `Link`) and their specs; the token and the
`More` flag in `Proof/go_etcd_io/etcd/cache/v3/InvEtcdTxn.lean`; deviations from the plan:
`decisions.md`, "Recipes", "Units 1b, 2 and 3".

- **The revision token** (`InvEtcdTxn.lean`): `etcdRevToken r` (an axiom beside `etcdState`,
  exclusive: `etcdRevToken_excl : etcdRevToken r ∗ etcdRevToken r ⊢ False`). The builder's
  `Commit` (`txnBuilderSpec`, under the prefix; so `isEtcdTxnKV` and `isEtcdTxnKVTodo`) returns
  `txnCommitResultTok`: `txnCommitResult`'s facts and, if the transaction wrote (`txnWrote`), the
  token of its revision; `txnCommitResultTok_result` drops it (the six concurrency call sites:
  `Mutex.tryAcquire`, `Election.Campaign/Proclaim/Resign`, the two STM commits, one line each).
  A read-only transaction makes no revision (etcd's `storeTxnWrite.End` advances the revision
  only if the transaction changed something) and gets no token. `putResult` carries the token (a
  put always writes). Not given: `deleteResult` (no caller needs it), leasing's
  `txnCommitResultO`. `deleteRevKey`'s `true`, `putNewKV`'s `nil` and `claimFirstKey`'s claimed
  item return it; `revKeyDeleted_once` (`InvRecipesClaim.lean`): two successful claims of one
  `(key, rev)` are impossible.
- **The get's `More` flag** (`getRespMore`, `InvEtcdTxn.lean`): `isEtcdKVTodo` also returns the
  response's `More`, etcd's (`asembleRangeResponse`: a positive limit cut the selection). The
  queues read it; without it the wait path could not say that the get listed every item.
- **Barrier** (`isBarrier b client key`: read-only fields, the bundle at the prefix `key`):
  `NewBarrier`, `Hold` (`newKey`: `keyCreatedAt`, or `ErrKeyExists` with the key present, or an
  error), `Release` (`nil`: the key absent at some `r ≥ lo`), `Wait` (`nil`: the key absent at
  some `r ≥ lo`: at the get's revision, the early return, or at the delete event's, from
  `R + 1`). `Wait` takes `0 ≤ lo` (the watch's revision `R + 1` must be non-negative).
- **Queue** (`isQueue q client kp`, `kp ≠ []`, the bundle at `kp`): `NewQueue`, `Enqueue`
  (`newUniqueKV`'s key under `kp ++ "/"` created with the value), `Dequeue` (Löb induction,
  `iloeb`, for the two retries: `More`, and a lost claim on the wait path; the recursive call is
  `rw [method_unfold ...]` then the induction hypothesis). `(v, nil)`: an item `it` with
  `v = it.value`, `dequeuedAt kp kp it r` (in etcd's state at `r - 1`, `revKeyDeleted` at `r`,
  the token of `r`) and `dequeueOrder kp kp modRevLe it r` (below).
  A get's `*KeyValue` may be a nil pointer as far as the contract says (nothing makes it
  non-nil), so the code's `kv != nil` is a real branch: a claimed item at a nil pointer counts as
  gone (`revKeyDeleted` gives `revKeyGone` at the same revision), and the proof goes on as if
  nothing were claimed.
- **Priority queue** (`isPriorityQueue q client key`: the prefix field `key ++ "/"`, the bundle at
  `""`): `NewPriorityQueue`, `Enqueue` (`Sprintf("%s%05d", ...)` by `SprintfOut.str_05d_uint16`:
  the key is under `key ++ "/" ++ padZeros 5 (decimal pr) ++ "/"`), `Dequeue` (the queue's
  proof, with `WithFirstKey()`'s resource-threaded options and `keyLe`).
- **Results** (`Results.lean`, `#print axioms` of each): the specs restated (`barrier_hold`,
  `barrier_release`, `barrier_wait_release`, `queue_*`, `pqueue_*`); `queue_dequeued_once`,
  `pqueue_dequeued_once` (two dequeues of the same `(key, mod revision)`: `False`, by the
  tokens); `queue_dequeued_was_enqueued`, `pqueue_dequeued_was_enqueued` (the item, with its
  value, under the prefix at `r - 1`; for the queue also absent at `r`); `queue_fifo`,
  `pqueue_min_key` (at the get's revision `r0 < r`: the item was there with the least mod
  revision / key under the prefix — **the get path** — or every item under the prefix at `r0`
  was gone at some revision in `[r0, r]` and the item was put at or after `r0` — **the wait
  path**); `queue_fifo_before_claim` (by `etcdState_modrev_persist`, below).
- **Weaker than planned, and why.** (1) *FIFO just before the claim* (`r - 1`) is not provable from
  the model's history laws: they do not exclude a key whose mod revision goes back within one
  lifetime (`etcdState_create_persist` keeps the key, not its record; `etcdState_modrev_det` says
  one record per mod revision), so an item older than the claimed one could be at `r - 1`
  without being at the get's revision. With the law that a key-value lives unchanged from its mod
  revision while present (`etcdState_modrev_persist`, the model's seventh history axiom since
  2026-10-11; a hypothesis `EtcdModRevPersist` of the result before), the get path's FIFO holds at
  `r - 1` (`queue_fifo_before_claim`). (2) *The wait path*:
  the watch contract (`rangeWatchRespOk`) says events are real, not that none is skipped, so
  nothing is said of items put between the get and the event; the wait path states that the
  get's items were all claimed by others by `r` and that the item was put at or after the get's
  revision (`WaitPrefixEvents` from `r0`, not `r0 + 1`: an event at `r0` itself is possible).
  (3) *The priority queue's least key* is at the get's revision only, and **is false at the
  claim** in etcd, not only unprovable: an `Enqueue` of a higher priority (a smaller key) between
  the get and the claim is not seen, and `Dequeue` returns a lower-priority item while a
  higher-priority one is present (no premise rules it out; the recipe is not a linearizable
  priority queue; its comment "returns Enqueue()'d items in FIFO order" is copied from the
  queue). Reproduction sketch: client A calls `Dequeue` on a queue holding priority 5 only;
  after A's `Get` returns the priority-5 item and before A's `deleteRevKey` commits (a
  breakpoint, or a delay injected in `claimFirstKey`), client B calls `Enqueue(v, 1)`; A returns
  the priority-5 item while the priority-1 item is present. FIFO for the plain queue has no such
  race: an item put after the get has a larger mod revision.
- **`pqueue_order`** (least key = highest priority, then FIFO) is not stated: it needs unit 1b's
  `SeqKeysWf` order theorem; the statement for the merge is in `decisions.md` (stated at the
  merge: "Merge of unit 2").
- **Numbers** (`etc/verified-code.py --reuse`): the recipes 25 of 38 functions verified (22
  sorry-free; 3 unfinished: unit 1b's), 203 of 401 Go lines (`barrier.go` 26/26, `queue.go` 37/37,
  `priority_queue.go` 38/38); etcd 360 verified of 3599. The enqueues reach unit 1b's `sorry`s
  (`newUniqueKV`, `newSequentialKV`).
- **Gates**: `lake build` passes (the cache, concurrency and leasing rebuilt on the contract
  change); `etc/tcb-report.py --collection etc/tcb-collections/recipes.txt --check --update`: new
  `etcdRevToken`, `etcdRevToken_excl` (the token), `etcdState_agree`, `etcdState_create_persist`,
  `etcdState_modrev_det` (already in the repository's base, now reached by the recipes);
  `etc/tcb-report.py --check --update`: the two token laws only (48 entries).

### Unit 3: the RWMutex and the double barrier (2026-10-11)

Files: `Proof/go_etcd_io/etcd/client/v3/experimental/recipes/` (`InvRWMutex`, `InvDoubleBarrier`,
one proof per function, `Results` (unit 3's section)) and their specs; decisions:
`decisions.md`, "Recipes", "Units 1b, 2 and 3" (the unit 3 bullets).

- **RWMutex** (`isRWMutex m s γ client id pfx`: session, `context.TODO()`, prefix `pfx` with
  `NewRWMutex`'s `/`, the bundle at `pfx`, `context.isClosedchanInit`; `rwMyKey m pfx o`: `myKey`).
  `waitOnLastRev(bp)`: the get `lastRevOp bp (myRev - 1)` (`WithLastRev()` appended with
  `WithMaxModRev`, `lastRevOp_kvs`); `(true, nil)` with `RWBlockFree bp myRev` at the get's
  revision, else `WaitEvents` for the last key's deletion and `false`. `RLock`/`Lock`: a fresh key
  under `pfx/read/` / `pfx/write/`, then `waitOnLastRev(pfx + "write")` / `(pfx)` until done:
  `nil` means `rwHeldAt pfx role key c R`. `RUnlock`/`Unlock`: `myKey.Delete()`
  (`rwUnlockResult`). **Exclusion** (`rwmutex_write_exclusion`, `rwmutex_read_write_exclusion`):
  as `Mutex`'s, plus the premise that the holders' keys are never modified (`keyUnmodified`): the
  recipe filters by mod revision, so a key rewritten by another client stops blocking.
- **DoubleBarrier** (`isDoubleBarrier b s γ client id key count`: with `0 < count`, a
  precondition of `NewDoubleBarrier`; `dbMyKey`). `enteredClients`: the waiters (prefix
  `key/waiters`) sorted by create revision (`waitersResp`). `Enter` (`enterResult`): `nil` with
  `enterReady` (the direct path's `count` waiters seen, `waitersSeen`; the waiting path's write of
  `key/ready` at or after its key's creation, `readyPut`); `ErrTooManyClients` with the key
  possibly left (its `Delete`'s error is ignored); results `double_barrier_enter_ready` (no
  premise) and `double_barrier_enter_count` (under `readyPutsCounted`: `count` waiters seen at a
  revision etcd has reached). `Leave` (Löb induction): `nil` means the key absent at some `r ≥ lo`
  (`double_barrier_leave`, for the record `Enter` leaves), or its record already deleted.
- **No finding.** Misuse is a precondition: `RUnlock`/`Unlock`/`Leave` with a nil `myKey` (a nil
  dereference; `Leave` only if waiters are left), `count ≤ 0`. The mod-revision filter of
  `waitOnLastRev` is the premise above, not an issue (only another client's `Put` into the
  prefix triggers it).
- **Link**: `NewRWMutex`, `NewDoubleBarrier` take `context_TODO`; the other unit 3 lines were in
  hypothesis order already. `Link.lean` regenerated (`--skip-unproved`).
- **Numbers** (`etc/verified-code.py --reuse`): the recipes 25 of 38 functions verified (21
  sorry-free: `RLock`, `Lock`, `Enter` and `newUniqueEphemeralKey` reach unit 1b's
  `newUniqueEphemeralKV` `sorry`), 249 of 401 Go lines (`rwmutex.go` 46/46,
  `double_barrier.go` 101/101); etcd 360 verified of 3599.
- **Gates**: `lake build` passes; `etc/tcb-report.py --collection etc/tcb-collections/recipes.txt`:
  the exclusion results add the existing history law `etcdState_create_persist` to the
  collection's baseline (updated); `etc/tcb-report.py --check` matches the repository baseline
  (42 axioms, 4 sorries).

### Merge of units 1b and 3 (2026-10-11)

Unit 3 (branch `recipes-u3`) merged onto unit 1b. Unit 3's proofs needed no change for 1b's spec
changes (they use `newUniqueEphemeralKey`, whose spec is unchanged, and discard `recipesInit`'s
first conjunct). Conflicts: `Link.lean` (regenerated from the merged `link-lean-first-recipes.txt`,
which merged cleanly), the notes (both units' subsections kept).

- **Numbers** (`etc/verified-code.py --reuse`): the recipes 28 of 38 functions verified, all
  sorry-free, 300 of 401 Go lines; etcd 363 verified of 3599 (unit 3's "21 sorry-free" above
  predates 1b's proofs).
- **Gates**: the full `lake build` passes; `gen-link.py --recipes --skip-unproved` reproduces
  `Link.lean`; the recipes collection: `etcdReachedAt`, `etcdState`, `etcdState_create_persist`,
  `etcdState_revs`, `fmt.Sscanf.wp_proof`, `proto.Clone.wp_proof`, no `sorry`;
  `etc/tcb-report.py --check` matches the repository baseline (43 axioms, 1 sorry), every other
  collection unchanged.

### Merge of unit 2 (2026-10-11)

Unit 2 (branch `recipes-u2`) merged onto units 1, 1b and 3.

- **Conflicts**: `InvEtcdTxn.lean` merged textually; resolved by hand so that 1b's
  `txnCommitErrTodo` (the `TODO()` builder's `Commit` with `clientErrIs`) returns unit 2's
  `txnCommitResultTok` (the token and the error premise both: `putNewKV`'s `nil` has the token,
  its third case `clientErrIs`). `putNewKV.lean`, `newKV.lean` (both sides' patterns combined),
  `Results.lean` (unit 2's section, then unit 3's, then the order below; every `#print axioms`),
  `Link.lean` (regenerated), `etc/tcb-collections/recipes.txt`, the notes (subsections in unit order).
- **Adaptations to unit 2's contract** (one line each): the `TODO()` `Get`'s third conjunct
  (`getRespMore`) in `newSequentialKV`, `RWMutex.waitOnLastRev`, `DoubleBarrier.enteredClients`,
  `Leave`; `newSequentialKV`'s `Commit` (`txnCommitResultTok_result`); `newUniqueKV` drops
  `putNewKV`'s token; `DoubleBarrier.Enter`'s `Put` result bound non-persistent.
  `newUniqueEphemeralKV`, `newKV`'s callers, `RLock`/`Lock`, `Barrier.Hold` needed nothing.
- **Adaptations to 1b's**: `PriorityQueue.Enqueue`'s spec returns `seqKeyPutAt [] (key/%05d(pr))
  k val g r` with `lo ≤ g ≤ r` (unit 2 had `keyCreatedAt`, which `newSequentialKV` no longer
  gives: it does not check the key's absence); `Queue.Enqueue` needed nothing.
- **`pqueue_order`** (`Results.lean`, section "The priority queue's order"): `pqKey key p n =
  key/%05d(p)/%016d(n)`; `PQKeysWf key s` (every key under `key/` is a `pqKey` with `p < 10^5`,
  `n < 10^16`); `pqKey_lt`/`pqKey_le` (key order is lexicographic (priority, sequence number):
  `padZeros_decimalNat_lt` and equal-width prefixes); `pqueue_order`: from `dequeuedAt` and
  `dequeueOrder … keyLe`, at the get's revision `r0 < r`, `it ∈ s0` and, under `PQKeysWf key s0`,
  `it.key = pqKey key p n` with `(p, n)` lexicographically least among the items under `key/`
  (or the wait path's facts); `pqueue_enqueue_order`: on `Enqueue`'s result, under
  `SeqKeysBelow (key/%05d(pr)) (10^16 - 1)` at the get, the key is `pqKey key pr n`, above every
  key of that priority then, `n` one past the greatest; `pqKeysWf_seqKeysWf`: `PQKeysWf` gives
  each priority's `SeqKeysWf`. No axiom (`EtcdModRevPersist` stayed a hypothesis until the
  owner promoted it, below).
- **Gates**: the full `lake build` passes; `gen-link.py --recipes` (plain: `--skip-unproved` now
  skips nothing, and the usage line for it is gone) reproduces `Link.lean`; the recipes collection
  (`--check --update`): `etcdReachedAt`, `etcdRevToken`, `etcdRevToken_excl`, `etcdState`,
  `etcdState_agree`, `etcdState_create_persist`, `etcdState_modrev_det`, `etcdState_revs`,
  `fmt.Sscanf.wp_proof`, `proto.Clone.wp_proof`, no `sorry`; `etc/tcb-report.py --check --update`:
  `etcdRevToken`, `etcdRevToken_excl` added (45 axioms, 1 sorry); the cache and concurrency
  collections gain `etcdRevToken` (their builder's `Commit` names it since unit 2; unit 2 left them
  stale; updated), the others match.

### The whole package (2026-10-11)

All 38 functions of `client/v3/experimental/recipes` (401 Go lines, at `bc8b52a50`) are specified
and proved, sorry-free (`etc/verified-code.py --reuse`: 38 of 38, 401 of 401 lines; etcd 373
verified of 3599, 3712 lines). `Results.lean` restates 33 results with `#print axioms`.

- **Results**: `barrier_hold` (`nil`: the key created), `barrier_release` (absent after the
  call), `barrier_wait_release` (`Wait`'s `nil` only once released); `queue_Enqueue`,
  `queue_Dequeue`, `pqueue_Enqueue`, `pqueue_Dequeue` (the specs); `queue_dequeued_once`,
  `pqueue_dequeued_once` (no item dequeued twice, by the revision tokens);
  `queue_dequeued_was_enqueued`, `pqueue_dequeued_was_enqueued` (the item was under the prefix
  just before the claim); `queue_fifo` (least mod revision at the get, or the wait path),
  `queue_fifo_before_claim` (least just before the claim, by `etcdState_modrev_persist`),
  `pqueue_min_key` (least key at the get), `pqueue_enqueue_order` (an enqueue's key above its
  priority's), `pqueue_order` (least priority, then earliest, at the get);
  `rwmutex_RLock`/`Lock`/`RUnlock`/`Unlock`, `rwmutex_unlock_released`,
  `rwmutex_write_exclusion`, `rwmutex_read_write_exclusion` (writer/writer and reader/writer
  exclusion); `double_barrier_Enter`/`Leave`, `double_barrier_enter_ready` (what each path saw),
  `double_barrier_enter_count` (`count` waiters seen), `double_barrier_leave` (the key gone); the
  constructors.
- **Premises**: the watch channel is never closed (the bundle, `isEtcdRangeWatcherOpen`: no
  compaction past a watched revision, the client not closed while a recipe waits; the fixed code
  would not need it); the session's lease (as `Mutex`'s exclusion); `keyUnmodified` (RWMutex: no
  other client rewrites a lock key); `SeqKeysWf`/`SeqKeysBelow`/`PQKeysWf` (the priority queue's
  order: the keys under its prefix are the recipe's, fewer than `10^16` per priority);
  `readyPutsCounted` (the double barrier's count: only `Enter`s write `key/ready`).
- **Trust base** (the recipes collection): the model's `etcdState` laws, now with
  `etcdState_modrev_persist` (a key-value lives unchanged from its mod revision while present;
  the owner promoted `queue_fifo_before_claim`'s hypothesis `EtcdModRevPersist` to this axiom on
  2026-10-11, so the result is unconditional), the token (`etcdRevToken`, `etcdRevToken_excl`),
  `fmt.Sscanf.wp_proof`, `proto.Clone.wp_proof`.
- **Findings** (unit 0; `issues/recipes-dequeue-closed-watch.md`,
  `recipes-barrier-wait-closed-watch.md`, fix branch `recipes-closed-watch-channel`): on a closed
  watch channel `Queue.Dequeue`/`PriorityQueue.Dequeue` panic on a nil `ev.Kv`, and
  `Barrier.Wait` (and `DoubleBarrier.Enter`) report release while held.
- **Design note, and a documentation issue**: the priority queue is not linearizable: an `Enqueue` of a
  higher priority between a `Dequeue`'s get and its claim is not seen, so `Dequeue` can return a
  lower-priority item while a higher-priority one is present (unit 2, "Weaker than planned");
  its order holds at the get's revision. Its comment ("returns Enqueue()'d items in FIFO order",
  copied from the queue) is recorded as a documentation issue,
  `issues/recipes-pqueue-dequeue-order.md`.

## Perennial `cb6a5921e`: one `AllG` (2026-10-11)

Perennial `cb6a5921e` (`lean`) makes `AllG GF` a singleton: `GooseGlobalGS` has the field
`gooseAllG : AllG GF` (a reducible instance, so `HeapGS` provides it), the ghost state of
the thread tokens and time receipts (`ThreadGS` and `ReceiptGS` no longer carry their own
`AllG`, and `ThreadGpreS`/`ReceiptGpreS` are gone: `GooseGpreS.goosePreGAllG`). A section
with `[hG : HeapGS hlc GF]` must not add `[AllG GF]`: that is a second instance, and its
resources do not match Perennial's (`iexact: cannot unify threadTok and threadTok` in
`Cache__Watch`, `dghostVar` in `Handoff`). Done here:

- `[AllG GF]` dropped from every `variable` line, theorem binder and `omit` next to `HeapGS`
  (654 files, mechanical; `etc`-free: a script over the `variable`/`theorem`/`omit` lines).
  The seven generic ghost-theory files without `HeapGS` (`raft/v3/Protocol/*`, `Results.lean`)
  keep it. `notes/porting-guide.md`, "Section variables", updated.
- `GF` is not an out-parameter of `HeapGS`, so a term whose `GF` nothing else fixes now
  needs `(GF := GF)`: `InvApply.skip_done`'s statement (`consInv`), and the register's
  `regStorIface_inj _ _ Hst` (a theorem whose binders include the section's `HeapGS`, so
  its `GF` is never inferable from its statement; three call sites). Everything else builds
  unchanged. Also in the pin: `114b847ff` (Goose: `range` over an integer) and `bf935cbd5`
  (`float64(n)` of an integer).
## The register's cluster driver: a closed program, safe from package initialization (2026-10-11)

`examples/register/cluster.go` holds `Main()`. It builds three replicas (ids 1, 2, 3): a
`NewStorage`, a `raft.RestartNode` with a `quietLogger{}` and PreVote off, then `New`. They are
connected in process by `deliver`, the `send` callback. A goroutine per node calls `Tick` 2^20 times,
sleeping 5 ms between calls. Two clients run on top: A does `Put("hello")` on replica 1 and then
signals B over a channel. B, on Main's own thread, does `Get()` on replica 2 and panics if the
result is not `"hello"`. `go test -race` runs it (`TestCluster`). The translation is regenerated.

Proved and linked (`Link.lean` by `etc/gen-link.py --register`; `#print axioms` in
`Results.lean`): `Main`, `deliver`, `deliverable`, `tick`, and `quietLogger`'s formatting methods.
The top-level statement (`register_Main`, `Spec/.../register/Main.lean`) is
`{{ isPkgInit register }} Main() {{ RET #(); True }}`, at `HeapGS HasLC.hasLC GF` with `[AllG GF]`
and no storage registry. It rests on raft's `reflect.DeepEqual.wp_proof` axiom only, with no
`sorryAx`: `RestartNode` reaches that axiom. The register's TCB collection was updated by
hand (see below).

- **Everything allocated in the proof.** The proof allocates the storage registry and
  instantiates the register's specs at it: `Main.wp_proof` takes its callees' specs at any
  `RegStor GF`. It also allocates `ownRaftGhost_alloc` for {1,2,3} with
  `γ.reCfg = listToSet voters`, `budget_alloc (3 * 2^20)` with the tick credits,
  `propDataInv_alloc`, `regInv_alloc` (the sequence tokens at 0), and the clients' invariant
  (`clientInv`, `Cluster.lean`: the client's half of the value and half of a flag "A's `Put`
  is done", whose other half A holds). Every premise of `RestartNode`, `NewStorage`, `New`,
  `node.Step` (in `deliver`), `node.Tick`, `Put` and `Get` is discharged there. None of them
  is vacuous.
- **A vacuity bug found by composing.** `isLogger` (raft's `Logger` contract, `InvLogger.lean`)
  held of no `Logger`. `logMethods` listed `Info`/`Debug`/`Warning`/`Error`, and `isLogger`
  states every method as a call on a format and then an argument slice. Those four take a single
  variadic parameter, so that call gets stuck. As a result `RestartNode`/`NewRawNode`, which
  take `isLogger`, were vacuous. `logMethods` is now `Infof`/`Debugf`/`Warningf`/`Errorf`.
  raft calls `Error` only on uncovered paths (`stepFollower`'s `MsgForgetLeader`,
  `releasePendingReadIndexMessages`). Every existing use was an f-variant, so no raft proof
  changed. This was found only because `Main` had to construct a `Logger`.
- **The transport.** `Ready` says of its messages only `isRaftMsg` and `termLB`. `node.Step`
  takes `stepP`, which needs more: `NetMsgOk` (the type, `To` the receiver, a nonzero term and
  sender, not self-sent), a context, and owned entries. `deliverable` checks in Go what
  `Ready` does not promise: the type, `From ≠ 0`, `From ≠ To`, a nonzero term but for a
  `MsgProp`, and a nil `Context`. A nil slice points to `[]` for free; an empty non-nil one
  does not. Routing by `peers[m.To]` makes `To` the receiver, and `deliver` copies the
  entries. raft drops nothing in practice: a temporary panic on a non-deliverable message
  never fired in 20 test runs. The proof pieces are `raftMsg_deliverable` and
  `stepP_deliverable` (`Cluster.lean`). No raft spec changed for the transport.
- **What an adequacy theorem needs from it.** Perennial's `goose_adequacy`
  (`GooseLang/Adequacy.lean`) takes
  `ffiGlobalStart -∗ ffiLocalStart -∗ ownGoState σ.packageState -∗ threadTok ={⊤}=∗ WP e {{ ⌜φ⌝ }}`.
  For `e = initialize' register #(); Main #()` from an `IsInit` state (empty package state),
  three things are missing. First, `ownGoState ∅` has to become `ownInitializing` (unfolding
  `ownInitializingDef` at the empty map). Second, a proved `register.wp_initialize'`: it needs
  raft's, and every standard-library package's, `wp_initialize'`, and Perennial's
  `time.wp_initialize'` is a `sorry`. Third, `register_Main` is then applied to the
  `isPkgInit` that initialization returns. Neither `Main` nor the register uses thread tokens
  (`wp_fork` without one), so any thread bound `T` works.

Not checked: `etc/tcb-report.py --collection etc/tcb-collections/register.txt --check --update`
needs a full build, and the disk (≈400 MB free) does not allow one. The collection's
`axiom reflect.DeepEqual.wp_proof` line was written from `#print axioms register_Main`.
Checked since (2026-10-11, the merge with Perennial `e4e126e46`): `--collection
etc/tcb-collections/register.txt --check` matches (1 axiom, 0 sorries) after a full build.

## Panic and recover: Perennial's panics adopted, the STM's axioms gone (2026-10-10)

Perennial branch `panic` (`b4f46e1dd`..`c46da895a`: a panic outcome `PanicV` in GooseLang,
`Catch`, `with_defer_recover:`; and `d958136aa`, `c01745d27`, `7cea8cc26`: standard-library
models) is adopted; **the pin is not moved in this tree**: the branch builds with
`lake build --packages=<a manifest whose perennial is a path to that checkout>` and needs
Perennial `7cea8cc26` pinned once pushed. Design and the implementation's deviations:
`decisions.md`, "Panic and recover" and "The standard library's models".

- **Adoption**: Goose translates only `runSTM`'s goroutine differently (its deferred literal calls
  `recover()`: `with_defer_recover:`); the 68 other `with_defer` sites are unchanged. Two proofs
  changed: `runSTM` (`wp_with_defer_recover`, `wp_recoverPanic`) and, indirectly,
  `EtcdServer.applyEntryNormal` (it binds `etcdserverpb.AlarmType_NOSPACE`, an axiomatized
  constant `val` a `let` can no longer bind without knowing it is not a panic: now translated,
  `etcdserverpb.toml`). Every other proof builds unchanged.
- **STM**: `fetch` and both commits state their abort (`stmRet`: a return, or the panic of
  `stmError{err}`, `err ≠ nil`; `wp_panic`); `Get`, `Rev`, the interface's triples and the closure
  (`applySpec`) propagate it; `runSTM` recovers it (`Catch`, the deferred literal's `recover()`,
  the assertion to `stmError`, `(nil, err)` sent). `NewSTM`'s spec is unchanged. The axioms
  `stmPanic.spec`, `stmRecover.spec` are gone.
- **Mutex**: `lockerMutex.Lock`/`Unlock` (`NewLocker`'s `sync.Locker`) specified and proved, a
  return or `panic(err)` (`locker_Lock`, `locker_Unlock` in `Results.lean`).
- **Leasing**: `strings.Compare`, `strings.TrimPrefix`, `errors.As`, `(*time.Time).Add` are
  Perennial's (`strings.wp_Compare`/`wp_TrimPrefix` from trusted models, `errors.wp_As` an axiom
  in Perennial with an error-tree precondition, `time.Time.wp_ptr_Add` from `ptr_Add_unfold`);
  their four axiom pairs here are gone. Contract change: `txnCommitResultO`'s error case carries
  `clientErr` (a leaf error without `As`/`Unwrap` methods, an `EtcdError` if of that type), which
  `acquire` gives `errors.wp_As`. `status.FromError` stays an axiom.
- **Merged** `lean` at `1bf5733bf` (leasing unit 5) on top: no conflict but the leasing link list
  (regenerated); builds unchanged.
- **Trust base** (after `--check --update`): 42 axioms, 1 `sorry` (`etc/tcb-baseline.txt`; −6:
  `stmPanic`, `stmRecover`, `strings.Compare`, `strings.TrimPrefix`, `errors.As`,
  `time.Time.Add`); collections: concurrency 11 axioms (the etcd model's), 1 `sorry`
  (Perennial's `context.wp_WithDeadlineCause`); leasing 8 axioms; btree 0, cache 9, raft 1,
  register 0, server 26, unchanged.
- **Gates** (with `--packages`): `lake build` passes (2176 jobs); `etc/tcb-report.py --check` and
  every collection pass; `etc/goose.py --check --perennial /shared/perennial-panic` passes;
  `etc/gen-link.py --cache/--concurrency/--leasing/--server` reproduce the Links;
  `etc/verified-code.py --reuse --package go.etcd.io/etcd/client/v3/concurrency`: 62 functions,
  61 verified, 1 unfinished (`Session.Close`, through Perennial's `sorry`), none translated-only
  (the two locker wrappers were).
- **Push order**: Perennial `panic` (`7cea8cc26`) first, re-pin, then etcd-grove.

## client/v3/leasing: the protocol premise and the lease cache (2026-10-10)

Units 1 and 2 of 5 of `client/v3/leasing` (the caching `KV`): its translation, the protocol as a
premise on etcd's history with its key lemma, and the lease cache (`cache.go`, `util.go`)
specified and proved: every function of `cache.go`, and of `util.go` but
`gatherOps`/`gatherResponseOps` (nested transactions, unit 5). Design: `decisions.md`, "Leasing: the protocol as a premise on the
history". Files: `Proof/go_etcd_io/etcd/client/v3/leasing/` (`Base`, `InvLeasingModel`,
`InvLeaseCache`, `InvLeaseEval`, lemma modules `InvLeaseCacheLemmas`, `InvLeaseCacheWrite`,
`InvLeaseEvalLemmas`, `Link`, `Results`), `Spec`/`Proof`
pairs for every function of `cache.go` and of `util.go` but `gatherOps`/`gatherResponseOps`.

- **Translation**: `client/v3/leasing` with bodies (`leasing.toml`), on the etcd fork's
  `0fc6f23b1` = `goose-lean` (`ab1deb078`) + one **Gooseable** commit (not pushed: push it to
  `upamanyus/etcd`'s `goose-lean` first): kv.go calls `lkv.cl.Watcher.Watch(...)` (the promoted
  `Watch` of `*Client` has no unfolding) and binds `resp.Events` to a `[]*mvccpb.Event` (the alias
  issue), as `207c8f747` did for concurrency. `client/v3.toml`: the `Op` getters
  (`KeyBytes`, `ValueBytes`, `IsGet`, `IsPut`, `IsDelete`, `IsTxn`, `Txn`, `IsKeysOnly`), `OpTxn`,
  `WithIgnoreLease`, `WithKeysOnly`, `WithLastRev`, `Cmp.KeyBytes`/`GetCompare`, the responses'
  `OpResponse`, `OpResponse.Get`; `etcdserverpb.toml`: the header's, `Compare`'s and `ResponseOp`'s
  getters. **Goose issue**: an untranslated type alias (`grpc/status.Status`, of
  `internal/status.Status`) is emitted as an axiomatized type (`axiom Status : go.GoType`) while its
  users name `Status.ty`: `status.toml` now translates the alias, and `grpc/internal/status` is a
  names-only package. Package init (`Base.lean`): `closedCh` holds a fixed channel (that it is
  closed is ghost, `closedChInit`, in `isLeaseCache`).
- **The protocol premise** (`InvLeasingModel.lean`; a hypothesis, not an axiom), in words: *there
  is a history `h` of etcd's whole keyspace — its state at every revision `r ≥ 0` is `h.st r`
  (`etcdState r "" (h.st r)`, keys unique) — and for each revision `z` the session lease of the
  leasing client that committed it (`h.writer z`), such that at every revision `0 < z < 2^63`, for
  every data key `k` (outside `pfx`): (1) if `k`'s record changes at `z`, then `pfx ++ k` is absent
  at `z - 1`, or present with a lease `L ≠ 0` and `h.writer z = L` (the holder wrote it); (2) a lease
  key present at `z - 1` and at `z` with the same create revision keeps its lease.* **Changed from
  the plan**: "`k` changes only while `pfx ++ k` is absent" is false, since the holder writes `k`
  while holding its lease (its guard is its own entry's revision); the model does not record
  writers, so the premise names them (`h.writer`).
- **`leased_value_stable`** (verbatim): `(hk : LeasingDataKey pfx k) (hab : sint.Z a ≤ sint.Z b)
  (hlv : kvOf sa (pfx ++ k) = some lv) (hlb : kvOf sb (pfx ++ k) = some lb)
  (hc : lb.createRev = lv.createRev) (hw : ∀ z, sint.Z a < z → z ≤ sint.Z b → h.writer z ≠ lv.lease) :
  LeasingProtocol pfx h ∗ etcdState a [] sa ∗ etcdState b [] sb ⊢ ⌜kvOf sb k = kvOf sa k⌝`: the
  lease key present at `a` and `b` with one create revision, and no transaction of its holder in
  `(a, b]`, give `k` the same record. Proved by induction from `a` (`leased_incarnation`, pure): the
  incarnation stays present (`etcdState_create_persist` from `b`) with its lease (premise (2)), so
  no revision changes `k` (premise (1)). **`revoked_protects`**: after the lease key has the record
  `lv` at `a` (e.g. `"REVOKE"`, a put keeping create revision and lease), a transaction at `z > a`
  of anyone but the holder that changes `k` runs once that incarnation is gone at `z - 1`.
- **Contract extensions** (`InvEtcdTxn.lean`): `TxnOp.putKeep`, a put with `WithIgnoreLease`
  keeping the key's lease (`txnOpOf` maps an `ignoreLease` put with no lease to it). The range
  comparison `Compare(CreateRevision(lkey).WithRange(lend), "<", n)` needed nothing (`cmpHolds` is
  over the range's keys). Not yet: nested transactions (`OpTxn`, `serverTxn`: unit 5) and an owned
  range response (the cache mutates the acquisition's response, which the contract gives
  read-only: unit 4).
- **The lease cache** (`InvLeaseCache.lean`): `isLeaseCache lc γ pfx X` (persistent: the
  `RWMutex` guard with the lock invariant `leaseCacheInv`, and `closedChInit`),
  `leaseCacheReader` (a reader slot), the state `LeaseCacheSt` (the entries map — nil until the
  session monitor makes it — its entries `LeaseEntry` with their `*leaseKey`, revision, waiter,
  response, cached `CachedKv`s, ghost lease and acquisition record, the revocation times, the latest
  header, the frozen entries, the installed `*leaseKey`s), `LeaseCacheWf`, and `entryFacts` (each
  entry's and frozen entry's acquisition: etcd's whole keyspace at `rev` has the key's record `acq`
  and the lease key with the holder's lease, created at most at `rev`). The lock invariant is
  fractional (a reader holds `rfrac`), with the client's part `X st q` (kv.go's fields under the
  same lock, its invariant over the state). **Specs, as exact transitions** (writers take the
  client's step `X st 1 ={⊤}=∗ X (f st) 1 ∗ Q st`; readers return what the client learns of the
  state read, `lcPeek`):
  - `Add(key, resp, op)` (verbatim, abridged): with `respOwn e0 (DFrac.own 1) ∗ entryFacts pfx key
    e0 ∗ ⌜e0.rev = e0.hm.revision ∧ e0.acq = e0.kv⌝ ∗ opFullAt opv o ∗ leaseCacheReady γ` and the
    step `∀ st li ch, X st 1 ={⊤}=∗ X (st.add key {e0 with li := li, waitc := ch}) 1 ∗ Q st`, returns
    `ret` with `∃ st, □ Qr st ∗ Q st ∗ freshGetResp ret e0.hm e0.more e0.count (getResult o e0)`
    (`LeaseCacheSt.add`: the old entry frozen, a fresh `*leaseKey`, the closed channel as waiter,
    the header replaced if newer).
  - `Get(ctx, op)` (verbatim, abridged): `(nil, false)` if `isBadOpM o`; otherwise `ok = true` and
    `nil`, or `∃ st e, □ Qr st ∗ ⌜st.entries !! o.key = some e ∨ (o.key, e) ∈ st.frozen⌝ ∗
    entryFacts pfx o.key e ∗ freshGetResp ret e.hm e.more e.count (getResult o e)` (the entry as it
    is at the second read: still the key's, or evicted since).
  - `Rev`, `notify`, `MayAcquire` (read lock); `Lock`, `LockRange`, `LockWriteOps` (fresh waiter
    channels the caller closes; `WaitcOnly`), `NotifyOps`; `Evict`, `EvictRange` (`LeaseCacheSt.evict`,
    `evictRange`: frozen entries, revocation times); `Update`, `delete` (on the owned state: the
    holder's put and delete applied to the entry, `LeaseEntry.update`, `del`), `Delete`;
    `clearOldRevokes` (a goroutine: some revocation times dropped, `RevokesSub`); `leaseKey.get`
    (`getResult`, a fresh response), `isBadOp`, `inRange` (`leaseInRange`), `compareInt64`,
    `copyHeader`, `copyGetResponseMetadataOnly`, `copyKeyValue`, `closeAll`; `evalCmp`,
    `leaseCache.evalCmp`, `leaseCache.evalOps` (`InvLeaseEval.lean`: what they compute).
- **Findings**:
  - **`EvictRange` evicts the wrong key** (upstream, `cache.go`): `for k := range lc.entries { if
    inRange(k, key, end) { delete(lc.entries, key); lc.revokes[key] = time.Now() } }` deletes
    `key`, not `k`. After a failed range delete (`deleteRangeRPC`'s error path, where the delete
    may have committed), the entries in the range other than `key` stay cached: stale reads.
    Confirmed by a unit test (`EvictRange("a", "c")` leaves `"b"` cached). The spec states it
    (`LeaseCacheSt.evictRange`).
  - **`evalCmp` is not etcd's comparison** (upstream, `util.go`), so a transaction whose
    comparisons' keys are all cached is answered from the cache with the wrong `Succeeded`: on a
    key cached as absent, `result` stays `0` for every target (`CreateRevision(k) < 5` fails,
    etcd: holds; `Version(k) = 3` holds, etcd: fails; `Value(k) = ""` holds, etcd: a value
    comparison on a missing key fails); and there is no `LEASE` case (`LeaseValue(k) = 8` holds for
    a key with lease 7). Confirmed by unit tests; the spec states what it computes
    (`leaseCmpHolds`).
  - To confirm in unit 4 (kv.go): `Update` writes the op's value even for a `WithIgnoreValue` put
    (the cache then serves an empty value) and never the lease (`WithLease`: stale `Lease`); with
    two concurrent puts of one key by one client, an `Update` applied out of order bumps the version
    without the value, so a cached `Get` in between returns a version etcd never had; `waitRescind`
    returns `nil` when the watch closes without a delete event, so `revokeRange`'s bound may cover a
    lease key still present (a range delete while another client's lease protects a key).
  - `gatherOps` appends `elseOps` to `thenOps` (`append(thenOps, elseOps...)`), writing into the
    op's spare capacity: a data race if two goroutines gather one `Op` (unit 5).
- **Trust base**: two new axioms, `strings.Compare.wp_proof` (`Spec/strings/Compare.lean`: Perennial
  has no model; a Perennial trusted model and `wp_Compare` were written and proved but lost: the
  shared `.lake/packages/perennial` was reset by another worktree's Lake (`/shared/etcd-grove-mvcc`
  links its `.lake/packages` to this one) while it was at the uncommitted pin; redo it in a
  separate Perennial checkout, `lake build --packages=<file>`, as `CLAUDE.md` says) and
  `time.Time.Add.wp_proof` (`Spec/time/Time__Add.lean`: `(*time.Time).Add`, Perennial models the
  value receiver only). No `sorry`.
- **Proof-mode notes**: `wp_load` does not find a struct field's points-to inside a whole struct's
  (`AccessStrict` instances exist; the search fails): `entryOwn` is field by field and
  `leaseKey_struct` converts for `Get`'s `*li`. `wp_apply` leaves persistent premises unframed
  unless written `$H` (`$$ [$Hlc ...]`). `unfold` of a predicate also unfolds the postcondition's
  instances: `rw [entryOwn_def]` (one instance) or `iunfold X at H`.
- **Linking**: `etc/gen-link.py --leasing` writes `Link.lean` from
  `etc/link-lean-first-leasing.txt` (namespace `leasing`; a callee named like the theorem's last
  component is qualified, `EtcdGrove.leasing.wp_evalCmp`); `etc/link-lean-first-concurrency.txt`
  names clientv3's `Compare` `v3_Compare` (now ambiguous with `strings.Compare`; its `Link.lean`
  reorders two theorems). `ResponseHeader.GetRevision`'s spec takes etcdserverpb's assumptions
  (was the cache's), so both links use it. `etc/verified-code.py` counts an axiom outside a Link's
  namespace (`strings.Compare.wp_proof`) as assumed.
- **Gates**: `lake build` passes (2061 jobs); no `sorry` of this work; `etc/tcb-report.py --check`
  after `--update`: 45 axioms, 1 sorry (new: `strings.Compare.wp_proof`, `time.Time.Add.wp_proof`);
  `--collection leasing` (new): 6 axioms (`etcdState`, `etcdState_agree`, `etcdState_create_persist`,
  `etcdState_revs` and the two above), no `sorry`; the other collections unchanged;
  `etc/goose.py --check` passes (with `ETCD_SRC=/shared/etcd` until `0fc6f23b1` is pushed);
  `etc/gen-link.py --cache/--concurrency/--server/--register/--leasing` reproduce;
  `etc/verified-code.py --reuse` (with `0fc6f23b1` fetched into `.lake/go-src/etcd`):
  `client/v3/leasing` 26 verified of 67, `cache.go` 20 of 20 (231/231 lines), `util.go` 6 of 8;
  etcd 278 verified of 3599.
- **Push order**: the etcd fork's `0fc6f23b1` (to `goose-lean`), then etcd-grove `lean`
  (Perennial unchanged).

### Units 3 and 4: `txn.go` and `kv.go` (2026-10-10)

Every function of `txn.go`, of `kv.go` but the monitors (unit 5: `NewKV`, `Close`,
`monitorSession`, `monitorLease`, `rescind`, `waitRescind`, `waitSession`), and `util.go`'s
`gatherOps`/`gatherResponseOps` specified and proved, no `sorry`. Design: `decisions.md`, "Nested
transactions, owned responses, `isLeasingKV`". Files: `Proof/go_etcd_io/etcd/cache/v3/
InvEtcdTxnOwn.lean` (operation trees `OpT`, nested and owned responses, `isEtcdTxnKVO`,
`isEtcdDoKV`), `Proof/go_etcd_io/etcd/client/v3/leasing/InvLeasingKV.lean` (`isLeasingKV`,
`leasingX`, the results' predicates), lemma modules `InvLeasingKVLemmas` (the log's steps, the wait
group), `InvLeasingTxnLemmas`, `InvLeasingPutLemmas`, `InvLeasingDeleteLemmas`,
`InvLeasingGetLemmas`, `InvLeasingCommitLemmas`, `InvLeasingResults` (the pure parts of the main
theorems); `Spec`/`Proof` pairs for the 31 leasing functions, ten clientv3 functions (`OpTxn`,
`Op.Txn`, `WithKeysOnly`, `WithIgnoreLease`, `WithLastRev`, `OpResponse.Get`, the four
`OpResponse()` conversions) and three `ResponseOp` getters.

- **Model and contract extensions** (every cache/concurrency proof unchanged): `TxnOp.txn`
  (nested transactions, run at the same revision on the state the operations before them left,
  the branch chosen by their comparisons), `TxnOp.putIgnVal` (`WithIgnoreValue`), `TxnOpResult.txn`;
  `applyTxnOp`/`runOps` mutually recursive. The owned-response builder `isEtcdTxnKVO` (a second
  contract of the client's `Txn`), `isEtcdDoKV`. `HdrM`, `hdrFull`, `CachedKv`, `cachedKvOwn` moved
  from `InvLeaseCache.lean` to `InvEtcdTxnOwn.lean`. Translation: grpc `codes.Unavailable` and
  `codes.Unimplemented` (`codes.toml`), and `rpctypes.EtcdError` as a struct (`rpctypes.toml`
  imports `codes`; it was an axiomatized type whose `sorry` instances `acquire` reached).
- **Unit 5's functions are hypotheses**: their specs are written (`leasingKV__waitSession`,
  `__waitRescind`, `__monitorLease`) and `Link.lean` links every result reaching them in
  `section links_pending`, with the specs as hypotheses (`etc/gen-link.py`'s `fn: ?`;
  `etc/verified-code.py` counts them as unfinished). `Results.lean` restates the main theorems
  with the same three hypotheses.
- **The main theorems** (`Results.lean`, with `#print axioms`):
  1. **Cached reads** — `leasing_get : leasingKV.Get.spec`: `getOutcome γ pfx lo o ret err`, whose
     cache case is `getCached`: `∃ st e, leasingSeen γ st ∗ ⌜st.entries !! key = some e ∨ (key, e)
     ∈ st.frozen⌝ ∗ entryFacts pfx key e ∗ freshGetResp ret e.hm e.more e.count (getResult o e)`;
     `leasing_getResult_acq` (`e.kv = e.acq → getResult o e` is `e.acq`'s answer) and
     `leasing_cached_get_stable` (verbatim: `LeasingDataKey pfx key → e.rev ≤ b → (∀ z, e.rev < z
     → z ≤ b → h.writer z ≠ e.lease) → LeasingProtocol pfx h ∗ entryFacts pfx key e ∗ etcdState b
     [] sb ⊢ ∃ s lv, □ etcdState e.rev [] s ∗ ⌜kvOf s (pfx ++ key) = some lv ∧ lv.lease = e.lease ∧
     ∀ lb, kvOf sb (pfx ++ key) = some lb → lb.createRev = lv.createRev → kvOf sb key = e.acq⌝`).
     **Changed from the plan:** "the returned kv is `e.acq`" holds only while this client has not
     written the key since acquiring it (`Update`/`delete` change the cached key-value, theorem 3),
     hence the hypothesis `e.kv = e.acq`.
  2. **Uncached operations** — `leasing_get`'s other cases (`kvGetResult [] lo o`: the client's
     answer, linearizable unless serializable; `getAcquired`: etcd's record at a revision `≥ lo`;
     `getNotAcquired`), `leasing_put` (`putCommitted`: the put at `r ≥ lo` on etcd's state at
     `r - 1`), `leasing_delete` (`deleteCommitted`: the range deleted at `r ≥ lo`, `Deleted` its
     size), `leasing_Txn_Commit`/`leasing_Do`.
  3. **The holder's writes** — `putCommitted` includes the cache's step `leasingStep γ st
     (st.modify key (e.update (freshKv …) … hdr hm vsl o.val))` with `hm.revision = r` (consecutive
     states of the cache's log: `Update` does not change `e.rev` or `e.acq`, so "the entry's facts at
     `r`" is not what the code does); `leasing_update_tracks_put`: the bumped key-value is etcd's
     record after a plain put iff the put's lease is the cached one; `leasing_update_new_key` (a key
     cached as absent: iff no lease); `leasing_update_ignoreValue` and
     `leasing_update_out_of_order` (findings below).
  4. **Locally evaluated transactions** — `leasing_Txn_Commit : txnLeasing.Commit.spec`:
     `commitOutcome`, whose cache case `evalResult`: in a state `st` of the log,
     `leaseEvalCmps st b.cmps = (ok, true)`, `st.header ≠ null`, every operation of the chosen
     branch a cached get (`leaseEvalOk`), a fresh response with a copy of `st`'s header, `Succeeded
     = ok`, `respOpFresh` of each; otherwise exactly `txnCommitResult [] lo` of the user's
     transaction. `leasing_evalCmpM_agrees`: `leaseCmpHolds m (kvOf s m.key) = cmpHolds s m` for
     a one-key comparison not of the lease, if an absent key is not compared by value and with
     operand `0`; `leasing_leaseEvalCmps_agrees` for a transaction whose keys are cached with
     etcd's records; `leasing_evalCmpM_absent_lt`, `leasing_evalCmpM_lease`: the divergences.
- **Spec changes made while proving**: `tryModifyOp` returns `((resp, wc), err)` (Goose's tuple);
  `tryModifyOp`/`revoke` do not claim `resp ≠ null`; `Put`/`Delete` take `(opPutModel …).t = 2`,
  `(opDeleteModel …).t = 3` (the option transformers are arbitrary; as `Get`'s); `guardRanges`'s
  error case has `cmps = nil` (`guard` appends it); `eval`, `Commit` and `Do`'s transaction case
  take `len(then) + len(else) < 2^63` (`make([]Op, 0, len+len)`); `Compact`'s delegation is for a
  pair result. Contexts: writes may `revoke`, whose `waitRescind` calls `WithCancel(ctx)`, so `put`,
  `delete`, `Commit`, `Do` take `isCancelCtxCtx ctx`. User transactions are flat (`Txn().Then`
  takes plain operations).
- **Findings** (the Go code is unchanged; reproductions in an integration test, kept out of the
  tree):
  - **A write of a key not in the cache is applied twice** (`kv.go`, `put`/`delete`):
    `tryModifyOp` commits the op (guard `CreateRevision(pfx+key) < 1`) and returns a nil waiter
    channel because the key has no entry; `put`/`delete` then call `revoke` because `wc == nil`,
    which commits the op again. Confirmed: on a fresh key `lkv.Put(ctx, "k", "v")` leaves etcd at
    version 2 (create 2, mod 3); `lkv.Delete(ctx, "k")` of an existing uncached key returns
    `Deleted: 0`. The spec describes the second commit.
  - **A failed acquisition ignores the get's options** (`get`): when another client holds the
    lease, `get` returns `acquire`'s answer to `OpGet(key)`: `WithCountOnly` returns the key-value,
    `WithKeysOnly` the value, the revision filters are not applied (confirmed: count-only gives 1
    kv, keys-only the value `"v"`). `getNotAcquired` states it.
  - **`Update` and `WithIgnoreValue`, leases** (confirmed by the proof): `put`'s step caches the
    op's value (empty for `WithIgnoreValue`, where etcd keeps the old value:
    `leasing_update_ignoreValue`) and never the lease (`leasing_update_tracks_put`: a put without
    `WithLease` of a key with a lease leaves the cached lease stale).
  - **Out-of-order `Update`s** (confirmed by `leasing_update_out_of_order`): two concurrent puts
    of one key at `r1 < r2` whose `Update`s run in the opposite order leave, in between, a cached
    record with `r2`'s value and mod revision but the version incremented once: etcd never had it,
    and a cached `Get` waiting on the later waiter channel can serve it.
  - **An entry can carry an old session's lease** (`get`): the lease ID is read in `acquire`, the
    entry added later; a session reset in between (the session monitor clears the map, then sets
    a new session) leaves an entry of the expired lease, whose lease key etcd deleted, cached until
    the next reset (`monitorLease` only rescinds on a `"REVOKE"` put). Not excluded by the specs
    (the facts are about the acquisition revision); this is why `leasingX` has no "entries carry
    the current lease" invariant.
  - `waitRescind` returning `nil` without a delete event (unit 1's list): confirmed by unit 5.
- **Trust base**: three new axioms, `strings.TrimPrefix.wp_proof` (`Spec/strings/TrimPrefix.lean`),
  `errors.As.wp_proof` (`Spec/errors/As.lean`, for a `*rpctypes.EtcdError` target), both
  standard-library functions Perennial does not model (to move to Perennial), and
  `status.FromError.wp_proof` (grpc, names only; its result's `Code()` returns). The existing
  `status.Error.wp_proof` and `proto.Clone.wp_proof` are now reached. `--collection leasing`: 12
  axioms, no `sorry`.
- **Gates**: `lake build` passes (2171 jobs); `etc/tcb-report.py --check` (after `--update`: 3 new
  axioms) and every other collection unchanged; `ETCD_SRC=/shared/etcd etc/goose.py --check`;
  `etc/gen-link.py --leasing` (and the other modes) reproduce; `etc/verified-code.py --reuse
  --package go.etcd.io/etcd/client/v3/leasing`: 42 verified of 67 (`cache.go` 20/20, `util.go`
  8/8, `txn.go` 7 of 12, `kv.go` 7 of 27 verified), 17 unfinished (resting on unit 5's specs), 7
  translated (unit 5's); 509 of 921 lines verified, 917 specified; etcd 304 verified of 3599.
- **Push order**: unchanged (the etcd fork's `0fc6f23b1` to `goose-lean`, then etcd-grove).

### Unit 5: the monitors; the package (2026-10-10)

Every function of `client/v3/leasing` but `init` (not translated apart from package
initialization, `Base.lean`) is specified and proved, no `sorry`: unit 5 proved `waitSession`,
`waitRescind`, `rescind`, `monitorLease`, `monitorSession`, `Close` and `NewKV`. Files:
`Spec`/`Proof` pairs for the seven (`rescind`, `monitorSession`, `Close`, `NewKV` newly specified),
lemma modules `InvLeasingSessionLemmas` (the cache's reset `LeaseCacheSt.reset m st := { st with
emap := m, entries := ∅, frozen := st.entries.toList ++ st.frozen }`, joining the session
monitor's halves) and `InvLeasingNewLemmas` (the wait group's two owed goroutines and `Wait`, the
cache's allocation). Design: `decisions.md`, "Leasing unit 5".

- **No hypotheses left**: the link list has no `fn: ?`; `Link.lean`'s `links_pending` section is
  gone and the 17 results that took the unit-5 specs (`leasingKV.wp_Get`, `wp_Put`, `wp_Delete`,
  `wp_Do`, `txnLeasing.wp_Commit` and their callees `get`, `put`, `delete`, `deleteRange`,
  `acquire`, `revoke`, `revokeLeaseKvs`, `revokeRange`, `guard`, `guardRanges`, `revokeFallback`,
  `serverTxn`) are unconditional; `Results.lean`'s theorems take no hypotheses, with
  `leasing_NewKV`, `leasing_Close`, `leasing_waitRescind`, `leasing_monitorLease`,
  `leasing_monitorSession` added.
- **Specs**: `NewKV` (`isLeasingEtcdClient`, `closedChInit`, a thread bound) returns
  `newKVResult`: the `KV` interface value of an `isLeasingKV` with every reader slot, the "open"
  token, `leasingCloseFn` and `waitSession`'s error; `Close` needs the whole "open" token; the two
  monitors return (`True`); `waitRescind`: an error, `nil` with `leaseKeyDeleted` (the lease key
  absent at a revision above `rev`), **or `nil` with no promise** (the watch closed without a
  delete event).
- **Changes to existing specs and contracts**: `leasingXBody` holds half of `session`/`sessionc`,
  `sessionMonitor` the other half (`monitorSession` reads `session` without the lock);
  `acquireResult`'s success gives `sessionReady` (`monitorLease` calls `leaseID`), `monitorLease`
  and `waitRescind` take a revision bound (`WithRev(rev+1)`; `txnCommitOk_guarded` exports the
  header's); the range watch contract gives a delete event's `Value`/`Lease` fields readable
  (`delKvAt`; `monitorLease` reads `Value` of every event); `isEtcdLease`'s `KeepAlive` success
  gives a channel (no nil: etcd's lessor always makes one), so `NewSession`'s nil session comes
  with an error (`monitorSession` would otherwise set a nil session and close `sessionc`).
- **Findings** (reproduced by integration tests kept out of the tree):
  - **`waitRescind` returns `nil` without a delete** (confirmed, the spec's third outcome): when
    the watch channel closes while `ctx` is live (the watch canceled: its start revision
    compacted, or the client closed), it returns `ctx.Err() == nil`. A single-key write then just
    retries (its guard still fails); a **range delete goes through another client's lease**:
    `revokeRange`'s bound covers the still-present lease key, so `deleteRangeRPC`'s guard holds.
    Reproduction: A caches `k` (`lkvA.Get("k")`, A's watcher stalled so its lease monitor has not
    run); B's watcher, before its `Watch`, puts twice and compacts; `lkvB.Delete("k",
    WithPrefix())` returns `Deleted=1` while A's lease key `pfx/k` still exists, and
    `lkvA.Get("k")` returns `"v1"` though etcd has no `k`. Without the stall, A usually rescinds
    first (a race). This breaks the protocol premise (`LeasingProtocol` (1)) for leasing clients.
  - **A stale entry survives a session reset** (confirmed): `get` adds the entry after `acquire`
    commits; a reset in between (`monitorSession` clears the map before `Add`) leaves an entry of
    the old lease, whose lease key etcd deleted with the lease. `monitorLease` ignores the delete
    event (its `Value` is not `"REVOKE"`: `continue`), and a `"REVOKE"` put carrying the old
    lease (`WithIgnoreLease`) is not this client's current `leaseID()`, so it returns without
    rescinding. The entry stays until the next reset. Reproduction: A's `KV` wrapped so that after
    the acquisition's `Commit` it revokes A's session lease (as an expiry would) and waits for A's
    new session (`WithTTL(2)`); then B (`NewKV` after) puts `"v2"` (its guard holds: no lease
    key), and `lkvA.Get("k")` returns `"v1"`.
- **Trust base**: no new axiom; `--collection leasing` 12 axioms, no `sorry` (unchanged); every
  collection unchanged; `etc/tcb-report.py --check`: 48 axioms, 1 sorry (unchanged).
- **Gates**: `lake build` passes (2184 jobs); `ETCD_SRC=/shared/etcd etc/goose.py --check`;
  `etc/gen-link.py` reproduces every `Link.lean`; `etc/verified-code.py --reuse --package
  go.etcd.io/etcd/client/v3/leasing`: **66 verified of 67** (every one sorry-free; `init`, 4
  lines, not translated), 0 unfinished, 917 of 921 lines verified (`kv.go` 26/27, `cache.go`,
  `txn.go`, `util.go` all); etcd 328 verified of 3599.
- **Push order**: unchanged (the etcd fork's `0fc6f23b1` to `goose-lean`, then etcd-grove).

## Merge: the register, `node.go` and thread tokens (2026-10-10)

Merged upstream `lean` (`67c6b9292`, 43 commits: Perennial thread tokens and the cache's
wait-group counter bounded by them, `node.go` proved, the `examples/register` replicated
register, raft translated from upstream `etcd-io/raft` `40f8be7` unmodified, bbolt's
`internal/common`) into the Mutex/Election/STM line (`e5406a399`).

- **Perennial `7c93f27aa`** (`lean`): our `9276bd1ed` (`Sprintf`/`HasPrefix` models, the map-length
  bound) merged cleanly with upstream's `105fb79f5` (thread tokens, `wp_fork_tok_*`, the revert of
  our `WaitGroup.Add` assumption, `wp_slice_append_undo`, the iframe heartbeat option).
  `etc/lean-ci.sh`: 374/374; the std-lib regeneration (`GOTOOLCHAIN=go1.26.0
  etc/update-goose-new.py --compile --std-lib`) is clean; `go test ./...` in `goose/` passes.
- **Conflicts**: only the Perennial pin (`lakefile.toml`, `lake-manifest.json`: `7c93f27aa`) and
  these notes (both sides' sections; the `WaitGroup.Add` assumption marked superseded in "The cache
  as shipped"). `etc/goose.py` is upstream's (raft from `etcd-io/raft`, the `register` project) and
  already has the concurrency package and the `ab1deb078` pin; `etc/tcb-baseline.txt` is ours
  (upstream added no axiom or `sorry`). The regenerated translation is identical to the merge.
- **Thread tokens**: no proof of ours changed. Our side never touched the cache's wait-group files,
  so they are upstream's (shared writers and `cacheBound` already in, from the earlier merge).
  `wp_fork` keeps its statement (the forked thread keeps its own token, `wp_fork_tok` underneath),
  so the other `go` statements (`NewDemux`, `Session`'s keep-alive, `Observe`, `waitTillRevision`,
  the progress requestor, STM/Mutex/Election) build unchanged. The exported statements are ours but
  for upstream's thread-token changes: `New`/`newCache` assume `threadBound GF + 3 ≤ 2^31`,
  `Watch` takes and returns a `threadTok` (see "The wait-group counter and thread tokens").
- **`etc/verified-code.py`**: crashed on the `register` project (no `repo`: `fork()` now names
  its directory), and did not resolve the register's results (`register.Register.Put`: a name
  qualified by the main package's own qualifier is now looked up there).
- **Gates**: `lake build` passes (1958 jobs); `etc/goose.py --check --perennial
  .lake/packages/perennial` passes; `etc/tcb-report.py --check`: 43 axioms, 1 `sorry` (the
  baseline unchanged); per collection: btree 51 roots, no axiom; cache 152, 9 axioms, sorry-free;
  concurrency 125 (124 sorry-free), 13 axioms, 1 `sorry` (`Session.Close`); raft 213, 1 axiom,
  sorry-free; register 19, no axiom, sorry-free; server 47, 26 axioms, sorry-free. `etc/gen-link.py
  --cache`/`--concurrency`/`--server`/`--register` and `etc/gen-btree-link.py` reproduce their
  `Link.lean` (raft's is by hand since upstream's `MemoryStorage` work). `etc/verified-code.py
  --reuse`: raft 203/323 (2608 of 3646 lines), all sorry-free; etcd 243 verified, 1 unfinished, 13
  assumed of 3599 (the cache 107/107 sorry-free; `client/v3/concurrency` 59 + 1 unfinished of 62);
  register 12/12 (96 lines).
- **Push order**: Perennial `lean` (`7c93f27aa`) first, then etcd-grove `lean`.

## STM (2026-10-10)

`client/v3/concurrency`'s software transactional memory (`stm.go`) is specified and proved: every
function (28), with atomicity theorems per isolation level. Design: `decisions.md`, "STM:
a higher-order closure spec, aborts as divergence, what each isolation level gives". Files:
`client/v3/concurrency/InvSTM.lean` (vocabulary), `InvSTMAtomic.lean` (the commit key by key, the
per-level theorems), lemma modules `InvSTMMaps`, `InvSTMReads`, `InvSTMCommit`, `InvSTMRun`; `Spec`/`Proof`
pairs `NewSTM`, `NewSTM{Repeatable,Serializable,ReadCommitted}`, `mkSTM`, `runSTM`, `With{Isolation,
AbortContext,Prefetch}`, `stm__{Get,Put,Rev,Del,commit,fetch,reset}`,
`stmSerializable__{Get,Rev,gets,commit}`, `readSet__{add,first,cmps}`, `writeSet__{get,cmps,puts}`,
`isKeyCurrent`, `respToValue`, and (until the panic adoption) the trust boundary `stmPanic`,
`stmRecover`; `Results.lean`.

- **The closure** (`applySpec pfx apply Q`): for any STM with the interface's triples
  (`stmMethods`), from any state, `apply` returns an error or `nil`, and `nil` means `Q` of the
  attempt's reads and writes (`STMSt`). `NewSTM` returns an error, or `nil` with a committed attempt
  `st`, `Q st` and `stmOutcome` (`stmResult`).
- **What each level is proved to give** (`stmOutcome`: a revision `R`, the state `s` the commit ran
  on, etcd's at `R - 1` if it wrote (at `R` otherwise), and `s'`, etcd's at `R`; `STMCommitted`):
  - all levels: `s'` is `s` with the attempt's writes applied, key by key, independently of the
    write set's order (`stm_read_committed`); every read is etcd's key-value at the revision it read
    (`readFact`); `R` is at least a revision the caller had seen if the commit had an operation.
  - `SerializableSnapshot`, `Serializable` (`stm_atomicity`) and `RepeatableReads`
    (`stm_repeatable_reads`): additionally, **every read of the committed attempt is `s`'s
    key-value of its key**: the attempt ran atomically at `R` (`R - 1` → `R`). `SerializableSnapshot`
    also: no written key was modified after `first()` (the least header revision of the reads).
  - within an attempt, a key read once reads the same (repeatable reads, `GetPost`), all levels.
- **Finding: a retried serializable attempt reads from two revisions.** The serializable levels
  document "reads within the same transaction attempt return data from the revision of the first
  read". After a failed commit, the next attempt's prefetched reads are at the failed commit's
  revision `r`; if its first read is of a key not prefetched, that read is at the latest revision
  `r2` and sets the snapshot to `r2`, while later reads of prefetched keys return values at `r`. An
  attempt can then see a state that never existed (the commit fails afterwards, so serializability
  holds, but the closure ran on an inconsistent view). The specs claim no snapshot. **Reproduced**
  on upstream main (`f061acd09`) by an integration test, for both levels; fix and test on
  `/shared/etcd-stm-repro`, branch `stm-serializable-snapshot` (`479a65c65`, not pushed): after a
  failed commit, the next attempt reads at the prefetched reads' revision (`WithRev`). The existing
  STM integration tests pass with the fix.
- **Other observations** (stated, not bugs): a `RepeatableReads`/`ReadCommitted` attempt with no
  write commits an empty transaction, which etcd answers from the member's state (no recency
  promise); `fetch` of a key listed twice keeps the later response (the same key-value); after
  `apply` fails, `runSTM` returns the response field an earlier attempt left (nil in practice: a
  failed commit). A successful commit's response is not known to be non-nil from the contract
  (the spec allows nil; `runSTM` would then retry).
- **Contract changes** (`InvEtcdTxn.lean`, definitions): **read transactions** (`isEtcdReadTxnKV`,
  `readTxnResult`: gets alone, each at the current revision or its `WithRev`, serializable or not;
  `isEtcdSTMClient` bundles it with `isEtcdTxnKV`); **linearizability corrected**: `txnCommitResult`'s
  `lo ≤ r` only for a transaction with an operation that is not a serializable get
  (`TxnModel.linearizable`; etcd serves the others from the member's state; no existing proof used
  such a transaction; Mutex/Election proofs discharge it by `rfl`); a range response's header exists
  (`rangeRespAt`).
- **Trust base** (`etc/tcb-baseline.txt` after `--check --update`: 43 axioms, 1 sorry; `--collection
  concurrency` updated): a new history law `etcdState_modrev_det` (same key, same mod revision ⇒ same
  key-value); the STM's abort `stmPanic.wp_proof` (`panic(stmError{err})`, `err ≠ nil`, does not
  return) and `stmRecover.wp_proof` (`recover()` returns nil; both gone since "Panic and recover"): Perennial's `panic` is stuck and it has
  no `recover`, see decisions.md. No `sorry`.
- **Perennial `9276bd1ed`** (on `d240c1732`): `len` of a map assumes fewer than `2^63` keys (as
  `append` assumes no overflow): `wp_map_len_lt`. Needed by `make([]T, 0, len(m))` (a negative
  capacity panics).
- **Gates**: `lake build` passes (1880 jobs); `etc/tcb-report.py --check` (and per collection) passes;
  `etc/goose.py --check` passes; `etc/gen-link.py --cache/--concurrency/--server` reproduce;
  `etc/verified-code.py --reuse`: `stm.go` 28 of 28 (243/243 lines); `client/v3/concurrency` 59
  verified, 1 unfinished (`Session.Close`) of 62; etcd 243 verified of 3599.
- **Push order**: Perennial `lean` (`9276bd1ed`) first, then etcd-grove `lean`. The etcd fork's
  `goose` is unchanged; the fix branch `stm-serializable-snapshot` is for an upstream PR.

## Election (2026-10-10)

`client/v3/concurrency`'s `Election` (`election.go`) is specified and proved: all 11 functions,
with the mutex's exclusion as the election's and a pure theorem that only the leader proclaims.
Design: `decisions.md`, "Election: the mutex's leader fact, no final check, what `Observe` can
promise". Files: `client/v3/concurrency/InvElection.lean` (vocabulary, `proclaimStep_guard`),
`Spec`/`Proof` pairs `NewElection`, `ResumeElection`, `Election__*`, `Results.lean`.

- **The leader fact** is the mutex's: `leaderAt pfx key c R := lockedAt pfx key c R` (at `R`,
  under the election's prefix, `key` present with create revision `c`, no key with a smaller one).
- **Specs, in words** (the prefix `pfx` is `NewElection`'s argument plus `/`, `ResumeElection`'s
  as given; `isElection` holds the session and prefix, `electionState e s st` the fields
  `leaderKey`/`leaderRev`/`leaderSession` (nil or `s`)/`hdr`; every method runs from any state,
  knowing etcd has reached `lo`):
  - `NewElection(s, pfx)`: `isElection` and the zero state; `ResumeElection(s, pfx, key, rev)`:
    the given key and revision, `s` as leader session (nothing checked).
  - `Campaign(ctx, val)` (cancelable `ctx`): `nil` ⇒ the key `key` (under the prefix) was created
    at `rev`, had value `val` at a revision `rv` (`keyValAt`: put, found, or proclaimed), and at
    `waitDeletes`' last revision `R ≥ rv` no key under the prefix was created before `rev`:
    **`leaderAt pfx key rev R ∨ campaignLost pfx key rev R`** (the second: `key` is not there with
    create revision `rev`); the state holds the key, `rev`, the session and the transaction's header.
    Errors: some state.
  - `Proclaim(ctx, val)`: `nil` ⇒ a leader session, and (key under the prefix) etcd's states at
    `r - 1` and `r ≥ lo` are a `ProclaimStep` (`proclaimedAt`: the guard
    `CreateRevision(key) = rev` held and the key was put with `val`); `ErrElectionNotLeader` ⇒ no
    leader session (unchanged), or the guard failed (the key is not there with create revision `rev`
    at some `r ≥ lo`, `notLeaderAt`; `leaderKey` cleared); other errors unchanged.
  - `Resign(ctx)`: no leader session ⇒ `nil`, unchanged; otherwise the guarded delete, leader key
    and session cleared, and on `nil` the key is not there with create revision `rev` at the
    header's revision `R ≥ lo`.
  - `Leader(ctx)`: `nil` ⇒ the response lists one key-value, the leader at its revision
    (`leaderKvAt`); `ErrElectionNoLeader` ⇒ the prefix is empty at some `R ≥ lo`.
  - `Observe(ctx)`: an SPSC channel (`isObserveChan`) of `*GetResponse`s each listing one
    key-value `v` with `observedAt pfx v R`, the `R`s non-decreasing from `lo` (a monotone ghost
    list). `observe` is its goroutine (Perennial `go`, the channel's producer).
  - `Key`, `Rev`, `Header`: the fields.
- **What `Observe` guarantees** (`observedAt pfx v R`): `v` is in etcd's state at `R` and either
  (1) it is the leader there, or (2) `v`'s key was the leader at an earlier `R0` with create
  revision `c0`, `v` is a later incarnation of it (`c0 < v.createRev`) and no key created before
  `c0` is alive at `R`, or (3) the prefix was empty at an earlier `R0` and every key alive at `R`
  (`v` too) was created after `R0`. Responses from `Get(pfx, WithFirstCreate)` are (1); a
  forwarded put on the leader's key is (1) if it has the leader's create revision, else (2); the
  first put after an empty prefix, and puts forwarded from it, are (3). (2) and (3) are the leader
  too with etcd's real watch (gap-free: the delete before a re-creation would end the forwarding;
  the first put's batch creates every key there is), but the client contract does not promise a
  gap-free stream, nor that a key's create revision is the revision of a put event, so the spec
  says what the code gives against it.
- **Finding: `Campaign` may return `nil` without being the leader.** After `waitDeletes`, `Campaign`
  returns `nil` without looking at its own key; if the key was deleted while it waited (the
  session's lease expired or was revoked, the session closed, another `Election` value on the same
  session and prefix (which shares the key `pfx/<lease>`) resigned, or anyone deleted it), `Campaign`
  still returns `nil` once the older keys are gone, and the caller believes it is the leader while
  another candidate may be. `Mutex.Lock` had the same gap and got a final `Get` of its key
  (`ErrSessionExpired`, upstream `b14c7cd44`, 2019, "concurrency: make lock more reliable");
  `Campaign` never did. The spec states it (`campaignLost`). Not yet reproduced by a Go test;
  a reproduction: candidate B campaigns behind leader A, B's key is deleted (e.g. `client.Delete`
  or revoking B's lease) while B waits, A resigns: B's `Campaign` returns `nil`, B's key absent.
  A fix would end `Campaign` as `Lock` does (a `Get` of the key comparing its create revision).
- **Contract extensions** (definitions; `InvEtcdTxn.lean`): the single-key watch becomes a
  **range watch** (`isEtcdRangeWatcher`, in `isEtcdMutexClient`: a key or a sub-prefix under the
  client's prefix, from `rev ≥ 0`): an event is a put or a delete, its key in the range, at a
  revision `≥ rev`, `< 2^63 - 1`, reached; a delete means absent; **a put's key-value is in etcd's
  state at the event's revision**; events sorted above the stream's position (a monotone list,
  as the cache's watch); the receiver **owns the header's `Revision`** of a response with events
  (`observe` writes it). The transaction builder's `Commit` gains a triple for **any** transaction
  (`txnAnyResult`). `waitDeletes` takes `maxCreateRev ≥ 0`. `concurrencyInit` holds Election's two
  errors. `Observe` takes `lo ≥ 0` (its gets' revisions are watched from, and `Watch` needs them
  non-negative; `0` is free).
- **Other observations** (stated, not bugs): `ResumeElection` does not add `/` to the prefix
  (`NewElection` does); after a failed `Proclaim` the leader key is `""` while the leader session
  stays, so a second `Proclaim` or a `Resign` commits a transaction on the key `""` (etcd rejects
  the empty key): their specs promise nothing beyond some header then (`txnAnyResult`).
- **Gates**: `lake build` passes (1814 jobs); no `sorry` of this work; `etc/tcb-report.py --check`
  unchanged (40 axioms, 1 sorry; `--collection concurrency`: 10 axioms, 1 sorry; no new trust-boundary
  item); `etc/goose.py --check` passes; `etc/gen-link.py --cache/--concurrency/--server` reproduce;
  `etc/verified-code.py --reuse`: `client/v3/concurrency` 31 verified, 1 unfinished (`Session.Close`)
  of 62, `election.go` 11 of 11 (164/164 lines); etcd 215 verified of 3599.
- **Push order**: etcd-grove `lean` only (Perennial and the etcd fork unchanged).

## Mutex: mutual exclusion (2026-10-10)

`client/v3/concurrency`'s `Mutex` (`mutex.go`, `key.go`) is specified and proved, with mutual
exclusion as a theorem over etcd's model. Design: `decisions.md`, "Mutex: `lockedAt`, exclusion from
the two history laws". Files: `client/v3/concurrency/InvMutex.lean` (vocabulary, exclusion),
`InvMutexLemmas.lean` (the gets, the transaction, the delete, `Lock`'s last step), `Results.lean`.

- **The ownership fact** `lockedAt pfx key c R`: etcd's state at `R` under the mutex's prefix has
  `key` with create revision `c`, and no key with a smaller one. **Mutual exclusion**
  (`lockedAt_exclusion`, exported as `mutex_exclusion`): two holders `(k1, c1)` at `R1`, `(k2, c2)`
  at `R2` with `c1 ≠ c2` are never both present in etcd's state at any revision `a ≥ R1, R2`; from
  `etcdState_revs` and `etcdState_create_persist` alone. `mutex_holder_unique`: two ownership facts
  at one revision have the same create revision (`etcdState_agree`). Equal create revisions with
  different keys (two keys created by one transaction) are not excluded: the model does not record
  who wrote a key (a mutex's transaction creates one).
- **Specs, in words** (the mutex's prefix `pfx` is `NewMutex`'s argument plus `/`; `isMutex` holds
  the session and prefix, `mutexState m st` the fields `myKey`/`myRev`/`hdr`, which every method
  accepts in any state; all knowing etcd has reached `lo`):
  - `NewMutex(s, pfx)`: `isMutex` and the initial state, for a client answering for `pfx + "/"`
    (`isEtcdMutexClient`). `NewLocker`: the same, wrapped in a `lockerMutex`.
  - `tryAcquire`: `myKey` under the prefix (`Sprintf`), then the transaction: an error, or
    `acquireResp` (at `r ≥ lo`, the key with create revision `myRev ≤ r`, and the owner get).
  - `TryLock`: `nil` ⇒ `lockedAt pfx key rev r`; `ErrLocked` ⇒ the key deleted (absent at some
    `r ≥ lo`), released state; other errors, some state.
  - `Lock` (a cancelable context): `nil` ⇒ at the last `Get`'s revision `R ≥ lo`,
    `lockedAt pfx key rev R` **or `keyRecreated`** (below); `ErrSessionExpired` ⇒ the key absent at
    `R`; other errors, some state.
  - `Unlock`: `nil` ⇒ the key absent at some `R ≥ lo`, released; `ErrLockReleased` ⇒ no key;
    other errors (the delete, the `HasPrefix` check), unchanged.
  - `IsOwner`: the comparison `CreateRevision(myKey) = myRev`; `Key`, `Header`: the fields.
  - `waitDelete(ctx, client, key, rev)`: `nil` ⇒ `key` absent at some `r ≥ rev` (a delete event);
    `waitDeletes(ctx, client, pfx, n)` (`n > 0`): `nil` ⇒ at some `R ≥ lo` no key under `pfx` has a
    create revision `≤ n`.
- **Finding: `Lock` may return `nil` without the lock.** `Lock`'s last check is that `myKey`
  exists (`len(gresp.Kvs) == 0`), not that its create revision is still `myRev`. Two `Mutex`
  values of one session on one prefix share the key (`pfx/<lease>`); if the other one unlocks
  (e.g. its `Lock`'s context is canceled, which calls `Unlock`) and locks again while this one
  waits, the key is re-created with a later create revision, `waitDeletes(myRev - 1)` returns, and
  `Lock` returns `nil` while a key created between `myRev` and the new create revision may hold the
  lock too. The spec states it (`keyRecreated pfx key rev R`: present with a create revision above
  `rev`, nothing older); with one `Mutex` per session and prefix the disjunct cannot arise, but the
  model cannot express that (it does not record who writes). Not confirmed by a Go test; a fix
  would compare `gresp.Kvs[0].CreateRevision` with `m.myRev`.
- **Client contracts, extended** (definitions; `isEtcdMutexClient` bundles them):
  `kvGetResult` lists, for any get of a range under the prefix at the latest revision, etcd's
  selection (`getRespRange`: sorted, limited, filtered — `rangeKvsOk`; the single-key `Get` and
  `waitDeletes`' `WithLastCreate, WithMaxCreateRev`); `isEtcdDeleteKV` (`Delete` as a
  one-operation transaction, `deleteResult`); `isEtcdKeyWatcher` (a single-key watch from `rev`:
  an SPSC channel whose events are of the key, at revisions `≥ rev` etcd reached, and a delete
  event at `r` means the key is absent at `r`, `keyWatchRespOk`); `txnOpRespAt`'s `ResponseOp` is
  non-nil.
- **`Sprintf`**: Perennial's model returned the format string, so `myKey` would have been
  `"%s%x"`, not under the prefix (the transaction's `Under` premise and `Unlock`'s `HasPrefix` need
  it). Perennial **`d240c1732`** (on `7d0b56b07`): `fmt.Sprintf` formats `%%` and `%s` of a string
  argument exactly and makes the rest arbitrary at any other directive or with arguments left
  over (`fmt.SprintfOut`, an over-approximation); `wp_Sprintf` needs `StringArgsWf` (an argument
  of dynamic type `string` holds a string), so raft's `fmt.Sprintf.spec` gained that premise
  (`newRaft` passes `uint64`s). The mutex gets `pfx <+: myKey`; nothing about `%x` (not needed:
  exclusion does not use distinct keys). Also a trusted model of `strings.HasPrefix`
  (`wp_HasPrefix`: `decide (pfx <+: s)`; a byte loop, Goose has no string slicing).
- **The panic question** (settled since "Panic and recover": specified, a return or `panic(err)`):
  `lockerMutex.Lock`/`Unlock` call `panic(err)` on any error of
  `Mutex.Lock`/`Unlock`, which every client call allows, and Perennial's `panic` is a stuck
  expression (a WP of it is unprovable). A `sync.Locker` spec would have to promise no error, which
  is false of the client contract: they are not specified (counted "translated"), and `NewLocker`
  is.
- **Translation**: `etcdserverpb.ResponseOp.GetResponseRange` (proved), `mvccpb.Event_PUT`/
  `Event_DELETE` (constants; were axiomatized `val`s). `withTop`/`WithFirstCreate`/
  `WithLastCreate` return the slice's capacity (`waitDeletes` appends to it). concurrency's package
  facts (`concurrencyInit`): Mutex's three errors. No change to etcd's Go code.
- **Perennial tooling** (worked around in `Mutex__tryAcquire.lean`): `wp_apply` fails silently on
  a triple whose continuation's premise is a local predicate (`B b`, the transaction builder's
  state): `wp_apply_post` calls `whnfR` outside the goal's context ("unknown free variable",
  swallowed); `wp_apply_raw` works. A fix in Perennial would run it under `mv'.withContext`.
- **Gates**: `lake build` passes (1791 jobs); no `sorry` of this work; `etc/tcb-report.py --check`
  after `--update`: 40 axioms, 1 sorry (new in the trust base, all existing model axioms:
  `etcdState_revs`, `etcdState_create_persist`, `etcdState_agree`); `--collection concurrency`
  (now `Link` and `Results`): 10 axioms, 1 sorry; the other collections unchanged;
  `etc/goose.py --check` passes; `etc/gen-link.py --cache/--concurrency/--server` and
  `gen-btree-link.py` reproduce; `etc/verified-code.py --reuse`: `client/v3/concurrency` 20
  verified, 1 unfinished (`Session.Close`) of 62, `mutex.go` 9 of 11 (89/101 lines), `key.go` 2 of 2;
  etcd 204 verified of 3599.
- **Push order**: Perennial `lean` (`d240c1732`, a fast-forward of `7d0b56b07`) first, then
  etcd-grove `lean`. The etcd fork is unchanged.

## The register example: verified over raft, logically atomic (2026-10-10)

`examples/register/register.go` (a replicated register on raft's `Node`; Goose project
`register`, `Code/github_com/mit_pdos/etcd_grove/examples/register.lean`) is specified,
proved and linked: `encode`, `decode`, `fits`, `NewStorage`, `(*Storage).InitialState`,
`(*Storage).Snapshot`, `New`, `run`, `apply`, `do`, `Put`, `Get`
(`Proof/github_com/mit_pdos/etcd_grove/examples/register/`; `Link.lean` generated by
`etc/gen-link.py --register` from `etc/link-lean-first-register.txt`, raft's callees linked
in raft's `Link.lean`; `#print axioms` in `Results.lean`; collection
`etc/tcb-collections/register.txt`). No `sorry`, and no axiom of this repository: the
results rest only on Perennial's axiomatized standard-library types.

The client-facing statements (`Results.lean`; decisions.md, "The register: TaDa proposals
over raft's client log"):

- `Put(val)` (`val.length < 2^62`): `{isRegister γr γp r ∗ opCred γp 1 ∗ AU <{∃∃ x, regVal γr
  x}> @ regMask, ∅ <{regVal γr val, COMM Φ}>} … {Φ}`; `Get()` the same with `<{regVal γr x,
  COMM Φ x}>`, returning `x`. The update runs when raft commits the operation's first entry
  (the linearization point); `regMask` is everything but raft's commit invariant and the
  register's.
- `New(id, node, storage, send)`: `regInv γr`, the node's driver token at `[]`
  (`nodeDriver`), the storage's record, `isCommitted γr.raft []`, `id ↪[γr.seq] 0` and
  `sendSpec send` give `∃ γp, isRegister γr γp r ∗ opCred γp (2^64 - 1)`; `run` is forked.
- `*register.Storage` is a raft `Storage` (`register_storage_isStorage`: `regStorRec ⊢
  isStorage (regStorIface s)`, the storage model `regStorageModel`), its `InitialState` what
  `RestartNode` asks (`register_storage_initialState`).
- The ghost state: `regStorInv_alloc`, `regInv_alloc` (`Alloc.lean`), from raft's
  `ownRaftGhost_alloc` (which now also hands the client `cLog γ []` and the authorities of
  the fresh-data tokens and of the proposed slices).

Raft changes for it (commit `b856a83be`): proposals are logically atomic over a client
log (`cLog`); `node.Propose` deposits the client's atomic update, which the ghost commit
fires; `node.Step` takes a forwarded `MsgProp` (`fwdP`); `isEntryR` records each entry's
client data (`entData`). `MemoryStorage.Append` takes an empty batch without a token
(`26a6bc1d4`). Go changes (`ec7dc0a13`, `b4a362514`, minimal, `go test -race` passes):
`apply` dedups by the operation's encoding (`applied map[string]bool`), not by a sequence
number (wrong under concurrent operations of one replica); `encode` appends
`[]byte(val)`; `InitialState` returns the empty `HardState` and the voters slice itself
(no `MemoryStorage` call: `RestartNode` takes a fixed `ConfState`); `run` spins rather
than append past `2^61` entries (`fits`).

Out of scope: liveness (an operation may wait forever), the transport (`send` is a
callback that gets the messages with what `Ready` says of them), `Stop`.

## `node.go`: the concurrent `Node` (2026-10-10)

Specified, proved and linked (`Link.lean` by hand, `etc/link-lean-first.txt`; `#print
axioms` in `Results.lean`): `RestartNode`, `newNode`, `node.run`, `node.Propose` (through
`stepWait`/`stepWithWaitOption`), `node.Step` (through `step`), `node.Tick`, `node.Ready`,
`node.Advance`, and `raft.hasLeader`. No `sorry`, no new axiom: every node result rests on
exactly the axioms of the RawNode results it calls. Out of scope (their channels carry
`P := False`, never sent on): `Stop`, `Status`, `ProposeConfChange`, `ApplyConfChange`,
`Campaign`, `ReadIndex`, `TransferLeadership`, `ReportUnreachable`, `ReportSnapshot`,
`ForgetLeader`, `StartNode`/`Bootstrap`; `ctx` is `context.Background()` only.

The client-facing specs (`InvNode.lean` defines the predicates; decisions.md, "node.go"):

- `RestartNode`: `NewRawNode`'s premises plus `inv budgetN (budgetInv bud) ∗ termLB bud 0`
  ⇒ `∃ γn n, ⌜γn.raft = γ ∧ γn.bud = bud ∧ γn.stor = si ∧ nd = interface.mkOk (*node) n⌝ ∗
  isNode γn id n ∗ nodeDriver γn id n []`.
- `Propose(ctx, data)`: `{isNode ∗ data ↦*□ _} … {err, True}`.
- `Step(ctx, m)`: `{isNode ∗ netP γ id m} … {err, True}`; `netP` = `NetMsgOk id m`, the
  entries/context read-only, `isMessage` of its abstraction, and `termLB bud m.Term`.
- `Tick()`: `{isNode ∗ tickCred bud 1} … {True}`.
- `Ready()`: `{isNode} … {ch, isReadyChan γ ch}`; receiving (`node_ready_receive`) with
  `nodeDriver γ id n ds` gives `readyData γ rd ds ce es ms` (the committed entries `ce`
  with `isCommitted (ds ++ ce)`, the entries `es` with `appendRight`, the messages with
  `isRaftMsg` and `termLB` of their terms) and `nodeDriverBusy γ id n (ds ++ ce) es`.
- `Advance()`: `{nodeDriverBusy γ id n ds es ∗ appendReceipt γ.stor es} … {nodeDriver γ id n ds}`.
- The term budget (`budget_alloc N`, `N < 2^64 - 1`): `M + c < 2^64 - 1` for the bound `M`
  on every term and `c` tick credits out; `budget_spend` turns a credit and `termLB t`
  into `t + 1 < 2^64 - 1` and `termLB (t + 1)`.

`run`'s proof (`node__run.lean`, lemmas in `InvNodeRun.lean`): the loop invariant
`runHead` (the node at `ownRawNode`, `headRest`: no `Ready` out with `rof` whole, `dlv`'s
half, a stale `Ready` possibly armed (`staleOk`); or one out, `rof`'s half recording it);
after the first statement `runMid` (also a fresh `Ready`, `ownRawNodeReady`, or an idle
node with a stale one). `wp_join` twice (the `HasReady` branch, the leader check), one
`select` of eight cases. `r.Step` on the node: `wp_rn_raft_Step_net`/`_prop` (the tails of
`RawNode.Step`/`Propose`); an abandoned `Ready` stays armed
(`ownRawNodeReady_abandon_keep`, `SliceShape` to rebuild its empty messages slice).

RawNode spec changes for `node.go` (this session; commits `b68a476e6`, `7796d5635`,
`9a67d5ce5`, `23c156cfc`): `HasReady`'s `false` gives `ownRawNodeIdle` (pinned: no
message queued, no unstable entry); `RNState` lower bounds `outlb`/`unst`/`clb`
(`NGhost` in `NState`) raised by `ownRawNodeReady_abandon`; `acceptReady` takes
`ownRawNodeReady … true` (the append right handed out first, `ownRawNodeReady_handout`,
`logHanded`) and no longer returns it; `raftLog.acceptUnstable` likewise; `Advance` takes
`rs.unst = false` and returns `t = rs.term`; `raft.Step`'s `MsgStorageAppendResp` premise
has `s.gh.unst = false`; `OutTermOk`: no `MsgPreVoteResp` with pre-vote off; the raft
struct's `id` and `logger` persistent (`raftOwn`, `rawNodeOwn`: `Tick` reads them
concurrently); `newRaft` returns `s.gh = {}`.

Not checked: `etc/tcb-report.py --check` (needs a full build; the disk is short).

## bbolt: not goosable as written; the `unsafe` it needs (2026-10-10)

bbolt (v1.5.0, etcd's dependency) works by reading `[]byte` buffers (the mmap'd file, heap
pages) as structs through `unsafe.Pointer`, with `uintptr` arithmetic. Perennial's typed heap
gives that no meaning, and it leaves `uintptr ↔ pointer` stuck on purpose. `notes/bbolt-unsafe.md`
inventories every use and says what a model needs: layout constants, a byte view of
pointer-free structs (the core change), byte-offset arithmetic, slices over raw memory, and a
file-backed mmap. It also covers the fork alternative. What is goosable now:
`internal/common`'s page-id helpers are translated with bodies
(`Code/go_etcd_io/bbolt/internal/common.toml`), with package init, the sorted-list model,
`wp_slice_append_in_place` and the `Mergepgids` spec in
`{Proof,Spec}/go_etcd_io/bbolt/internal/common/`. `Mergepgids` is proved (no `sorry`; `Results.lean` prints its axioms). Most of
`internal/freelist` and `errors` are goosable too.

Toward modeling and verifying all of bbolt (`notes/bbolt-unsafe.md`, "Where Perennial stands"):
- Perennial's array allocation is a `-- TODO` that diverges (`AngelicExit`), so every proof past
  a non-empty `make` here holds vacuously (31 files use `wp_slice_make*`/`wp_slice_append`).
- Perennial has no byte-level memory and no crash semantics; both are core changes.
- Goose now folds `unsafe.Sizeof`/`Offsetof`/`Alignof`, `uintptr` constants and labeled loops
  (Perennial branch `goose-bbolt`, `ff60796`; not pinned).

## `node.go` groundwork: abandoning a `Ready`, pre-vote off, the messages' terms (2026-10-10)

Three pieces `node.go`'s proof will need (uncommitted Perennial change: `Slice.lean`).

- **Abandoning a computed `Ready`.** Perennial: `wp_slice_append_undo` (`Slice.lean`, next
  to `wp_slice_append`): `wp_slice_append`'s triple plus a wand
  `s' ↦* (vs ++ vs') ∗ ownSliceCap V s' (DFrac.own 1) -∗ sl ↦* vs ∗ ownSliceCap V sl
  (DFrac.own 1)` -- in place, the new slice is split at `len(sl)` and the rest goes back
  to `sl`'s capacity (`ownSlice_append_undo_in_place`); reallocating, the old slice and
  capacity are kept. `readyWithoutAccept` builds `rd.Messages` with it, so
  `ownRaftPhysReady` holds `Hundo` (from `rd.Messages`' contents and capacity back to
  `r.msgs`'), and `ownRawNodeReady` gained the index `ms` (the messages handed out;
  `acceptReady.spec` takes it as one more `∀`). `ownRawNodeReady_abandon`
  (`InvRawnodeReady.lean`): `rd.Messages' ↦* ms -∗ ownSliceCap … -∗ ownRawNodeReady γ rn
  id rs rd ce es ms -∗ ownRawNode γ rn id rs` (premises `rs.steps = []`,
  `rs.unpersisted = []`, `readyWithoutAccept`'s); `readyWithoutAccept.spec` returns it as
  `"Habandon"`.
- **Pre-vote off at the RawNode.** `NetFrame` and `LocalFrame` (hence `TickStep`) gained
  `s'.prevote = s.prevote` (`keep_frame`/`stepdown_frame`/`keep_frame_logst`/
  `NetFrame.of_logst` take it as an auto-param `rfl`; `hup`'s post states it);
  `ownRawNode` and `ownRawNodeReady` have the scope conjunct `"%Hpvoff" ∷ ⌜s.prevote =
  false⌝` (named so as not to clash with the proofs' `Hpv`), `ownRawNode_intro` takes it,
  and `NewRawNode.spec` requires `cv.PreVote' = false`.
- **The terms of `Ready`'s messages.** `readyWithoutAccept.spec` and `Ready.spec` return
  `"%Hmsgs_term" ∷ ⌜∀ m ∈ ms, uint.Z m.Term' ≤ uint.Z rs.term⌝`. The route, the cheapest
  sound one found: `ownRaftPhys` records of every queued message (both queues)
  `OutTermOk s.prevote s.term m` -- `s.prevote = false → Term ≤ s.term` (monotone in the
  term, `wp_store_Term` keeps it; `ownRaftPhys_intro`, the queue accessors' wands,
  `ownRaftPhys_view` and its `Hclose` carry it). `send` stamps the node's term into
  everything but a forwarded `MsgProp` (`0`) and a vote message, whose term `SendOk`'s
  vote clause now bounds: `s.prevote = false → Term ≤ s.term`. Its callers: a
  `MsgVote`/`MsgVoteResp` is of the node's term (`campaign`'s election, `Step`'s vote
  branches); a pre-vote message is sent only by `campaign`'s pre-election, which (with
  `hup`) now takes `t = campaignPreElection → s.prevote = true` (`Step`'s `MsgHup`
  branch calls it so exactly when `r.preVote`), or in answer to a `MsgPreVote`, for which
  `raft.Step.spec` now requires `s.prevote = true` (a transport premise: pre-vote
  messages reach only nodes with pre-vote on, the setting being the cluster's;
  `RawNode.Step` takes no pre-vote message, so it is vacuous there). So no ghost
  tracking of "no pre-vote message in the outbox" was needed. *Rejected*: tracking
  "no `MsgPreVoteResp` to another node in the outbox" in `ownRawNode` (needs a new
  `raft.Step` postcondition on the outbox's growth, proved per branch) or a ghost flag in
  `NState` (the same per-branch frame work).

`lake build Proof.go_etcd_io.raft.v3.Link Proof.go_etcd_io.raft.v3.Results` passes; no
new `sorry` or axiom.

## `RawNode.Ready` split: `readyWithoutAccept` and `acceptReady`, for `node.go` (2026-10-10)

`node.go`'s `run` does not call `Ready`: it calls `readyWithoutAccept`, hands the `Ready`
to the application (`readyc <- rd`), and only then `acceptReady(rd)`, with no raft step in
between. Both halves are now specified, proved and linked (Lean-first), and `Ready`'s proof
composes their specs; `RawNode.Ready.spec` is unchanged.

- `ownRawNodeReady γ rn id rs rd ce es` (`InvRawnodeReady.lean`, new): the node between
  the two -- `ownRawNode`'s conjuncts at an empty queue and nothing unpersisted, with the
  raft struct open without the outbox's contents (`ownRaftPhysReady`: `ownRaftPhys_view`'s
  output minus `r.msgs`' slice, which `readyWithoutAccept` built `rd.Messages` from in
  place), and what `acceptReady` reads of `rd`: `SoftState` `nil` or read-only, no snapshot
  nor read states, `CommittedEntries ↦*□ ce` with its capacity (for the queued
  `MsgStorageApplyResp`), `ce` the next committed entries (`logCommittedEnts`) extending
  `rs.delivered` (`isCommitted`), `es = nextUnstable`. `acceptReady` does not read
  `rd.Messages` (it reads `msgsAfterAppend` again, which the node keeps, and sets both
  outbox fields to `nil`).
- `RawNode.readyWithoutAccept.spec`: premises as `Ready`'s (`rs.steps = []`,
  `rs.unpersisted = []`); post `ownRawNodeReady γ rn id rs rd ce es` and everything the
  application gets with `rd` (`CommittedEntries`, `isCommitted γ (rs.delivered ++ ce)`,
  `Entries`, `Messages` with their capacity and `isRaftMsg`, no snapshot/read states).
- `RawNode.acceptReady.spec`: from `ownRawNodeReady … rd ce es` to `ownRawNode γ rn id
  { rs with delivered := rs.delivered ++ ce, unpersisted := es, steps := steps }` and
  `appendRight rs.storage es`.
- The proofs are the old `Ready` proof cut at the call of `acceptReady`
  (`RawNode__readyWithoutAccept.lean`, `RawNode__acceptReady.lean`; the helpers went with
  the half that uses them). `acceptReady` keeps less of `rd`: `prevSoftSt`/`prevHardSt`
  become some read-only `SoftState`/some value (no spec states them), so the joins no
  longer track `nodeSoftstate`/`nodeHardstate`. Neither half needs the `maxHeartbeats`
  bump the one proof had.
- Linked by hand in `Link.lean` (`RawNode.wp_readyWithoutAccept`, `RawNode.wp_acceptReady`,
  `RawNode.wp_Ready` from the two); `etc/link-lean-first.txt` lists the two and overrides
  `RawNode__Ready`'s Rocq callees; `Results.lean` prints their axioms.

**Open** (closed the same day: `ownRawNodeReady_abandon`, "`node.go` groundwork" above):
abandoning a `Ready` (`node.go` recomputes `rd` when its `select` takes another
case, then steps the node) has no lemma: the messages would have to go back to the node,
but `readyWithoutAccept`'s appends to `rd.Messages` may reallocate, consuming `r.msgs`'
slice. A `node.go` proof needs either such a lemma (e.g. `readyWithoutAccept` keeping
`r.msgs`' slice and handing out only a copy's worth, or a spec variant) or to treat the
outbox as handed out once computed.

`lake build Proof.go_etcd_io.raft.v3.Link Proof.go_etcd_io.raft.v3.Results` passes; no
new `sorry` or axiom (`wp_Ready`, `wp_readyWithoutAccept`, `wp_acceptReady` have no
`sorryAx`).

## The storage contract: a pending append, for `node.go` (2026-10-10)

The application may now append a `Ready`'s entries while raft keeps reading the storage
(decisions.md, "Storage: a pending append, for node.go"):

- `StorState.pend` (the batch being appended); `isStorageWith P AT DT st` answers `Term`
  and `Entries` only below the batch (`PendFrom`), `LastIndex` only with nothing pending,
  and has two laws, `Hhandout` and `Habsorb`; `StorageModel` gained `appendTok` and
  `appendedTok`. `storApp` moved to `InvStorage.lean` (`storAbsorb`, `PendOk`).
- `ownRaftLog`: `Hstor` (`lv.storage' = ls.storage`, the new `LogState.storage`) and
  `Hpend` (`PendLogOk`: the batch is `unpersisted`, at or above `unstable.offset`); the
  reseal macro tries `exact Hstor`/`exact Hpend`. `NetFrame`/`LocalFrame`, the
  `maybeAppend`/`handleAppendEntries` frames and `newRaft`'s post keep the storage.
- `raftLog.acceptUnstable` takes `ls.snap = none` and returns `appendRight ls.storage
  (nextUnstable ls)`; `RawNode.Ready` returns `"Happ" ∷ appendRight rs.storage es`.
  `ownRawNode_persist` is gone: `ownRawNode_appended` absorbs `appendReceipt rs.storage
  rs.unpersisted`. `RNState.storage` (new): `NewRawNode` returns `storage := interface.ok
  si` and takes `σ.pend = []` (as `newRaft`, `newLogWithSize`).
- `MemoryStorage`: `ownMemoryStorage ms γs σ` (names `MemStorNames`: `hist`, `done`, `ep`,
  see `InvMemstorage.lean`'s header), `memAppendTok`/`memAppendedTok`, the laws
  `memStorage_handout`/`memStorage_absorb`; the method specs take `γs` and the new
  premises (`Snapshot` no longer promises non-emptiness); `MemoryStorage.Append`
  (consumes the right, returns the receipt, under the lock) and `NewMemoryStorage` (at
  `memStorEmpty`) specified and proved, linked (`etc/link-lean-first.txt`, `Link.lean` by
  hand: `etc/gen-link.py` against the Rocq checkout no longer reproduces `Link.lean`).
  `is_Storage_MemoryStorage ms γs` is for `ownMemoryStorage ms γs σ ∗ ⌜σ.ss.index ≠ 0⌝`.

**Open**: a new `MemoryStorage` (empty snapshot) is not an `isStorage`: `maybeSendSnapshot`
follows `ErrUnavailable` too (a peer's `Next` past the log), not only `ErrCompacted`, so the
`Snapshot` clause cannot be weakened to "non-empty once compacted" without a bound
`Next ≤ lastIndex + 1` in the tracker invariant (decisions.md, same section).

`lake build Proof.go_etcd_io.raft.v3.Link Proof.go_etcd_io.raft.v3.Results` passes (and
every raft module); no new `sorry` or axiom.

## Merge: upstream's RawNode work (2026-10-10)

Merged upstream `lean` (`f380444db`: `RawNode.Step`/`Tick`/`Campaign`/`NewRawNode` proved,
the `Advance` gap closed, `raft.Step` framing, the generic TCB/verified-code scripts, their
replacement of the `Sprintf`/`Join`/`rand.Int` axioms, Perennial `f52ce33dc`) into the
cache-as-shipped and `client/v3/concurrency` line (`56084b262`). Resolutions:

- **Pin**: ours, Perennial `7d0b56b07` (contains their `f52ce33dc`; on GitHub). Their
  lakefile change was only the pin.
- **Scripts**: theirs (`etc/proof_roots.py`, `tcb-report.{py,lean}`, `verified-code.{py,go}`).
  They find the roots themselves (every `Link.lean`/`Results.lean`), so the cache's
  `Link`/`Results`, the concurrency `Link`, the btree's and the server's (its own Lean run,
  through `EtcdDeps`) are roots without a list. Two additions for the concurrency `Link`,
  whose results are in a namespace of their own: `proof_roots.link_namespace`, and
  `verified-code.py` drops that namespace before another package's qualifier
  (`concurrency.v3.wp_OpPut` is clientv3's `OpPut`; what our `NAMESPACED` did, now generic);
  and `resolve_local` takes a qualifier shared by a part's package and another (`v3`: the
  `EtcdDeps` raft and clientv3) as the other's when that package has the function (else
  clientv3's 23 linked functions counted as `EtcdDeps`'s raft). New collections
  `etc/tcb-collections/{cache,concurrency,server,btree}.txt`, and every collection's
  baseline recorded (raft: `reflect.DeepEqual` only; cache 9 axioms; concurrency 4 axioms +
  `context.wp_WithDeadlineCause`; server 26 axioms; btree none).
- **Axioms**: both sides proved `fmt.Sprintf`/`strings.Join` from Perennial's models; theirs
  (`66665c735`) also proves `rand.Int`, with `mz < 2^63` added to its spec (what Perennial's
  model covers; `lockedRand.Intn` passes an `int64`, and proves the bound), which is sound:
  taken, the axiom is gone. The merged files have one theorem each; `Base.lean` no longer has
  `isRandInitialized` (Perennial's).
- **Baseline** (`etc/tcb-baseline.txt`): the union, relative to `d45daf8ab`: +
  `etcdStep_delete_present`, `proto.Clone.wp_proof`, `sorry Perennial.context.wp_WithDeadlineCause`
  (ours), − `rand.Int.wp_proof` (theirs; their RawNode work added none); 37 axioms, 1 sorry.
- **Gates**: `etc/goose.py --check` (both translations up to date at Perennial `7d0b56b07`,
  etcd `ab1deb078`); `lake build` passes (1764 jobs), no proof fix needed; `etc/tcb-report.py
  --check` matches without `--update`; every collection `--check`s; `etc/gen-link.py
  --cache`/`--concurrency`/`--server` and `etc/gen-btree-link.py` reproduce their `Link.lean`
  (raft's needs the Rocq directory: untouched); `etc/verified-code.py --reuse`: etcd-raft
  187/323 (2322 of 3641 lines), etcd 193 verified, 1 unfinished, 13 assumed of 3599; the cache
  107/107 sorry-free; `client/v3/concurrency` 9 verified + 1 unfinished (`Session.Close`);
  `client/v3` 58; the server's `etcdserver` 6, `cindex` 8, `schema` 5. (`Compare.GetKey`, named
  `concurrency.Compare.wp_GetKey` in the concurrency `Link`, still resolves outside the totals.)
- **Push order**: Perennial `7d0b56b07` is on GitHub; the fork's `ab1deb078` on `goose-lean`;
  so etcd-grove alone.

## `RawNode.Step`: a `MsgApp` between `Ready` and `Advance` (2026-10-10)

`RawNode.Step.spec` lost its premise `m.Type' = MsgApp → rs.steps = []`: every message type
may be stepped with a `Ready` outstanding, as the concurrent `node.go` does (decisions.md,
"RawNode: the acknowledgement across a truncation"). The premise was there because the
queued `MsgStorageAppendResp` asked `e.index < offsetInProgress` (`PendingOk`), which a
truncating `MsgApp` breaks. A single-step argument does not repair it: a first `MsgApp`
may truncate the log below `e`, and a second, from a leader of a higher term that has
`e`, put it back, so the acknowledgement hits with `e.index ≥ offsetInProgress` (reachable,
Figure 8 of the Raft paper). It is still right because the storage holds the log of the
`Ready` up to `e`, which agrees with the log up to `e` by Log Matching. So:

- `LogState` gained the ghost field `stored` (what the storage holds once `unpersisted` is
  appended; `LogPersistOk`'s new last conjunct `storApp σ pend = stored`); only `Ready`
  changes it (`logAcceptUnstable`: the whole log); `newLogWithSize`/`newRaft` start it at
  the storage's entries.
- `StableOk` (`raft.Step`'s `MsgStorageAppendResp` premise, `raftLog.stableTo`'s) asks
  `stored = (sents ++ uents).take (id.index - prev.index)` instead of
  `id.index < offsetInProgress`; `persist_stable` covers both cases.
- `NetFrame` and `LocalFrame` (`raft.Step`'s postconditions) also keep `prev` and `stored`
  (`HandleAppResult`, `raftLog.maybeAppend`'s spec, `logStableTo_fields`,
  `logAcceptApplying_fields` say so; `keep_frame`/`stepdown_frame` take them as
  auto-params, `rfl`).
- `PendingOk (.appendAck t e)` is `t ≤ term ∧ plogLast prev stored = e`; `stepsOk_mono_le`
  takes `prev`/`stored` kept instead of `offsetInProgress` not moving back.
- `ownRawNode` keeps `storedRecs γ prev stored` (`PlogWf` and `logRecs` of `stored`,
  `Hstrecs`; `ownRawNode_intro` takes it); `Ready` takes it from the ghost state
  (`ownRaftGhost_storedRecs_keep`), `NewRawNode` has `stored = []`. `Advance` derives
  `StableOk` with `stableOk_of_stored` (`stored_agree`: Log Matching via `logRecs_agree`
  and `plog_match_down`).

`lake build Proof.go_etcd_io.raft.v3.Link Proof.go_etcd_io.raft.v3.Results` passes; no new
`sorry` or axiom.

## The `Advance` gap closed (2026-10-10)

`RawNode.Advance` steps any queue `Ready` left, the node's own responses included;
`RNState.advanceable` is gone (decisions.md, "RawNode: client-facing specs", "The gap --
closed"). `Advance` now takes `rs.term + 1 < 2^64` and returns the term up by at most one
(`∃ t, ownRawNode … { rs with steps := [], term := t } ∗ ⌜rs.term ≤ t ≤ rs.term + 1⌝`);
`Ready` returns no flag. Underneath: `ownRaftPhys` records `msgsAfterAppend`'s messages
(`AAMsgOk`) and the term never moves back (`raft.wp_store_Term`'s premise, threaded through
`reset`/`becomeX`/`loadState`); `SendOk`'s response clauses, `appendEntry`/`becomeLeader`
(`s.term ≠ 0`), `handleAppendEntries`/`handleSnapshot` (`m.From ≠ id`),
`stepFollower`/`stepCandidate`/`stepLeader` gained premises; `raft.Step`'s spec gained
`RespStep` in its postcondition and its `MsgPreVoteResp` no-wrap premise is only for a
pre-candidate; `ownRaftGhost_term_nz` (`Protocol/Facts.lean`). `lake build
Proof.go_etcd_io.raft.v3.Link Proof.go_etcd_io.raft.v3.Results` passes; no new `sorry`
or axiom.

## `RawNode.Campaign`, `RawNode.Step` (2026-10-09)

Both proved and linked (`RawNode.wp_Campaign`, `RawNode.wp_Step`; Lean-first, in
`etc/link-lean-first.txt`, added to `Link.lean` by hand: `etc/gen-link.py`'s output already
differed from the checked-in file, e.g. `confchange.Restore`'s callees). `RNState` gained
`term` (`ownRawNode`: `rs.term = s.term`).

- `Campaign`: for `rs.term + 1 < 2^64` (Go panics when the campaign wraps the term), `nil`,
  the term up by at most one; the rest of `rs` kept, also between `Ready` and `Advance`
  (`stepsOk_mono_le`: the queue survives a higher term).
- `Step`: for a message of replication or election (`NetMsgOk`: `MsgApp`, `MsgAppResp`,
  `MsgVote`, `MsgVoteResp`, `MsgHeartbeat`, `MsgHeartbeatResp`, with `raft.Step`'s transport
  premises; no pre-vote, snapshots, read-index or leader transfer), its `isMessage`, read-only
  entries with the capacity owned, a `Context` that is not the transfer marker: the term
  moves up to at most the message's, `err` unspecified (the guards' rejections change
  nothing). A `MsgApp` only with no `Ready` outstanding (`rs.steps = []`: it may lower
  `offsetInProgress`; premise gone 2026-10-10, see above). The guards' `IsLocalMsg`/`IsResponseMsg` (`isMsgInArray`) are
  specified to return some `bool` (for a nonnegative type: `MessageType` is an `int32`, a
  negative one panics); `isInitialized` gained their tables and the two error globals.

- `Tick` (proved and linked, `RawNode.wp_Tick`): for `rs.term + 1 < 2^64`, the term up by at
  most one, the rest of `rs` kept (also between `Ready` and `Advance`). `ownRaftPhys` now
  records `r.tick` (`Htick`: once `NState.ticking` is set, `TickFnOk r rv.tick'`: the method
  value `r.tickElection` or `r.tickHeartbeat`, not tied to the role -- both are safe in any
  role); every `becomeX` model sets `ticking`, and `NStateWf` says it is set (only
  `newRaft`'s struct before its `becomeFollower` has `r.tick = nil`). `raft.tickElection`
  and `raft.tickHeartbeat` are specified like `raft.Step` (`TickStep`: `NetFrame`, the term
  up by at most one, `offsetInProgress` not back) and proved, with `pastElectionTimeout`.

- `NewRawNode` (proved and linked, `wp_NewRawNode`): a node of a new cluster -- an empty
  storage, no `HardState`, nothing applied, synchronous writes, and `ownRaftGhost γ id
  initPState` with `isCommitted γ []` (what `ownRaftGhost_alloc` hands out) -- comes out as
  `ownRawNode` with nothing delivered, to persist or to step, at term `0`. `newRaft`'s
  postcondition gained the initial log (`prev`, `sents`, `uents`, `committed`, `applying`,
  `unpersisted`, `snap`) and gives the `validate`d `Config` back (`ConfigPreserved` gained
  `AsyncStorageWrites`); `raft.softState`/`raft.hardState` are specified and proved;
  `newRaft_post_init` moved from `Results.lean` to `Spec/NewRawNode.lean`.

Next: the `Advance` gap.

## `raft.Step` frames the log and bounds the term (2026-10-09)

Towards `RawNode.Step`/`Tick`/`Campaign` (a network message, a tick): `raft.Step`'s
postcondition gained, for every type but `MsgSnap`, `"%Hframe"` (`NetFrame s s'`:
`applying`, the pending snapshot and `unpersisted` kept; not for a
`MsgStorageApplyResp`) and `"%Hterm"` (`TermStep m s s'`: the term never moves back, a
`MsgHup` raises it by at most one, any other message but a `MsgPreVoteResp` at most to the
message's term, and `offsetInProgress` moves back only on a `MsgApp`). Every branch
lemma under `Proof/go_etcd_io/raft/v3/raft__Step/` states both (`stepPost`,
`finish_branch` carry them); `raft.hup`'s spec says the log is untouched and the term
moves up by at most one; `raftLog.maybeAppend`'s and `handleAppendEntries`'
(`HandleAppResult`) postconditions keep `applying`, `snap`, `unpersisted`. `lake build
Proof.go_etcd_io.raft.v3.Link Proof.go_etcd_io.raft.v3.Results` passes; no `sorry` added.

## Perennial `f52ce33dc`; retargeting raft to upstream (2026-10-09)

Re-pinned to Perennial `f52ce33dc` (`lean`: `79adaac01` below merged with the Goose
work for upstream raft, `b0293f805`/`d57475ff3`: each loop iteration has its own iteration variables where that
is observable, range loops over arrays, `fallthrough`, a `break` in a `switch`/`select`
case ends that statement, function-local types, an empty void function body is
`return: #()`). Regenerated: `Code/go_etcd_io/raft/v3.lean` (the `trace*` stubs; `node.run`'s
`select` is wrapped in `catchBreak`; `entsSize`'s range variable `ent`, whose address
`ent.Size()` takes, is allocated in the body), `Code/go_etcd_io/etcd/cache/v3.lean`
(`demux.resyncLaggingWatchers`'s `w, nextRev`, captured by the `AscendGreaterOrEqual`
callback, allocated in the body) and `cindex.lean` (empty bodies). Proofs: `entsSize` and
`demux.resyncLaggingWatchers` drop the per-iteration variables from their loop invariants
(each iteration allocates them afresh); nothing else changed.

**Retargeting raft to upstream `etcd-io/raft` (2026-10-10: done, to `40f8be7`).** Raft is
now goosed from upstream `etcd-io/raft` unmodified, at `40f8be7` (2026-04-15), the last
commit before raftpb moved to protobuf-go v2; the fork `upamanyus/etcd-raft` is gone from
`etc/goose.py`. Relative to the fork's translation: `JointConfig.IDs` ranges over the array
value with `array.forRange 2` (its proof is a `wp_for` over the index, unrolled for the two
elements, with the old map-range proof inside); `ConfChange`/`ConfChangeSingle`'s `NodeID`
and `ID` fields are `NodeId`/`Id` (`addNodeCC` in `InvConfchange.lean`); the enum constants
`MessageType_*`, `EntryType_*`, `ConfChangeType_*`, `ConfChangeTransition_*` are translated
(raftpb.toml), with `MsgHup`-style aliases; `MajorityConfig.String`/`Describe` format ids in
hex (not proved). No spec changed. The original goal was upstream `1c0011d2` (2026-09-22):
(upstream `24643b3` of 2026-03-10 plus two edits in `quorum/`: `JointConfig.IDs` ranging
over the two configs by index, and `MajorityConfig.Describe`'s local type `tup` hoisted;
the new Goose translates both as written). Between those two upstream commits raft moved
raftpb from gogoproto to protobuf-go v2 (March to May 2026: `Entry`, `Message`, `Snapshot`,
`HardState`, `ConfState`, `ConfChange*` are passed as pointers, their fields are pointers read
through `GetXXX` getters, `[]pb.Entry` is `[]*pb.Entry`, `proto.Clone`/`Marshal`/`Unmarshal`/
`Size` replace the generated methods). The mechanics work: branch
`raft-upstream-1c0011d2-wip` has `etc/goose.py` pointed at upstream `1c0011d2` (with
`google.golang.org=` as a Lean root, so raft's `proto` import is the names-only
`Code.google_golang_org.protobuf.proto` of the etcd project) and a new
`Code/go_etcd_io/raft/v3/raftpb.toml` (everything but the protobuf runtime plumbing), and
the regenerated `Code/` and `GeneratedProof/` build against Perennial `d57475ff3`. The proofs
do not: 154 Spec/Proof files (36k lines) mention the raftpb types as values (`List
raftpb.Entry` in `LogState`, `absMsg`, ...), so the retarget is a redesign of the raft proof's
entry/message/snapshot ownership (heap entries shared between the log, messages and
`Ready`), not an adaptation. The last upstream commit before the migration, `40f8be7`
(2026-04-15), translates unmodified with the new Goose and differs from the fork's
translation only by the gogoproto option cleanups (`NodeID` to `NodeId` in `ConfChange*`,
the `MessageType_*`/`EntryType_*` enum constants with `MsgHup`-style aliases) and the
Goose changes above: that is the cheap retarget, taken on 2026-10-10 (above). The retarget to
`1c0011d2` stays parked on that branch.

Gates (2026-10-09): `lake build` passes (1659 jobs); `etc/goose.py --check` passes;
`etc/tcb-report.py --check` matches the baseline. Building against a Perennial checkout
other than `.lake/packages/perennial` (other worktrees share it): `lake build
--packages=<override manifest>`, and `LAKE_OPTS=--packages=<file> etc/tcb-report.py`.
`etc/goose.py` needs a Go toolchain that can load etcd (`go 1.27`): with an older default
`go`, `GOTOOLCHAIN=go1.27.1 etc/goose.py ...`.
## Perennial `7d0b56b07`: Goose with per-iteration loop variables (2026-10-09)

Perennial `lean` at **`7d0b56b07`**: our `9092f8eaa` merged (cleanly) with upstream's
`724880f7b` (Goose: range over arrays, `fallthrough`, `break` out of `switch`/`select`, local
types), `a938c20b1` and `3a79c5282` (each loop iteration has its own iteration variables),
`79adaac01` (`context.wp_WithCancel` builds again) and `d57475ff3` (only the local types of
translated functions). In Perennial: `etc/lean-ci.sh` 372/372; the std-lib regeneration
(`GOTOOLCHAIN=go1.26.0 etc/update-goose-new.py --compile --std-lib`) changes nothing; `go test
./...` in `goose/` passes. No Perennial follow-up commit.

- **The generated code** (`etc/goose.py`; `ab1deb078` from `--src etcd=/shared/etcd`, not yet
  on `goose-lean`): 3 files (`Code/`; `GeneratedProof/` and `EtcdDeps/` unchanged), +20/−29.
  - *Per-iteration loop variables*: Goose allocates a loop variable per iteration only where
    sharing it would be observable (captured by a function literal, or its address taken,
    including a pointer-receiver call); every other loop keeps one shared cell, unchanged. Two
    loops here: raft's `entsSize` (`ent.Size()` has a pointer receiver: `ent` is now allocated
    in the body from `$value`) and the cache's `demux.resyncLaggingWatchers` (`w` and
    `nextRev`, captured by the `AscendGreaterOrEqual` callback, now allocated in the body from
    `$key`/`$value`, no longer stored at the end of each iteration).
  - *`break` out of `select`*: `node.run`'s `select` is wrapped in `catchBreak`. Its
    `case m := <-n.recvc` filters a response from an unknown peer with `break`, which the old
    translation took as breaking out of the `for` loop (ending `run`): a mistranslation, now
    fixed. `node.run` has no spec here, so nothing depended on it.
  - *Empty function bodies* end in `doReturn #()` instead of `doExecute #()`: raft's 11 `trace*`
    no-ops (`state_trace_nop.go`), `cindex`'s `fakeConsistentIndex.UnsafeSave`/`SetBackend`.
    `wp_start` handles both; no proof changed.
  - Nothing translated here uses `fallthrough`, array ranges or local types. The fork's "Avoid
    fallthrough" commit (`client/v3/leasing/kv.go`) is in a package not translated here: it
    does not matter for this repository (it could be reverted now that Goose translates
    `fallthrough`).
- **Proofs**: 2 fixed, both loop invariants that named the shared cell: `entsSize.wp_proof`
  (drop `ent` from the `wp_for` invariant; each iteration's fresh cell is passed to
  `Entry.Size`) and `demux.resyncLaggingWatchers.wp_proof` (drop `nextRev`, `w` from the
  `wp_map_for_range_mut_keys` invariant and from its three re-establishments). No spec, no
  `Link.lean` changed.
- **Gates**: `lake build` passes (1740 jobs); `etc/goose.py --check --src etcd=/shared/etcd
  --perennial .lake/packages/perennial` passes; `etc/tcb-report.py --check` matches without
  `--update` (38 axioms, 1 sorry); `etc/gen-link.py --cache`/`--concurrency`/`--server` and
  `etc/gen-btree-link.py` reproduce; `etc/verified-code.py --reuse` unchanged: Raft 175/323,
  cache 107/107 sorry-free, `client/v3/concurrency` 9 verified + 1 unfinished, server 19, etcd
  193 verified, 1 unfinished, 13 assumed of 3599.
- **Push order**: Perennial `lean` (`7d0b56b07`) first; the etcd fork's `ab1deb078` to
  `goose-lean` (if not pushed yet); then etcd-grove `lean`.

## Merge: the cache as shipped and client/v3/concurrency (2026-10-09)

Branch `cache-as-shipped` (the four commits of "The cache as shipped", made on `d45daf8ab`) merged
into the concurrency work ("client/v3/concurrency", below). Conflicts only in `etc/goose.py` (the
etcd pin: **`ab1deb078`**, which is `207c8f747` plus the two cache reverts, with the concurrency
side's packages and roots) and this file (both sections kept); `InvEtcd.lean`, `InvCache.lean`,
`InvNew.lean`, the Perennial pin (**`9092f8eaa`**) and `etc/tcb-baseline.txt` merged cleanly
(`isEtcdClient` is the concurrency side's: the cache side did not change its shape). Rerunning
`etc/goose.py` changed no generated file. No proof needed a fix: `Session`'s proofs use none of
the store or loop predicates the cache side redesigned.

- **Gates**: `lake build` passes (1740 jobs); `etc/goose.py --check --src etcd=/shared/etcd
  --perennial .lake/packages/perennial` passes; `etc/tcb-report.py --check` matches the merged
  baseline without `--update`: 38 axioms (the cache's 36 + `etcdStep_delete_present` +
  `proto.Clone.wp_proof`), 1 sorry (Perennial's `context.wp_WithDeadlineCause`);
  `etc/gen-link.py --cache`/`--concurrency`/`--server` and `etc/gen-btree-link.py` reproduce
  their `Link.lean`; `etc/verified-code.py --reuse` (`ab1deb078` fetched into
  `.lake/go-src/etcd`): cache 107/107 verified, sorry-free, 1202/1202 lines;
  `client/v3/concurrency` 9 verified, 1 unfinished (`Session.Close`) of 62; etcd 193 verified
  (all sorry-free), 1 unfinished, 13 assumed of 3599; Raft 175/323.
- **Push order**: Perennial `lean` (`9092f8eaa`) first; then the etcd fork's `ab1deb078` to
  `upamanyus/etcd` `goose-lean` (a fast-forward of `6ab61a1c7` through `207c8f747`); then
  etcd-grove `lean`.

## The cache as shipped: shared writers, a revision bound, no code change but the fix (2026-10-09)

Rule (the user's): no change to etcd's code unless it fixes a bug. The fork's fix branch
`cache-ready-after-retry` had three commits; only `64313a1f8` (`Init` before the store watcher
is registered: finding 2) fixes a bug. The verified code is now `upamanyus/etcd` branch
`goose-revert` at **`ab1deb078`** (on `goose` `207c8f747` = `goose-lean` `6ab61a1c7` plus the
concurrency package's Gooseable commit): two plain reverts, `43c553f32` (of `a7de41a72`: `watch`
waited for `applyStorage`, the goroutine left the wait group) and `ab1deb078` (of `21ac13e0d`: the
upstream watch in a child context canceled on return), so `cache/cache.go` is upstream main plus
the readiness fix and the Gooseable changes. `go build ./...`, `go vet ./cache/`, `go test
./cache/ -race -count=2` pass (`TestCacheReadyAfterWatchRetry`, from the fix, passes).
`etc/goose.py` pins it; only `Code/go_etcd_io/etcd/cache/v3.lean` changed (`watch`,
`watchEvents`). Design: `decisions.md`, "No code changes unless a bug".

- **Perennial `9092f8eaa`** (branch `wg-assume`, on `56b1b6651`; push Perennial first;
  **the `WaitGroup.Add` assumption is superseded** by the thread-token bound, Perennial `105fb79f5`,
  see "The wait-group counter and thread tokens"):
  `614fa61d3` **`WaitGroup.Add`'s counter overflow is a model assumption**: `WaitGroup.Add` is a
  trusted model (`TrustedCode/sync.lean`), Goose's translation of Go's `Add` verbatim but for the
  atomic add, which is `waitGroupStateAddAssume` (a compare-and-swap loop that `assume`s the
  `int32` counter plus the delta is at most `2^31 - 1`; with the assumption true, Go's atomic
  add); `wp_Add`'s caller bounds the counter only from below and the commit gives it the
  no-overflow fact; `Add`'s and `Done`'s atomic updates open at `⊤ \ ↑N` (as `Wait`'s). The
  shipped loop `Add(1)`s per iteration with each `Done` in a goroutine the demonic scheduler may
  delay for ever: without the assumption it is unprovable. `9092f8eaa`: a token-free writer
  spec for `RWMutex` (`isRWMutexGuard`, `wp_Lock_guard`, `wp_Unlock_guard`): any number of
  goroutines write the store. `etc/lean-ci.sh`: 369/369.
- **The store has shared writers** (`InvStore.lean`). No `storeWriter` token: the lock
  invariant holds the whole state (and the newest snapshot's counter `γ.snap`, `Synced`, the
  latest tree's lending flag); the latest tree lives in an invariant of its own
  (`storeTreeInv`, in `isStore`), borrowed under the write lock; writers use the persistent
  `isStoreWriter`. The new statements:
  - `store.Restore.spec`: `{{ isStore ∗ isStoreWriter s γ cap E R ∗ kvs… ∗ P ∗
    ⌜∀ r, (P ∗ R r ⊢ ⌜r ≤ rev⌝)⌝ ∗ □ E rev (restoreMap kvs) ∗ □ R rev }} s.Restore(kvs, rev)
    {{ kvs… ∗ P ∗ storeRevLb γ rev ∗ storeSnapLb γ rev }}` (for whatever state it finds; `P`
    dominates every revision the store can be at).
  - `store.Apply.spec`: `{{ isStore ∗ isStoreWriter ∗ respAt resp r ∗ ⌜EvRevSorted⌝ ∗
    storeSnapLb γ lo ∗ ⌜0 ≤ lo⌝ ∗ storeApplyCert cap E R lo r }} s.Apply(resp) {{ err;
    ⌜r.canceled ∧ err ≠ nil⌝ ∨ ∃ st, ⌜StoreInv cap st ∧ st.Synced ∧ ∃ Y, newest snapshot of st is
    (Y, st.latest) ∧ lo ≤ Y⌝ ∗ storeRevLb γ (applyResp cap st r).1.latestRev ∗
    monoNatLbOwn γ.snap (storeSnapKey (applyResp cap st r).1) ∗ ⌜err iff (applyResp cap st
    r).2⌝ }}`; `storeApplyCert cap E R lo r` is the caller's persistent certificate for any
    state `st` whose newest snapshot `(Y, st.latest)` is at or above `lo`, given `□ E Y st.latest`:
    `Apply` changes nothing or succeeds, and its snapshots and revisions are certified.
  - `newStore` returns `isStoreWriter` (persistent) instead of the writer.
- **The revision bound** (`InvCache.lean`, `CacheFields.γb`): a cache-level `monoNat` the watch
  loop alone advances (`cacheBound cf B`: the authority at `B`, with `etcdReached B`), before
  each `Broadcast` to the response's revisions (`respCert_cacheCert`) and before each `Restore`
  to the `Get`'s revision. The store's `R` is `cacheRev cf` (`etcdReached` and at most the bound),
  the demux's certificate `cacheCert cf` (`etcdStepCert` and at most the bound): every revision
  the store can reach, now or by a pending drain, is at most the bound, and the `Get`, from
  `etcdReached` of the bound, returns at least it (`cacheBound_dom`: `Restore`'s dominance).
- **A new model axiom, `etcdStep_delete_present`** (`InvEtcd.lean`): a delete event of a step
  removes a key present when it is applied (etcd emits no delete event for a missing key). The
  store's `Apply` fails on a delete of a missing key; with one writer a failure was followed by
  a `Restore`, but with shared writers another writer could build on the half-applied map. With
  the axiom, a batch etcd certifies applies to a map that is etcd's state before it
  (`isEtcdKvs_applyBatch_ok`, `applyEvents_ok`), so `Apply` never fails on a response it
  accepts and the store stays synced. Reached by `cache_New` only (the watch loop).
- **The loop as shipped**: `applyStorage` (any goroutine; `storeSnapLb (s - 1)`; returns
  `True`), `get` (`cacheBound B` in, `cacheBound R` out, `R ≥ B`), `watch` (`cacheWriter`, the
  wait-group token `cacheWgRunning`, `storeSnapLb R`, `0 < rev ≤ R + 1`; per iteration
  `wp_cacheWg_AddRunning` and a goroutine with a deferred `Done`; no wait; `applyErr` a handoff
  carrying nothing), `getWatch`, `getWatchLoop` (the wait-group token in and out), `watchEvents`
  (no `WithCancel`: the internal context; raises the bound before `Broadcast`).
- **Changed statements** beyond dropping the writer token: `applyStorage`, `get`, `watch`,
  `getWatch`, `getWatchLoop`, `Restore`, `Apply`, `newStore` (above); `RequestProgress`'s demux
  handle is `cacheCert cf`'s (was `etcdStepCert cf.pfx`'s); definitions behind unchanged
  statements: `isCacheFields` (the demux at `cacheCert`, `isStoreWriter`), `cacheReader` (`R =
  cacheRev`), `cacheWatchSlot` (the demux handle at `cacheCert`), `cacheWriter` (the bound's
  authority), `cacheWgInv` (spent budget tokens apart from the counter), `isStore` (the tree
  invariant), `StoreNames` (`snap`, `tree`). **`Get`'s, `Watch`'s and `New`'s statements are
  unchanged** (`Watch`'s channel stays `etcdStepCert`'s: the demux's publications are weakened
  to it, `demuxPubBody_cacheCert`), and so is every `Results.lean` statement.
- **`Close`**: `Wait` returns once the counter is zero, i.e. once every goroutine added to the wait
  group has run its `Done`, the drained `applyStorage` goroutines of every iteration included;
  its postcondition is unchanged (the "open" token; nothing comes back through the wait group).
- **Gates** (2026-10-09): `lake build` passes (1660 jobs), no `sorry` of this work;
  `etc/tcb-report.py --check` after `--update`: 37 entries, all axioms, 0 sorries (new:
  `etcdStep_delete_present`; the WaitGroup assumption is trusted code, not an axiom, and adds
  nothing); `Results.lean`'s `#print axioms`: unchanged but for `cache_New`, which gains
  `etcdStep_delete_present`; `etc/goose.py --check --src etcd=/shared/etcd-cache-revert
  --perennial .lake/packages/perennial` passes; `etc/gen-link.py --cache` reproduces `Link.lean`;
  `etc/verified-code.py --reuse` (with `ab1deb078` fetched into `.lake/go-src/etcd`): the cache
  107 of 107 verified, sorry-free, 1202 of 1202 lines; Raft 175/323, etcd 161 verified, 13 assumed.
  Push Perennial (`wg-assume`, `9092f8eaa`) first; the fork's `goose-revert` (`ab1deb078`).

## The wait-group counter and thread tokens (2026-10-10)

Perennial `105fb79f5` (merged into `lean`) reverts `614fa61d3`: `WaitGroup.Add` is
Goose's translation again and `WaitGroup.wp_Add` asks its caller to bound the new counter by
`2^31` (two `Add(1 << 30)` calls panic in Go, so the overflow was reachable and must not be
assumed). The bound is discharged with Perennial's **thread tokens** (`GooseLang/Threads.lean`;
`docs/PERENNIAL_PROOF_REFERENCE.md`, "Thread tokens"): the trusted semantics counts the live
threads (`GlobalState.threads`; `Fork e` spawns `e ;; ThreadExit`), the bounded layer has a
thread fuel next to the step fuel, and `threadToks n ⊢ n < threadBound GF` for a bound `T`
fixed at adequacy time (`goose_adequacy N T`, about executions along which fewer than `T` threads
are live). `Fork` hands the forking thread a token (`wp_fork_tok`, `wp_fork_tok_self`,
`wp_fork_tok_body`) and the forked thread returns one at its exit.

- **`cacheWgInv`** (`InvCache.lean`): the counter is `k + d`; `k` goroutines (`cacheWgRunning`,
  `γwr`) have their **thread token deposited** in the invariant (`threadToks k`), `d` goroutines
  (`cacheWgRunningOwed`, `γwo`) keep their own token and spent a capacity (`cacheWgOwedCap`,
  `γwc`; `cacheWgOwedMax = 3`: the resync loop, the watch loop, the progress requestor, for the
  cache's lifetime). `k` tokens give `k < threadBound GF`, so the counter is below
  `threadBound GF + 3`; **`New` assumes `threadBound GF + cacheWgOwedMax ≤ 2^31`** (a pure
  premise of `New.spec`/`newCache.spec`, kept in `isCacheFields` as `%Hthreads`): fewer than
  `2^31 - 3` threads are live at once. The `cacheWgBudget` slots are unchanged.
- **Who deposits.** The watch loop (`getWatchLoop`, `getWatch`, `watch`: `cacheWgLoopRunning`,
  its owed running token and its own thread token) deposits its token at each iteration's
  `Add(1)` (`wp_cacheWg_AddRunning`) and gets a fresh one at the `go` statement
  (`wp_fork_tok_self`); the iteration's goroutine exits with the token its deferred `Done`
  returns (`wp_cacheWg_Done`). `Watch` (`threadTok` in and out of its spec) does the same with a
  budget slot (`wp_cacheWg_Add`). `NewDemux`'s slot protocol and `newCache`'s `Add(2)` start the
  three owed goroutines (`wp_cacheWg_AddOwed`, `wp_cacheWg_Add2`; `wp_cacheWg_DoneOwed` returns
  the capacity); `New`'s spec needs no token of its own.
- **Changed statements**: `New`, `newCache` (the thread-bound premise), `Watch` (`threadTok`),
  `watch`, `getWatch`, `getWatchLoop` (`cacheWgLoopRunning` for `cacheWgRunning`). `Close` and
  the delivery theorem are unchanged.
- **Trust base**: the model assumption is gone from Perennial's trusted code; what replaces it is
  the semantic thread count and thread fuel (Perennial's `Lang.lean`, `BoundedLang.lean`,
  `Threads.lean`, `Lifting.lean`, `Adequacy.lean`; see Perennial's README) and the adequacy
  hypothesis `RealThreadsBelow T`, instantiated here by `New`'s premise. `etc/tcb-report.py
  --check` is unchanged (the premise is a hypothesis of a spec, not an axiom).

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

## Perennial models of `fmt.Sprintf`, `strings.Join`, `crypto/rand.Int` (2026-10-09)

The three standard-library axioms of the Raft proof are theorems now, from trusted models
in Perennial (`Perennial/TrustedCode/{fmt,strings,crypto/rand}.lean`, wired through
`trusted` in the packages' `.toml`; Perennial `00b3c10ea`, merged with upstream's
`3ae7dc6a4` as `56b1b6651`; pinned at `79adaac01`, which also fixes `context.lean`'s
`wp_withCancel`: at `3ae7dc6a4` `Perennial.Proof.context` does not build, so neither does
`lean` at `55d80f991`):

- `fmt.Sprintf`: returns its format string (as `Errorf`'s model does); `fmt.wp_Sprintf`
  promises some string, which is all `Spec/fmt/Sprintf.lean` says.
- `strings.Join`: goose's translation of a `+` loop; `strings.wp_Join` returns
  `sep.intercalate xs`. Go's panic when the length overflows `int` is not modelled (as
  for `append` and string `+`), which is the overflow the old axiom's no-panic claim
  glossed over.
- `crypto/rand.Int`: an arbitrary value in `[0, max)` and no error for `0 < max < 2^63`,
  read from `max`'s sign and one magnitude word; a panic otherwise; the reader is not
  read. `crypto.rand.wp_Int` is for the package's own `Reader` (which never returns an
  error), so `Spec/crypto/rand/Int.lean` gained `mz < 2^63` (`lockedRand.Intn` passes an
  `int64`). Perennial's `math.big.ownInt` now records a normalized magnitude (Go's
  invariant), which reading a value below `2^63` as one word needs, and Perennial owns
  `math/big`'s and `crypto/rand`'s `isPkgInit` (the `Reader` points-to, formerly
  `isRandInitialized` in `Base.lean`).

(`d45daf8ab`, from a parallel session, had proved `Sprintf` and `Join` from the same
models, kept `rand.Int` an axiom and pinned `56b1b6651`; this supersedes it.)
`etc/tcb-report.py --check` (after `--update`): 35 axioms, no `sorry`. The Raft proof's one
remaining axiom is `reflect.DeepEqual`, which `RawNode.wp_Propose`, `wp_Advance`,
`wp_newRaft` and `raft.wp_Step` reach (through `assertConfStatesEquivalent` in `newRaft`
and `raft.restore`); `RawNode.wp_Ready` and `wp_HasReady` rest on none of this
repository's axioms.

## The TCB and verified-code scripts: generic, per-collection trust base (2026-10-09)

`etc/tcb-report.py`, `etc/tcb-report.lean`, `etc/verified-code.py` and `etc/verified-code.go`
name no project any more: what they need comes from the layout and `etc/goose.py`, through
the new `etc/proof_roots.py` (shared by the two Python scripts):

- **Roots**: every `Link.lean`/`Results.lean` under `Proof/` and a part's `<root>/Proof/`
  (was a hard-coded list in each script and in `tcb-report.lean`'s defaults, which are gone:
  it takes the modules and `--part=ROOT` for each part root). Lean runs are grouped by the
  part roots a module reaches through the import graph (here: the server's `Link` alone, as
  before). The namespace stripped from names is the common one of the `Link.lean` files.
- **`.lake/tcb.json`** starts with a meta line (modules, commit), is written only when every
  Lean run succeeds, and `--reuse` refuses one of other modules. Before, a failed run left
  it empty and `--reuse` then counted nothing as verified (what the main checkout's empty
  `tcb.json` did: its build lacked the cache's `Link`).
- **`tcb-report.py --roots PATTERN...`** / **`--collection FILE`**: the axioms and `sorry`s a
  set of roots rests on (regexes over the name, module file and spec file), the roots that
  reach a `sorry`, and `--check [--update]` against the collection's own baseline.
  `etc/tcb-collections/raft.txt` is the Raft proof (`Link` and `Results`); its baseline is
  not recorded yet (no build of this commit on the machine when written): run
  `etc/tcb-report.py --collection etc/tcb-collections/raft.txt --check --update` after
  `lake build`.
- **`verified-code.py`**: tables per project of `etc/goose.py` (by module if it has more than
  one, by package for the packages Goose touches, by file), not "Raft"/"etcd". The counted
  Go modules are `Project.counted_modules` in `etc/goose.py` (the list that was `ETCD_MODS`,
  and raft's main module: its checkout also has `go.etcd.io/raft/tools/v3`). The by-file
  tables (and `--functions`) now include every file with a function translated with its
  body or specified: the server's `server.go` (apply thread), `cindex.go`, schema's
  `cindex.go`, `client/v3`'s `op.go`/`watch.go` were missing, so `server/v3` showed
  nothing verified there. `--package PREFIX` adds a summary row and narrows those tables.
  Specs of packages whose Go code is not in the sources (the btree, zap, raft v3.7's raftpb
  in `EtcdDeps/`, humanize) are listed with the package instead of as "outside"
  (`zap.Int'`, methods of names-only packages, `go-humanize` were mis-resolved). Totals are
  unchanged (checked on the same `tcb.json`); `raftpb/confchange.go` (nothing translated, in a
  package with names-only functions) is no longer listed.

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
  higher-level spec changes" as the constraint; since 2026-10-09 only `reflect.DeepEqual`
  remains, the other three are Perennial models, see the section at the top):
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
  (delivered committed log, entries to persist, queued steps, term); `Ready`'s
  committed entries come with `isCommitted γ (rs.delivered ++ ce)`, no `applying`.
  `PstepCommitMono` and `ready_stable_ok` are proved; `raft.Step`'s spec gained a frame
  for local messages. The `Advance` gap (`advanceable`) is closed since 2026-10-10 (see
  the section of that date).
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

- **Verified against the code as shipped (2026-10-09; supersedes the fixed-code verification).**
  The verified code is upstream main plus the readiness fix only: `goose-revert` at `ab1deb078`
  (`64313a1f8` kept; `a7de41a72` and `21ac13e0d` reverted, `43c553f32` and `ab1deb078`). See
  "The cache as shipped" (top) and `decisions.md`, "No code changes unless a bug". From
  2026-10-09 until then the verified code was `goose-lean` `6ab61a1c7`, with all three commits,
  and `watch`/`getWatch`/`getWatchLoop` were proved with a single store writer (a token threaded
  through the loop and handed back through `applyErr`, `Handoff.lean`).
  - `Cache.watch`: with the demux's writer (and the revision bound), the wait-group token, the
    store's newest snapshot at least `R` and `0 < rev ≤ R + 1`, returns a non-nil error, the token
    and the demux's writer; it does not wait for the iteration's goroutine, which is one of the
    store's writers (`applyStorage` needs only `storeSnapLb (rev - 1)`).
  - `Cache.getWatch`, `Cache.getWatchLoop`: the demux's writer and the wait-group token through.
  - `watchEvents` watches in the internal context; the stream it opens is never canceled before
    the cache is (see finding 1b).
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
  since the cache as shipped, only 2 is fixed in the verified code, `ab1deb078`: 1 and 1b are not
  bugs):
  1. *Two writers of the store: not a bug.* `watch` does not wait for an iteration's
     `applyStorage` goroutine before the next iteration, nor `getWatchLoop` before the next
     `get`'s `Restore`: after `Unregister`, the old goroutine keeps draining its watcher's
     buffered responses into `store.Apply`, concurrently with the next writer. The shared-writer
     proof shows this is harmless: a drained response at or below the store's latest revision is
     rejected by `validateRevisions` (`applyResp_stale`) and changes nothing; every revision a
     drain can apply is at most the revision bound, at or below which the next `Get` returns
     (linearizability); an accepted one follows the store's newest snapshot along etcd's steps.
     It does rest on etcd's semantics: a delete event is of a present key
     (`etcdStep_delete_present`), else a failed `Apply` could leave a half-applied map another
     writer builds on. The fix `a7de41a72` is reverted.
  1b. *The upstream watch is not canceled when `watchEvents` returns* (a finding for the
     maintainers, not a correctness issue): `watchEvents` watches in the cache's internal context,
     so each retry leaves the previous client watch (its goroutines, the server-side watcher) open
     until the cache is closed. A resource leak; the proofs are unaffected. The fix `21ac13e0d`
     is reverted.
  2. *The cache can stay not ready after a retry* (**the one bug; fixed by `64313a1f8`, kept**).
     Before the fix, `watch` registered the store watcher (352) before `Init` (406); on a retry whose `Get` revision `R'` differs from the demux's `maxRev`
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
- **What the cache's results rest on, since the cache as shipped** (2026-10-09): as below, plus
  the model axiom `etcdStep_delete_present` (`cache_New`), and (superseded 2026-10-10 by the
  thread-token bound and `New`'s thread-bound premise, see "The wait-group counter and thread
  tokens") Perennial's model assumption that
  `WaitGroup.Add`'s `int32` counter does not overflow (trusted code, `TrustedCode/sync.lean`, not
  an axiom: every result using the cache's wait group, `cache_New`, `cache_Watch`, `cache_Close`).
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
