# Changes to Perennial this repository needs

A running list of the Perennial changes (Goose, the standard-library models and specs, the proof
framework) that proofs here are waiting on or working around. Each is a general change, designed
and reviewed on its own on a branch off Perennial's `lean` and landed by Perennial's workflow
(CLAUDE.md, "Changes to Perennial"); never a change shaped by one proof. Add an entry when a
proof hits a limitation (with the local workaround); move it to "Landed" with the Perennial commit
when the pin reaches it, and drop the workaround.

Each entry: what is missing, who needs it, the workaround here, the proposed change, status.

Started 2026-10-22 with the Kubernetes etcd3 store survey (`notes/k8s-etcd3-plan.md`, branch
`k8s-etcd3-goose`, `notes/k8s-etcd3-goose.md` there). Earlier limitations are recorded where
they were found (`notes/STATUS.md`, `notes/decisions.md`) and not yet collected here.

Perennial pin at the start: `a39a3d14c` (Perennial's `lean` head on 2026-10-22).

## Open

### Tactics: `word`'s caches shared between parallel declarations

- **Missing.** Deterministic elaboration under a parallel build. `word`'s caches
  (`Perennial/Std/Word/Cache.lean`: `wordCache` and `failCache`, process-global `IO.Ref`s) are
  shared between the declarations Lean elaborates in parallel within one module, so whether a
  `word` call hits the cache, and hence the heartbeats a proof uses, depends on which declaration
  ran first. A proof near its heartbeat limit then fails on some runs only (and a cached failure
  could in principle leak between contexts). The same class as the flaky `stepLeader.lean` build
  (`notes/flaky-stepleader-build.md`, fixed in Perennial `fb1ecb030`, "no global mutable state
  shared between parallel declarations").
- **Needed by.** `Proof/go_etcd_io/raft/v3/raft__Step/MsgStorageAppendResp.lean`'s
  `wp_Step_MsgStorageAppendResp_snap` (D22 S-d3b): it ran out of 1000000 heartbeats once under a
  parallel full build (2026-10-21) and passes alone, on the same tree. Any proof near its limit.
- **Workaround here.** That theorem's limit raised to 4000000, with a comment citing
  `notes/STATUS.md`, "`word`'s shared cache" (what is proved is unchanged).
- **Proposed change.** The caches keyed per declaration, or held in the tactic's own state
  (`MetaM`/`TacticM` state, or an environment extension reset per declaration), so that a
  declaration's elaboration does not depend on its siblings'.
- **Status.** Not started (found 2026-10-21, `raft-retarget`, now on `lean`).

### Specs: `context.WithCancel`'s cancel function not `nil`

- **Missing.** `context.WithCancel`'s specs (`context.WithCancel.spec`, `wp_WithCancel_Background`,
  `wp_WithCancel_gen_of`, ...) return the cancel function with its triple (`cancelSpec`) but not
  that it is not `nil`, which is true (it is the closure `func() { c.cancel(true, Canceled, nil) }`,
  a `func.mk`; the proof's `simp only [recv_eq_func_mk]` sees it) and which a caller that tests the
  function against `nil` needs.
- **Needed by.** `pkg/v3/schedule`'s `fifo.Schedule` (2026-10-22, branch `fifo-sched`): it panics
  when `f.cancel == nil`, and before `Stop` `f.cancel` is the context's cancel function.
- **Workaround here.** `Proof/go_etcd_io/etcd/pkg/v3/schedule/WithCancel.lean`: local copies of
  `wp_WithCancel_gen_of` and `wp_WithCancel_Background_of` with `⌜cancel ≠ func.nil⌝` added
  (`wp_WithCancel_Background_nn`); no axiom.
- **Proposed change.** `⌜cancel ≠ func.nil⌝` in the postconditions of `WithCancel`'s specs (and of
  `WithTimeout`/`WithDeadline`'s, whose cancel functions are closures too).
- **Status.** Not started (found 2026-10-22).

### Goose: range over a function (`iter.Seq`/`iter.Seq2`)

- **Missing.** Goose rejects `for k, v := range f` when `f` is a function (`[unsupported]: range
  over func(...) (only integers, maps, slices, channels and arrays are supported)`). The iterator
  functions themselves, closures calling `yield`, already translate.
- **Needed by.** The k8s etcd3 store's `GetList` (`store.go:825`, over `pagedChunks` or
  `streamChunks`): every list. Blocks `notes/k8s-etcd3-plan.md`'s phase 5. The standard library
  increasingly returns iterators (`maps.Keys`, `slices.All`, ...).
- **Workaround here.** `store.GetList` names-only (survey branch's `etcd3.toml`); alternatives: a
  Goose fork of k8s.io/apiserver rewriting the loop, or a trusted model.
- **Proposed.** Desugar the loop as Go's compiler does: call the iterator with a closure for the
  body that returns `false` on `break`, and records a `return` (with its values) or a labelled
  `break`/`continue` in flags checked after the call; plus the runtime check that `yield` is not
  called after it returned `false` (Go panics).
- **Status.** Not started. The largest item here.

### Goose: field selection through a type alias of a struct

- **Missing.** `getStructInfo` (`goose/types.go:358`) matches `*types.Named` without
  `types.Unalias`, so a selector on a value of an alias type (`clientv3.Event = mvccpb.Event`) is
  rejected (`[impossible(go)]: expected (pointer to) struct type for base of selector`).
- **Needed by.** The k8s etcd3 watcher (`parseEvent`, `event.go:80`; `watchChan.startWatching`,
  `watcher.go:516`) and compactor (`compactor.fromWatchResponse`, `compact.go:308`). Not the
  store's unary methods.
- **Workaround here.** The three functions names-only (survey branch's `etcd3.toml`); the
  compactor configured off.
- **Proposed.** `types.Unalias` on the type and on a pointer's element in `getStructInfo`. Tried
  in a scratch copy of the pinned translator: the three translate and their `Code` and
  `GeneratedProof` elaborate; nothing else changes.
- **Status.** Not started; small. Needed before the watcher.

### Goose: imports of packages whose types a body names, and same-named packages

- **Missing.** When a body uses a method or value whose type belongs to a package the Go file
  does not import, Goose adds no import for it, and `pkgRef` (`goose/goose.go:2967`) refers to it
  through an imported package of the same name if there is one. The second is a silent
  mistranslation: `storage.InvalidError.Error` calls apimachinery's `utilerrors.Aggregate.Error`,
  emitted as the standard library's `errors.Aggregate`.
- **Needed by.** The k8s etcd3 store: `utilfeature.DefaultFeatureGate.Enabled` names
  `featuregate.FeatureGate` (`New`, `store.Delete`, nine functions in all);
  `storage.InvalidError.Error`.
- **Workaround here.** `util/feature.toml` imports `featuregate` names-only, so the name reaches
  importers; `InvalidError.Error` names-only (unreached by the store's paths).
- **Proposed.** Import the Lean module of every package whose types a translated body names, and
  make `pkgRef` an error, never a substitution, when the package is not imported under its own
  name.
- **Status.** Not started. The substitution is worth fixing first: it is wrong, not missing.

### Specs: `reflect`

- **Missing.** Perennial translates `reflect` (`Perennial/Code/reflect.lean`) but has no specs.
- **Needed by.** The k8s etcd3 store's unary methods: apimachinery's `conversion.EnforcePtr`
  (`reflect.ValueOf`, `Kind`, `Elem`) and `reflect.New(v.Type())` in `Delete` and
  `GuaranteedUpdate`; lists add `MakeSlice`, `Append` and `Value`'s methods (`growSlice`,
  `getNewItemFunc`). Plan phase 1.
- **Workaround here.** None yet; local trust-boundary specs if the Perennial change is not ready
  by phase 1.
- **Proposed.** Specs of the `reflect` subset generic code uses on pointers and slices: `ValueOf`,
  `TypeOf`, `Kind`, `Elem`, `New`, `Indirect`, `MakeSlice`, `Append`, `Len`, `Cap`, `Set`,
  `Interface`, over Perennial's model of interface values and types.
- **Status.** Not started.

### Standard library: packages not translated, and functions without specs

- **Missing translations.** `encoding/json`, `encoding/base64`, `iter`, `path` (Perennial
  translates none of them).
- **Missing specs.** `strconv.ParseInt`, `ParseUint`, `FormatInt`, `FormatUint`, `ParseBool`;
  some of `strings`; `fmt.Sprint`, `Sprintln`, `Fprintf`; `os.Getenv`; `json.Marshal`,
  `Unmarshal`; `base64.RawURLEncoding`'s methods; `path.Join`, `Clean`.
- **Needed by.** The k8s etcd3 store and `k8s.io/apiserver/pkg/storage`: continue tokens (JSON in
  base64), `prepareKey` (`path`), resource versions (`strconv`), `GetList`'s iterators (`iter`).
- **Workaround here.** The four packages names-only in this repository's configuration (survey
  branch: `Code/encoding/{json,base64}.toml`, `Code/iter.toml`, `Code/path.toml`); specs as
  needed, local until proposed.
- **Proposed.** Translations (or trusted models) of the four in Perennial's standard library, and
  the specs above, each with the subset proofs use.
- **Status.** Not started.
- **Also `hash` (2026-10-22, branch `kvhasher`).** Perennial does not translate `hash`, so mvcc's
  `kvHasher` (a `hash.Hash32` field) was an axiomatized type with `sorry` instances, the
  repository's last two `sorry`s. Workaround here: `hash` types-only in this repository
  (`Code/hash.toml`, `-lean-root hash=`, as `encoding/hex`), which makes Goose translate
  `kvHasher` as a struct. Proposed: `hash`'s interfaces in Perennial's standard library (and
  `hash/crc32`'s model, which would make `newKVHasher`, `kvHasher.WriteKeyValue` and `Hash`
  provable); then this repository's `hash` translation goes.

### Tactics: framing up to the projections of a structure instance

- **Missing.** The proof mode's matching of a hypothesis against a goal (`iframe`, the `$$`
  arguments of `iapply`/`ihave`) does not see through the projection of an anonymous constructor:
  `dghostVar (γ.withPhys p).rst dq v` does not frame `dghostVar γ.rst dq v`, nor `crevFrozen γ`
  the premise `crevFrozen (γ.withPhys p)`, though they are definitionally equal (`rfl`) and Lean's
  `exact` accepts them.
- **Needed by.** The store's names at the current physical names (`mvcc.StoreNames.withPhys`,
  D22 receiver epochs S5b, 2026-10-22): every proof that works at `γ.withPhys p` and uses a
  logical fact of `γ`.
- **Workaround.** Explicit rewrites by `rfl` lemmas (`mvcc.isStore_withPhys`, ..., the
  `withPhys_simp` tactic of `InvStore.lean`), lemmas bridged in term mode
  (`readerPool_checkout_p`, `revMuInv_open_cur`), and `revMuBody` with separate logical and
  physical names.
- **Proposed.** iris-lean's (not Perennial's) frame and specialization matching could unify up to
  `whnfR` of projections of constructor applications (structure eta), as Lean's `isDefEq` does at
  reducible transparency for `instances`. Not proposed yet: to be weighed against the cost of
  every match.
- **Status.** Open (observed; no change drafted).

## Landed

### Proof idioms: a synchronous SPSC channel, a thread-token join, a ghost update at a fork

Three of the watch client's local workarounds (D25, `notes/decisions.md`, "S1c's findings" and
"R4's findings"; `notes/status-history.md`, "watch-resume"), proposed as general idioms.

- **Missing.** (1) Perennial's SPSC idiom (`Idioms/Spsc.lean`) does not tie its pending channel
  states to the sides' tokens, so the holder of both tokens of an unbuffered channel cannot show
  that nothing is in flight (Go's synchronous handoff). (2) Its `WaitGroup` join idiom
  (`sync.join`) bounds the `Add`s since the last `Wait` (`num_added < 2^31 - 1`), not the
  goroutines running. (3) `wp_fork_tok`'s premise is a plain wand: no ghost update (no invariant
  opened) at the fork step, which is not atomic (`Fork` may stutter).
- **Needed by.** The watch client's reconnection: `respc` and every substream's `recvc` (`run`'s
  epoch switch and a substream's restart need `sent = recv`); `waitCancelSubstreams`' local wait
  group (one `Add(1)` per resuming substream, F4); its goroutines' inner `go` statement, which
  refills a lent slot at the fork.
- **Workaround here (until the pin moves).** `Proof/go_etcd_io/etcd/client/v3/SyncSpsc.lean` (a
  copy of `Spsc.lean` with pending flags); `InvWcJoin.lean`'s local join (`wcjAdder`, `wcjDone`,
  `wcjDoneB`, `wp_wcj_Add`/`Done`/`Wait`) and its copy of `wp_fork_tok`, `wp_fork_tok_upd`.
- **Proposed change.** Perennial branch `idioms` (off `lean` `a39a3d14c`), one commit each:
  `3c3e83e2c` `Idioms/SyncSpsc.lean` (`isSspsc`, `sspscProducer`/`sspscConsumer`, `sspsc_sync`,
  the `recvAu`/`sendAu`/`closeAu` lemmas and `wp_sspsc_receive`/`send`/`close`); `9e52da638`
  `wp_fork_tok_upd` in `GooseLang/Lifting.lean` (`wp_fork_tok` derived from it, statement
  unchanged); `537c426e0` `Proof/sync/WaitGroupTokJoin.lean`, `sync.tokJoin` (`ownAdder`,
  `ownDone`, `WaitGroup.wp_Add`/`wp_Done`/`wp_Wait`, the counter backed by thread tokens; a slot's
  token lendable, `lend_acc`/`unlend_acc`, under a client's lending law `lendLaw N L`). New
  definitions and theorems only; no existing statement changes. Reviewed (`trusted-delta.py`: no
  tier 0-2 trust change), recorded with `etc/land.sh mark-reviewed`.
- **Status.** Landed 2026-10-22: Perennial `lean` `537c426e0` (`3c3e83e2c`, `9e52da638`,
  `537c426e0`), the pin since; the local copies are deleted (etcd-grove branch `perennial-idioms`).
