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

### Proof idioms: a closed theorem from a program's initializer and body

- **Missing.** A form of `goose_adequacy` for the usual closed theorem: a program
  `init #() ;; body` run from a fresh state (`IsInit`) with one thread, the receipt and thread
  bounds `n + 1`, `n + 2` of an `n`-step execution, the right to initialize (`ownInitializing`)
  from the empty package state, and the conclusion with `v.isPanic = false` for each final value
  (from `UnrecoveredPanic`'s exclusion). Every closed theorem repeated these steps.
- **Needed by.** The examples' closed theorems (2026-10-22, D36): kv's, the counter's and
  kvwitness's over `goose_adequacy`; the etcd examples' over this repository's
  `goose_adequacy_start` (`Proof/runtime/Start.lean`), which stays here.
- **Workaround here.** `Proof/github_com/mit_pdos/etcd_grove/examples/common/Adequacy.lean`:
  `init_adequate` (over `goose_adequacy`, its WP obligation `progOk0`: the initializer's triple
  and the body's WP from the package's predicate and the main thread's token, at every ghost-state
  instance at the state's local context), `adequate_of_unrecovered`, `ownInitializing_of_empty`;
  no axiom. (`etcd_adequate`, the same over `goose_adequacy_start`, is this repository's.)
- **Proposed change.** `init_adequate`, `adequate_of_unrecovered` and `ownInitializing_of_empty`
  in `Perennial/GooseLang/Adequacy.lean` (or beside `IsInit` in `Perennial/Golang/Theory/Pkg.lean`).
- **Status.** Not started (2026-10-22).

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

### Context: `Canceled`'s message cell in `context`'s package facts

- **Missing.** Perennial's context initialization allocates `Canceled` with `errors.New("context
  canceled")` and persists the `errorString`'s `s` field, but `isInit`'s `"#HCanceled"` keeps only
  `isTypedErr`: a proof cannot tell `Canceled` apart from another `errors.New` value (D37, D19k).
- **Needed by.** `ctxErrClientAllW_of` (`client/v3/ErrorsNewOk.lean`): a context's error is no
  caller's `errors.New` value (`errCellOk`), for the Kubernetes driver's sentinel errors.
- **Workaround here.** `context.ErrAny` (this repository's trust-boundary axiom) states the cell
  of `Canceled`'s value and that `DeadlineExceeded`'s is no `*errorString` (true of Go).
- **Proposed change.** `"#HCanceled"` with the cell (`x.[errorString, "s"] ↦□ "context
  canceled"`, as this repository's `errStrCell`), and `"#HDeadlineExceeded"` with its dynamic type
  (`deadlineExceededError`); then `ErrAny` drops the two facts.
- **Status.** Not started (found 2026-10-23).

## Landed

### Specs: `context.WithTimeout`/`WithDeadline` of `Background()`

- **Missing.** A spec of `context.WithTimeout(parent, d)` (and `WithDeadline`,
  `WithDeadlineCause`) whose parent is `context.Background()` (or `TODO()`): Perennial's
  `context.WithTimeout.spec` takes `isContext parent`, which `Background()`'s value is not (its
  `Done()` is `nil`). `WithCancel` has the counterpart (`wp_WithCancel_Background`,
  `WithCancelGen.lean`), and the pieces of the deadline case are there too (`wp_background_Deadline`,
  `wp_propagateCancel_background`, `isContext_timerCtx_of`).
- **Needed by.** The pattern of client/v3's documentation, `ctx, cancel :=
  context.WithTimeout(context.Background(), timeout)` around each call: the examples' call sites
  since 2026-10-23 (`notes/client-timeouts-plan.md`, D-T2, D-T3) and the server's read loop
  (`sendReadIndex`, the request path's unit 4a).
- **Workaround here.** The trust-boundary axiom `context.WithTimeoutBackground.wp_proof`
  (`Spec/context/WithTimeoutBackground.lean`: an `isContext` of some descriptor and a callable
  `cancel`), in the `read`, `server` and every etcd example's collection; the examples use it
  through `client.wp_WithTimeout_bg` (`Proof/go_etcd_io/etcd/client/v3/TimeoutCtx.lean`).
- **Proposed change.** `wp_WithTimeout_Background` and `wp_WithDeadline_Background` (the
  `Background()` parent of `WithDeadlineCause`'s proof, as `wp_WithCancel_Background` is of
  `WithCancel`'s), with the descriptor they give (`Deadline := some d`, `PDone := True`, fresh
  Done names). Then the axiom here becomes a theorem (one axiom fewer in the baseline and in
  those collections: the plan's T3).
- **Status.** Landed: Perennial `c25bef57e` (branch `with-timeout-background` off `lean`
  `d761e15b2`, 2026-10-23: `wp_WithDeadlineCause_Background_of`, `wp_WithDeadline_Background_of`,
  `wp_WithTimeout_Background_of` in `Proof/context/WithDeadlineBackground.lean`, exposed in
  `Results.lean`; `propagateCancel`'s spec takes any child for a `Background()` parent,
  `wp_propagateCancel_background_any`); the pin moved to it and the axiom here is the theorem
  `context.WithTimeoutBackground.wp_proof` over `wp_WithTimeout_Background` (one axiom fewer in
  the baseline and in the `read`, `server` and every etcd example's collection).

### Std, PostLifting: generic lemmas the client, the cache and the examples each proved a copy of

- **Missing.** Facts about Perennial's and Lean's own definitions, proved in several places here
  (`notes/dedup-plan.md`, C1-C4 and D): a points-to at `q` as two halves and back, with agreement
  (twelve copies by value type: `ptsto_w64_halves`, `loc_halves`, `chan_split`, ...), half a
  points-to fractional (`half_pointsto_fractional_loc`/`_chan`); `N.@x` disjoint from `N.@y` and
  `N.@z` (the `*_mask` lemmas); setting the first entry of a `replicate` padding (five copies);
  one more function of a `foldl (fun o g => g o)` (`opFold_take_succ`, `stmOptsFold_take_succ`,
  `cfgApply_take_succ`); indexing and prefix facts Lean core lacks (`zip_get_snd`,
  `getElem?_snoc_cases`, `prefix_drop_cons`, the `crl_*_mid` three, `flatten_getElem?`, ...);
  `GoStringLt` on cons cells (`client/v3/PrefixRange.lean`).
- **Needed by.** `Proof/go_etcd_io/etcd/{client,cache}/v3/`, `examples/{linkvtxn,lintest}`.
- **Workaround here.** None now (the local copies stayed until the pin moved).
- **Proposed change.** Perennial branch `dedup-lemmas` (`f97c83add`, off the pin `537c426e0`;
  worktree `/shared/perennial-dd`): `typedPointsto_half_split`/`_half_combine`/`_half_fractional`
  (`Golang/Theory/PostLifting.lean`), `mask_ndot_ne2` (`Std/Namespaces.lean`), the list lemmas
  (`Std/List.lean`, sections `list_index`, `subslice_take`, `join_same_len_index`),
  `goStringLt_cons_iff`/`_nil_cons`/`_not_nil` (`Golang/Defn/String.lean`). Theorems only.
  Then, here: each copy deleted and its uses pointed at Perennial's (the `_take_succ` three stay
  one-liners over `foldl_apply_take_succ`: `opFold` and its kin are in specs' statements).
- **Status.** Landed 2026-10-22: Perennial `lean` `f97c83add`, the pin since; the local copies are
  deleted (etcd-grove branch `dedup-pin`), their uses pointed at Perennial's (the server's
  `mask_ndot_ne2` at `nroot` and the three `_take_succ` one-liners over Perennial's; raft's
  `ptsto_halves` too). Found 2026-10-22.

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
