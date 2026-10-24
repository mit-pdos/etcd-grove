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

### `encoding/binary`'s `Write`/`Read`, and protobuf at the bytes (2026-10-22, rafthttp stage 3, branch `rafthttp-plan`)

- **Missing.** Perennial translates `encoding/binary`'s byte orders but not `Write`/`Read`
  (names-only: they go through `reflect`); and `google.golang.org/protobuf` is names-only, so its
  `Size`/`Marshal`/`Unmarshal` have no spec there.
- **Needed by.** rafthttp's message codecs (`messageEncoder.encode`, `messageDecoder.decodeLimit`,
  the msgappv2 pair next): a length prefix written with `binary.Write` and read with `binary.Read`,
  and raft's messages marshalled.
- **Workaround here.** Trust-boundary axioms: `Spec/encoding/binary/{WriteUint64,WriteUint8,
  ReadUint64}.lean` (Go's fast path of an integer, stated over the writer's `Write` / the reader's
  `io.ReadFull`), and generic protobuf specs over a per-type wire model (D33a:
  `Proof/google_golang_org/protobuf/proto/InvProto.lean`'s `PbType`, `Spec/google_golang_org/
  protobuf/proto/{Size,Marshal,Unmarshal}Pb.lean`).
- **Proposed.** Specs of `binary.Write`/`Read` of fixed-size integers in Perennial (or a trusted
  model of their fast path); and, if the generic vocabulary proves itself across the codecs and
  the older per-type specs move onto it, `PbType` and its three specs as Perennial's protobuf
  boundary.
- **Status.** Not started.

### The `WaitGroup` join idiom's `Add(n)`, and `Sprintf` of a `Stringer` (2026-10-23, rafthttp stage 4d, branch `rafthttp-plan`)

- **Missing.** (1) `sync.join.WaitGroup.wp_Add_of` (and `sync.tokJoin`'s) covers `Add(1)` only,
  though `sync.WaitGroup.Add.spec` takes any delta. (2) `fmt.wp_Sprintf` admits arguments of
  predeclared basic types only (`fmt.ArgsWf`): an argument with a `String` method (a
  `types.ID`) is outside it, though Go's formatting then only calls that method.
- **Needed by.** (1) rafthttp's `pipeline.start`, `p.wg.Add(connPerPipeline)` (`4`). (2) rafthttp's
  `peerStatus.deactivate`, `Sprintf("failed to %s %s on %s (%s)", action, s.id, source, reason)`.
- **Workaround here.** (1) `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/
  WaitGroupAdd.lean`, `wgJoin_wp_Add4_of` (`wp_Add_of`'s proof with four ghost steps; proved, no
  trust). (2) `Spec/fmt/SprintfID.lean`, a trust-boundary axiom for `types.ID` arguments (as
  `SprintfNamed`, `SprintfClientPtr`).
- **Proposed.** (1) `wp_Add_of` for a delta `n` (`0 < n`, the bound `num_added + n < 2^31`),
  giving `n` `ownDone`s (a `[∗list]` over `List.replicate n`); the `Add(1)` statement derived.
  (2) `wp_Sprintf` over arguments whose `String`/`Error` method has a given spec (a WP returning
  some string), covering `Stringer`s generally.
- **Status.** Not started.

### `fmt.Errorf`'s result: a fresh pointer error (2026-10-23, rafthttp stage 4e, branch `rafthttp-plan`)

- **Missing.** `fmt.Errorf.spec` gives only that the error's `Error()` returns some string; it does
  not say the error is a fresh pointer (`*fmt.wrapError` or `*errors.errorString`: `IsPointerError`,
  as `errors.New.spec` says), so a caller cannot show it differs from a package's error variable.
- **Needed by.** rafthttp's `checkPostResponse`, whose `fmt.Errorf` errors must not be
  `errMemberRemoved` (`postErr`: `pipeline.post`'s caller reports only that one on `errorc`).
- **Workaround here.** None yet: `checkPostResponse` is a spec only. (Stage 5e-3) The stream
  reader's `dial` uses a local trust-boundary spec, `Spec/fmt/ErrorfPlain.lean`: with no `%w` the
  error is an `*errors.errorString` (Go's `Errorf` returns `errors.New(s)`), whose `Error()`
  returns the message, so a leaf of an error tree (`errors.Is` of it, in `run`).
- **Proposed.** `fmt.Errorf.spec`'s postcondition with `IsPointerError err` (for a format without
  `%w`), as `errors.New`'s; or the `*errors.errorString` form above.
- **Status.** Not started.

### `strings.TrimSuffix` without a spec (2026-10-23, rafthttp stage 5e-3, branch `rafthttp-plan`)

- **Missing.** Perennial translates `strings.TrimSuffix` names-only and has no spec for it
  (`TrimPrefix` has one).
- **Needed by.** rafthttp's `streamReader.dial` (a `412`'s body, `TrimSuffix(string(b), "\n")`).
- **Workaround here.** `Spec/strings/TrimSuffix.lean`, a trust-boundary axiom: some string.
- **Proposed.** A translation or model of `TrimSuffix` with a spec (the string without the suffix,
  if it ends with it), as `TrimPrefix`'s.
- **Status.** Not started.

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

### Small gaps met by rafthttp's stream writer (stage 5b, 2026-10-23)

- **Missing.** (1) A typed points-to's halves: `typedPointsto l v (own 1) ⊣⊢ half ∗ half` is
  proved only in an example (`goose/testdata/examples/channel/etcd_session/Base.lean`,
  `pointsto_halves`), not the library. (2) `len(ch)` of a channel: `wp_auto` does not unfold
  `functions go.len [chan]` (`FuncUnfold`'s `len_chan`) to `Channel.Len`, so `chan.wp_Len` applies
  only after `wp_func_call; wp_call`. (3) `make([]T, n)` of a large concrete `n` (rafthttp's 1 MiB
  `msgAppV2BufSize`): `wp_slice_make2`'s postcondition names `List.replicate n zero`, which the kernel
  unfolds when a proof frames it (a deterministic timeout); a spec with the contents abstracted
  (`∃ zs, sl ↦* zs ∗ ⌜zs.length = n⌝`) avoids it.
- **Needed by.** `streamWriter.close` (the writer's fields split between its goroutine and its
  lock), `streamWriter.closeUnlocked` (`len(cw.msgc)`), `newMsgAppV2Encoder` (its buffer).
- **Workaround here.** `rafthttp/Writer.lean`'s `typedPointsto_halves` and
  `typedPointsto_combine_halves`; `wp_func_call; wp_call` before `wp_Len`;
  `newMsgAppV2Encoder.lean`'s `wp_make_bytes_abs`.
- **Proposed change.** (1) The halves lemma in `Golang/Theory/PostLifting.lean`; (2) `len_chan`'s
  unfolding in `wp_auto`'s simp set; (3) `wp_slice_make2_abs`/`make3_abs` beside the existing specs.
  Not yet proposed.
- (2026-10-23, rafthttp stage 5c) **A non-blocking send on a bag channel** (`select` with a
  `default`): the bag idiom (`Idioms/Bag.lean`) has the blocking send only. Workaround:
  `rafthttp/Reader.lean`'s `bag_nonblocking_send_au` (`bag_send_au` without the waiting case).
  Proposed change: the lemma beside `bag_send_au`. Not yet proposed.
- (2026-10-24, rafthttp stage 6d) **`wp_apply` aborts silently inside a `wp_join` case**: in
  `raftNode.start`'s loop, `wp_apply HSend $$ [...]` of the transport's `Send` (an interface method,
  its spec a hypothesis whose precondition now holds the loop's `E.S`) throws "unknown free
  variable" (visible with `+noauto`) and, without `+noauto`, an abort that leaves the case's goal
  admitted with no error: the module builds with a `sorry` only `#print axioms` and
  `etc/tcb-report.py` see. Workaround here: `wp_bind` the call and `iapply` the hypothesis
  (`raftNode__start.lean`). Proposed change: find the escaping free variable (probably the case's
  generalized context) and make `wp_apply` report it as an error. Not yet proposed.
- (2026-10-24, rafthttp stage 6f) **An axiomatized type's `sorry` instances shadow its `TypeRepr`**:
  for a type Goose cannot translate (`net/http`'s `Request`, `Response`) the generated proof has
  `X_typed_pointsto`/`X_into_val_typed` as `sorry -- axiomatized type`, and instance search takes
  `TypeRepr X.underlying X` from them (`IntoValTyped.type_repr`) although the translation's
  `X.TypeAssumptions.type_repr` gives it: a field reference (`StructFieldRef`, `req.Header`)
  then reaches the `sorry` (`etc/tcb-report.py`), with no load or store of the whole value.
  Workaround here: `Proof/net/http/Boundary.lean`'s `Request_typeRepr`,
  `Request_underlying_typeRepr` (and `Response`'s), high-priority instances from the type
  assumptions. Proposed change: Goose emits no `IntoValTyped` instance for an axiomatized type
  (or one of low priority), so its `TypeRepr` comes from the type assumptions. Not yet proposed.
