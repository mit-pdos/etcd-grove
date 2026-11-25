# The spec plan's change ledger

A spec defect that a proof (or a review, a test, a user's critique) finds in a spec of the spec plan
(`SpecPlan/Spec/`), or a divergence between a real spec (`Spec/`) and the plan's, is recorded here
**before** either spec is edited (CLAUDE.md, "The spec plan and convergence"). The ledger is how the
plan stays the target the real proofs converge toward: no silent edits.

One entry per defect, newest first, in this format:

```
## <date>: <spec> -- <one-line defect>

- **Spec.** The file and the declaration (`SpecPlan/Spec/<pkg>/<fn>.lean`, `<fn>.spec`; or a law,
  `<pred>_<law>.spec`), and the real spec it corresponds to (`Spec/<pkg>/<fn>.lean`), if any.
- **Defect.** What is wrong: unprovable (false of the Go code), too weak for a user, too strong (a
  premise no caller can meet), not local, vacuous, ...
- **Evidence.** What shows it: the proof step that fails (file:line, the goal), the Go path (a
  panic, an error the post omits), the user or snippet (`examples/specreq/<alias>/`) it breaks, a
  failing test.
- **Proposed change.** The new statement (or its delta), and what else it moves: the snippets, the
  callers' and callees' specs and proof sketches, the open questions it touches.
- **Decision.** Pending / accepted (by whom, date; the commit that applied it) / rejected (why).
```

A change that needs the user's approval (a spec's statement at the client boundary, new
client-visible ghost state, a trust-boundary spec) says so in **Decision** and waits for it.

## 2026-11-25: the antithesis harness's `CfgOk` -- `0 ≤ MaxDelay` goes with the delay (#33 S4)

- **Spec.** `Proof/.../raft/antithesis/HarnessDefs.lean` (`CfgOk`, `defaultCfg`, `clusterRO`), the premise
  of `Spec/.../raft/antithesis/RunCluster.lean`; `Cluster__isolate.lean`, `Cluster__isolatedNow.lean`
  (removed); the headers of `Cluster__send.lean`, `DefaultConfig.lean`, `RunCluster.lean`.
- **Defect.** None in the spec: the Go program lost the knobs it was about (the robustness review's items
  4, 5, 7, 8: no per-message delay, drops or isolator; an unbounded proposer).
- **Evidence.** `send` no longer calls `below(uint64(MaxDelay) + 1)`; `Config` has no `MaxDelay`,
  `Cluster` no `isoMu`/`isolated`.
- **Proposed change.** `CfgOk cfg := cfg.Nodes' = W64 3 ∧ 0 < sint.Z cfg.Tick'`; `clusterRO` without the
  mutex; `defaultCfg` the three remaining fields. `RunCluster.spec`, `Main.spec`, `Cluster.send.spec`
  unchanged but for their headers. No SpecPlan counterpart.
- **Decision.** Applied (the S4 lead's brief: spec changes that only drop what the removed knobs needed).

## 2026-11-23: `maps.Keys.spec_objMap` -- `slices.Sorted` needs the map below `2^62` keys (maps-keys, #36)

- **Spec.** `Spec/maps/Keys.lean` (`maps.Keys.spec_objMap`, the axiom `maps.Keys.wp_proof_objMap`), and the
  checker's model vocabulary that must supply its new premise: `itemsRO` (`Proof/.../k8s/etcd3/correctness/Defs.lean`),
  the specs `Model.create`, `Model.update`, `Model.execute`, `Model.Step`, `initialModel`, `toPorcupineModel`,
  `realCheck` (all under `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/`), `stepPre` and `realMS`'s `rep`.
  No SpecPlan counterpart.
- **Defect.** Too strong to prove: Perennial's `maps.wp_Sorted_Keys_string` (`ccfeb3895`) proves the pair only for
  a map of at most `2^62` keys (`slices.Sort`'s heapsort premise: its index arithmetic overflows past that, real
  in Go). The axiom claimed it for every map.
- **Evidence.** `Perennial/Proof/maps/Results.lean`, `wp_Sorted_Keys_string`'s `⌜GMap.size M ≤ 2 ^ 62⌝`.
- **Proposed change.** `spec_objMap`'s closure takes `⌜GMap.size M ≤ 2 ^ 62⌝` (and the axiom becomes a theorem from
  Perennial's). The checker supplies it from a new invariant of the model's items, carried in `itemsRO`: at most
  `2^62` items. A model that grows (`create`, `update`, so `execute`, `Step`) takes `GMap.size m.items < 2 ^ 62`;
  `initialModel` takes its store's items at most `2^62`; `realMS`'s value at index `k` has at most `2^61 + k` items
  (porcupine steps below index `2^60`), so `toPorcupineModel` takes an initial model of at most `2^61` items;
  `stepPre` (so `ReplayPre`) carries the strict bound along the replay; `realCheck` takes the seeded store's items
  below `2^60`, which `Check` has from `Model`'s premise (`g0.st.items.length + g0.hist.length < 2 ^ 60`). No
  top-level statement moves (`Check.spec` is unchanged).
- **Decision.** Accepted by the coordinator (option 1, #36), 2026-11-23; applied on branch `maps-keys`.

## 2026-11-23: `idClusterInv` / `NewGenerator.spec` -- the cluster's claims hold every machine's generator facts (etcd-dist D7)

- **Spec.** `Spec/go_etcd_io/etcd/pkg/v3/idutil/NewGenerator.lean` (`idutil.NewGenerator.spec`), its vocabulary
  `idClusterInv`/`idKeyGenFacts`/`idGen` (`Proof/go_etcd_io/etcd/pkg/v3/idutil/Defs.lean`), and its users
  `Spec/go_etcd_io/etcd/server/v3/etcdserver/NewServer.lean`, `NewServerR.lean`. SpecPlan: the idutil and server
  specs of `SpecPlan/Spec/` that take the cluster's claims (to check when implemented).
- **Defect.** Not local: the cluster-wide invariant `idClusterInv` holds, per key, its generator's `prefix` points-to
  and the issue record's facts (`idIssueFragD`, the machine-local extension state), and compares generators' `Loc`s
  across keys. Sound in one process; it cannot be allocated once for a deployment of machines (D7: the start has no
  heap), nor hold facts of several heaps.
- **Evidence.** D7's re-sectioning (`d7-resection`): `idClusterInv` is the one cluster definition that does not
  move to a global section (it reaches `HeapGS`/`GooseLocalGS`); `notes/etcd-dist-plan.md`, "The idutil split".
- **Proposed change.** The plan's "The idutil split": `idClusterInv` without the generator facts (type unchanged);
  a per-prefix heap-level `idPfxInv` holding them (both arguments that use them are per prefix, and a prefix is one
  machine's); `IdNames.gen`; `NewGenerator.spec`'s pre gains `idPfxInv γi.gen γi.pfx`; `NewServer.spec`/`NewServerR.spec`
  gain it; `idGen`'s body. No top-level theorem's statement changes (checked; the plan lists the files).
- **Decision.** Pending (the coordinator posts it on #28 before implementation; idutil's specs are shared).

## 2026-11-23: zap's logger and entry vocabulary -- `zapLoggerOk` narrowed to `NewNop`'s loggers, `zapcore.zapEntry` defined (zap Z0/Z1, #40)

- **Spec.** `Spec/go_uber_org/zap/Defs.lean`: `zapLoggerOk` (until now `⌜l ≠ null⌝ ∗ □ zap.loggerRaw l`,
  `loggerRaw := nopLogger ∨ loggerOther`, `loggerOther` opaque), `zap.nopLoggerVal`/`zap.nopLogger` (core some
  value of type `nopCore`) and `zapcore.zapEntry` (opaque). The two trust-boundary axioms over them,
  `zap.Logger.check.wp_proof` and `zapcore.CheckedEntry.Write.wp_proof`
  (`Spec/go_uber_org/zap/{Logger__check,zapcore/CheckedEntry__Write}.lean`): their statements do not change.
  The spec plan's zap specs (`SpecPlan/Spec/go_uber_org/zap/`) keep their opaque predicates.
- **Defect.** None in what callers rely on; the vocabulary was opaque only because zap's cores were not
  translated. No spec produces `loggerOther` (only `Defs.lean` names it): every proved example builds its
  logger with `zap.NewNop()`, so its case is dead weight that keeps `check` an axiom. `nopLogger`'s core was
  `interface.mkOk nopCore.ty w` for some `w : val`, which a proof cannot call a method on (`wp_call` needs the
  receiver not to be a panic value).
- **Evidence.** `grep loggerOther`: `Defs.lean` and `NewNop.lean` only; no top-level statement names zap.
  zap v1.28.0 `logger.go:330-343`: below `DPanicLevel`, `check` returns `nil` when `log.core.Enabled(lvl)` is
  false, which `nopCore.Enabled` always is (`zapcore/core.go:51`); the rest of `check` (clock, caller, stack)
  is never reached on a `NewNop` logger at those levels. `CheckedEntry.Write` (`zapcore/entry.go:243-290`) on
  an entry that is not dirty, has no `before` hooks, no cores and no `after` hook marks it dirty and returns
  it to `_cePool`. `NewNop`'s core is `nopCore{}` (`zap_wp_NewNop_init` proves the field `rfl`).
- **Proposed change.** `zapLoggerOk l := ⌜l ≠ null⌝ ∗ □ zap.nopLogger l` (`loggerOther`, `loggerRaw` deleted);
  `nopLoggerVal`'s and `nopLogger`'s core is `interface.mkOk nopCore.ty #nopCore.mk` (the other fields
  unchanged: `check` below `DPanicLevel` reads only `core`). `zapcore.zapEntry ce` := `ce` points to a
  `CheckedEntry` (owned) that is not dirty, with no `before` hooks, no cores and no `after` hook (its `Entry`
  and `ErrorOutput` any): what `Write` writes without effect, and the only entries a `NewNop` logger could
  hand out (none: `check` returns `nil` below `DPanicLevel`). Still exclusive. `Logger.check` is proved;
  `CheckedEntry.Write` stays an axiom, now over this entry: its proof reaches zap's generic
  `pool.Pool[T].Put`, whose Goose translation omits the conversion of `x : T` to `any`
  (`notes/perennial-changes.md`). A non-`NewNop` logger (Z3, #40) brings `loggerOther` back with its cores'
  specs.
- **Decision.** Z0 decided by the coordinator on #40 (2026-11-23); applied on branch `zap-z1`.

## 2026-11-23: six server-side trust-boundary axioms -- their errors' `deadlineExceededError`s hold `deadlineExceededError{}` (errors-is-deadline, #31)

- **Spec.** Five axioms whose posts promise `applyErrIs`
  (`Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/Base.lean`). The first four promise it directly,
  `NewAuthStore` through its auth checks' `authApplyErrIs`:
  - `leasehttp.RenewHTTP.spec`
  - `EtcdServer.leaseTimeToLive.spec`
  - `EtcdServer.rangeStream.spec`
  - `proto.MarshalIRR.spec`
  - `auth.NewAuthStore.spec`

  And `bcrypt.GenerateFromPassword.spec`, whose non-pointer error `UserAdd` makes an `applyErrIs`
  (`applyErrIs_valLeaf`). No spec-plan counterparts.
- **Defect.** Too weak for `togRPCError`'s `errors.Is(err, context.DeadlineExceeded)`, which every
  handler error reaches (`srvErrIs` ⊇ `applyErrIs`). Perennial's `errors.Is` needs the tree's errors
  of the target's type to hold a value of it (`errors.ComparableErr`), and the model does not type
  interface values.
- **Evidence.** `errors.IsDeadlineExceeded.spec`'s `⌜deTyped S⌝` (entry below), at `togRPCError`'s
  tree for `context.DeadlineExceeded` (`applyErrIs_treeDE`).
- **Proposed change.** `applyErrIs`'s tree (and `errTreeOk`) gains `deTyped S`. This strengthens what
  the five axioms post, and their docstrings say so. Go's typing makes it true of every Go error:
  `deadlineExceededError` is a field-less struct, whose only value is `deadlineExceededError{}`.
  `bcrypt.GenerateFromPassword`'s non-pointer branch gains `ei.ty ≠ deadlineExceededError.ty`: it
  is an `InvalidCostError`, a named type of bcrypt's own. The proved constructors of `applyErrIs`
  discharge it: `nil`; pointer leaves; `%w` wraps; `applyErrIs_valLeaf`, which takes
  `deTypedErr e`, given by the context errors (`deadlineExceeded_deTypedErr`) and bcrypt's new
  conjunct.
- **Decision.** Accepted by the coordinator under the user's approval of the same typing class
  (2026-11-23); review requested on #31.

## 2026-11-23: grpc's `ctxErrsErr` (and the client's `ctxErrClient`) -- an error of type `deadlineExceededError` holds `deadlineExceededError{}` (errors-is-deadline, #31)

- **Spec.** `ctxErrsErr` (`Proof/google_golang_org/grpc/InvGrpc.lean`, the trust boundary's contract
  of a context's `Err()` outside Perennial's model), and `ctxErrClient`
  (`Proof/go_etcd_io/etcd/client/v3/InvKVConn.lean`), which is `rfl`-equal to it
  (`ctxErrClient_eq_errs`). No spec-plan counterpart.
- **Defect.** Too weak for `errors.IsDeadlineExceeded`'s proof. The model does not type interface
  values: an error whose dynamic type is `deadlineExceededError` may hold any value. Perennial's
  `errors.Is` compares the target `context.DeadlineExceeded` with the tree's errors of its type, and
  for that it needs them to hold a value of the type (`errors.ComparableErr`).
- **Evidence.** `deadlineExceededError_comparable` (`Proof/errors/CtxErr.lean`) needs
  `∀ ii ∈ S, ii.ty = deadlineExceededError.ty → ii.v = #(zero_val deadlineExceededError)`. The
  client's `contextErrToGRPCErr` passes `errors.Is` the error `Err()` returned (`ctxErrLeaf`), and
  nothing says what it holds.
- **Proposed change.** The non-nil disjunct's pure conjunct gains, at its end, `e.ty =
  deadlineExceededError.ty → e.v = #(zero_val deadlineExceededError)`. Go guarantees this by typing:
  the field-less struct's only value. Producers: Perennial's contexts (`ctxErrClientAllW_of`:
  `Canceled` is a pointer, `DeadlineExceeded` holds the zero value, by `context`'s `isInit`), k8s's
  `channelContext` (`Canceled`), and the quiet contexts (no non-nil error). `ctxErrLeaf` carries the
  fact (`ctxErrLeaf_of_isCtxErr`, `ctxErrLeaf_of_errs`).
- **Decision.** Accepted by the user 2026-11-23 (a trust-boundary contract, relayed by the
  coordinator; #24 notified).

## 2026-11-23: `errors.IsDeadlineExceeded` takes `isPkgInit context` and the tree's typing (errors-is-deadline, #31)

- **Spec.** `errors.IsDeadlineExceeded.spec` (`Spec/errors/IsDeadlineExceeded.lean`); no spec-plan
  counterpart.
- **Defect.** Unprovable once it is no longer an axiom, for two reasons.
  - The precondition gives of `target` only the cell `context.DeadlineExceeded` it was read from.
  - Go's `err == target` on the tree's errors of `target`'s type, a field-less struct, needs those
    errors to hold `deadlineExceededError{}`. The model does not type interface values
    (`errors.ComparableErr`, perennial#677).
- **Evidence.** The proof over `errors.wp_Is` needs `ComparableTarget S target`. Its
  `deadlineExceededError_comparable` (`Proof/errors/CtxErr.lean`) takes the typing of `S`.
- **Proposed change.** The precondition gains `isPkgInit pkg_id.context`, which pins `target` to
  `deadlineExceededError{}` (`isInit`'s `"#HDeadlineExceededTy"`). It also gains `⌜deTyped S⌝`
  (`Proof/errors/CtxErr.lean`): every error of `S` whose type is `deadlineExceededError` holds
  `deadlineExceededError{}`.
  - Server's `togRPCError`: `applyErrIs`'s tree carries `deTyped` (`apply/Base.lean`).
    `applyErrIs_valLeaf` takes it of its leaf. Its callers pass context errors, and `isCtxErr_deTypedErr`
    gives it for them.
  - Client's `contextErrToGRPCErr`: `ctxErrLeaf` carries it, from `ctxErrsErr`'s new conjunct
    (entry above).
  - The post is unchanged.
- **Decision.** Accepted (internal: premises both callers meet; the spec stops being a trust
  boundary, and the axiom `errors.IsDeadlineExceeded.wp_proof` is retired), upamanyus-agent
  2026-11-23. The server's side needs the typing fact of six trust-boundary axioms (entry above).
## 2026-11-23: `DescribeConfChange` proved; `ConfChangeType.String`/`ConfChangeTransition.String` trusted models with exact specs (builder-fprintf-leaves, #25)

- **Spec.** `Spec/go_etcd_io/raft/v3/DescribeConfChange.lean` (unchanged; `DescribeConfChange.wp_proof` an
  axiom until this change, now a theorem); new: `Spec/go_etcd_io/raft/v3/raftpb/ConfChangeType__String.lean`,
  `ConfChangeTransition__String.lean` (exact: `raftpb.ccTypeString`/`ccTransitionString`, the name table's
  entry else the decimal), against the plan's `SpecPlan/Spec/go_etcd_io/raft/v3/raftpb/ConfChangeType__String.lean`
  (assumed, some string). raftpb's package fact (`Proof/go_etcd_io/raft/v3/Base.lean`) grows by the two tables.
- **Defect.** None in a statement: the axiom's triple was unprovable only for want of models. `%v` of the
  transition and of each change's type calls their `String()`, which raftpb translated names-only, and
  Perennial's `fmt` admits such an argument only with a `stringMethodSpec`.
- **Evidence.** `Proof/go_etcd_io/raft/v3/DescribeConfChange.lean`, over Perennial `9da0efb89`'s
  `strings.Builder` and `7b2259a12`'s `fmt.wp_Fprintf`/`wp_Fprintf_bytes`. Go test
  `TestConfChangeEnumStringIsNameTable` (`examples/raft/tracecheck/msgtype_string_test.go`).
- **Proposed change.** The two methods trusted (`Code/go_etcd_io/raft/v3/raftpb.toml`; models in
  `TrustedCode/go_etcd_io/raft/v3/raftpb.lean`, `MessageType.String`'s precedent, Q9), their specs exact as
  `MessageType.String`'s (stronger than the plan's; the plan's follows when its raftpb is next reworked).
  Trust base: -1 axiom (`DescribeConfChange.wp_proof`), +2 trusted models.
- **Decision.** Trusted models approved by the coordinator under the user's delegation (2026-11-23); review
  requested on etcd-grove#25. Applied (builder-fprintf-leaves).
## 2026-11-23: `addFeatureGateMetrics.spec` -- `isFeatureGate` does not give what the body needs (featuregate-2, claim #36)

- **Spec.** `Spec/go_etcd_io/etcd/server/v3/etcdserver/addFeatureGateMetrics.lean`, `addFeatureGateMetrics.spec`
  (the premise `isFeatureGate fg`, `Proof/go_etcd_io/etcd/server/v3/features/Defs.lean`); the plan's
  `SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/addFeatureGateMetrics.lean` (over `Features.serverGate`).
- **Defect.** Unprovable over the real body (`server.go:2496-2506`) as stated. `isFeatureGate fg` is only a
  contract on `Enabled(f)` for `f ∈ serverFeatures`. The body calls `fg.(MutableFeatureGate).GetAll()`, which
  loads `f.known`: the premise owns nothing of the gate's fields, so the load cannot be stepped (and in the
  logic a `*featureGate` whose `enabled` holds the server's features but whose `known` is empty meets the
  premise, and `GetAll`'s type assertion of `nil` panics). And `GetAll` returns `known`, which holds
  `featuregate`'s own `AllAlpha` and `AllBeta` (`defaultFeatures`, cloned by `New`), not in `serverFeatures`:
  the loop's `fg.Enabled("AllAlpha")` is outside the contract.
- **Evidence.** The body read against the predicate; no proof attempted (the gate's provider,
  `features.NewDefaultServerFeatureGate.wp_proof`, is still an axiom: its post states `isFeatureGate`).
- **Proposed change.** `isFeatureGate fg` also gives `GetAll`'s contract: it returns a fresh map whose keys
  are features `Enabled` answers (the contract's feature set widened from `serverFeatures` to a set `S ⊇
  serverFeatures` the gate's `known` has, `AllAlpha`/`AllBeta` included) and whose `PreRelease` strings are
  valid UTF-8 (`labelMapOk` for `serverFeatureEnabled`'s `With`). The five proofs that destructure the
  predicate (`EtcdServer__{FeatureEnabled,NewUberApplier,Txn}`, `NewServer`, `NewServerR`) take one more
  component. Made after `NewDefaultServerFeatureGate` is proved (until then the change strengthens that
  axiom's post, a trust-boundary spec).
- **Decision.** Accepted by the coordinator; review requested on #36. Made on `featuregate-4`
  (2026-11-23), after featuregate-3 proved `NewDefaultServerFeatureGate`: `isFeatureGate fg` is now
  `∃ fi K, fg = ok fi ∗ ⌜serverFeatures ⊆ dom K ∧ featureLabelsOk K⌝ ∗ □ Enabled(f) for f ∈ dom K ∗
  □ GetAll() returns a fresh m ↦$ K` (`featureLabelsOk K`: each name and `PreRelease` valid UTF-8).
  `featuregate.featureGate.GetAll` translated and proved (over `maps.Copy`); `NewDefaultServerFeatureGate`
  gives the new components (`K = serverFeatureSpecs ∪ defaultKnown`, ASCII literals);
  `addFeatureGateMetrics.spec` unchanged, now proved (the axiom retired); the five proofs take the
  extra components.

## 2026-11-23: net/rpc model's server -- the server codec's frame read errors are sticky (`rerr`); its read specs, `newServerCodec.spec` and the loop's vocabulary follow

- **Spec.** `models/net/rpc/codec.go` (the model, trusted): `serverCodec` gains `rerr`, the first frame read
  error, which every later `ReadRequestHeader`/`ReadRequestBody` returns without reading.
  `Net/Spec/net/rpc/serverCodec__{ReadRequestHeader,ReadRequestBody}.lean`: a premise `rerr ↦ r0`; with `r0`
  not `nil` the read returns `r0` and reads nothing, otherwise as before, `rerr` then holding a frame read's
  error (`nil` after a success or a header that does not parse). `newServerCodec.spec` gives `rerr ↦ nil` and
  `closed ↦ false` too. `Net/Proof/net/rpc/ServerDefs.lean`: `readerSt` (prepared, unused) redefined over
  the frames read and the count `k` (`reqPls` via `reqPlsFrom`); `srvEnv`'s `invalidRequest` is the unit
  `struct{}{}` value (it was an interface value, of the wrong type for the load); new `rdrOwn`, `rdrMid`,
  `callReady`, `ansRes`, `errCont`, `rdErr`, `srvCodecAt`, `srvCodecOwn`.
- **Defect.** Found proving `ServeCodec`. Go's `ServeCodec` answers a request whose body read failed and reads
  on (`readRequest` returns `keepReading` true); gob's decoder keeps no read error, so the next header is
  read from the middle of the failed request. The net extension's semantics lets a read return bytes after a
  read error (a `sys` error on a cut direction with unread bytes kept), so the reader could decode bytes no
  client wrote as a request, and run a method on them without a deposit: the server's guarantee (each run
  answers a request a client deposited) is unprovable over the unchanged model.
- **Evidence.** `models/net/rpc/server.go` (`ServeCodec`, `readRequest`); Go 1.27.3's `encoding/gob`
  (`DecodeValue` resets `dec.err`); `GooseLang/Ext/Net/Impl.lean` (`ReadAvail`'s `sys` case, `ReadOutcome`'s
  break keeping a prefix); Linux: a read error comes once the unread bytes are read, then EOF
  (`examples/net/semantics`' `TestResetInNetwork`, `TestKilledWithUnreadInput`, `TestTimeoutOnBreak`), but for
  a read deadline's timeout. `nonissues/go-netrpc-server-reads-on-after-body-read-error.md`.
- **Proposed change.** As above: the model's codec, Go's behavior over Linux when the program sets no read
  deadline on a served connection (the model's claim says so, `codec.go`'s doc);
  `models/internal/rpcdifftest/run.sh` still passes. The client codec is unchanged (its reader stops at the
  first error). Not done: `Register`/`RegisterName`'s premises excluding the logging paths (entry below) could
  now go, `log.Println` being modelled and specified (`Net/Spec/log/Println.lean`).
- **Decision.** Applied (branch `models-rpc-server`) for the sticky error and the specs; the premises' removal
  pending. The sticky error narrows the model's trusted claim (no read deadlines on served connections): for
  the user to confirm.

## 2026-11-23: net/rpc model's server -- `decErr` gains a non-empty message; `CodecSpec` gains `rcv`; the net model's `OpError.Error` is never empty

- **Spec.** `Net/Proof/net/rpc/Codec.lean`: `decErr err` (a decoding error) now also says its message is not
  empty; `CodecSpec` gains a field `rcv : GoInterface → (Loc → IProp) → IProp` (what `Receiver(rcvr)` needs,
  returning a `*Receiver` with `Ψ`), and `codecIs` holds `rcvOk C v.Receiver'`. `Net/TrustedCode/net.lean`
  (trusted): `OpError.Error.impl` returns an arbitrary string that is not empty (was any string).
- **Defect.** Found stating the server's request loop. When a request's header reads but its body does not
  read or decode, `ServeCodec` answers it with `sendResponse(..., err.Error())`; with a message `""`
  `sendResponse` sends a *success* response, encoding the placeholder `invalidRequest`, which no generated codec
  lists (its `Encode` panics). Both errors that can reach there were allowed an empty message: a decoding error
  (`decErr`) and the `Read`'s `*OpError` (the model's `AnyString`). And `register`'s dispatch goes through the
  codec's `Receiver`, about which `CodecSpec` said nothing (the first part had left it "to state").
- **Evidence.** `models/net/rpc/server.go` (`ServeCodec`, `sendResponse`, `readRequest`); the generated
  codec's decoding error is `errors.New("net/rpc model: malformed value")` (`rpcgen_core.py`); Go's
  `(*OpError).Error()` starts with `e.Op` (`net.go`), measured: `TestErrorsAreOpErrors`
  (`examples/net/semantics/errors_test.go`, now checking every message starts with the operation and holds `": "`).
- **Proposed change.** As above. The client's proofs destructure the longer `codecIs` and `decErr` (patterns
  only); `errAny_opErr` is derived from the new `errNE_opErr` (`Errs.lean`). No client statement changes.
- **Decision.** Applied (branch `models-rpc-server`): strengthenings the generated codec and Go meet; the
  `OpError.Error` model change is a narrowing of trusted behaviour backed by the measured test (D14).

## 2026-11-23: net/rpc model's server -- `Register`/`RegisterName` cover only the receivers they accept without logging; a method spec must accept error answers

- **Spec.** `Net/Spec/net/rpc/Server__{register,Register,RegisterName}.lean` vs dsverify-lab's
  `Server.RegisterName.spec`/`Register.spec` (`old/dsverify/.../ServerDefs.lean`), and `errOk`/`srvServes`
  (`Net/Proof/net/rpc/ServerDefs.lean`) vs dsverify's `srvServes`/`rcvrOk`.
- **Defect.** dsverify's statements return "`nil` and the registration, or some error" for any receiver. Go's
  `register` logs (`log.Print`) before returning three of its errors (no service name, not exported, no suitable
  methods), and Perennial has no model of `log.Print` (names only), so those paths are stuck. And dsverify's
  `rcvrOk` gave `Φ reply msg` only through the method's run; Go's server also answers requests it does not run
  (the body did not read or decode, the method is not registered) with an error message.
- **Evidence.** `Net/Code/net/rpc.lean`, `Server.register.impl` (`FuncResolve log.Print`); Perennial
  `Code/log.toml` (`trusted = ["Printf", "Println", ...]`). `server.go`'s `ServeCodec` error path.
- **Proposed change.** `register`'s premise `regNameOk` (a non-empty `name` with `useName`; without it, `rcvr`
  not a nil pointer, where Go panics, and its type's name starting with an upper-case ASCII letter, where the
  model's `IsExported` is exact) and `rcvrIs`'s at-least-one-method; the remaining error (a name taken) stays.
  `srvServes` asks each service spec for `errOk S` (an error answer, message not empty, from the deposit).
  When Perennial models `log.Print` (`notes/perennial-changes.md`, 2026-11-23), the premises can go.
- **Decision.** Applied (branch `models-rpc-server`); kits register receivers of exported types with methods,
  and their specs' continuations accept `ServerError`s (Go's client returns them for any call).
## 2026-11-22: `errors.IsCtxErr` takes `isPkgInit context` (errors-is-axioms, #31)

- **Spec.** `errors.IsCtxErr.spec` (`Spec/errors/IsCtxErr.lean`); no spec-plan counterpart.
- **Defect.** Unprovable once it is no longer an axiom: the precondition pins `err` (`context.isCtxErr`)
  but gives of `target` only the cell it was read from (`Canceled` or `DeadlineExceeded`). When the two
  come from different variables, nothing says what `target` holds, and Go's `err == target` (which `Is`
  runs first) needs `target`'s type comparable (`errors.ComparableTarget`, perennial#677).
- **Evidence.** The proof over `errors.wp_Is` (perennial#677): `ComparableTarget (· = err) target` for an
  unknown `target`.
- **Proposed change.** Add `isPkgInit pkg_id.context` to the precondition: with it, `target` is a context's
  error too (`context.isCtxErr_of_Canceled`/`_of_DeadlineExceeded`), a `*errorString` or
  `deadlineExceededError{}`, both comparable. The four callers (`parseProposeCtxErr`, `PromoteMember`,
  `LeaseRenew`, `watchServer.Watch`) have it. The post is unchanged.
- **Decision.** Accepted (internal: a premise every caller holds; the spec stops being a trust boundary,
  the axiom `errors.IsCtxErr.wp_proof` is retired), upamanyus-agent 2026-11-22.

## 2026-11-22: `FollowerStats.Succ` takes the stats' mutex (prove-ps2-succ)

- **Spec.** `v2stats.FollowerStats.Succ.spec` (`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v2stats/`; a
  trust-boundary axiom until this change, `leader.go` names-only for it); SpecPlan's `FollowerStats.Succ.spec` already
  takes `isFollowerStats p`. Moved with it: `v2stats.isFollowerStats` (now guarding all of `Counts` and `Latency`),
  `newMsgAppV2Encoder.spec` and `startStreamWriter.spec` (premise `v2stats.isFollowerStats fs` added beside
  `fs ≠ null`), `v2EncOwn` and `swFixed` (which keep it).
- **Defect.** Not provable over the real code: `Succ` locks the stats' embedded `sync.Mutex` and updates
  `Counts.Success` and the six `Latency` fields (`leader.go:104-128`), and the premise (`fs ≠ null`) gave no mutex and no
  points-to. True of Go by its type safety, not provable in the logic (as `Fail`'s, the entry of 2026-11-21).
- **Evidence.** The translation (`Code/go_etcd_io/etcd/server/v3/etcdserver/api/v2stats.lean`, `FollowerStats.Succ.impl`).
- **Proposed change.** As above: `isFollowerStats fs` owns `Counts` and `Latency` whole (`Follower` allocates them
  with the mutex); `Succ` and `Fail` take it. Its callers discharge it: the pipeline from `pipeHandleOk` (as for
  `Fail`), the msgappv2 encoder from `v2EncOwn`, which `newMsgAppV2Encoder` builds from its new premise, which
  `streamWriter.run` takes from `swFixed`, which `startStreamWriter` builds from its new premise, which `startPeer`
  has (its premise since 2026-11-21). The user's decision (2026-11-21): an ownership premise every caller discharges
  may be added.
- **Decision.** Applied (prove-ps2-succ, 2026-11-22): `Succ` translated and proved over Perennial's `math.Sqrt`
  (mit-pdos/perennial#675, in review: `sqrt`, compiled to the square-root instruction, trusted as an arbitrary
  float), the axiom retired once the pin includes #675.
## 2026-11-22: kvnet's `StartNode`/`Run`/`RunNode` -- the start resource `S` cannot name the node's configuration, and the file invariant cannot be allocated where the crash obligation needs it

- **Spec.** `KvNet/Spec/.../kvnet/StartNode.lean` (`StartNode.spec F rep cf S`, `S : IProp GF`), `Run.lean`,
  `RunNode.lean` (the same `S`); kvnet's `Defs.lean` (`kdFileInvK γ id n γd`, `kdWriter` over `γ.wr id`).
- **Defect.** (1) Not provable: `StartNode`'s start resource is one proposition for every `cfg`, but
  what the start needs names the configuration: the file of `cfg.Dir`/`cfg.ID`, raft's vacancy of
  `cfg.ID`, the bootstrap voters `1..cfg.Opts.Voters` (`kdCluster γ vs`), every other address's protocol
  (`newTransport`), raft's `Config` premises on `cfg.Opts`; and `newTransport` reads `cfg.Addrs`, which the
  precondition does not own. (2) Not provable: the file invariant (which holds `raftState`) is allocated
  after `RestartNode`, parameterized by its node; with a real crash (decision C) it must exist from the
  generation's start, carrying a crashed side the crash obligation can take (`inv (… ∨ crashed ∗ tok)`),
  so it cannot name the node; the writer's ghost variable `γ.wr id` is the store's, so the dead
  generation's `dmu` and the next generation's writer would share it.
- **Evidence.** `notes/kvnet-part.md`, "`StartNode` and the crash frame"; Perennial's crash adequacy
  (`DistAdequacy.lean:555`: the obligation `crashed -∗ extsCrashStart L L' ={⊤}=∗ P i L'` is fixed at the
  generation's start).
- **Proposed change.** (1) `S : w64 → GoString → Options → GMap w64 GoString → IProp GF` (id, dir, options,
  the address map), and `StartNode`'s precondition `cfg.Addrs' ↦$□ M ∗ S cfg.ID' cfg.Dir' cfg.Opts' M`;
  `Run.spec`/`RunNode.spec` pass the same indexed `S` (RunNode at the options and map it builds). (2) The file
  invariant `kdFileInvK γ id ph` over the incarnation's file names (`KdDmuNames` gains the writer variable
  `wr`, the invariant's crash token `tk`, the arm `x`): `∃ S s pb, durSt ∗ ghostVar ph.wr ½ (S,s,pb) ∗
  ((raftState S ∗ kdFileState γ id ph.x S s pb) ∨ crashed ∗ token ph.tk)`, the pending batch's record
  holding its node existentially (`∃ n, nodeArm n γ x ∗ readyEnter n … ∗ nodeRunning n q ∗ …`), the share
  `q` coming back to the writer through a saved proposition (`pb` gains its name); `kdWriter ph …`.
  Internal to kvnet's part (no client outside it); the top level allocates the file invariant at each
  generation's boot.
- **Decision.** Accepted (the kvnet-proof session, 2026-11-22; kvnet's own seam, decision C's plan).

## 2026-11-22: raft's `RestartNode` -- its client update cannot open a crash invariant (no crash token), so a client cannot keep `raftState` where a crash obligation can take it

- **Spec.** `Spec/go_etcd_io/raft/v3/RestartNode.lean`, `RestartNode.spec`: the update
  `AU <{ ∃∃ S, ▷ raftState γ cv.ID' S ∗ ⌜StorageHolds S σ⌝ }> @ ⊤ ∖ ↑N, ∅ <{ raftState γ cv.ID' S, COMM Q S }>`
  (and the RaftNoAx/KvNet copies).
- **Defect.** Too weak for a client whose process really crashes (kvnet, decision C). Perennial's crash
  adequacy takes each generation's crash obligation at the generation's start
  (`∀ L', crashed -∗ extsCrashStart … ={⊤}=∗ P i L'`), so the next generation's exclusive start resources
  must sit, from that start on, in invariants the obligation can empty: `inv (body ∨ crashed ∗ tok)`. Raft's
  `raftState γ id S` is one (exclusive; the next `RestartNode`'s update needs it). Every other opener of such
  an invariant must refute `crashed ∗ tok` with the generation's `notCrashed`, which a thread holds only at a
  step (`wp_ncfupd`, `wp_atomic_nc`, the channel updates' `ncfupd`). `RestartNode`'s update is a plain atomic
  update fired inside `RestartNode`: the client has no token there, and on the crashed side it would have to
  produce `raftState` (taken) and `StorageHolds S σ` of its own `σ`. Borrowing `raftState` out of the
  invariant before the call loses it to a crash during `RestartNode`.
- **Evidence.** `notes/kvnet-part.md`, "`StartNode` and the crash frame (2026-11-22)". The same problem was
  met and solved for durable's sync update (`durWriteSync`, `notes/kvnet-part.md`, "`persist`", item 1).
- **Proposed change.** `RestartNode`'s update given and returning the token, as `durWriteSync`:
  `notCrashed -∗ AU <{ ∃∃ S, ▷ raftState γ cv.ID' S ∗ ⌜StorageHolds S σ⌝ }> @ ⊤ ∖ ↑N, ∅
  <{ raftState γ cv.ID' S, COMM notCrashed ∗ Q S }>` (under `[CrashGS GF]`, as `nodeCrash`). Raft's proof fires
  it before any step of `RestartNode`, where `wp_ncfupd` gives the token. Existing clients (kvdurable,
  kvreconf, the server's start paths) pass a plain update through a lemma like `durWriteSync_of_au` (the token
  unused). Raft's change, not kvnet's.
- **Decision.** Accepted as proposed (the kvnet-proof session, 2026-11-22, on the coordinator's brief), after
  checking the shape:
  - *Sound, nothing trusted moves.* The token is the state interpretation's (`HeapGS`'s
    `goose_crashGS`); raft's proof already ran the restart's ghost step under `wp_ncfupd` (the
    vacancy's arm needs it, `armed_read`), so it only lends the token to the client's update and takes it
    back (`raft_restart`'s accessor now `notCrashed -∗ |={…}=> … (… ={∅,…}=∗ notCrashed ∗ R S)`). No axiom,
    no `Assumptions` field, no Perennial change.
  - *Minimal.* The token appears once in the precondition's update and once in its `COMM`, nothing else in
    the triple changes; the same shape as durable's `durWriteSync` and raft's own trace updates (`TraceFire`,
    `TracedCap.lean`). A weaker alternative (the client update as an `ncfupd` around a plain AU) gives the
    client nothing more and needs an atomic-update rule Perennial lacks.
  - *Clients.* `restartAu_nc` (`InvNodeRule.lean`) makes a plain update one; kv, kvreconf (two), kvdurable
    (and its RaftNoAx copy) and the server's `newRaftNode` wrap theirs before the call. RaftWitness keeps its
    own (older) spec, untouched; RaftTla/RaftNoAx/KvNet copies regenerated.
  - SpecPlan's `RestartNode` (and its `newRaft`/`NewRawNode` updates) not changed: its crash story is the
    vacancy's `raftState_crash` law, to be reconciled when kvnet's form is ported back (open).

## 2026-11-21: raft's node API -- `isCluster` holds one machine's heap (the node table), and the node predicates agree on a node's names only through it

- **Spec.** `Spec/go_etcd_io/raft/v3/StartNode.lean`, `RestartNode.lean` and the `node.*` method specs;
  `InvNode.lean`'s `isNode`, `nodeRunning`, `nodeDriver`, `nodeStopped`, `nodeConfig`, `nodeTagPin`,
  `nodeArm`, the snapshot-source and ready-token facts; `InvNodeRule.lean`'s `isCluster`. SpecPlan's
  raft node specs, likewise.
- **Defect.** Not local enough for a distributed client. `isCluster` contains `nodeTabInv`, which keeps
  `n ↦□` for every node, so it can be neither allocated in a distributed adequacy theorem's `Hstart`
  (only `[GooseGlobalGS]`) nor held by another machine. Keyed by `Loc`, the table also breaks across
  generations: a new heap can reuse a dead node's address.
- **Evidence.** `notes/kvnet-proof-plan.md` gap 2 and decision B; `notes/raft-cluster-global.md` (a),
  (b).
- **Proposed change.** An opaque node handle `nh : NodeH` (location and names; `nh.loc` for code
  values):
  - the node predicates take `nh` in place of `n : Loc`;
  - `StartNode`/`RestartNode` return `∃ nh, ⌜nd = … #nh.loc⌝ ∗ …`;
  - the node table goes, and `isCluster` is global.
  The shared predicates and the allocation lemmas are stated at `[GooseGlobalGS]` (their statements
  unchanged). Clients: kv, kvreconf, kvdurable, the etcd server, etcdstart, the trace check.
- **Decision.** Accepted (the coordinating session, 2026-11-21, option 3 of
  `notes/raft-cluster-global.md`); applied on branches `raft-cluster-global` and
  `raft-cluster-global-2` (2026-11-22). As applied:
  - the shared predicates and laws are stated over `{GF} [AllG GF] [ReceiptGS GF] [InvGS GF]` (not
    `[GooseGlobalGS]`: a fancy update's instance must be the caller's, `notes/raft-cluster-global.md`
    (d)); the node-level predicates, `nodeBoot` and `cluster_alloc(_ns,_traced)` stay under `HeapGS`
    (`bootMarshal` is a WP); the new `cluster_alloc_nb` is the global allocation without a bootstrap
    log;
  - `NodeH.installs` and `nodeInstalledIndex_installs` (`NodeInstalls.lean`): the etcd server pinned
    its node's location in a ghost variable before `StartNode` returns it, and `NodeH` is not
    `Pos.Countable` (it holds the cluster's names, functions among them); it pins the handle's
    install record's name instead;
  - kvdurable's store vocabulary (`rkvInv`, `opSlot`, `readSlot`, `kvCore`, `waitP`, `kvLb`,
    `readAns`, `kdSnapInv`, `KdNames`) moved to `kvdurable/Store.lean`, global, statements unchanged;
  - kvreconf's and kvdurable's sections lose their second `[AllG GF]` (`notes/decisions.md`, "One
    `AllG`"), which made a client's terms differ from raft's global laws.

## 2026-11-21: `kvdurable.getEntry` -- reads only persistent bytes, so a caller holding owned bytes cannot use it

- **Spec.** `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurable/getEntry.lean`, `getEntry.spec`
  (and its copies, RaftNoAx's kvdurablenoax and KvNet's kvnet, `etc/copy-part.py`). No SpecPlan counterpart.
- **Defect.** Too strong a premise: the bytes must be persistent (`b ↦*□ (encEntry e ++ r)`, the rest given
  back persistent). kvnet's `getMsg` (KvNet, issue #22) decodes the entries of a message and then its snapshot
  from the same owned bytes, and `getSnapshot` needs the snapshot's bytes owned; with `getEntry` persisting them,
  a message with both entries and a snapshot could not be decoded (`getMsg` took the premise
  `st.ents = [] ∨ st.snap = none`).
- **Evidence.** `KvNet/Proof/.../kvnet/getMsg.lean` (fork C's report, 2026-11-21). The Go only reads `b`
  (`getUint64`, `getBytes`: subslices), so any fraction suffices; the entry's data, a subslice of `b`, must be
  read-only for `entOwn`, which the proof gets by persisting that subslice alone.
- **Proposed change.** `∀ b (dq : DFrac) e r, EntWf e → {{ … b ↦*{dq} (encEntry e ++ r) }} getEntry b
  {{ l rest; entOwn l e ∗ rest ↦*{dq} r }}` (the data slice persisted inside the proof). The one main-tree caller,
  `openStorage`, passes `dq := DFrac.discard` (its statement unchanged); kvnet's `getMsg` passes its own fraction
  and drops its premise.
- **Decision.** Accepted (the coordinator, issue #22, 2026-11-21).
## 2026-11-21: raft's node API -- no node of an id is restartable after a real crash (`nodeVacant` returns only from `node.Stop`)

- **Spec.** `Spec/go_etcd_io/raft/v3/StartNode.lean`, `RestartNode.lean`, `node__Stop.lean`,
  `RawNode__Ready.lean` (the enter wand); `InvNode.lean`'s `readyEnter` and the new laws
  `nodeVacant_arm`, `nodeCrash`. SpecPlan's raft node specs, likewise.
- **Defect.** Too weak for a crashing client: a process killed at any instruction loses its threads'
  resources, so `nodeVacant` (needed by `RestartNode`) never comes back. kvnet's crash obligation
  (`goose_dist_crash_adequacy`'s wand, given the dead generation's `crashed`) cannot be met.
- **Evidence.** `notes/kvnet-proof-plan.md` gap 1; `notes/raft-crash-law-design.md` (a).
- **Proposed change.**
  - `nodeVacant_arm : nodeVacant ={E}=∗ ∃ x, nodeVacantA ∗ nodeCrashTok` and
    `nodeCrash : crashed -∗ nodeCrashTok ={E}=∗ nodeVacant`.
  - `StartNode`/`RestartNode` take `nodeVacantA γ id x`, and `node.Stop`'s post gives it back (same `x`).
  - `readyEnter` and `Ready`'s enter wand become crash-token updates (`ncfupd E`: the client applies them
    at a step, by `wp_ncfupd`).
  - Clients: kvdurable keeps its `node.Stop` path and drops its `nodeCrashTok`; the etcd server likewise;
    kvnet's boot obligation arms.
- **Decision.** Accepted (the coordinating session, 2026-11-21, design route 1, sections (b1), (f),
  (i)); applied on branch `worktree-agent-aa878c2e224f33d0c`.
- **As applied** (2026-11-21, the implementing session):
  - "Same `x`" needs the client to know the arm the node started from. `StartNode`/`RestartNode` give
    a persistent `nodeArm n γ x` (sealed; `nodeArm_agree`). `node.Stop`'s post is
    `∃ x, nodeVacantA γ id x ∗ nodeArm n γ x`, so its precondition is unchanged.
  - `nodeCrash` also takes `isCluster γ N` and `↑N ⊆ E` (for `↑(raftN) ⊆ E`).
  - `nodeVacant_armD : nodeVacant ={E}=∗ ∃ x, nodeVacantA γ id x` (the token dropped) is for clients
    whose crash is `node.Stop`'s: kv, kvreconf, kvdurable and the server. They keep the vacancy as
    `∃ x, nodeVacantA …` where they kept `nodeVacant` (kvdurable's `Cluster.start`, `Replica.stop`,
    `Replica.crash`; the server's restart image, `rnStopImage`, `rnBootPre`'s restart).
  - `examples/lib/durable`'s `Write.spec`: the update may use `notCrashed` when it opens (handed back
    at once; `wp_atomic_nc` at the extension's step). Strictly more permissive for a client. kvdurable's
    *enter* runs in the write's update, so it needs the token there.
  - The server's `raftNode.stop` post (`Spec/go_etcd_io/etcd/server/v3/etcdserver/raftNode__stop.lean`)
    gives `∃ x, nodeVacantA …` in place of `nodeVacant`.
  - The traced `StartNode.tracedSpec` (`TracedNodeApi.lean`) and the Draft's `StartNode.gatedSpec`
    (`TracedApiDraft.lean`) changed as `StartNode.spec` did.
  - In raft's `with_tla` build (`RaftTla/`, per (f)), the trace logger's contract (`isTraceLogger`) and
    the trace check's `SyncRecorder.TraceEvent.spec` take the update in its crash-token form: the
    token is lent at the commit and handed back.

## 2026-11-20: `cache.wp_Errorf_setArgs` -- reads the maps it formats without owning them

- **Spec.** `Proof/k8s_io/client_go/tools/cache/ErrorfSet.lean`, `wp_Errorf_setArgs` (a lemma over Perennial's
  previous model of `Errorf`; no `SpecPlan` counterpart).
- **Defect.** False of Go: no ownership of the `sets.Set[string]` maps, which `fmt` reads; a concurrent write
  is the runtime's fatal `concurrent map read and map write`.
- **Evidence.** go1.27.3 `fmt/print.go:793-815`, `internal/runtime/maps/map.go:432`;
  `notes/axiom-review/errorf-setargs.md`.
- **Proposed change.** Premise: a fraction of each map's points-to, given back in the post. The one caller
  (`storeIndex.addIndexers`) passes the intersection's.
- **Decision.** Applied (fmtmodel, 2026-11-20; a strengthening of the premise, the caller's obligation discharged).

## 2026-11-20: `fmt.argsOk` (Errorf, Sprintf, Printf) -- `reflect.Value` admitted; slices; a methodless integer under a non-method verb

- **Spec.** `Spec/fmt/Errorf.lean`'s `fmt.argsOk`/`fmt.argOkAt`/`fmt.argOk`, now Perennial's
  (`Perennial/Proof/fmt/Args.lean`, `79517dbdf`), under `fmt.Errorf`, `fmt.ErrorfLeaf`, `fmt.SprintfArgs`,
  `fmt.Printf`; `SpecPlan`'s `fmt` specs use the same vocabulary.
- **Defect.** (1) The `String()` case admitted a `reflect.Value`, which Go unwraps (false: the held value's methods
  run unconstrained). (2) Read-only slices under `%v`/`%s` were admitted, which Perennial's model does not cover.
  (3) The non-method-verb integer case admitted any integer-kind type without `Format`; Perennial's requires an
  `Error() string` or `String() string` (the other such types are `ArgWf` already, or have methods the model
  does not follow).
- **Evidence.** go1.27.3 `fmt/print.go:734` (`case reflect.Value`); `notes/axiom-review/errorf-setargs.md`.
- **Proposed change.** (1) No method `CanInterface` in the `String()` case. (2) The slice calls move to
  `fmt.ErrorfSlice`/`fmt.SprintfSlice` (premise `fmt.argsOkSl`, the old one with slices), axioms. (3) As Perennial's.
  No caller passed a `reflect.Value` or used (3)'s extra types.
- **Decision.** Applied (fmtmodel, 2026-11-20).

## 2026-11-20: `metadata.AppendToOutgoingContext.spec`, `withVersion.spec`, `streamKeyFromCtx.spec`, `context.WithCancelValCtx.spec`, `context.WithTimeoutBackgroundMd.spec`, `grpc.ClientConn.NewStream.spec` -- posts fix a pure function of an allocated context

- **Spec.** The real specs above (`Spec/google_golang_org/grpc/metadata/AppendToOutgoingContext.lean`, ...), and
  the definitions in trusted contracts that use `metadata.outgoingOf` (`grpcAttemptMd`, `grpcInvokerOk`); the
  plan's `outMD` (`SpecPlan/Spec/google_golang_org/grpc/Api.lean:283`).
- **Defect.** Unprovable by any implementation: each post equates `metadata.outgoingOf` (a fixed Lean
  function) of a context the call allocates with caller-chosen metadata; a fresh allocation may be any
  location (etcd-refimpl `README.md`, "Findings").
- **Evidence.** The refimpl finding; `notes/errdesc-ghost-plan.md` §0.
- **Proposed change.** `metadata.outMD ctx md` (the plan's `outMD`, with `Option` metadata: the 2026-11-18
  entry below) in place of `outgoingOf`: each spec takes `∀ md`, `outMD ctx md` in its precondition, and
  states the result's `outMD` at `md` (`mdAdd md k v`, `mdSet md …`, `md`, `none`); `streamKeyFromCtx`
  returns `streamKeyOf md`; `grpcAttemptMd conn om md` over the metadata `om` the attempt contract's
  precondition relates to the context.
- **Decision.** Accepted (the user's soundness fix, task of 2026-11-20); applied on branch
  `prove-errdesc/2026-11-20` (stage 1).

## 2026-11-18: `leaseStep`'s grant -- a server-chosen id is fresh in the history, the plan says only "not live"

- **Spec.** `SpecPlan/Spec/go_etcd_io/etcd/api/v3/Model.lean`, `leaseStep` (`.leaseGrant`: `σ.leases id' = none`);
  the real counterpart `writeGrantG` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/ProposeOn.lean`), read by
  `v3rpc.opGrantT`'s `.leaseGrant` row (frozen `opGrantTN`, `notes/auth-lease-s4-freeze.md`, "Thaw 1").
- **Defect.** Too weak for a user: a client holding a persistent grant update (auth on) cannot rule out a
  re-grant of a revoked id, so a later re-delivered put could re-attach a key to it; the auth-lease driver's
  check 6 (keys of a revoked lease stay deleted) is unprovable.
- **Evidence.** `questions.md` (auth-lease S4, "Item 9, the Cell: BLOCKER", 2026-11-18); Go: `EtcdServer.LeaseGrant`
  draws `r.ID` from `reqIDGen` while it is 0 (`v3_server.go:436`), ids distinct per member prefix (`kvGrantIds`).
- **Proposed change.** Real spec (done, approved): `writeGrantG` gains `∀ g, rqRevGrantId γk.lm rq₀ = some g → ∀ r ≤
  σ.rev, ∀ kv ∈ (σ.at r).kvs, kv.lease ≠ 0 → kv.lease ≠ g`. Plan: `leaseStep`'s chosen-id case (`id = 0`) adds
  `id' ∉ σ.granted` (the plan's own history of granted ids), which implies the real form.
- **Decision.** Real spec: accepted (the user, 2026-11-18, option (A), via etcd-grove-03). Plan change: pending.
## 2026-11-18: `SpecPlan/Spec/google_golang_org/grpc/Api.lean` `ctxInMD_agree.spec` -- unprovable from the definitions, false in the intended model, and used by no spec or proof

- **Spec.** `ctxInMD_agree.spec` (`Api.lean:922-925`: `ctxInMD ctx o ∗ ctxInMD ctx o' ⊢ ⌜o = o'⌝`, and the
  same for `ctxPeerCN`); the real counterpart is the perheap redesign's `metadata.ctxInMD`
  (`notes/perheap-scope.md` §2, not yet in the tree; today `metadata.incomingOf`, a pure opaque function).
- **Defect.** An entailment with a pure conclusion over a per-heap relation (wording corrected after the
  Scope's review 2, (3)). With `ctxInMD` defined over Perennial's `context.ctxValue` (what makes the refuted
  `incomingOf_cancelCtx`/`incomingOf_cancellableContext` provable, `/shared/tmp/perheap/Probe.lean`) it is
  **unprovable from the definitions**: `ctxChain`'s root may be a context of a foreign type with a `Value` WP
  form (`Perennial/Proof/context/CtxValue.lean:79-82`; any chain can reach one: at another key a `valueCtx`
  continues the chain, `:90-94`), and a partial-correctness WP admits every result; the leaves have no
  agreement either. It is **false in the intended model** (in a run with a real transport `MD`, a context whose
  `Value` diverges carries both `none` and `some f`). It is **consistent as a Lean axiom** (interpret the leaf
  as `False`: `some` is never derivable and agreement holds trivially, making grpc's producers vacuous). As an
  opaque with trusted transfer entailments it is consistent only with leaves indexed by the heap's names,
  producers restricted to immutable chains, and an intended model (the review-1 m1 attack otherwise crosses
  worlds).
- **Evidence.** `notes/perheap-scope.md` §5; the incomingof refutations (`notes/axiom-review/incomingof.md`,
  `notes/incomingof-crossworld.md`); reviews 1 and 2 of the perheap Scope (`/shared/tmp/perheap/review-1.md`,
  M1, M2, m1; `/shared/tmp/perheap/review-2.md`, (3)). **Unused:** no `SpecPlan/` spec and no
  `examples/specreq` snippet uses it (its only mentions: the definition, `Api.lean:923`, and
  `notes/specs-only/integration-I3.md:65`). Its two would-be consumers in the real tree are restated with one
  metadata value from one producer (`notes/perheap-scope.md` §3, §4.2, §4.3: `ctxBound` indexed by the token,
  `AuthInfoFromCtx` taking the token, `grpcAccepted` the source of the `md` a spec is about).
- **Proposed change.** Delete `ctxInMD_agree.spec` (both halves) from `SpecPlan/`; keep `ctxInMD_persistent`,
  `rpcCtx_inMD`, `ctxInMD_background`; specs that would use agreement take the metadata (or the token) as a
  parameter.
- **Decision.** Accepted (decided by etcd-grove-03, 2026-11-18, the perheap Scope's Q2): both halves deleted from
  `SpecPlan/` in the perheap step 0 commit.

## 2026-11-18: `SpecPlan/Spec/google_golang_org/grpc/Api.lean` `errView` -- no case for an error wrapping a status error; no message-only view

- **Spec.** `errView` (`Api.lean:266`), `plainErr` (`:256`); real counterparts: `status.FromError.spec`
  (`Spec/google_golang_org/grpc/status/FromError.lean`) and the perheap redesign's `descIs`
  (`notes/perheap-scope.md` §2.2).
- **Defect.** Incomplete, not unsound: grpc v1.84.0's `FromError` (`status/status.go:112-125`) gives an error
  wrapping a status error the wrapped code with message `err.Error()`; `errView` covers status errors, plain
  errors (`Unknown`) and `nil` only. The server's and client's description reasoning (`togRPCError`'s
  fallback, `rpctypes.ErrorDesc`, the handler outcome) needs the message without the code, for wrap errors too
  (mvcc's `fmt.Errorf("…%w", ctx.Err())`).
- **Evidence.** Review 1 of the perheap Scope, m4; `Proof/go_etcd_io/etcd/server/v3/storage/mvcc/InvStore.lean:5632`
  (`rangeKeysErr`), `…/v3rpc/ServerKVOn.lean:961`.
- **Proposed change.** Add `descIs err m` (the message `FromError(err).Message()` returns: `nil` and `""`; an
  error without `GRPCStatus`, wrapping or not, and its stable `Error()`; a status error's message), with the
  value pin (`∀ y : EtcdError, err = mkOk #y → m = y.desc`), and `descIs_of_errView`; `errView` unchanged.
- **Decision.** Pending: with the perheap Scope's Q4 (the user).

## 2026-11-18: k8s `trace.Trace.LogIfLong.spec`/`Step.spec` -- false on a nil receiver

- **Spec.** `Spec/k8s_io/utils/trace/Trace__LogIfLong.lean` (the axiom `trace.Trace.LogIfLong.wp_proof`),
  `Trace__Step.lean` (a named hypothesis of the reflector's `list`), and `New.lean` (the axiom
  `trace.New.wp_proof`). No SpecPlan counterpart.
- **Defect.** Unprovable: both took any `t : Loc` with precondition `True`, but both lock `t.lock`
  first (k8s.io/utils `trace/trace.go:161-169,207-212`), so a nil `t` panics (nil dereference).
- **Evidence.** The Go code; a closed program `(*trace.Trace)(nil).LogIfLong(0)` panics, yet the axiom
  gave it a triple.
- **Proposed change.** A pure opaque fact `trace.fromNew t` (`Proof/k8s_io/utils/trace/Defs.lean`),
  which `New`'s post gives and `Step`/`LogIfLong` require. Opaque, not `t ≠ null`, so that a reference
  model of `New` returning `nil` still meets the spec, reading it as `True`. The callers
  (`RealFIFO.Pop`, `Reflector.list`, `processorListener.run`) get it from their `New` call. The same two
  axioms, restated.
- **Decision.** Accepted (the coordinator's list, 2026-11-18); applied on branch `axthm/2026-11-18`.

## 2026-11-18: grpc health `SetServingStatus.spec`/`ServingStatus.String.spec` -- a `val` argument admits a panic value

- **Spec.** `Spec/google_golang_org/grpc/health/Server__SetServingStatus.lean`,
  `Spec/google_golang_org/grpc/health/grpc_health_v1/HealthCheckResponse_ServingStatus__String.lean`
  (both axioms). No SpecPlan counterpart.
- **Defect.** Unsound: the status was any `val`, a panic value included; applying a function to it
  unwinds to that panic, so the post can never hold, and `String`'s axiom (precondition `True`) gives a
  triple no execution meets.
- **Evidence.** The semantics of application to a panic value (Perennial's panic propagation).
- **Proposed change.** The status a `w32` (`HealthCheckResponse_ServingStatus` is `int32`), passed as
  `#status`/`#st`. The one caller (`healthNotifier.startServe`) passes the translated constant
  `HealthCheckResponse_SERVING`.
- **Decision.** Accepted (the coordinator's list, 2026-11-18); applied on branch `axthm/2026-11-18`.

## 2026-11-18: `prometheus.observerSpec` -- `Observe`'s argument any `val`

- **Spec.** `Spec/github_com/prometheus/client_golang/prometheus/HistogramVec__WithLabelValues.lean`
  (`prometheus.observerSpec`, the post of the axiom `HistogramVec.WithLabelValues.wp_proof`).
- **Defect.** Unsound, as the health specs above: `∀ f : val` includes a panic value.
- **Evidence.** As above; `gaugeSpec` and the mvcc/backend/WAL observers already take `x : w64`.
- **Proposed change.** `∀ f : w64`, `(Val #f)`. The five users (`EtcdServer.Range`/`Txn`/
  `processInternalRaftRequestOnce`, rafthttp's `snapshotSender.send`/`snapshotHandler.ServeHTTP`) pass
  `time.Duration.Seconds`'s `w64`.
- **Decision.** Accepted (the coordinator's list, 2026-11-18); applied on branch `axthm/2026-11-18`.

## 2026-11-15: real bbolt's `flock.spec`, `DB.close.spec_owned` and writer invariant -- the descriptor's `flock` lock unaccounted

- **Spec.** `Proof/go_etcd_io/bbolt/Open/Flock.lean` (`flock.spec`, internal), `Open/Close.lean`
  (`DB.close.spec_owned`, internal), `Inv/Locks.lean` (`wdbCoreG`: the descriptor and the `path` field), the
  internal specs naming the database's descriptor (`fdatasync.spec`, `Tx.write` ext, the remaps', `Open/Core`'s,
  `DB.loadFreelist`'s pre).
- **Defect.** Unprovable after the merge of `wal-int` `7fe119fb19` (the file-lock semantics, pending the
  user's review): `OsFd` gains lock fields (`ofd`, `flk`), `syscall.Flock` changes them (`lockOut`) and
  `os.File.Close.spec` takes the description's lock tokens (`lockToks`). bbolt's `flock` kept the
  descriptor unchanged, and `close` had no token for `funlock`/`Close`.
- **Evidence.** The full build: `Proof/go_etcd_io/bbolt/Inv/Locks.lean:293` (`⟨p.ino, true, true⟩`: 3 of
  `OsFd.mk`'s 5 fields), then `Open/Flock.lean`, `Open/Close.lean`, `Open.lean` against the new
  `syscall.Flock.spec`/`os.File.Close.spec`.
- **Change (made).** As minibolt's on `wal-int`: `flock.spec` takes `d.flk = none` and returns, on `nil`, the
  descriptor `d.setLk .flock (some ex)` with its `lockTok`, on an error `d` unchanged; `close.spec_owned`'s file
  takes `lockToks fd d` (its `funlock` passes the `flock` token through, `File.Close` gets both); the database's
  descriptor after `Open`'s `flock` is `dbFd i` (`⟨i, true, true, none, some true⟩`); its token rides with the
  `path` field in the writer's core (`dbPathLk db p fd`, `wdbCoreG`), which only `Open`, `close`, `loadFreelist`
  and the remaps touch. No exported statement changed (`Open.spec`, `DB.Close.spec` unchanged).
- **Decision.** Repair made on `wal-lean` (session 3, `notes/wal-units/lean-integration.md`), following the
  coordinator's instruction ("rebuild bbolt and repair as minibolt was"); stands or falls with the lock
  semantics' review.

## 2026-11-15: the etcd examples' closed theorems -- over no file extension, but `fileutil`'s initializer needs one

- **Spec.** The closed theorems of the etcd and Kubernetes examples (`Proof/.../examples/{etcd,k8s}/*/Adequacy.lean`
  and their restatements in `Results.lean`): `etcd_{compacted,putget,putget3,restart1,lease,leasegrant,leaseexpiry,
  leasecatchup,compactwatch,txnlin,partition}_adequate` (`_safe`), `etcd_partition_watch_adequate`, `k8s_compactor{,
  _partition}_adequate`, `k8s_etcd3{,_cluster,_partition}_adequate`, and, through the same cause, `etcd_{auth,auth3,
  watch,cache}_adequate`.
- **Defect.** Unprovable on `wal-lean`: they ran over `TrivialExt.lean`'s `[idIssueExt]`, but `fileutil` (now
  translated with bodies) has a package `init` (lock_linux.go) that probes `F_OFD_GETLK` through
  `syscall.FcntlFlock`, whose model is over the Linux file extension, and the server imports `fileutil`, so every
  etcd program's `wp_initialize'` takes `[ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]`.
- **Evidence.** The full build of `wal-lean` (session 2 of `notes/wal-units/lean-integration.md`): 13 adequacy
  modules fail with `failed to synthesize HasExt Fs.fsExt` (the other four import `putget`'s or `partition`'s and
  were not attempted).
- **Change (made).** Each theorem runs over `etcdFsExts` = `[idIssueExt, fsExt]` (`lib/etcdstart/FsExts.lean`; the
  file extension's own semantics `fs_semantics`, no premise on the environment; its ghost state `fs_interp`) and
  takes one new premise, `Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world)` (the file extension's initial state: no
  process state, nothing logged, every file named and on disk, the roots well formed), as the osfs programs'
  results do. The conclusion is unchanged. The proofs use none of the extension's start resources (the probe takes
  no extension step, `syscall.FcntlFlock.wp_getlk`).
- **Decision.** The user's, option (A) (2026-11-15; the alternatives were a trust-boundary fact for `fileutil`'s
  initializer, or a names-only second translation of `fileutil` for the server). Made on `wal-lean` (session 3 of
  the log, which lists the restated theorems for the user's review).
## 2026-11-16: the client watch's element (`watchStateRespOk`, `client_Watch_field`) -- too weak for a user: a watch response's close error has no known dynamic type

- **Spec.** `Proof/go_etcd_io/etcd/client/v3/WatchStateDefs.lean`, `watchStateRespOk` (and the server-side
  `rawRespOk`), the element of every client `Watch` spec (`Spec/go_etcd_io/etcd/client/v3/
  Client__Watch*.lean`, `client_Watch_field`); the plan's client watch (`SpecPlan/Spec/go_etcd_io/etcd/
  client/v3/`) states no close error at all.
- **Defect.** Too weak: the error arm gives only `statusErrOk v.closeErr'`. k8s's `watchChan.startWatching`
  hands `wres.Err()` to `sendError`/`isCancelError`, which need the error's dynamic type (one of
  `clientErrTys`, a leaf) and, for an `*errors.errorString`, that it is a pointer (`kErrOk`'s `==` with
  `context.Canceled`). The placeholder `clientWatchCE.spec` asked `clientErr` and `errCellOk`; `errCellOk`
  is FALSE: a refused create's close error is `rpctypes.Error(errors.New(resp.CancelReason))`, an
  `*errors.errorString` holding the server's message (permission denied, `"mvcc: watcher range is empty"`).
- **Evidence.** `watchChan__startWatching.lean`'s pending hypothesis (7f-5a-P step 5); Go:
  `nonissues/etcd-watch-refused-create-err-plain.md` (its test); the stream errors' shape:
  `examples/k8s/etcd3/streamerr_test.go` (T-CE).
- **Proposed change.** New client vocabulary `errPtrOk e` (an `*errors.errorString` error is a pointer) and
  `closeErrOk e := statusErrOk e ∗ ⌜(e ≠ nil → clientErr e) ∧ errPtrOk e⌝`; the element's error arm, `run`'s
  published close error (`closeErrPub`), the stream's `closeErr` field and the receive errors (`errP`) carry
  `closeErrOk` in place of `statusErrOk`. Needs the trusted `cliStreamErr` to give `errCellOk` (T-CE).
  startWatching then uses the client's `Watch` spec instead of `clientWatchCE.spec`.
- **Decision.** Accepted with `errPtrOk`, not `errCellOk` (etcd-grove-81, 2026-11-16); T-CE approved (same).

## 2026-11-15: `fmt.ErrorfPlain.spec` (trust boundary) -- false for a flagged `w` verb (`%+w`, `%-5w`): the premise `¬ List.IsInfix "%w" format` lets them through

- **Spec.** `Spec/fmt/ErrorfPlain.lean`, `fmt.ErrorfPlain.spec`; its axiom `fmt.ErrorfPlain.wp_proof`
  (`Proof/fmt/ErrorfPlain.lean`). No SpecPlan counterpart.
- **Defect.** False of Go: a `w` directive with flags, width or precision has no `%w` infix, parses as
  a `w` directive (`fmt.fmtDirectives`), which `fmt.argsOk fmt.errorfVerbs` admits, and Go's
  `doPrintf` wraps at every `w` verb (`fmt/print.go:1051-1052,1146-1147`, go1.27.3): `Errorf` returns a
  `*fmt.wrapError`, not the leaf `*errors.errorString` the post claims. Latent: the two callers
  (`rafthttp.checkPostResponse`, `streamReader.dial`) use literal formats with no `w` verb.
- **Evidence.** `notes/axiom-review/errorfplain.md` (k8s 7f-5a-P, 2026-11-15); the counterexample
  `examples/axiomcx/errorfplain` (`errors.Is(fmt.Errorf("%+w", io.EOF), io.EOF)` is true).
- **Proposed change.** The premise becomes E3's (`notes/k8s-7f5a-draft.md` §11.3): `∃ ds,
  fmt.fmtDirectives format = some ds ∧ ∀ d ∈ ds, d.verb ≠ W8 119`; the post unchanged. Evidence of the
  new premise: `examples/premisefix/errorfwrap` (`TestNoWDirectiveGivesErrorString`, 200000 random
  formats). The callers discharge it by `refine ⟨_, rfl, ?_⟩; decide`.
- **Decision.** Accepted (etcd-grove-81, 2026-11-15; branch `errorfplain-fix`).

## 2026-11-15: `applyAll.spec` (proof sketch) -- the merge's guard is no longer only `m.term = raftTerm`, `index ≤ appliedi`: the verified fork defers a merge inside the replay window

- **Spec.** `SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__applyAll.lean`, `applyAll.spec`
  (its proof sketch and "Changes" paragraph; the statement is unchanged); the real spec
  `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__applyAll.lean`, `applyAll.specBatch`.
- **Defect.** The sketch describes the merge's select at the pin as "the code's" guard (`m.term = raftTerm`,
  `index ≤ appliedi`, then `createMergedSnapshotMessage`/`sendMergedSnap`). The verified Go code changed
  (restart3 A1, route (A) via A-g, approved by the user 2026-11-15): the goose fork's commit `6e8f0c004`
  adds a third test, `ep.appliedi < s.consistIndex.ConsistentIndex()` (inside the replay window) under
  which the merge is replaced by `s.ReportSnapshot(m.GetTo(), raft.SnapshotFailure)`, and reports a
  message dropped by the term or index guard failed too (D-A0-6). The sketch's callees miss
  `consistentIndex.ConsistentIndex`, `raftpb.Message.GetTo` and `ReportSnapshot`.
- **Evidence.** `notes/restart3-a0-draft.md` §3 and §8 (the change, the Go runs: the guard fires and the run
  stays correct; unreported drops wedge a follower); the real proof `applyAll.wp_proofBatch`
  (`Proof/.../EtcdServer__applyAll.lean`, `wp_ci_get` for the guard's read, `ReportSnapshot` on each drop).
  The plan's statement already had no window premise, so it needs no change; the real spec's window row
  (`winNoMergedSendR … ∗ T ∗ srvSnapBagN`) is deleted, converging toward the plan.
- **Proposed change.** The sketch's merge paragraph and "Changes" paragraph name the window test, the
  `ReportSnapshot` on a deferred or dropped `MsgSnap`, and the three callees. Statement unchanged.
- **Decision.** Accepted (decided by etcd-grove-81 with the A-g route, 2026-11-15; text only; the restart3 A1
  commit that applies it).

## 2026-11-14: `leaseCheckFrom` (the lease checks' and lease methods' posts) -- admits the empty user unbound

- **Spec.** `Proof/go_etcd_io/etcd/server/v3/etcdserver/LeaseCheck.lean`, `leaseCheckFrom` (the lease-keys
  plan's Part B vocabulary, frozen 2026-10-31), in the posts of `EtcdServer.checkLease{Renew,Leases,TimeToLive}.spec`
  and `EtcdServer.Lease{Leases,Renew,TimeToLive}.spec`; its stream form `v3rpc.leaseCheckT`
  (`api/v3rpc/InvLeaseKeepAlive.lean`, through `infoBoundTM`), in the keep-alive stream's `kaDn`. The spec plan's
  `SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__checkLeaseRenew.lean` (and the other two) state
  nothing of the principal on success: no plan change.
- **Defect.** Too weak. With auth on, the principal is named through `infoBoundM` (`ReqOn.lean`), whose first
  disjunct admits `info.Username' = ""` unbound to the context; for an absent or keyless lease, where the keys'
  verdict `K info` holds trivially, a proof may pick the empty user, so the post does not say "authenticated".
- **Evidence.** The code refuses it: `checkLeaseRenew`, `checkLeaseTimeToLive`, `checkLeaseLeases` return
  `auth.ErrUserEmpty` for a `nil` auth info (`v3_server.go:585, 617, 764` at the pin `2eaeb872bc`); the Scope's
  E2 (`notes/auth-lease-scope/zz_authlease_rows_test.go`) shows it on every lease method, keyless leases included.
  The three check proofs already establish the stronger disjunct (`infoBoundM_of_ctxBound`'s last step,
  `principalBound_of_ctxBoundOrTLS`).
- **Proposed change.** `leaseCheckFrom`'s principal: `□ (⌜E.authOn = true⌝ → principalBound s E.authMode ctx
  (some info))` in place of `infoBoundM E.authOn s E ctx info`; `leaseCheckT`'s: `□ (⌜E.authOn = true⌝ →
  principalBoundT s E.authMode tok info)` (new, `principalBound` over the token) in place of `infoBoundTM`
  (deleted). The TLS fallback (`srvTLSId`) stays admitted: its common name may be empty (E8). No other
  statement text changes; the proofs of the three checks, `leaseCheckFrom_mono`, `leaseCheckFrom_ctx` and
  `leaseCheckT_of_from` are repaired.
- **Decision.** Accepted (Q3 and the CP0 decision, etcd-grove-81, 2026-11-14; branch `auth-lease`, S1).

## 2026-11-14: the mode-`on` KV model (`kvEntryOn`) -- a refused revocation would be applied once the model has leases

- **Spec.** `Proof/go_etcd_io/etcd/server/v3/etcdserver/KVAuthModel.lean`, `kvEntryOn`'s refusal guard
  `apply.isKVKind (apply.dispatchKind rq) = true ∧ ¬ kvGranted s.1 rq`; the auth-lease Scope's Draft
  (`notes/auth-lease-scope.md` §2.3), which replaces `kvGranted` by `kvGrantedL` with a `.leaseRevoke` case.
- **Defect.** Wrong once the auth-on model admits revocations (S3): `isKVKind` excludes `.leaseRevoke`, so the
  Draft's revocation case of `leaseGrantedM` is never consulted and a revocation the auth layer refuses
  (`authApplierV3.LeaseRevoke`'s `checkLeasePuts`, `apply/auth.go:191-196`) would delete the lease's keys in
  the model. Today harmless (the mode-`on` log has no lease request, `plainEntryOn`).
- **Evidence.** The S0 probe (`Scratch/AuthLeaseProbeModel.lean` of the `auth-lease` worktree); `apply.authChecks`
  (`apply/Chain.lean:153`) includes `.leaseRevoke`, `isKVKind` (`apply/InvRequest.lean:299`) does not.
- **Proposed change.** The guard over `authKVKind k := isKVKind k || k == .leaseRevoke`, in S2's Draft of the
  triple-state model (`kvEntryOnL`).
- **Decision.** Accepted (CP0 item 3, etcd-grove-81, 2026-11-14); applied in S2's Draft.

## 2026-11-14: `Http` headers -- Go rewrites header values, adds request headers, decompresses gzip

- **Spec.** `SpecPlan/Spec/net/http/Api.lean`: `hdrView` (the client's view of committed response
  headers), `srvReq r R rd` (the handler's view of the request's headers), the response writer's
  `Flush`; the real boundary's `srvView`, `reqAt`, `hdrsReady`, `Flush_spec` (`Proof/net/http/`).
- **Defect.** Unsound: Go's server turns CR/LF in a response header value into spaces, its client
  trims values and drops non-token keys, and decompresses a body whose handler set
  `Content-Encoding: gzip`; the handler sees `Accept-Encoding`, `User-Agent`, `Content-Length` the
  client never set, and trimmed values; `Flush` on an uncommitted writer commits `200`.
- **Evidence.** The independent review of `http-boundary-fix` (etcd-grove-81, 2026-11-14);
  `examples/premisefix/{httpgzip,httphdr,httpreqhdr}`.
- **Proposed change.** As the real boundary on `http-boundary-fix`: committed response headers
  `respHdrsOk` (token keys, `hdrValOk` values, none of `respNoKeys`); the handler's request headers
  `reqHdrView R.hdr hs` (trimmed, but at `reqTpKeys`); `Flush` of a committed writer.
- **Decision.** Pending (trust-boundary specs of the plan).

## 2026-11-14: `Http.roundTripperOk` -- a response's status may be the server's own, not a handler's

- **Spec.** `SpecPlan/Spec/net/http/Api.lean`, `roundTripperOk` (and the header's "The response's
  status and headers are the handler's"), `reserve.spec`; the real spec `http.roundTripperOk`,
  `http.reserve` (`Proof/net/http/`).
- **Defect.** Unsound: `RoundTrip`'s post gives `respPre P R τ st hs` of a status that may be one
  Go's server answered with itself, running no handler (`400`, `417`, `431`, `501`, `505`), which no
  premise puts in `P.resp`. (The plan's tickets already follow `onceOnly`, the real boundary's other
  finding of the same review.)
- **Evidence.** The network fault review (etcd-grove-81, 2026-11-14);
  `examples/premisefix/httpsrvstatus`.
- **Proposed change.** As the real boundary on `http-boundary-fix`: `reserve` asks of the protocol
  family that each member admits those statuses at any headers/bytes (`Proto.srvOk`, with
  `srvStatuses`), or the post splits handler and server answers.
- **Decision.** Pending (a trust-boundary spec of the plan; the real one fixed on
  `http-boundary-fix`, awaiting review).

## 2026-11-12: `Bucket.node.spec`, `Cursor.node.spec` (internal) -- no panic promised on a deleted handle

- **Spec.** `SpecPlan/Spec/go_etcd_io/bbolt/Bucket__node.lean`, `SpecPlan/Spec/go_etcd_io/bbolt/Cursor__node.lean`
  (internal); no real spec.
- **Defect.** Unsound: `Bucket.node` begins with `common.Assert(b.nodes != nil, ...)`
  (`bucket.go:867`), and `DeleteBucket` sets `child.nodes = nil` on the handle it deletes (`:321`).
  A deleted handle keeps its persistent `bktH` (and its cursors their `boltCur`), so the pre
  `wtxCore ∗ bktH b p` holds where Go panics; `Cursor.node` calls `c.bucket.node(...)` when the
  stack has no leaf node, with its currency `C.bkts b = some p` only as a hypothesis of its post.
- **Evidence.** The 2026-11-12 review of the bucket-handle change (`9fb353a5d1`), finding 1. No
  public triple is affected: each supplies `bktUse`, from which `wtxCore_bktOwn` gives the currency.
- **Proposed change.** `⌜C.bkts b = some p⌝` a premise of both (the cache holds the handle, so it
  is not a deleted one: `DeleteBucket` drops it from `bkts` before clearing its `nodes`); both posts
  keep `C'.bkts = C.bkts` (materializing nodes touches no bucket cache), so a caller's later calls
  keep it. Callers: `Put`, `Delete`, `CreateBucket*`, `Cursor.Delete`, `DeleteBucket` (its `seek`
  on the parent), `SetSequence`/`NextSequence` get it from their `bktUse` by `wtxCore_bktOwn`;
  `node.childAt` from a cached node's bucket; `spill`/`rebalance` walk the cached handles
  (`b.buckets`, `bucket.go:860`).
- **Decision.** Accepted by the coordinator, 2026-11-12. Applied in `c1297a6c6d`.

## 2026-11-12: bbolt's bucket handles -- a generation counter in the view is unobservable, redundant state

- **Spec.** `SpecPlan/Spec/go_etcd_io/bbolt/Model.lean` (`TxView.gen`, `TxView.gens`, `TxView.dropBkt`), `SpecPlan/Spec/go_etcd_io/bbolt/Api.lean`
  (`bktH tx γ b p gs`, `boltCur … gs …`, `bktH_live`), and every triple taking a handle (`Tx.Bucket`,
  `Tx.CreateBucket(IfNotExists)`, `Tx.DeleteBucket`, `Tx.Cursor`, `Tx.ForEach`, `Bucket.*`,
  `Cursor.*`). Real spec: `Spec/go_etcd_io/bbolt/Api.lean` (`boltBkt tx b n g`, the same counter).
- **Defect.** A handle is valid while the per-path counters `T.gens p` equal those it was made at;
  `DeleteBucket` bumps them. No operation lets the client observe the counter: it is state in the
  client's view that exists only to invalidate stale handles, which ownership already does (using
  a bucket takes its token, deleting it consumes the token). The user, 2026-11-12: "it was
  unobservable state. It introduced a redundancy in the specs which we found was not necessary by
  instead using ownership."
- **Evidence.** What the counter excludes is real (`nonissues/bbolt-deleted-bucket-handle.md`: a
  handle used after delete and re-creation panics in `Put`), and Go has a field that says which
  handle is current: in a write transaction `Tx.Bucket`/`Bucket.Bucket` return the parent's cached
  `*Bucket` (`bucket.go:89-110`), `DeleteBucket` removes the cache entry (`bucket.go:318`),
  `CreateBucket` returns a newly allocated one (`bucket.go`, `return b.Bucket(newKey)`;
  `newBucket`, `:116`). A read transaction has no cache (`bucket.go:50`) and cannot delete.
- **Proposed change.** Write transactions: ownership of buckets, `bktOwn tx γ p o q` (fractional;
  `o : Option Loc` the parent's cache entry for `p`), the only handle predicate of a writer.
  `Begin(true)` gives `bktOwn tx γ p none 1` for every bucket path of the data; a lookup turns `o`
  into `some b` (fraction 1 to fill the cache), `CreateBucket` gives `bktOwn … (some b') 1`,
  `DeleteBucket` consumes the full tokens of the deleted bucket and every bucket below it. Read
  transactions: a persistent `bktH tx γ b p` without generations. One handle premise by cases
  (`bktUse`), so each function keeps one triple. `TxView.gen`/`gens` removed; `bktH_live` restated
  over `bktUse`. Moves no spec above bbolt (none names a handle); the real proved bbolt converges
  to it later.
- **Decision.** Accepted by the user, 2026-11-12 ("I want the ownership version"); read
  transactions keep a persistent handle (the coordinator's proposal: no Go operation can
  invalidate one, and etcd's shared read transaction caches handles across goroutines,
  `read_tx.go:49, 97-104`). Applied in `9fb353a5d1` (with the departures recorded there: `Tx`,
  `Writable`, `Cursor` and `openBucket` take only the persistent `bktH`, which they need alone and
  `bktOwn_bktH` gives from a token; the root's handle, in both kinds, is the persistent `bktH`, which
  `Tx.Cursor` returns; every cursor move, `Next`/`Prev`/`Delete` included, takes the handle premise,
  since without generations a deleted and re-created bucket can leave the view as it was; the
  lookup token is `bktTok`; the data's bucket paths `Ent.bktPaths`, `Ent.bktsUnder`).

## 2026-11-12: `Tx.DeleteBucket.spec`, `Bucket.DeleteBucket.spec` -- the empty name's error arm is false after the first leaf is emptied

- **Spec.** `SpecPlan/Spec/go_etcd_io/bbolt/Tx__DeleteBucket.lean`, `SpecPlan/Spec/go_etcd_io/bbolt/Bucket__DeleteBucket.lean`; real spec
  `Spec/go_etcd_io/bbolt/Tx__DeleteBucket.lean` (D-M: either error, true).
- **Defect.** Unsound: `ErrIncompatibleValue` only when `kb = [] ∧ T.ents p = []`, else
  `ErrBucketNotFound`.
- **Evidence.** `c.seek("")` descends to the first leaf; a leaf node emptied by the transaction's
  deletes gives a nil key, `bytes.Equal([]byte{}, nil)`, flags 0: `ErrIncompatibleValue`
  (`bucket.go:296-305`) with buckets left. Test:
  `nonissues/bbolt-deletebucket-empty-name/emptied_leaf_test.go` (2000 buckets, first 50 deleted:
  `incompatible value`).
- **Proposed change.** For `kb = []`: either error, the transaction unchanged (the frozen spec's
  arm). No caller passes the empty name.
- **Decision.** Accepted (coordinator, 2026-11-12; a sound repair to the real spec's form).
  Applied in `9fb353a5d1` (the `kb = []` arm before the lookup: either error, the transaction
  unchanged).

## 2026-11-12: `Model.lean` -- no laws over the data model

- **Spec.** `SpecPlan/Spec/go_etcd_io/bbolt/Model.lean` (`Ent.setKey`, `modAt`, `atPath`, `curEnts`, `bktAt`).
- **Defect.** Too weak for users: nothing states lookup after a put or delete, the cursor order
  after a put, or what `modAt` leaves at other paths; each client (the backend's range and
  compaction proofs) would re-derive them.
- **Evidence.** The 2026-11-12 strength review (etcd's server path); `examples/specreq/bbolt/
  backend.go`'s range-after-put in `ReqBackendBatch`.
- **Proposed change.** Pure laws as `def … .spec : Prop` in `Model.lean`: `atPath` after `modAt`
  (same path, other paths), `setKey` then lookup, `curEnts` of `setKey` (sorted insertion/removal),
  `wf` preserved by `setKey`/`modAt` under the entry bounds.
- **Decision.** Accepted (coordinator, 2026-11-12; adds laws, changes no triple). Applied in
  `b899a66c70` (`Ent.atPath_modAt`, `atPath_modAt_other`, `lookup_setKey`, `atPath_child_setKey`,
  `curEnts_put`, `curEnts_del`, `wf_setKey`, `wf_delKey`, `wf_modAt`, `bktPaths_mem`,
  `bktsUnder_mem`). The review of 2026-11-12 (finding 3): how `bktPaths` changes, so the backend's
  lock invariant can rebuild its token list (`Ent.bktPaths_create`, `bktPaths_dropBkt` up to
  `List.Perm`, `bktPaths_setVal`, `bktPaths_setSeq` equal), applied in `e6c84e32fd`.

## 2026-11-12: `DB.Path.spec` (and the close right) -- `Path` needs the exclusive close right, which non-blocking defrag does not hold

- **Spec.** `SpecPlan/Spec/go_etcd_io/bbolt/DB__Path.lean`, `SpecPlan/Spec/go_etcd_io/bbolt/Api.lean` (`boltOpened db γ`, exclusive), `DB.Sync.spec`,
  `DB.Close.spec`.
- **Defect.** Too strong a premise: etcd's defrag calls `b.db.Path()` without the backend's lock
  (`backend.go:515, 712`), so it cannot hold the exclusive right. A share is enough: `Path` reads
  `db.path`, which only `close()` writes (`db.go:832` at the pin, `db.path = ""`).
- **Evidence.** The 2026-11-12 completeness review (etcd's server).
- **Proposed change.** `boltOpened db γ q` fractional; `Path` (and `Sync`, if its Go body only
  races with `close()`) take a share and return it; `Close` takes the whole. Exclusivity at 1.
- **Decision.** Accepted (coordinator, 2026-11-12; weakens a premise, no new ghost state).
  Applied in `9fb353a5d1` (`boltOpened db γ q`, used at `1`) and `6eae035a46` (`Path` and `Sync`
  take a share: `Sync`'s body, `Logger`, `db.path` and `fdatasync`'s `db.file`, races only with
  `close()`, `db.go:829, 832` at the pin).

## 2026-11-12: `Open.spec` -- written against bbolt `743299d`, the pin is `ea4cab5`

- **Spec.** `SpecPlan/Spec/go_etcd_io/bbolt/Open.lean`; the API's header (`743299d`).
- **Defect.** Out of date: at the pin a writable `Open` with `NoSync` off (`!db.NoSync ||
  IgnoreNoSync`) `fdatasync`s the file before any commit and, on its error, closes under the locks
  and returns it (`db.go:320-334`; `issues/bbolt-open-unsynced-meta-kill-then-power-loss.md`,
  blocks-proof: yes). The spec has neither the sync's effect on the durable state nor the error path.
- **Evidence.** `diff` of the two module versions: the only non-test change (`db.go`).
- **Proposed change.** `Open.spec` at `ea4cab5`: with `NoSync` off, the state `Open` read is durable
  (the post's state records it, as a successful sync does), the sync's error is an `Open` error
  (`boltClosed` back); the API header names the pin.
- **Decision.** Accepted (coordinator, 2026-11-12; follows the pinned code). Applied in
  `ac1de7621a`: with `NoSync` off (`IgnoreNoSync` is false on Linux) `Open` takes a sync update
  (`σ.sync ok`, as `DB.Sync.spec`'s), the success post gives `Ss true`, an error `Ss` of the outcome
  or the update back. With `NoFreelistSync` off too, the freelist commit's updates are nested in
  the sync update's `COMM` (a holder of one `boltState` builds both; the review's finding 2):
  applied in `dc5d1f1826`.

## 2026-11-12: `Open.spec`, `DB.Close.spec` -- their errors cannot be excluded, and the server panics on both

- **Spec.** `SpecPlan/Spec/go_etcd_io/bbolt/Open.lean`, `SpecPlan/Spec/go_etcd_io/bbolt/DB__Close.lean`; the backend's `New`/`Close` specs.
- **Defect.** Too weak for the server: over OsFs every system call may fail; `newBackend` panics
  on an `Open` error (`backend.go:234-236`), `applySnapshot` on the old backend's `Close` error
  (`server.go:1149-1151`). The backend's opaque `dbOpenOk` is tied to nothing, so a proof closes
  only if it is `False`.
- **Evidence.** The 2026-11-12 completeness review; `req/go_etcd_io_bbolt.md` item 1.
- **Proposed change.** As the main tree (the user's decision for mvccrand, 2026-11-08): named
  environment premises `dbOpenOk`/`dbCloseOk`, with `Open`'s/`Close`'s error giving their negation
  (a trust-boundary layer over the proved specs); or an environment resource the call consumes.
- **Decision.** Pending: the user's (a trust-boundary statement).

## 2026-11-12: bbolt's file vocabulary -- no law for a file renamed over while open (snapshot install)

- **Spec.** `SpecPlan/Spec/go_etcd_io/bbolt/Api.lean` (`fileHolds`, `boltFile`, `boltRelease`, `boltCrash`).
- **Defect.** Incomplete: the snapshot install renames the new file onto the open database's path
  (`storage/backend.go:68`) and closes the old database later; bbolt names a file by its path, so
  its release and crash laws would hand out the path's resources, now the new file's.
- **Evidence.** The 2026-11-12 completeness review; recorded only as the generic missing OsFs
  `rename` (C42/C43).
- **Proposed change.** Name a database by its OsFs file, not its path, or a rename law moving the
  path's name to the new file while the old file's resources stay with `boltFile γ`. With OsFs's
  `rename`.
- **Decision.** Pending (needs OsFs's `rename`; the file extension's owner).

## 2026-11-12: `backend.Defrag.spec` -- no reader slot, yet defrag opens read transactions

- **Spec.** `SpecPlan/Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__Defrag.lean` (or its
  file).
- **Defect.** Unprovable: defrag's read transactions (`backend.go:597, 812, 883, 963`) each need a
  `threadTok` for `Begin(false)`; the spec takes none (`Hash` takes one).
- **Evidence.** The 2026-11-12 completeness review.
- **Proposed change.** `Defrag.spec` takes a `threadTok` and gives it back, as `Hash`.
- **Decision.** Pending (a new premise on a spec with clients: the user's).

## 2026-11-12: the backend's realization -- bbolt's state in `mu`, though commits and non-blocking defrag run without it

- **Spec.** `SpecPlan/Spec/go_etcd_io/etcd/server/v3/storage/backend/Api.lean:44` (realization
  note), `batchTx__commit.lean:4-5`, `Durable.lean:36-39`.
- **Defect.** The intended realization keeps `boltState` in the `mu` lock; batch commits and
  non-blocking defrag's `Begin` run without `mu`, and the crash law wants a share in a
  crash-surviving invariant, so the commit's update cannot be built as sketched.
- **Evidence.** The 2026-11-12 reviews (both).
- **Proposed change.** The realization keeps `boltState` in an invariant (the bank's pattern),
  the commit's update opening it.
- **Decision.** Pending (the backend's; no statement changes).

## 2026-11-13: `wal.WAL.ReadAll.spec` -- the success post `walReadCut … = some σ` is false of a Save-then-SaveSnapshot history

- **Spec.** `Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__ReadAll.lean` (the W4a axiom; its proved
  replacement over `fsExt`, `notes/wal-fsext-plan.md`).
- **Defect.** Unprovable: Go's `ReadAll` folds from `Open`'s start snapshot `s` (the entries' base fixed
  at `s.Index`), while `walReadCut`'s fold moves its base only at snapshot records it has read.
- **Evidence.** `readAllFold_zero_dev` (branch `wal-fold`, `Proof/go_etcd_io/etcd/server/v3/storage/WalEncFold.lean`,
  proved): the history `Save({Term 1, Commit 5}, [entry 6 term 1])`, `SaveSnapshot({Index 5, Term 1})`;
  `Open` starts at `(5,1)`; Go's `ReadAll` succeeds with `[e6]`, `walRead I = none`. Raft does not
  produce this order (etcd saves the snapshot record before entries above it), but `Save`'s spec allows it.
- **Proposed change.** `ReadAll`'s success post states Go's fold, `walReadAt I k s` (the fold from the
  base `s`), and a lemma gives `walReadAt I k s = walReadCut I k` under a history condition the server's
  and the tester's histories meet (the condition to be found: e.g. every entry above a snapshot record's
  index is saved after it), so the clients keep `walReadCut`.
- **Decision.** Adopted (the coordinator, the user away; an intermediate spec, no client-visible ghost
  state added); the condition and the lemma on branch `wal-fold`.

## 2026-11-13: the WAL decoder's `isEofOk` -- `errors.Is` asked of `nil`, and `io.EOF` must be neither `io.ErrUnexpectedEOF` nor an `IoE` error

- **Spec.** `LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/DecDefs.lean`, `isEofOk` (in `decEnv`, the
  precondition of `decoder.Decode`/`decodeRecord`; W3a of `notes/wal-fsext-plan.md`).
- **Defect.** Unprovable `decodeRecord`: (1) Go asks `errors.Is(err, io.EOF)` of `readInt64`'s error also
  when it is `nil` (decoder.go:95), which `isEofOk` did not cover; (2) with `io.EOF = io.ErrUnexpectedEOF`
  a short length word would drop the file; (3) with `IoE io.EOF` a reader may end a file early with
  `io.EOF` (`decRdErr`), and the decoder goes on in the next file, which `goDecode` does not say.
- **Evidence.** The proof of `decoder.decodeRecord` (branch `wal-dec2`): the three cases are where it stuck.
- **Proposed change.** `isEofOk` also covers `e = nil` and carries `⌜eof ≠ ueof ∧ ¬ IoE eof⌝`; all three are
  true of Go (`errors.Is(nil, t)` is `nil == t`; the two `errors.New` allocations differ; the client's `IoE`, the
  `os` file errors, are expected not to include `io.EOF`), a client obligation like the rest of `isEofOk`.
- **Decision.** Adopted (proof agent, minor: an intermediate client obligation, no ghost state).

## 2026-11-13: the WAL decoder's `proto.Unmarshal` -- a failure is not `recDecode bs = none`; the decoded record cannot be reset

- **Spec.** `LinuxFs/Spec/google_golang_org/protobuf/proto/UnmarshalWalRecord.lean` (a hypothesis of
  `decoder.decodeRecord`), `walpb.Record.Reset.spec`, `decoder.{decodeRecord,Decode}.spec` and `decPost`
  (`DecDefs.lean`), the registered `walpb.Record`'s `decC` (`PbRecord.lean`); W3a of `notes/wal-fsext-plan.md`.
- **Defect.** (1) `UnmarshalWalRecord.spec` said `Unmarshal` fails exactly when the canonical decoding
  `recDecode` does; `proto.UnmarshalPb.spec` (D1/D2) gives only "success is the canonical decoding" and
  "a valid encoding succeeds", so it was not derivable. (2) Its precondition `l ↦ zero_val` and `Reset`'s
  post, against the registration's `blank`. (3) The registered `decC` put the record's hidden fields in an
  invariant, so a decoded record could never be `Reset` (the decoder reuses `rec`) without duplicating them.
- **Evidence.** The derivation attempt (`wal-dec2`, notes W3a), and `UnmarshalPb`'s error post, which
  returns no record.
- **Proposed change.** The coordinator's decision (2026-11-13): the weaker model. `Unmarshal` may fail on
  bytes that are no record's encoding (`UFail`), a failure being a `badRec` stop of the Go decoder
  (`GoFail`, `decPost`'s third disjunct, the record not given back; `ReaderRun.fail`); success is
  `recDecode`. The spec stated over `walCodec` and `pbRecordC.data.blank`, derived from `UnmarshalPb`;
  `decodeRecord`/`Decode` take `C = walCodec`; `Reset` returns `blank`; `decEnv` gains `isPkgInit proto`;
  the registered `decC` owns the decoded record whole (trusted, pending the user's review with the
  registration).
- **Decision.** Adopted (the coordinator for the model; proof agent for the `decC` ownership, flagged for review).

## 2026-11-13: `wal.WAL.Sync.spec` -- the error arm keeps the handle, though a failed flush leaves a partial write

- **Spec.** `Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__Sync.lean` (the W4a axiom; its proved replacement
  over `fsExt`, `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/`, branch `wal-save`).
- **Defect.** Unprovable: `sync` flushes the encoder's page writer first; a failed flush drops the pending
  buffer after part of it reached the file, so the handle's state no longer matches the file and no
  later operation on it can be proved.
- **Evidence.** The W6 proof attempt (`notes/wal-fsext-plan.md`, W6 log); `ioutil.PageWriter.Flush.spec`'s
  error post (proved, branch `wal-enc3`).
- **Proposed change.** On error, `Sync` consumes the handle (as `Save`'s and `SaveSnapshot`'s error arms
  do, plan §3); etcd's callers stop on that error (`Fatal`).
- **Decision.** Adopted (the coordinator, the user away; an intermediate spec, every client stops there).

## 2026-11-13: `wal.WAL.SaveSnapshot.spec` -- a snapshot's index must not be below an earlier snapshot record's

- **Spec.** `Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__SaveSnapshot.lean` (the W4a axiom; its proved
  replacement over `fsExt`, `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/`).
- **Defect.** `SaveSnapshot` sets `w.snapi` to the saved snapshot's index (not the maximum), and `cut` names
  the next segment after `max(w.enti, w.snapi) + 1`, which must exceed every index in the history
  (`walLastIdx`) for the segment names to stay increasing; a snapshot saved below an earlier one breaks
  it (the W6/W2 proofs, `notes/wal-fsext-plan.md`).
- **Evidence.** The handle fact `walLastIdx H ≤ max(enti, snapi)` (W2, `wal-cut7`) cannot be kept by
  `SaveSnapshot` otherwise (W6, `wal-save8`'s log).
- **Proposed change.** `SaveSnapshot.spec` takes `∀ s ∈ snapshot records of H, s.Index ≤ m.Index`. etcd
  saves the snapshots raft hands it (received, above the committed index) and its own (at the applied
  index, at least every snapshot applied before): monotone, to be checked at C6.
- **Decision.** Adopted provisionally (the coordinator, the user away); **for the user's review**: a new
  client obligation on the server (C6).

## 2026-11-13: `wal.WAL.SaveSnapshot.spec` -- the index premise above is not needed (withdrawn); the handle's snapshot bound is

- **Spec.** The previous entry (`SaveSnapshot.spec`'s proposed `∀ s ∈ snapshot records of H, s.Index ≤ m.Index`);
  `walHandleIn` (`LinuxFs/Proof/.../wal/Handle.lean`).
- **Defect.** The previous entry's defect does not hold at the pin: the translated `SaveSnapshot` (fork
  `0b50f0426`, S/wal.go:1161-1167) raises `w.snapi` and `w.enti` to the snapshot's index only when it is
  larger, so `walLastIdx (H ++ [snap m]) ≤ max(enti', snapi')` follows from the old bound with no premise.
  The real gap is elsewhere: `Save` of entries below an earlier snapshot record (`saveEntry` *sets* `w.enti`,
  S/wal.go:1086) needs `walMaxSnapIdx H ≤ snapi`, which the handle did not carry (with `enti = 120`,
  `snapi = 50`, a snapshot record of 100 read back, a `Save` of entries 60-70 would leave `walLastIdx = 100 >
  max(70, 50)`).
- **Evidence.** The W6 proofs (`wal-save9`): `walLastIdx_snap`, the Go code above.
- **Proposed change.** No premise on `SaveSnapshot`. `walHandleIn`'s index facts become `(rest = 0 →
  walLastIdx H ≤ max(enti, snapi)) ∧ walMaxSnapIdx H ≤ snapi` (internal; `saveEntry`/`saveState` take the
  `rest = 1` case as a premise, which `Save` supplies). Obligation for `ReadAll` (W3/W5) and `Create` (W4) when
  they build the handle: `walMaxSnapIdx H ≤ snapi` (`ReadAll`: every snapshot record before its first segment
  is below that segment's name index, at most the target snapshot's, which it reads; `Create`: 0).
- **Decision.** Adopted (proof agent; withdraws a provisional client obligation, so nothing for the user to
  approve; flagged in the W6 log).

## 2026-11-14: `wal.WAL.Save.spec`, `wal.WAL.SaveSnapshot.spec` -- no bound on the records' size

- **Spec.** The WAL specs over `fsExt` (`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__Save.lean`,
  `WAL__SaveSnapshot.lean`).
- **Defect.** The append's commit (`walTail_append`, before any record is written) must keep the
  invariant's static relation, whose `fit` says every record's encoding is below `2^56` bytes (the
  frame's 56-bit length field: `encodeFrameSize` puts the padding in the top byte, so a longer record
  corrupts its frame); the encoder's spec needs each record below `2^47` (`encode.specG`'s `recSize`,
  protobuf-go's `MarshalAppend`). Nothing bounds `Mr.encEntry e` or `Mr.encSnap md`: the part's `Save`
  dropped the main tree's `walSaveEnts sized` (whose `entSizeOk` bounded the entries), and `entIn` has no
  size.
- **Evidence.** `Append.lean`/`HandleAppend.lean` (`walHandleIn_append`'s `hfit`: `∀ c, RecsFit walCodec
  (chainRecs walCodec c (opDs Mr o.toM))`); `encoder__encodeG.lean`.
- **Proposed change.** A premise of `Save`: `∀ e ∈ es, (Mr.encEntry e).length < 2 ^ 40`, and of
  `SaveSnapshot`: `(Mr.encSnap md).length < 2 ^ 40` (the hard state's record: `walAreaOk`'s law). True of
  etcd: raft entries are bounded by the server's request size limit (`--max-request-bytes`, below
  `2^31`), snapshot metadata is a few varints and the conf state's member ids. A C6 obligation on the
  server.
- **Decision.** Adopted as a minor fix (`wal-save11`, for the coordinator's and the user's review): the two premises
  are in the part's specs.

## 2026-11-14: `wal.WAL.SaveSnapshot.spec` -- `walSnapAt` does not determine the bytes `SaveSnapshot` writes

- **Spec.** `walSnapAt sp md cs` (the WAL vocabulary, `Proof/go_etcd_io/etcd/server/v3/storage/WalDisk.lean`),
  taken by `SaveSnapshot.spec`; in the part over `fsExt`, `LinuxFs/Spec/.../wal/WAL__SaveSnapshot.lean`, whose
  history records `.snap md` written as `Mr.encSnap md` (`WalEncRecs.opDs`).
- **Defect.** `walSnapAt` fixed the index, the term and whether the conf state is nil, not the conf state's
  content nor either level's unknown fields, all of which `pbutil.MustMarshalMessage` writes; so the bytes
  of the snapshot record were not a function of `md`, and the law `MustMarshalMessage.specWalSnap` (bytes
  `Mr.encSnap md`) was false of the real marshaller. It also held the object as a whole frozen struct
  (`sp ↦□ s`), which protobuf-go's `Marshal` (it writes `sizeCache`) cannot read.
- **Evidence.** The W6 proof (`notes/wal-fsext-plan.md`, W6 log, fifth and ninth sessions);
  `MustMarshalMessageWalSnap.lean`'s former "Open" note.
- **Proposed change (made, in the part).** `walSnapAt Mr sp md cs` (`LinuxFs/Proof/.../wal/walpb/
  PbSnapshot.lean`): a frozen `walpb.Snapshot` at a wire content `c` (`snapRoC`, the registered
  `walpb.Snapshot`, hidden fields of both levels in invariants) with `c.model = md`, `Index`/`Term` set,
  `cs = c.confState.isSome`, and **`snapEnc c = Mr.encSnap md`**. `walSnapIdTerm` is over the same content
  (the getters' index and term). **New client obligation (C6):** the server's marshaller parameter `Mr`
  must give one wire form per snapshot metadata, the one of every `walpb.Snapshot` it passes. Plausible: the
  server builds each one the same way (`storage.go:62-66`, `Index`/`Term` copied from raft's metadata, the
  conf state raft's own object), so `Mr.encSnap md` is `snapEnc` of that shape provided raft's conf states
  carry no unknown fields (raft builds them; a decoded one from a peer could, which C6 must exclude or
  carry). The main tree's `walSnapAt` (the W4a axioms' vocabulary) is unchanged until the part's specs
  replace them.
- **Decision.** Adopted (the coordinator's decision, W6 ninth-session plan; the user away). **For the
  user's review** with the two trusted axioms `snapEncC_ok`, `pbSnapC_reg` (plan §10).

## 2026-11-14: the WAL's marshaller parameter `Mr` -- a bound on the hard state's encoding

- **Spec.** The WAL specs over `fsExt` (`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/`), their parameter
  `Mr : WalMarshal` (the client's marshallers of entries, hard states, snapshots).
- **Defect.** `cut` writes the hard-state record into a new segment's headers and needs
  `h.md.length + (Mr.encState h.st).length < 2^42` (W2, `wal-cut9`); nothing bounds `Mr.encState`.
- **Proposed change.** A law of `Mr` (in `walAreaOk` or `WalMarshal.Ok`): `(Mr.encState hs).length < 2^32` for
  every hard state; `md` is bounded at `Create`. raft's `HardState` encodes as three varints (at most
  ~33 bytes): discharged at C6 from raftpb's encoder.
- **Decision.** Adopted (the coordinator, the user away): a client-visible law on a parameter, true of
  etcd's marshaller.
- **Made** (`wal-save11`): the law is the last conjunct of `walAreaOk` (`CreateDefs.lean`;
  `walAreaOk_encState`); the metadata's bound `h.md.length < 2^41` is a conjunct of the sealed client
  handle `walOpenWF` (`Handle.lean`), an obligation of its producers: `Create` (a premise
  `md.length < 2^41` when its spec returns `walOpenWF`) and `ReadAll` (the WAL's metadata is `Create`'s:
  needs the invariant to keep `d.metadata.length < 2^41`, established at `Create`'s commit). The cuts'
  increase (`cut.spec`'s `h.cuts.Pairwise`) is not carried by the handle: the append's commit returns it
  from the invariant's static relation (`walTail_append`).

## 2026-11-14: `wal.Create.spec` (the part's, over `fsExt`) -- its success post is the ghost-only handle

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Create.lean` (`wal.Create.spec`), success arm:
  `walOpenW w dir` (the sealed ghost handle: mode and lock token) and `osCallPerm ½`.
- **Defect.** `Save`/`SaveSnapshot`/`Sync`/`Close` (W6/W10) take the client handle `walOpenWF P Mr w dir`
  (`Handle.lean`: `w`'s fields, encoder, tail, pipeline, directory share, `walOpenW` inside), as `ReadAll`
  returns it; a WAL made by `Create` could not be appended to. The commit's out-record, the tails' authority half,
  the named entry and the metadata belong in that handle, and were dropped.
- **Evidence.** W4 log, eleventh session ("For the coordinator"); the coordinator's decision of 2026-11-14
  (task 3 of `wal-create12`).
- **Change (made).** `wal.Create.spec (P : WalPbIn GF) (Mr : WalMarshal)` over `walAreaOk walCodec Mr` (the
  handle's codec, as `Save`'s), `HeapGS HasLC.hasLC` (the handle's receipts); success arm `Q ∗ walOpenWF P Mr w dir ∗
  walNamed dir ∗ walLenLb w dir 0 ∗ walSyncedLb dir 0 ∗ walPurgeW w dir`, the call permission's half now inside the
  handle (`walDirH`). An internal refinement: no new client-visible ghost state (`walOpenWF` is the existing
  handle; it implies `walOpenW`, `walOpenWF_iff`); no client of `Create`'s part spec exists yet.
- **Decision.** Adopted (coordinator's decision; proof agent, `wal-create12`).
- **Addendum (2026-11-14, `wal-save11`'s obligation).** `Create.spec` also takes `md.length < 2 ^ 41` (a
  premise: the handle `walOpenWF` now holds `h.md.length < 2^41`); minor, the metadata etcd writes is small.
  The invariant's `d.metadata.length < 2^41` (for `ReadAll`) is to be established at `Create`'s commit
  (`walCreate_osAUnc`), not yet done.

## 2026-11-14: `wal.Exist.spec` -- the lock token, and a `false` that `fsExt` cannot exclude

- **Spec.** `wal.Exist.spec` (the main tree's W4a axiom `Spec/go_etcd_io/etcd/server/v3/storage/wal/Exist.lean`),
  restated over `fsExt` in `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Exist.lean` (W12 of
  `notes/wal-fsext-plan.md`).
- **Defects.** (1) *The token.* To read a present WAL's directory, `Exist` needs a fraction of its directory's
  claim, which `walParked` holds while no handle is open; taking it out needs the lock (`walParked_lock`,
  as `Open`'s pin). The old spec took no token. (2) *Q4 (b).* `Create`'s failure after its rename leaves a
  fresh, unnamed WAL whose directory `cleanupWAL` may have moved aside (plan §11): `false` must allow it.
  (3) *`false` on a present WAL.* `Exist` returns `false` when `ReadDir` fails with an error
  `errors.Is(_, os.ErrNotExist)` accepts. `fsExt` lets every failing system call return any errno, `ENOENT`
  included (`IsFsStep` "Open", "Readdir"), so the model has runs where `Exist` of a present, named WAL
  returns `false`: the old post (`false → o = none`) is false of the model, though true on configuration C
  (Linux's `open(2)` returns `ENOENT` only for a missing component; `getdents64` only on a removed
  directory, which a WAL directory under the area discipline is not).
- **Evidence.** `GooseLang/Ext/Fs/Impl.lean`, "Environmental failure is a nondeterministic errno"; the W12
  proof (the plan's W7-W12 log).
- **Proposed change.** (1) `Exist` takes `walUnlockedTok` (framed), as `Open` and `Create` do; its callers
  (the server's bootstrap, the tester's restart) call it with no handle open. (2) `false → o = none ∨ ∃ d,
  o = some d ∧ d.H = [] ∧ d.named = false`. (3) Kept the strong post, proved over the hypothesis
  `fileutil.ReadDir.specChildIs` (a present directory's read fails only with an error `errors.Is` does not
  take for `os.ErrNotExist`), unprovable against the current model; the model fix ("`ENOENT` only when the
  path does not resolve", for `open` and `getdents`) is the user's (trusted semantics) -- the alternative,
  a `false` that claims nothing, would leave `Create` (which needs `walAbsent`) unreachable from the
  server's bootstrap.
- **Decision.** (1), (2) adopted (minor; (2) is the coordinator's Q4 (b)). (3) **for the user**: the
  hypothesis stays until the model tightens `ENOENT` (`notes/wal-fsext-plan.md`, W7-W12 log).
## 2026-11-14: `wal.openAtIndex.spec`, `wal.Open.spec`, `wal.OpenForRead.spec` (the part's, over `fsExt`) -- the WAL directory's length and name

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/{openAtIndex,Open,OpenForRead}.lean`.
- **Defect.** `openWALFiles` (`filepath.Join(dir, name)`) and `newFilePipeline` take `dir.length < 2^61`; the
  specs bound neither `dir` nor the area `r` (the invariant records no length of a WAL's directory path).
  For an absent WAL, `selectWALFiles.specAbsent` (`os.Open` of a missing name) takes `NameOk nm`, which
  `walNameOk nm` does not give (it allows a NUL byte).
- **Evidence.** `openAtIndex`'s proof (W3/W5 log, twelfth session): the premises of `openWALFiles.spec` and
  `newFilePipeline.spec`.
- **Change (made).** The three take `dir.length < 2 ^ 59` and `NameOk nm`, as `wal.Create.spec` does (a path to
  a WAL directory is short in practice: Linux's `PATH_MAX` is 4096; etcd's name is `wal`).
- **Decision.** Adopted (minor, proof agent `wal-read12`; no client of the part's `Open` exists yet).

## 2026-11-14: `wal.Open.spec` (the part's, over `fsExt`) -- the call permission counted twice

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Open.lean` (`wal.Open.spec`), success arm:
  `walOpeningF w dir s ∗ osCallPerm ½`.
- **Defect.** The client's `osCallPerm 1` is split by `openAtIndex` in write mode: half to the file pipeline
  (`walPipeH`), half returned. `Open` returned that half to the client, but the handle `ReadAll` makes from
  `walOpeningF` (`walOpenWF`, its `walDirH`) holds a half of its own (as `Create`'s does, ledger 2026-11-14):
  after `Open` and `ReadAll` the client would hold 3/2 of the permission, and `ReadAll` could not be proved
  (nothing in `walOpeningF` supplies the handle's half).
- **Evidence.** `openAtIndex`'s proof and `ReadAll`'s obligations (W3/W5 log, twelfth session, item (a)).
- **Change (made).** `Open`'s success arm is `walOpeningF w dir s` alone; the sealed `walOpeningF`
  (`ReadDefs.lean`) holds the half (`osCallPerm ½`), which `ReadAll` moves into `walDirH`. A resource
  placement, no new client-visible ghost state; `OpenForRead` (read mode: no pipeline, the whole permission
  returned to the client) and `openAtIndex` unchanged.
- **Decision.** Adopted (the coordinator's decision of 2026-11-14, task 1 of `wal-read13`; no client of the
  part's `Open` exists yet).

## 2026-11-14: `wal.decoder.Decode.spec` (the part's, over `fsExt`) -- the error's identity

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/decoder__Decode.lean` (`decPost`, `stopErr`,
  `isEofOk` in `DecDefs.lean`).
- **Defect.** A reader looping to the end (`ReadAll`, S/wal.go:523-611) tests `errors.Is(err, io.EOF)` on the
  error `Decode` returned. (1) `stopErr`'s catch-all (`e ≠ nil`, for a bad frame, a CRC mismatch, a frame too
  large) allows `io.EOF` itself: `ReadAll` would then take a stop in the middle of the WAL for its end and succeed
  with the records after it missing, so its success post cannot be proved. (2) `isEofOk` answers `errors.Is` only
  on `nil`, `io.EOF`, `io.ErrUnexpectedEOF` and the readers' `IoE` errors, not on the decoder's own errors
  (`fmt.Errorf`'s, `proto.Unmarshal`'s), so the call cannot be stepped on them at all.
- **Evidence.** `ReadAll`'s proof (W3/W5 log, fourteenth session): the loop's exit and the write-mode stop check.
- **Change (proposed, not made).** `Decode.spec` (and `decodeRecord.spec`) add to `decPost`: `err = io.EOF` only
  at `goDecode`'s `.eof` stop, and `errors.Is(err, io.EOF)`'s answer for a non-nil `err` (`isEofAns`). Stated as
  `decoder.Decode.specR` (`decoder__DecodeR.lean`), a hypothesis of `WAL.ReadAll.wp_proof` until then. The
  proof needs Perennial's `fmt.Errorf` model to give an error distinct from `io.EOF` with `errors.Is` answering
  false on it (its wrapping is not kept) and the same of `proto.Unmarshal`'s error.
- **Decision.** Adopted (the coordinator, 2026-11-14; made by `wal-readall15`). `decPost` (`DecDefs.lean`) is now
  `decPostB ∗ decAns eof err`: the old body, and `errors.Is(err, io.EOF)`'s answer on a non-nil error
  (`isEofAns`); `stopErr`'s catch-all is `e ≠ nil ∧ e ≠ eof`, so `io.EOF` comes only from the `.eof` stop
  (the `IoE` arm excludes it by `isEofOk`). `Decode.spec`'s and `decodeRecord.spec`'s statements read the same
  (over `decPost`); `decoder.Decode.specR` is gone. The proof's new inputs: `fmt.ErrorfErrsNot.spec` (`Errorf`'s
  result is not `t` and `errors.Is(_, t)` is false on it when it is so of every error argument, `t` a package
  variable's value; a hypothesis, `LinuxFs/Spec/fmt/ErrorfErrsNot.lean`), `proto.UnmarshalWalRecordE.spec`
  (`Unmarshal`'s error is not `io.EOF`, the same answer; a hypothesis), `walpb.Record.Validate.spec` with the
  same of its error (statement change: targets `X`/`t`, premise `errIsNot ErrCRCMismatch t`), and `decEnv`
  holding `errIsNot ErrCRCMismatch io.EOF` (a client obligation, as `isEofOk`). `notes/perennial-changes.md`,
  2026-11-14, "`errors.Is` on `fmt.Errorf`'s result".

## 2026-11-14: `wal.WAL.Save.spec` (the part's, over `fsExt`) -- the batch's size, not each entry's

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__Save.lean`, premise
  `∀ e ∈ es, (Mr.encEntry e).length < 2 ^ 40` (ledger 2026-11-14, "Records' size").
- **Defect.** Each entry bounded, the batch is not: the tail's stream grows by the whole batch before `Save`
  checks `SegmentSizeBytes`, and nothing then bounds the encoder's offset and pending bytes by ext4's maximum
  offset (`0xffffffff000`, `walHandleIn`'s `o0 + |out| + |pend|` bound, `Seek`'s and the writes' arithmetic):
  `saveEntry`/`saveState`/`encode.specTail` claimed it in their posts with no source (W6 log, twelfth
  session).
- **Evidence.** W6 log, thirteenth session (`wal-save13`): the bound is the stream before the call (a handle
  fact at quiescence, below) plus the batch's frames; a frame is at most its data plus 64 bytes
  (`frame_walRecEnc_tight`).
- **Change (made).** `Save` takes `walBatchBytes Mr es < 2 ^ 40` (each entry's encoding plus 64 bytes, summed;
  implies the per-entry bound). `SaveSnapshot`'s per-record premise is already its batch's. The handle fact
  (sealed `walOpenWF`, no client-visible change): the tail's stream end `o0 + |out| + |pend| < 2 ^ 43` at
  quiescence (`Save` cuts once the offset reaches `SegmentSizeBytes`, the pending bytes at most the page
  writer's buffer, 2^18; a cut's or `Create`'s headers at most the metadata, below 2^41, and the state).
  **C6 obligation**: raft bounds a `Ready`'s entries (`MaxSizePerMsg`, the uncommitted-size limit), so the
  server's batches are far below 2^40 bytes.
- **Decision.** Adopted (the coordinator's decision of 2026-11-14 for `wal-save13`, task 2), with two
  corrections to its wording found in the proof: the fact is on the stream's end, not the offset (a `Save` that
  syncs flushes its pending bytes after its `Seek`, so the next `Save` may start at `SegmentSizeBytes` plus the
  buffer), and its bound covers a cut's headers (the metadata may reach 2^41 bytes).
- **Withdrawn (2026-11-14, `wal-maxb14`).** The model now bounds every file at ext4's `s_maxbytes`
  (`fsExt`'s `maxBytes = 0xffffffff000`, a trusted semantics change pending the user's review:
  `examples/osfs/semantics/data_maxbytes.go`, measured on configuration C). A write never lands a byte at or
  past it, so the tail's written stream stays below it by the writes' success alone, and nothing needs a
  bound on the stream before the write: `Save` is back to the per-entry premise of "no bound on the records'
  size" (needed by the frame encoding, not by the offsets), the handle's stream-end fact
  (`o0 + |out| + |pend|`, in `walHandleIn` and the sealed `walOpenWF`) is gone, and so are
  `saveEntry`/`saveState`'s stream premise and `encode.specTail`'s (entry below).

## 2026-11-14: `wal.WAL.Save.spec` (the part's, over `fsExt`) -- the batch premise withdrawn: the model's file-size bound

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__Save.lean` (premise
  `walBatchBytes Mr es < 2 ^ 40`); the internal `WAL__saveEntry.lean`, `WAL__saveState.lean` (premise
  `(tailStream Mr h.H h.md h.cuts).length ≤ 0xffffffff000`), `encoder__encodeTail.lean` (premise
  `o0 + |out| + |pend| + |frame| ≤ 0xffffffff000`, and the same of the result in its post); the sealed handle
  (`walHandleIn`'s `o0 + |out| + |pend| ≤ 0xffffffff000`, `walOpenWF`'s `< 2 ^ 43`).
- **Defect.** `SaveSnapshot` never cuts (S/wal.go:1137-1162), so `n` calls in a row grow the tail by `n`
  records, and no constant bound on the stream holds across them (`SaveSnapshot.wp_proof`'s `sorry`, W6 log,
  thirteenth session); the batch premise only moved the problem.
- **Evidence.** W6 log, thirteenth and fourteenth sessions; ext4's `s_maxbytes` (`ext4_max_size`,
  `generic_write_check_limits`, `inode_newsize_ok`, `vfs_fallocate`), measured on C (`TestMaxBytes`).
- **Change (made).** The model: `PWriteFinish` lands nothing at or past `maxBytes`; `FtruncateFinish`,
  `FallocFinish` land no target past it; `CrashFile`, `FsInit` sizes at most it (`OsWf.sizes`). Clients get
  it through `PwCut` (a write's landed end) and `wp_osMeta_size` (any `OsMeta`'s size, before a step). The
  WAL: `Save`'s premise back to `∀ e ∈ es, (Mr.encEntry e).length < 2 ^ 40`; the stream premises and the
  handle's stream-end fact removed (the handle keeps `o0 + |out| ≤ sz ≤ 0xffffffff000`, which the writes'
  success now gives). A client-visible weakening of `Save`'s premise; no new ghost state.
- **Decision.** Adopted provisionally (the coordinator's decision of 2026-11-14 for `wal-maxb14`), pending
  the user's review of the trusted semantics change.

## 2026-11-14: `wal.WAL.Close.spec` (the part's, over `fsExt`) -- the directory's `Close` error after everything is closed

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__Close.lean` (`wal.WAL.Close.spec`, new: the
  main tree's axiom's first conjunct with plan §3's binders), post `(∃ d, Q d ∗ walSyncedLb dir |d.H| ∗
  walUnlockedTok ∗ osCallPerm 1) ∨ ⌜err ≠ nil⌝`.
- **Defect (of the main axiom).** Its success arm required `err = nil`, its error arm was `¬ walCloseOk`. The Go
  code (S/wal.go:1053-1077) returns `w.dirFile.Close()`'s error after the sync, every lock's close and the
  put-back: an error there leaves everything closed and released, so a spec giving only `err ≠ nil` would lose
  the lock token and the update's `Q` for no reason; and `¬ walCloseOk` cannot be proved from an errno (plan §6 Q6).
- **Evidence.** `WAL.Close.wp_proof` (`LinuxFs/Proof/.../wal/WAL__Close.lean`): the put-back (`WalCloseLaw`) runs
  before `dirFile.Close()`.
- **Change (made).** The success resources whatever `err` (the left disjunct does not constrain it); a failed
  sync (S/wal.go:1064-1066, returned before the locks) gives only `err ≠ nil` (the handle is lost, as `sync`'s
  error arm loses it). The main axiom's second conjunct (`Close` of an opening or failed handle) is not restated
  here: `Open`'s error arm takes `WAL.Close.specOpening` (a hypothesis), the failed handle (`walReadFailedF`) waits
  for `ReadAll`.
- **Decision.** Adopted (the W10 session, 2026-11-14; plan §6 Q6's honest error posts; no client of the part's
  `Close` yet).

## 2026-11-14: `wal.WAL.saveEntry.spec` (the part's, internal) -- no bound on the entry's encoding

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__saveEntry.lean`.
- **Defect.** `encoder.encode.specTail` (as every encode spec) needs the record's size below `2 ^ 47`
  (`recSize`, the frame's length word); `saveEntry.spec` gave no bound on `Mr.encEntry e` (the per-entry
  bound was withdrawn with the batch premise, 2026-11-14, and moved back to `Save`'s premise only).
- **Evidence.** `WAL.saveEntry.wp_proof` (W6, fifteenth session): the encode's premise.
- **Change (made).** `saveEntry.spec` takes `(Mr.encEntry e).length < 2 ^ 40` (`Save`'s premise for each of its
  entries, which `Save`'s proof passes); internal spec, no client-visible change.
- **Decision.** Adopted (minor, internal; W6 fifteenth session).
## 2026-11-14: `WalDecEnvSupply` and `decEnv`'s `isEofOk` (the part's WAL decoder, over `fsExt`) -- the readers' errors and `errors.Is`

- **Spec.** `WalDecEnvSupply` (`LinuxFs/Proof/.../wal/openAtIndex.lean`, a hypothesis of `openAtIndex.wp_proof`,
  hence of `Open`/`OpenForRead` through it) and the decoder's environment `decEnv`/`isEofOk` (`DecDefs.lean`).
- **Defect 1 (made, fixed).** The supply put every pointer error in the readers' errors `IoE`, while `isEofOk`
  needs `¬ IoE eof` and `io.EOF` is a pointer error (an `errors.New` `*errorString`, `io.eof_of_init`): the
  hypothesis proved `False` under `isPkgInit wal`, and `openAtIndex`/`Open`/`OpenForRead` were vacuous.
- **Change (made).** `IoE` holds of every `*PathError` (`∀ pe, IoE (mkOk *PathError #pe)`); `os.File.Stat.spec`'s
  error is the model's `*PathError` (was: some pointer error; its proof already knew it). Sanity check:
  `walDecEnv_eof_not` (`io`'s initialization: `io.EOF` is no `*PathError`), so the pure part `¬ IoE eof`,
  `∀ pe, IoE (PathError pe)` is met by `IoE` = the `*PathError`s.
- **Defect 2 (open, not mine to fix).** Even so the supply is not true of Go: `isEofOk` asks
  `errors.Is(e, io.EOF)` to answer `false` for every `IoE` error with no precondition, and `errors.Is` of a
  `*PathError` unwraps its `Err` field (heap), so it answers `true` for a `&PathError{Err: io.EOF}`. No pure `IoE`
  can hold of the `*PathError`s `os.File.Read`/`Stat` return (fresh allocations, `os.errnoPathErr`'s persistent
  fields) and of no other: the errors' evidence is a heap fact, and the decoder's readers pass errors through
  pure predicates only (`io.readerStream`'s `E`, `bufio.ownReader`, `decRdErr`, and the trust-boundary axiom
  `io.ReadFull.wp_proof`, `Spec/io/ReadFull.lean`).
- **Proposed change.** Carry the error's evidence with it: `io.readerStream ri S E` with `E` a persistent Iris
  predicate (`List w8 → GoInterface → IProp`), so `ReadFull`'s axiom, `bufio`, `readInt64` and the decoder pass
  it on; `decRdErr`'s I/O arm then `os.errnoPathErr e n` (`n ≠ 0`, which `Read.wp_eof`'s error arm gives with a
  small strengthening), and `isEofOk`'s I/O branch is provable from an `errors.Is` fact on `errnoPathErr`
  against an `*errorString` (as `errors.IsPathErrnoNotExist.spec`, `ExistCallees.lean`). Changing
  `io.ReadFull.wp_proof`'s statement is a trust-base change: **the user's decision**.
- **Decision.** Defect 1 fixed (2026-11-14, `wal-readall16`). Defect 2: **adopted provisionally** by the
  coordinator (2026-11-14, `wal-readall17`; a trust-boundary axiom's statement changed: **pending the
  user's review**, listed in `notes/wal-fsext-plan.md` §10; kept off `lean` until reviewed).
- **Change (made, `wal-readall17`).** `io.readerStream ri S E` takes `E : List w8 → GoInterface → IProp GF`
  and returns `nil` or an error with `□ E (r ++ ys) err` (`io.errAt`); `io.ReadFull.wp_proof`'s statement
  (`Spec/io/ReadFull.lean`) returns `io.readFullRes E eof ueof r0 ys m err`:
  `⌜ys.length = m ∧ err = nil⌝ ∨ ∃ e, ⌜ys.length < m ∧ e ≠ nil ∧ (e = eof ∧ ys ≠ [] → err = ueof) ∧
  (¬ (e = eof ∧ ys ≠ []) → err = e)⌝ ∗ □ E (r0 ++ ys) e` (the old pure `readFullOk` with the evidence
  made Iris; `io.readFullRes_pure` gives the old form back). `bufio.ownReader`/`Reader.Read`,
  `FileBufReader.Read`, `readInt64` pass it on. The decoder's readers return `decRdE bs eof IoE r e :=
  ⌜decRdErr bs eof IoE r e⌝ ∗ isEofAns e eof` (each error with `errors.Is(e, io.EOF)`'s answer), its
  `FileInfo` errors `decAns`; `isEofOk` asks the answer only on `nil`, `io.EOF`, `io.ErrUnexpectedEOF`.
  The `os.File` bridge proves the answer on the model's `*PathError`s (`os.File.Read.wp_eof`'s and
  `Stat.spec`'s errors now `os.errnoPathErr err e`, `e ≠ 0`) from the hypothesis
  `errors.IsPathErrnoEof.spec` (`LinuxFs/Spec/errors/IsPathErrnoEof.lean`; true of Go, as
  `IsPathErrnoNotExist.spec`: needs `(*PathError).Unwrap`, `Errno.Is` translated). `WalDecEnvSupply` is
  then true of Go but still a hypothesis: `errors.newVar` keeps no trace of the allocation, so `io.EOF`,
  `io.ErrUnexpectedEOF` and `walpb.ErrCRCMismatch` cannot be shown distinct from the packages' facts
  (`notes/perennial-changes.md`, 2026-11-14).
## 2026-11-14: `wal.WAL.renameWAL.spec` (internal, the part's) -- the spine law cannot open the invariant

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__renameWAL.lean`, `RenameWALOk`'s third
  conjunct: `∀ x, Sp -∗ renDirOut … (some x) ={⊤}=∗ osPathS R dir dq J ∗ osPathS R dir dq J ∗ SpR x`.
- **Defect.** The caller (`Create`) can discharge it only with the invariant's post-commit split
  (`walInv_splitNew`, `CreateSplit.lean`), which opens `walInv` (needs `notCrashed`) and takes the lock token
  `walLockedTok` that the committed update's result `U (some x)` (`walCreateQ`) holds; the conjunct gives
  neither.
- **Evidence.** The W1 log, fourteenth session, "Not done" (1); `walInv_splitNew`'s statement.
- **Change (made).** The conjunct is `∀ x, Sp -∗ notCrashed -∗ U (some x) -∗ renDirOut … (some x) ={⊤}=∗
  notCrashed ∗ U (some x) ∗ osPathS R dir dq J ∗ osPathS R dir dq J ∗ SpR x`; `renameWAL` applies it at a
  program step after the rename (`wp_notCrashed_acc`). `dq` is fixed by `Create`.
- **Decision.** Adopted (the coordinator's decision, 2026-11-14, `wal-path15` task 3; internal spec, no client).
## 2026-11-14: `wal.WAL.renameWAL.spec` (internal, the part's) -- no bound on the directory's length

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__renameWAL.lean`, `RenameWALOk`.
- **Defect.** `newFilePipeline.spec` needs `dir.length < 2 ^ 61` (its `Join`s of `dir` and `0.tmp`/`1.tmp`);
  nothing in `RenameWALOk` bounds `dir` (`osPathS` gives no length).
- **Evidence.** `renameWAL.wp_proof`'s `newFilePipeline` step (`wal-create14`).
- **Change (made).** `RenameWALOk`'s second conjunct `dir.length < 2 ^ 59` (`Create.spec`'s premise, which
  `Create` passes on).
- **Decision.** Adopted (minor, internal; `wal-create14`).
## 2026-11-14: `wal.WAL.renameWALUnlock.spec` (internal, the part's) -- unprovable as stated

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__renameWALUnlock.lean`.
- **Defects.** (1) Its `w.Close()` flushes the encoder, fdatasyncs the tail and closes the lock fds, but the pre
  (`walPreIn`) has neither `ownEncoder` nor the tail file's ownership (`os.ownFile`/`osFd`, its writer stream):
  `Create` gives the segment to the rename's update (`walCreateP`), so a generic `U` hides it. (2) Its `Open`/
  `ReadAll` need `walAreaRes jr`, `walUnlockedTok`, `osCallPerm 1` and an `AU` on `walDirIs dir`; after a
  committed rename the lock token is in `U (some x)` (`walCreateQ`) and the client's `walDiskAt` in its `Q`, so no
  generic law gives `Open`'s `AU`. (3) After a rename that committed with an error (`o = some x`), the second
  `os.Rename(nm.tmp, nm)` has an absent source: no `os.Rename` spec covers it (`wp_osRenameAbsentS` is internal
  to `Proof/os/Rename.lean`).
- **Evidence.** `renameWAL.wp_proof` (`wal-create14`) uses the spec as a hypothesis; `WAL.sync.specPreL`'s pre;
  `Open.spec`'s pre; `os.Rename.specDirSnc`'s premises.
- **Change.** Decided by the coordinator (2026-11-14) for (1): the pre carries what `Close` consumes (the
  encoder, the tail file, the lock fds) as `Create` holds them before the rename; the first `Close` proved inline
  over `os.File.Close`, `os.File.Close.specNil` and the encoder's flush spec, not through `WAL.Close.spec`.
  **Not yet made** (`wal-create14` stopped at its context budget; `Create`'s body has not reached the encoder, so
  the exact form is open). (2) and (3) need a design: proposed, a caller-supplied law (like `Sp`/`SpR`) from the
  committed result to `Open`'s pre, which `Create` discharges by releasing the fresh WAL's lock and merging the
  names back, or a `Create`-specific (non-generic) `renameWALUnlock` spec; and a public `os.Rename` spec for an
  absent source (`ENOENT`, no effect).
- **Decision.** (1) adopted (coordinator); (2), (3) pending the coordinator.

## 2026-11-14: `wal.Create.spec` (the part's, over `fsExt`) -- the initial snapshot record's bytes

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Create.lean`.
- **Defect.** `Create` writes `&walpb.Snapshot{Index: new(0), Term: new(0)}` through `SaveSnapshot`
  (S/wal.go:181), whose bytes are protobuf-go's (`snapEnc snapC0`; `SaveSnapshot.specPre` writes
  `Mr.encSnap sm` of a `walSnapAt Mr sp sm cs`, which ties the object's encoding to `Mr.encSnap`). The
  committed state `walDurFresh md` has `Mr.snap0` there (`hdrDs`). Nothing relates `Mr.snap0`, `Mr.encSnap`
  and `snapEnc`: with an arbitrary marshaller the spec's commit is false.
- **Evidence.** `Create.wp_proof`'s `SaveSnapshot` step (`wal-create15`); `WalEncRecs.lean` (`hdrDs`).
- **Change (made).** Premise `WalMarshalCreateOk Mr` (`CreateSnap.lean`: `Mr.snap0 = snapEnc snapC0 ∧
  Mr.encSnap snapC0.model = Mr.snap0`), a pure fact of the client's marshaller parameter, which the
  server meets with the real one (as `walSnapAt`'s tie, ledger 2026-11-13).
- **Decision.** Adopted (minor: a pure premise on a parameter, no ghost state; `wal-create15`).

## 2026-11-14: `wal.WAL.renameWALUnlock.spec` (internal, the part's) -- (2) Create-specific: blocked on `Open`'s update

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__renameWALUnlock.lean`, defect (2) of the
  entry above, and the coordinator's decision (b) (make `renameWAL`/`renameWALUnlock` `Create`-specific, naming
  `walAreaRes`, `walUnlockedTok` and the client's update on `walDirIs dir`).
- **Finding (`wal-create15`).** `Create`-specific statements give `walAreaRes jr` (`Create` holds it through
  `walAreaRes_open`'s parts, merged back by `walInv_merge2` after the unminting or the commit) and
  `walUnlockedTok` (the commit's `walCreateQ` returns `walLockedTok`; `Close` of the pre-rename `w` does not
  give it back, so the retry must release it first: `walLockedTok_unlock` needs the handle's
  `walOutFrag`/`walTailsFrag`/`walNamesFrag none`, which `walCreateQ (some x)` holds). **But `Open`'s update
  cannot be built**: after the second rename commits, the client's update (`walAbsent dir` to `walDiskAt dir
  (walDurFresh md)`) has been spent (its `COMM Q` is in `walCreateQ (some x)`), and `Open.spec` asks for an
  atomic update on `∃∃ o, walDirIs dir o`, which only the client's resources open. `Create` owns no
  `walDirIs`/`walDiskAt` fragment after the commit (they are the client's, inside `Q`). So the retry's
  `Open`/`ReadAll` are provable only if `Create.spec` takes a **second client update** for the reopen
  (`AU <{ ∃∃ o, walDirIs dir o }> @ walAuMask, ∅ <{ walDirIs dir (o.map …), COMM Q' o }>`, used only on the
  retry path; on every other path returned or dropped), or if `Create`'s success arm on the retry path
  returns without the reopened handle (not what the code does).
- **Evidence.** `Open.spec`'s pre (`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Open.lean`); `walCreateQ`
  (`CreateAu.lean`); `Create.spec`'s pre.
- **Change.** None made: a second client update in `Create.spec` is a change to the client's contract (the
  coordinator's / the user's decision). (3) (the second rename's absent source) and (1) (the pre carries the
  encoder and the tail file) are independent of it.
- **Decision.** Pending the coordinator.

## 2026-11-14: `wal.Repair.spec` (the part's, over `fsExt`) -- the lock token taken (plan §6 Q7)

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Repair.lean` (`wal.Repair.spec`, new): the main
  tree's axiom (`Spec/go_etcd_io/etcd/server/v3/storage/wal/Repair.lean`) with plan §3's binders (`walAreaOk`, the
  area's spine and `walAreaRes`, `osCallPerm 1`, the update at `walAuMask`; `Open`'s premises, as `Repair` reads
  the same directory), and `walUnlockedTok` framed.
- **Defect (of the main axiom).** It promised that `Repair` blocks on the tail's lock while a handle holds it,
  then acts as with no handle. Over `fsExt` the file locks are bookkeeping (plan §6 Q1: no lock state), so
  `LockFile` waits for nothing and a concurrent appender would race the truncation: the axiom's statement
  without the token is not provable (and with Q1's model, not true of the model).
- **Evidence.** Plan §3 ("`Repair` takes `walUnlockedTok`") and §5/§6 Q7; both callers comply: the WAL tester
  calls `Repair` after a successful `Close` (examples/etcd/wal/wal.go:192-198), `openWALFromSnapshot` before
  any `Open`.
- **Change (made).** The token in the pre and the post (framed); the "blocks until the handle's `Close`"
  scenario dropped until the lock model. Otherwise the main tree's: committed as accessed, the boolean unconstrained.
- **Decision.** Adopted (the coordinator, plan §6 Q7, 2026-11-13; stated in the W7-W12 log's fifth session).

## 2026-11-14: `wal.WAL.sync.specC` (internal, the part's) -- the post says the tail is durable

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__syncC.lean` (a hypothesis of
  `WAL.Close.wp_proof`, for the `sync` owner): its success post's handle `walHandleC … h'` (tail facts
  `TailMeta`: `lo = size = hi`).
- **Defect.** Too weak for `Close`'s unregistration: the invariant now requires an idle WAL's tail to be synced
  (`TailSynced`, `TailIdle`'s third part: every byte durable, zeros known only past the end; plan's W7-W12 log,
  sixth session), so that `Close` of an unread handle can fdatasync an unregistered tail without changing the
  invariant. `TailMeta` says nothing of the bytes.
- **Evidence.** `sync`'s last step is `fileutil.Fdatasync(w.tail().File)`, whose success post is the synced
  `OsMeta` and the bytes `bs.map durB` (`fileutil.Fdatasync.wp_tail`, `TailFdatasync.lean`).
- **Change (made).** The post's handle is `walHandleC … h' TailMetaS` (`TailMetaS m bs := TailMeta m bs ∧ ∀ y ∈ bs,
  y = durB y.1`, `CloseHandle.lean`; `TailMetaS.of_sync` from `TailMeta m bs` to the synced pair). `WalCloseLaw`
  takes `TailMetaS`; `WAL.Close.wp_proof` unchanged.
- **Decision.** Adopted (the coordinator's `TailSynced` decision, 2026-11-14).

## 2026-11-14: `wal.WAL.cut.spec` (internal, the part's) -- the history nonempty at a cut

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__cut.lean` (`WAL.cut.spec`, a hypothesis of
  `WAL.Save.wp_proof`, proved by `WAL.cut.wp_proof`).
- **Defect.** Too weak for `ReadAll`: its premise `walCutPos (h.H.map toM) |H|` allows `|H| = 0`, so a cut at
  position 0 could enter the invariant's layout; `ReadAll` from a cut file reads past a nonempty prefix
  (`readAll_ok_pure`'s `hk0`), and a cut at 0 would make that prefix empty (W3/W5 log, fourteenth to sixteenth
  sessions: the cuts' positivity).
- **Evidence.** `cut`'s only caller, `Save` (S/wal.go: `if curOff < SegmentSizeBytes { ... return nil }; return
  w.cut()`), cuts after appending a save record: its history is `H ++ [save]`, nonempty.
- **Change (made).** The premise `0 < h.H.length` after `walCutPos`; the invariant's `WalAbsD.cutPos` (every cut
  `> 0`, `CutLay` from the premise, the crash keeping the cuts). `WAL.Save.wp_proof` supplies it.
- **Decision.** Adopted (eighteenth W3/W5 session, minor: a premise its one caller meets; no client-visible
  change, `cut` is unexported).

## 2026-11-14: minibolt's `DB.init.spec`/`DB.init.specCrash` (the part's example) -- the post's `cz`; `os.File.WriteAt.specCrashS` -- the bytes written

- **Spec.** `LinuxFs/Spec/.../examples/osfs/bboltfs/DB__init.lean` (post: `({ m with size := max m.size 16384 }).synced`),
  `DB__initCrash.lean` (`initDoneMeta`, the same); `LinuxFs/Spec/os/CrashSt.lean`'s `os.File.WriteAt.specCrashS`
  (success post: the bytes written, the size, but not how far the loop got, `nn`).
- **Defect.** Since `wal-save16` (the extension's `pwCz`) a complete `pwrite` whose end reaches the zeros known
  raises `cz` to its end's page, so `init`'s first write (16384 bytes at 0) leaves `cz = pwCz m 0 16384 16384`,
  not `m.cz`; the later metas' writes (inside the first four pages, below the zeros a sync made known from the
  size on) leave it. The posts stated the old `cz`: false. `specCrash`'s proof also needs the loop's end state to
  be a completed `WReach` (`nn = |data|`), which `specCrashS`'s success post did not say (its proof had it, `hfk`).
- **Change (made).** Both posts' `OsMeta` is `({ m with size := max m.size 16384, cz := pwCz m 0 16384 16384 }).synced`;
  `specCrashS`'s success post gains `nn = data.length` (proved; `WReach.czInv`/`WReach.cz_done`: a completed
  `WriteAt`'s `cz` is one complete write's, `pwCz m off |data| |data|`; `pwCz_eq_of_lt`, `synced_zf_ge`, all in
  `CrashSt.lean`). Clients (`Open`, `OpenCrash`, `DB.commit.wp_proof_crash`) repaired; no other user.
- **Decision.** Made (`wal-save17`, the coordinator's task 1: the posts' `cz` as `pwCz m 0 16384 16384`).

## 2026-11-14: `WalDecEnvSupply` and `walReadH` -- no I/O error is `nil`

- **Spec.** `openAtIndex.lean`'s hypothesis `WalDecEnvSupply` (the decoder's environment: `∃ IoE eof ueof,
  decEnv IoE eof ueof ∗ ⌜∀ pe, IoE (*PathError pe)⌝`) and the sealed `walReadH` (`ReadDefs.lean`), which keeps
  the decoder's `IoE` existential.
- **Defect.** Too weak for `ReadAll`: `decoder.Decode`'s post (`decPostB`) has an I/O-error arm `⌜IoE err⌝` with
  the decoder no longer live; nothing excluded `IoE nil`, so at `err == nil` the loop (S/wal.go:523) would go on
  into its body with a dead decoder and an unknown record (the next `Decode` needs a live one): the loop's
  invariant is not provable.
- **Evidence.** The readers' errors are `*PathError`s (`os.File.Read`, `Stat`): `nil` is none of them. The
  decoder's own code returns a reader's error only under `err != nil`.
- **Change (made).** `WalDecEnvSupply`'s pure part `(∀ pe, IoE (*PathError pe)) ∧ ¬ IoE nil`; `walReadH`'s
  `decEnv IoE eof ueof` is `(decEnv IoE eof ueof ∗ ⌜¬ IoE nil⌝)`; `openAtIndex` passes it through. (The
  alternative, `err ≠ nil` in `decPostB`'s I/O arm, would reprove the decoder's specs.)
- **Decision.** Adopted (`wal-readall20`, minor: a hypothesis true of Go, and a sealed body; no client-visible change).

## 2026-11-14: `fileutil.CreateDirAll.specTmp` (internal, the part's; a hypothesis of `wal.Create.wp_proof`) -- nothing about the new directory's history

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/CreateCallees.lean`, `fileutil.CreateDirAll.specTmp`
  (not proved; `CreateDirAll.spec`, proved, is its `name`-absent case).
- **Defect.** Too weak for `Create`'s commit: `walCreate_osAUnc`'s `hJC` asks that after **any** crash of `J`'s
  claim (`hJ.valAfter J K`, every `K`) the only `.wal` file is the new segment's. The success post says only
  `hJ.cur = ∅`; a history with older `.wal` values of `J`'s names (an inode reused, or an existing `nm.tmp`
  emptied earlier in the generation) would make `hJC` false.
- **Evidence.** `Create.wp_proof`'s commit (`wal-create16`): `createJ_*` (`CreateJ.lean`) derive `hJC`, `hsn` and
  the layout's `walInos` from the merged claim of `J`, given that `J`'s claim, as `CreateDirAll` returns it, has
  no name at any crash (`valAfter … = none`).
- **Change (made).** The success post gains `∀ K b, hJ.valAfter J K b = none`. True of the directory `CreateDirAll`
  creates (its `mkdir`'s claim, `TreeShared`'s `hJ.cur = ∅ ∧ hJ.next = x + 1`: a fresh inode, nothing logged on
  it before the `mkdir`, which writes it empty), which the extension's `mkdir` law does not yet say (an allocator
  fact: `st.fs.nextIno` above every inode the log writes): **obligation for the extension's owner** (the `mkdir`
  law's post, then `CreateDirAll.spec`'s and `specTmp`'s). The existing-directory case of `specTmp` (an empty
  leftover `nm.tmp` that `Exist` missed) needs an argument too: the leftover's history in the generation must not
  hold a `.wal` value, or `walCreate_osAUnc`'s `hJC` be weakened to the crashes that keep `J`'s entries committed
  before the rename (`syncDir(nm.tmp)`'s `osCommitLb`, `Create`'s `Hcm1`, unused so far), which needs the
  invariant's commit bound compared with the program's. Open.
- **Decision.** Made, minor and internal (`wal-create16`): a hypothesis's post strengthened; its truth is an
  obligation recorded here and in the W4 log's eighteenth session.
  **Superseding direction (the coordinator, decided; `wal-create17`, not yet made)**: limit `hJC` to the
  crashes that keep `J`'s entries (`∀ y e E, (y, e, E) ∈ hJ.ents → K y`), under which `hJ.valAfter J K b =
  hJ.cur !! b`; `walCreate_osAUnc` then takes `osCommitLb m` with `J`'s entries below `m` (`syncDir(nm.tmp)`
  gives `osCommitLb n` for any `osLogLb n`: pass `J`'s claim's `next`) and raises the invariant's commit
  bound to `max n m` at the commit (`walsOk_mono`, `walsNamed_mono`, `absentNone_mono`, as `walInvBody_named`
  does), so every `RegionCrashedK` it quantifies over keeps them; then the post's `valAfter … = none` is
  dropped from `specTmp` (no allocator fact). Note also that `Create` removes an existing `nm.tmp` before
  `CreateDirAll`, so only `specTmp`'s `mkdir` case is reached.

## 2026-11-14: `wal.WAL.renameWAL.spec` / `renameWALUnlock.spec` (internal, the part's) -- the error arms lose the lock file and the spines

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__renameWAL.lean` (`renameWALPost`, arms 3 and 4),
  `WAL__renameWALUnlock.lean`; decisions (1) and 2b of the entries above.
- **Defect.** Too weak for `Create`'s exits after the call (`wal-create16`, which reaches them: `Create` now calls
  `renameWAL` with every `RenameWALOk` law discharged). On `renameWAL`'s error `Create` returns at once, and its
  deferred `f.Close()` (`retErr ≠ nil`) runs on the lock file: arm 3 (`walPreIn … ∨ emp`) and arm 4 (nothing)
  do not say whether `f` is still open (`os.ownFile`/`osFd`, as `Create` framed them around the call) or was
  closed by `renameWALUnlock`'s `w.Close()` (then the deferred close is a second close of a closed `*os.File`,
  which needs its own `os.File.Close` spec: `ErrClosed`, no effect; none exists). Arm 4 also drops the two spines
  to `dir` that the spine law made (`osPathS R dir dq J`, fractions of the area's spine and of `nm`'s claim), so
  `Create` cannot give back the area's spine fraction it lent (`osPathS R r (own qp) jr` in `Create.spec`'s post).
- **Evidence.** `Create.wp_proof`'s frontier `sorry` after `renameWAL` (`Create.lean`); `renameWALPost`.
- **Proposed change** (with (1), the pre carrying what `Close` consumes): the pre takes the encoder, the tail file
  (`os.ownFile f fd …`, `osFd`, `os.ownOff`) and the tail's lock (`fileutil.lockedFile lt f` is in `walPreIn`);
  arm 1 returns them; arms 3 and 4 return them open (the rename failed before `renameWALUnlock`'s `Close`, or
  `OpenDir` failed after a committed rename) or a closed-file token for the deferred `f.Close()` (a spec
  `os.File.Close.specClosed` to add: a closed `*os.File` returns an error and changes nothing); arm 4 returns the
  two spines (`osPathS R dir dq J ∗ osPathS R dir dq J`, for `osPathS_unchild`). Arm 2 (the retry's reopen) as
  decided in 2b: proved over `Create`'s held resources (`createU (some x)`: `walLockedTok`, `walOutFrag`,
  `walNamesFrag (some dir)`, the segment's halves), its `Open`/`ReadAll` through variants of `walInv_openAt`
  without the client's update (the open position of index 0 leaves `unl`, so no commit is needed; the
  state from `walCreateQ`'s `walPast`), and its success arm adding `walLenLb w' dir 0 ∗ walSyncedLb dir 0`
  (`Create.spec`'s success post). Not yet made.
- **Decision.** Adopted in part (`wal-create17`, the coordinator's task 1, decided). **Made**: the pre takes
  `walLockIn e f fd fname d c off` (the empty encoder, the segment's `*os.File`, its fd and descriptor, its
  offset); arm 1 returns it; arms 3 and 4 return `walLockLeft f fd fname d` (open: `os.ownFile f fd`,
  `osFd`; or closed by `renameWALUnlock`'s `Close`: `os.ownFile f (-1)`), and arm 4's case list names the
  retry's failed `Open`/`ReadAll`; `renameWALUnlock.spec`'s pre the same; `renameWAL` re-proved. The second
  close is `os.File.Close.specClosed` (`LinuxFs/Spec/os/File__CloseClosed.lean`): **not provable from the
  model** (`File.Close.impl` asks `FdKind(-1)`, stuck on a closed fd), a hypothesis of `Create.wp_proof`;
  proposed trusted change (pending the user): the model returns Go's `&PathError{"close", name,
  ErrClosed}` on fd -1. **Changed from the proposal**: arm 4 does not return the two spines (one stays
  with the pipeline `renameWAL` started, which an error leaves running, so `Create` could never give the
  caller's area spine back); instead their area part is the invariant's lend (`walInv_areaPath`,
  `AreaPath.lean`), and `Create`'s caller's spine is never lent. **Not made** (arm 2): as stated it is
  unprovable (`walOpenWF` holds `walNamed dir` and `walNamesFrag none`, which only `Create`'s parent fsync
  and registration give, after `renameWAL` returns; and `U (some x)` holds the lock token the handle holds
  too, so the arm is contradictory for `Create`, which does not use that). It needs a handle before
  naming (`walDirH` without `walNamed`, with `walNamesFrag (some dir)`), which `Create`'s arm 1 would build
  too, both then going through the parent fsync and the registration: not designed. `Create` leaves arm 2
  a `sorry`.

## 2026-11-14: `os.File.Truncate.specAu` (the part's, `LinuxFs/Spec/os/File__TruncateAu.lean`) -- the outcome's `tc` domain

- **Spec.** `os.ftDoneH`/`os.ftUndoneH`, the caller's halves of a truncate's outcome in `os.File.Truncate.specAu`'s
  post (and so in the fileutil `Au` specs over it: `preallocExtendTrunc.specAu`, `ZeroToEnd.specAu`): `∃ tc rz,
  osMeta ½ (… .withTc tc rz)`, the candidates known past the size existential.
- **Defect.** Too weak for the WAL's `os.File.Truncate.specWalTail`: its post's `TailMetaW` includes `TailZ` (the
  candidates of every byte between the size and the known zeros known, `wal-save16`), which the caller cannot
  derive from an unknown `tc`; the supply (`walInv`) knows it is `rsTail`, but nothing carries the fact out (an
  invariant opening outside an atomic step has no `notCrashed`). W1 log, nineteenth session, last item.
- **Evidence.** Every outcome the extension leaves for a file with no sync cut (the WAL's segments: `WalsOk`'s
  `cut = none`) has `tc = rsTail …` (`rsPostK true`, `rsUnMeta true`); `TcKnows.rsTail`.
- **Change (made, `wal-tc10`).** `os.ftDoneH p m tg zs` carries `⌜TcKnows m tg tg tc⌝`, `os.ftUndoneH p m tg xs'`
  `⌜TcKnows m tg m.size tc⌝` (`TcKnows m tg sz' tc := ∀ b, (rsTail true m tg sz' 0 [] !! b).isSome → (tc !!
  b).isSome`, `LinuxFs/Proof/os/TcKnows.lean`: the domain of the outcome's `rsTail`, landed at `tg` or not at the
  old size). A strengthening of the post; a supply (only the WAL's, not yet written) must prove it, which a supply
  for a file with a sync cut could not (its outcome keeps the announcement's `tc`): none exists. The retry loop
  carries it (`TcKnows.of_announce`, `TcKnows.of_rsPost`). The proposal had one `TcKnows m tg tc`; the not-landed
  outcome keeps no candidates of the bytes in `[tg, size)` (below its size), hence the size argument.
- **Decision.** Adopted (the coordinator's task list for `wal-tc10`, "decided").

## 2026-11-14: `fallocDoneH` (the part's `syscall.Fallocate` updates, `LinuxFs/Proof/syscall/FallocateAu.lean`) -- the growth's `tc` domain; `ZeroToEnd.specAu`'s post

- **Spec.** `fallocDoneH i m tg w` (the caller's halves of a growth landed with the size `w`, in `fallocOutH`, the
  share `fallocSup` hands back, and so in `preallocExtend.specAu`/`Preallocate.specAu`/`ZeroToEnd.specAu` through
  `preGrownH`): `∃ tc rz, osMeta ½ ((rsPost false m tg w).withTc tc rz) ∗ …`, `tc` existential, as `os.ftDoneH` was
  before `wal-tc10`.
- **Defect.** Too weak for `ReadAll`'s `ZeroToEnd` instance, whose post must give the tail's `TailZ` (the candidates of
  every byte between the size and the known zeros known): after the growth back to the size the caller cannot tell
  which bytes past it have known candidates (I3b, `wal-tc10` entry, last item).
- **Evidence.** The outcome the extension leaves for a file with no sync cut has `tc = rsTail false m tg w n []`
  (`rsDoneK true false`, `wp_osFallocFinishK`); `TcKnowsF.rsTail`.
- **Change (made, `wal-tc11`).** `fallocDoneH` carries `⌜TcKnowsF m tg w tc⌝` (`TcKnowsF m tg sz' tc := ∀ b,
  (rsTail false m tg sz' 0 [] !! b).isSome → (tc !! b).isSome`, `TcKnows`' growth form, in `FallocateAu.lean`). No
  supply exists yet (the WAL's, `fallocSup` at the tail, is the first); `fallocDoneH_preGrownH` drops it. The undone
  arm of `fallocOutH` is the exact announcement (`rsUndone false`), unchanged: see the obligation below.
- **Proposed, not made (needs `preGrownH`'s fact first): `ZeroToEnd.specAu`'s success post** gains
  `⌜ZteMeta m m'⌝`, `ZteMeta m m' := (∀ b, m.size ≤ b → (m.pc b).isSome → (m'.pc b).isSome) ∧ m.cz ≤ m'.cz ∧ ∀ z0,
  m.zf = some z0 → ∃ z', m'.zf = some z' ∧ z0 ≤ z' ∧ z' ≤ max z0 (pageEnd m.size)` (with `TailZ m` it gives `TailZ m'`,
  the size and `pageEnd m.size ≤ m'.cz` given). Its proof chains `TcKnows` (the truncate to `o`, landed), `TcKnowsF`
  (a partial or full `fallocate`) and `TcKnows` (the fallback's truncate): `preGrownH` (`DefsAu.lean`) must carry
  the pc-domain and `zf` facts through `preGrownH_trans` (`Preallocate.specAu`'s post), a change to
  `preallocExtend.specAu`/`Preallocate.specAu` and `filePipeline.alloc`'s use of `preGrownH`.
- **Decision.** `fallocDoneH`'s fact adopted (the coordinator's task list for `wal-tc11`, "decided"). `ZteMeta`
  adopted (the coordinator's task list for `wal-tc12`, "decided") and **made, simplified** (`wal-tc12`): `ZteMeta m m'
  := PcKeep m m' ∧ (m.ZfGe → m'.ZeroPg)` (`DefsAu.lean`; `PcKeep m m' := ∀ b, m.size ≤ b → m'.size ≤ b → (m.pc
  b).isSome → (m'.pc b).isSome`, `LinuxFs/Proof/os/PcKeep.lean`). `wal-save18`'s `ZeroPg` (zeros known from `z ≥ size`
  with `pageEnd z ≤ max size cz`) replaces the proposal's `zf` bound and `cz` clause: with `TailZ m` (which gives
  `ZfGe m`, and `m.pc` known at every byte past the size) and `m'.size = m.size`, `ZeroPg m'` and `PcKeep` give `TailZ
  m'`. Carried by **`preGrownH i m w Z`** (as `wal-save18`'s `preGrown`: `PcKeep m m'` always, `Z → m'.ZeroPg`),
  so `preallocExtend.specAu`'s post is `preGrownH … (err = nil ∧ m.ZeroPg)`, `preallocExtendTrunc.specAu`'s `(err = nil
  ∧ m.ZfGe)`, `Preallocate.specAu`'s (`preallocPostH`) `(err = nil ∧ m.ZeroPg)`, as the whole specs'. `PcKeep` from each
  outcome's `TcKnows`/`TcKnowsF` (`PcKeep.of_tc`); the undone `fallocate` arm of `fallocOutH` became `∃ tc rz,
  ⌜TcKnowsF m tg m.size tc⌝ ∗ osMeta ½ ((m.announce …).withTc tc rz)` (the extension's `rsOutF` undone arm
  `rsUndoneK m.cut.isNone false`, `wal-tc12`), which the obligation above asked for.

## 2026-11-14: `fileutil.Preallocate`/`preallocExtend`/`preallocExtendTrunc` (the part's) and `os.OpenFile.specCreateTruncS`'s `trFile` -- the zeros known on success

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/{Preallocate,preallocExtend,preallocExtendTrunc}.lean`
  (posts: `preGrown i m w`); `LinuxFs/Spec/os/OpenFileTruncS.lean`'s `trFile i P` (the new or `O_TRUNC`-truncated file).
- **Defect.** Too weak for `filePipeline.alloc` (`pipeFile`'s `ZeroPg`, W6 log, sixteenth session): neither post said
  anything of the zeros known (`zf`) or the page cache known zero (`cz`), so `alloc`'s `ZeroPg` was a `sorry`. It was not
  provable from stronger posts alone either (seventeenth session): a `fallocate` landing left `cz` behind the zeros
  it announced, and an `O_TRUNC` of an arbitrary leftover gave no zeros fact.
- **Evidence.** Linux keeps no page past the size's last page (the page cache reads zeros there); the extension now
  says so (`MetaOk.ce`, untrusted ghost), and a landed resize raises `cz` (`rsCz`: an `ftruncate` to past the zeros
  known and its announcement's end; `fallocate`'s growth when the old size's page was known zero). Then an
  `ftruncate` landed makes `ZeroPg` (from `ZfGe`), `fallocate`'s growth landed keeps it; a resize that did not land
  keeps neither (its `OsMeta` is the announcement's, unchanged, so that the WAL's layouts stay `rsUnMeta`).
- **Change (made).** `preGrown i m w Z` (a condition `Z`: the grown `OsMeta` has `ZeroPg` if `Z`; `GrowMeta` keeps
  `ZfGe`): `Preallocate`/`preallocExtend` post `Z := err = nil ∧ m.ZeroPg`, `preallocExtendTrunc` `Z := err = nil ∧
  m.ZfGe`. `trFile i P` gains `m.ZfGe ∧ (P → m.ZeroPg)` (not unconditional `ZeroPg`, as proposed: a leftover from
  `alloc`'s error path after a `fallocate` that did not land has none). `alloc`'s `ZeroPg` proved; `zerosA_trFile`
  takes `ZfGe` (`filePipeline.run`, from `pipeFile`'s `ZeroPg`).
- **Decision.** Made (`wal-save18`, the coordinator's task 1, `rsCz`; the shape adjusted as above and logged).

## 2026-11-14: `fileutil.CreateDirAll.specTmp` (internal, the part's) -- the `valAfter` clause and `.touch`

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/CreateCallees.lean`, `fileutil.CreateDirAll.specTmp`
  (the success post's `∀ (K : Nat → Prop) (b : GoString), hJ.valAfter J K b = none`, added by the 2026-11-14 entry
  above).
- **Defect.** False, also in the case the entry above took for true (`CreateDirAll` makes the directory):
  `CreateDirAll` runs `TouchDirAll`, whose `IsDirWriteable(J)` writes `J/.touch` and removes it
  (`fileutil.go`), through `J`'s claim (`IsDirWriteable.spec` takes `osNames J (.only [.touch]) 1`), so the returned
  `hJ.ents` hold the create and the remove of `.touch`; with `K` keeping the create's index and not the remove's,
  `hJ.valAfter J K .touch` is the file, not `none`. The clause quantifies over every `K`, and the claim's history
  cannot be dropped, so no proof exists.
- **Evidence.** `NamesH.valAfter` (`GooseLang/Ext/Fs/NamesGhost.lean`: the last kept entry writing `b`);
  `IsDirWriteable.spec`'s post (`LinuxFs/Spec/.../fileutil/IsDirWriteable.lean`). Found proving the inventory's leaf
  specs (`wal-leaf1`, plan §8 "Leaf specs log").
- **Proposed change.** None new: the coordinator's superseding direction in the entry above (limit `hJC` to the
  crashes keeping `J`'s entries, drop the clause from `specTmp`) removes the false clause; this entry is one more
  reason for it (a clause restricted to `b ≠ .touch` would instead need the extension's allocator fact).
- **Decision.** Recorded only (`wal-leaf1`); the restatement is `wal-create17`'s.

## 2026-11-14: `decoder.Decode.spec`/`decodeRecord.spec` (internal, the part's) -- the files left behind are lost

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/decoder__Decode.lean`, `decoder__decodeRecord.lean`,
  through `decPostB` (`LinuxFs/Proof/.../wal/DecDefs.lean`): the record and stop arms give the decoder live over
  `fs.drop k`, the files it has not left.
- **Defect.** Too weak: the `k` files the decoder leaves (`d.brs = d.brs[1:]`, decoder.go's `decodeRecord` at a
  file's end) are dropped from the post with their readers' stream states (`F.S`, for the WAL's segments
  `walFileS`: the open file, its offset and the program's halves of the segment). At `io.EOF` the decoder has left
  every file (`goDecode`'s last-file `.eof` stop returns `[]`), so `ReadAll` (S/wal.go:622-670) cannot `Seek` its
  tail, `ZeroToEnd` it or build the encoder on it, and cannot give the other segments' halves back to the invariant.
- **Evidence.** `decPostB`'s `∃ k, … ownDecoder d IoE eof (fs.drop k) …`; `goDecode_eof_last`; found at `ReadAll`'s
  phase 3 (`wal-readall22`, W3/W5 log, twenty-second session).
- **Proposed change.** `decPostB`'s first arm `∃ k, ([∗list] F ∈ fs.take k, ∃ q, F.S q) ∗ match …`: the left files'
  streams given back (no change to the I/O and `GoFail` arms, whose decoder is dead). Callers: `ReadAll`'s loop keeps
  them (`fs.take kD`).
- **Decision.** Made (`wal-readall22`): no client-visible ghost state (the streams are the caller's own resources,
  lent to the decoder by `NewDecoder`'s spec).

## 2026-11-14: `fileutil.CreateDirAll.specTmp` / `walCreate_osAUnc` (internal, the part's) -- the clause dropped, the commit bound raised

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/CreateCallees.lean` (`specTmp`'s success post);
  `walCreate_osAUnc` (`CreateAu.lean`), `walsNamed_create` (`CreateKeys.lean`), `createFresh_osAUnc`, `createU_none`,
  `createJ_claims` (internal lemmas).
- **Defect.** The two entries above: `specTmp`'s `∀ K b, hJ.valAfter J K b = none` is false (`.touch`), and was there
  only for `walCreate_osAUnc`'s `hJC` over every crash of `J`'s claim.
- **Evidence.** The entries above; `ClaimCoh` (`Cut.lean`: with every entry kept, `valAfter = cur`).
- **Change (made, `wal-create18`, the coordinator's direction).** The clause is dropped from `specTmp` (nothing
  relies on it). `walCreate_osAUnc` takes `osCommitLb m` (a wand argument) with `J`'s entries below `m` (`hJm : ∀ xe
  ∈ hJ.ents, xe.1 < m`) and raises the invariant's commit bound to `max n m` at the commit (`walsOk_mono`,
  `absentNone_mono`, `walsNamed_mono`, the new `dirKeysOk_mono`); `hJC` is now `SegsNamedC lay.segs hJ.cur` (the
  claim's names now), and `walsNamed_create` gets every crash's `J`-names from `ClaimCoh` (each crash the claims
  allow at the raised bound keeps `J`'s entries). `Create` passes `syncDir(nm.tmp)`'s `osCommitLb` at `max
  (J's claim off the segment's name).next (x0 + 1)` (`osNames_next`, `crOut_logLb`), and `createJ_claims` returns
  the entries bound of the claim off the pipeline's names (`ClaimCoh` of the merged claim, `osNames_merge`'s
  `next`) instead of `createJ_val` (deleted).
- **Still open for `specTmp`'s proof** (the `wal-leaf1` finding): a narrower error post, and the existing-directory
  case: it stays, since `Create`'s `RemoveAll(nm.tmp)` returning `nil` gives only `tmpDirH` (`wp_removeAllTmp`,
  `os.RemoveAll.specDirS`), not the name's absence; restricting `specTmp`'s pre to an absent name would need
  `RemoveAll`'s success post to give absence (arguable since the extension's `ENOENT` decision, not made).
- **Decision.** Made (the coordinator's, decided; internal, no client-visible change).

## 2026-11-14: `os.truncSup` / `os.File.Truncate.specAu` (the part's, Lean-first) and `walTailW` -- the caller's property of the start state

- **Spec.** `LinuxFs/Spec/os/File__TruncateAu.lean` (`os.truncSup`, `os.File.Truncate.specAu`); `walTailW`
  (`LinuxFs/Proof/.../wal/Handle.lean`, the handle's tail, internal).
- **Defect.** The truncate at the tail's write position (`cut`'s, `os.File.Truncate.specWalTail`, whose pre is a tail
  that may be in a window) needs `lo ≤ wr` of a window for its first step's crash condition (`crashOkA_rzStart`):
  the crashes of size in `[wr, lo)` are new. The invariant kept it (`WalAbsD.winLo`), but it is false of a write past
  the size from an exact tail (W6 log, twentieth session, finding 1), so the writer past the size could not be
  proved. The supply (`os.truncSup`) quantifies over every state and could not be told the handle's fact.
- **Evidence.** W6 log, twentieth and twenty-first sessions (findings 1 and B); option (A).
- **Change (made, `wal-save22`).** `os.truncSup K p tg P` (`P` defaults to `True`) tells the supply `m0.lo ≤ tg ∨ P
  m0` of each attempt's state; `specAu` takes `P` and `P m` of the state it starts from (every later attempt starts
  from a state an attempt announced or landed, `lo ≤ tg`: `os.announce_lo_le`, `os.rsPost_lo_le`). The four fileutil
  AU specs keep the default (their proofs pass `fun _ => True`). `walTailW`'s pure facts gain `LoWr m (o0 + |out|)`
  (no window open, or `lo ≤` the write position); `walTail_truncSup` takes `P := LoWr · wr`. The invariant's
  window branch (`WinLast`) has `WinHead` in place of `lo ≤ wr` (internal).
- **Decision.** Made (the coordinator's option (A), decided; internal, no client-visible change).

## 2026-11-14: `os.ftDoneH` / `os.ftUndoneH` (the part's, Lean-first) -- the candidates' values past the old size (`TcFrom`)

- **Spec.** `LinuxFs/Spec/os/File__TruncateAu.lean` (`os.ftDoneH`, `os.ftUndoneH`, the caller's halves of a
  truncate's outcome); `TcFrom` (`LinuxFs/Proof/os/TcKnows.lean`).
- **Defect.** The caller learns only which bytes past the size have known candidates (`TcKnows`), not what they
  are, so after `cut`'s truncate the handle cannot know that nothing but zeros is known past `hi` (`PastZ`, W6
  log, twenty-second session), which the writer past the size needs of the bytes it grows over.
- **Evidence.** `rsTail`: past the old size a truncate's outcome knows `m.pc b ++ [(0, n)]` or the announcement's
  `tc` (a subset of `m`'s); the caller cannot see either through its half.
- **Change (made, `wal-save22`).** Both posts' pure fact is `TcKnows … ∧ TcFrom m (max m.size tg) tc rz`: `rz`
  keeps `m.rz`, and each candidate of `tc` from `max size tg` on is one `m.pc` knew or a zero stamped 0 or with a
  stamp of `rz`. Proved for the WAL's supply (`TcFrom.rsTail`) and carried by the retry loop (`TcFrom.trans`);
  consumers (`DefsAu`, `ZeroToEndAu`, `preallocExtendTruncAu`, `TruncWalTail`) take `.1`. `fallocDoneH` unchanged
  (no user needs it yet).
- **Decision.** Made (internal, weaker-or-equal knowledge given to the caller; no client-visible change).

## 2026-11-14: `os.File.Close.specClosed` (the part's, `LinuxFs/Spec/os/File__CloseClosed.lean`) -- the package's initialization

- **Spec.** `os.File.Close.specClosed` (a closed `*os.File`'s `Close`), and `wp_lockedCloseLeft`
  (`CreateLockedLeft.lean`, internal), which calls it.
- **Defect.** Over the closed-file model (`File.Close.impl` returns `&PathError{"close", name, ErrClosed}` on fd -1,
  `wal-create18-closewip`), the result loads `os.ErrClosed`, whose points-to (and the error's `fmtErrorOk`) only
  `isPkgInit pkg_id.os` gives (`os.errClosed_of_pkgInit`); the pre had none, so the spec was unprovable over the new
  model too.
- **Evidence.** The proof attempt (`LinuxFs/Proof/os/File__CloseClosed.lean`); `os.File.Close.specNil`, which returns
  `os.ErrInvalid`, takes the same premise.
- **Change (made, `wal-create19`).** The pre gains `isPkgInit pkg_id.os` (persistent; `Create` has it from `wal`'s
  dependencies, `Hos`); `wp_lockedCloseLeft`'s pre the same. The spec is proved (`os.File.Close.wp_proofClosed`).
- **Decision.** Made (internal, no client-visible change).

## 2026-11-14: `wal.WAL.renameWAL.spec` / `renameWALUnlock.spec` (internal, the part's) -- arm 2 over the handle before naming

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__renameWAL.lean` (`renameWALPost`'s arm 2),
  `WAL__renameWALUnlock.lean`; the "error arms" entry above, its "Not made (arm 2)".
- **Defect.** Arm 2 (`renameWALUnlock`'s retry returned a reopened WAL) was `U (some x) ∗ SpR x ∗ walOpenWF P Mr w'
  dir ∗ walNamed dir ∗ walPurgeW w' dir`: contradictory for `Create` (`createU (some x)`'s `walCreateQ` and the
  handle's `walOpenW` both hold `walLockedTok`) and unprovable (`walNamed` needs the parent's fsync, which
  `Create` does after `renameWAL` returns), and not where arm 1 leads `Create` (a handle it must still name).
- **Evidence.** `Create.wp_proof`'s arm-2 `sorry` (`Create.lean`); `walCreateQ` (`CreateAu.lean`); `walOpenW`
  (`Ghost.lean`).
- **Change (made, `wal-create20`).** The handle before naming, `walOpenWFU P Mr w dir` (`Handle.lean`, sealed):
  `walOpenWF` with `walDirH`'s naming fact a parameter (`nmd`, default `walNamed dir`; `emp` here), the
  registration done (`walNamesFrag none`: `walInv_register` needs no naming, and the retry's `Open` needs the lock
  token back, which needs the registration first). Laws (`HandleUnnamed.lean`): `walOpenWF_unnamed`,
  `walOpenWFU_named` (with `walNamed dir`), `walOpenWFU_dirAcc`. Arm 2 is `∃ x, UH x ∗ walOpenWFU P Mr w' dir ∗
  walPurgeW w' dir`, `UH : Nat × Nat → IProp GF` a new parameter of `renameWALPost`, `renameWAL.spec`,
  `renameWALUnlock.spec`: the caller's residue once the handle holds its share. `Create`'s is `createUH`
  (`CreateRename.lean`: `Q`, the fresh past state, a fraction of the new name's claim with the rename its last
  writer, `osLogLb (x.1 + 1)`, the absent `nm.tmp`'s claim, the area's split record with `nm`), which arm 1
  reaches too; `createSpR` now carries the last-writer fact and the log bound (from `renDirOut`'s `logOut`,
  `lastWrite_log_restrict`). Supersedes the "error arms" entry's suggestion (`walDirH` with `walNamesFrag (some
  dir)`).
- **Obligation.** `renameWALUnlock`'s proof needs a `RenameWALOk` law turning `U (some x) ∗ SpR x` (and what
  `Create` lends through `Sp`: the split record, for the registration) into `UH x` and the reopen's resources
  (`walUnlockedTok` after the registration and `walLockedTok_unlock`): to design with its `Open`/`ReadAll`
  variants (the "(2) Create-specific" entry above).
- **Decision.** Made (internal, no client: `renameWAL` is `Create`'s; the coordinator's task 1, `wal-create20`).

## 2026-11-14: `wal.WAL.SaveSnapshot.specPre` (internal, the part's) -- the indices after the call

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__SaveSnapshotPre.lean`.
- **Defect.** The post returned `walPreIn … snapi' enti'` for some `snapi' enti'`, nothing said of them; `Create`'s
  handle (`walHandleIn`) needs `max enti snapi + 1 < 2^64` of the fields it returns.
- **Evidence.** The pinned `SaveSnapshot` raises `w.enti` and `w.snapi` each to the snapshot's index if below it
  (the translation, `WAL.SaveSnapshot.impl`). `Create.wp_proof`'s arm 1 (`wal-create21`).
- **Change (made, `wal-create21`).** The post adds `⌜(snapi' = snapi ∨ snapi' = sm.Index') ∧ (enti' = enti ∨
  enti' = sm.Index')⌝` (every arm); the proof unchanged but for the fact.
- **Decision.** Made (internal; strengthening a post).

## 2026-11-14: `walCreateQ` / `walDirH` (internal, the part's) -- the tail registered at the commit; the tail's name

- **Definitions.** `walCreateQ` (`CreateAu.lean`), `walDirH` (`Handle.lean`).
- **Defect.** (1) `walCreateQ`'s committed arm gave `walTailsFrag ∅`, the handle to register its tail later. A
  later registration (`walTailsRes_register`, inside `walInv`) finds the invariant's history and layout only up to
  `WalAbsD` (no step after the commit pins them to the fresh WAL's), while the handle's encoder CRC and file offset
  are the fresh WAL's: the tail record's `H`/`md`/`cuts`/`wr` could not be shown to match. (2) `walDirH` asked the
  tail file's name to be `child dir nm0`; `Create`'s segment was opened as `dir.tmp/0000…0000.wal`, and Go's
  `f.Name()` keeps that path after the rename.
- **Change (made, `wal-create21`).** (1) The commit registers the tail (`walTailsRes_register` on the new layout,
  `createLay_tailBound` its record boundary): `walCreateQ`'s committed arm holds `walTailReg dir t` (the holder's
  half of the tails' authority `{dir ↦ γ}`, the key, the tail record's half `t`), `t` a new parameter
  (`createTailG Mr md jr nm J g` from `createU`). (2) `walDirH`'s name fact is `∃ pd, name = child pd nm0` (`cut`'s
  `w.seq()` reads only the base, `baseModel_child_walFileName`).
- **Obligation.** `renameWALUnlock`'s `RenameWALOk` law (the retry's `w.Close()` and the reopen) now unregisters the
  tail too (`walTails_unregister`, `Close`'s).
- **Decision.** Made (internal, no client-visible change).
## 2026-11-14: `pbutil.MustMarshalMessage.specWalSnap` (internal, the part's) -- the size premise

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/pkg/v3/pbutil/MustMarshalMessageWalSnap.lean`.
- **Defect.** No bound on the encoding's size: `proto.Marshal` allocates it, and an allocation above Go's
  `maxAlloc` panics (`proto.MarshalPb.spec`'s premise `size c < 2 ^ 48`); `walSnapAt` bounds nothing, so the
  triple is unprovable over the part's `MarshalPb.spec`.
- **Evidence.** The proof (`wal-leaf3`): `wp_Marshal pbSnapC pbSnapC_reg sp c trivial ?_` has no argument.
- **Change (made, `wal-leaf3`).** The premise `(Mr.encSnap sm).length < 2 ^ 48`. Both callers have it:
  `SaveSnapshot.spec`'s pre gives `< 2 ^ 40`; `SaveSnapshot.specPre`'s frame bound `≤ lim < 2 ^ 47` (the record's
  data within its encoding, `recSize`). The non-nil result is derived (the encoding is non-empty, `Index` set:
  `snapEnc_ne_of_index`), not assumed.
- **Decision.** Made (internal, minimal, no client-visible change).

## 2026-11-14: `pbutil.MustUnmarshalMessage.specWalSnap` (internal, the part's) -- `U` says nothing of protobuf-go (proposed, not made)

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/ReadAllCallees.lean`.
- **Defect.** (1) The premise `U.decSnap bs = some s` is about the client's parameter `U : WalUnmarshal`, which no
  hypothesis ties to protobuf-go (`WalUnmarshal.Ok` ties it to `Mr` only): `bs` need not be any snapshot's
  encoding, `proto.Unmarshal` may fail (the code panics) and the decoded index/term need not be `s`. (2) The pre
  lacks `isPkgInit pbutil` (the call to `proto.Unmarshal` needs `proto`'s, which comes from it).
- **Evidence.** `proto.UnmarshalPb.spec` (part copy) at `pbSnapC`: success only when `bs = snapEnc c₀` for a
  `c₀` with valid unknown fields; the decoded content is `c₀` only then.
- **Proposed change.** A premise on `U` (a `ReadAll` hypothesis the client discharges for its codec, as
  `walSnapAt` ties `Mr` to `snapEnc`): `∀ bs s, U.decSnap bs = some s → ∃ c : WalSnapC, (∀ p ∈ c.levels,
  ufWire p.1 p.2) ∧ bs = snapEnc c ∧ (c.model.Index', c.model.Term') = s`, and `isPkgInit pbutil` in the pre.
  Then the proof is `MustUnmarshalMessagePb.wp_proof`'s over the part's `UnmarshalPb.spec`, with
  `snapOwnC_freeze` for the read-only snapshot.
- **Decision.** Open: it adds an obligation to `ReadAll`'s callers (`U`'s coherence with protobuf-go), the
  coordinator's call. **Adopted** (the coordinator, decided; made on `wal-leaf4`): the law is
  `WalEnc.WalUnmarshal.SnapCoh U` (`ReadAllCallees.lean`, a pure `def`, for C6 to discharge with the client's
  codec), a premise of `specWalSnap U` itself (`U.SnapCoh → ∀ sp d dq bs s, …`), and `isPkgInit pbutil` in the
  pre. Proved (`MustUnmarshalMessage.wp_proofWalSnap`). `WAL.ReadAll.wp_proof` takes `hUs : U.SnapCoh` next to
  `hU : U.Ok Mr`. (A canonical-only `U`, one decoding exactly the `snapEnc` images, satisfies both `Ok` and
  `SnapCoh` when `Mr.encSnap` is `snapEnc` of a valid content, as `walSnapAt` already requires.)

## 2026-11-14: `fileutil.CreateDirAll.specTmp` (internal, the part's) -- the commit bound on an existing directory

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/CreateCallees.lean`, `specTmp`'s success post
  (`h'.next ≤ n ∧ … ∗ osCommitLb n`: every entry that wrote `name` committed).
- **Defect.** False when `name` already holds a directory (the case `specTmp` adds): `TouchDirAll` (the fork's,
  F-N2) syncs `name`'s parent only in its `Exist` branch and, in the other, for each directory its climbing loop
  collected (`created`). `Exist(d)` is `Stat(d) == nil`, and `Stat` of an existing directory may fail (any errno:
  `os.Stat.wp_dirS`, the extension's environmental failure); after such a failure the loop's `Exist(d)` may
  succeed, so `created = []`, `MkdirAll` returns `nil` on the directory, nothing is synced, and `CreateDirAll`
  returns `nil` with `name`'s entries possibly uncommitted (the leftover `nm.tmp`'s `mkdir` from earlier in the
  generation). No premise `Create` can give rules it out (its `RemoveAll(nm.tmp)` leaves `tmpDirH` of any history).
- **Evidence.** The translation of `TouchDirAll` (`LinuxFs/Code/.../fileutil.lean`, fileutil.go:49); found
  designing `specTmp`'s existing-directory proof (`wal-leaf4`). Recorded as a durability gap of the fork's F-N2
  patch: `nonissues/etcd-fork-touchdirall-stat-error-no-parent-sync.md`.
- **Change (made, `wal-leaf4`).** The success post drops `h'.next ≤ n` and `osCommitLb n` (`∃ h' hJ J, ⌜h'.cur !!
  name = some (.dir J) ∧ hJ.cur = ∅⌝ ∗ …`). `Create` never used them (since `wal-create18` its commit bound comes
  from `syncDir(nm.tmp)` and the later parent fsync); its pattern loses `%n0`/`#Hcm0` and `hJs.2.2` becomes `hJs.2`.
- **Decision.** Made (internal, weaker post nobody used; no client-visible change).

## 2026-11-14: `fileutil.CreateDirAll.specTmp` (internal, the part's) -- a leftover `.touch` needs its file

- **Spec.** `specTmp`'s pre (`tmpDirH jp name h`: `name` holding nothing or a directory of files, the claims
  whole) and `tmpSub` (`CreateCallees.lean`).
- **Defect.** Too weak for the existing-directory case: the directory may hold a leftover `.touch` (a crash, or an
  error, between `IsDirWriteable`'s create and remove), and `IsDirWriteable`'s `os.WriteFile(dir/.touch, "",
  O_TRUNC)` then truncates that file, a step on its `OsMeta` and bytes (`os.OpenFile.wp_truncS` takes `trFile i
  False`). `tmpSub` holds only claims (names), no file's `OsMeta`; neither does any producer of `tmpDirH`
  (`walAreaRes`'s `TmpOk`, `os.RemoveAll.specDirS`'s `rmAllOut`, `TouchDirAll`'s error arms: `specEmptyS` drops the
  probe's `trFile`). So the case is unprovable: nobody owns the file the truncation changes.
- **Evidence.** `IsDirWriteable.specFile` (`wal-leaf4`, proved) needs `trFile i False` of `.touch`'s file;
  `walAreaRes` (`CreateDefs.lean`); `rmAllOut` (`Spec/os/RemoveAll.lean`).
- **Proposed change.** `tmpSub`'s directory arm also holds each file whole: `∃ hJ, ⌜FilesOnly hJ.cur⌝ ∗ osNames J
  (.except []) 1 hJ ∗ [∗map] c ↦ n ∈ hJ.cur, (∃ i, ⌜n = .file i⌝ ∗ trFile i False)` (or only `.touch`'s). Its
  producers then give the files: `RemoveAll.specDirS` (its pre's files, minus the unlinked ones), `TouchDirAll`'s
  error arms (`os.WriteFile.specEmptyS` returning the probe's `trFile`), and `walAreaRes`'s `TmpOk` for a leftover
  from before a crash (the crash rebuild's file ownership: the deep part). Alternatively restrict `specTmp` to a
  directory with no `.touch` (`Create` cannot show it).
- **Decision.** Open: the coordinator's call (the change reaches `walAreaRes` and the crash rebuild).
  **Adopted** (the coordinator, decided; made on `wal-leaf5`), in its "only `.touch`'s" form: `tmpSub`'s
  directory arm holds `WalFs.tmpEnt (hJ.cur !! .touch)` (nothing, or the file whole, `trFile i False`;
  never a directory). Only `.touch`'s file, because it is the one a callee changes (the probe's
  truncation); the other files of a temporary directory are only unlinked (`RemoveAll.specDirS`, which
  takes no file), and holding them all whole would make `Create`'s unminting give back the new WAL's
  first segment as a `trFile` (`walCreateP` holds its `OsMeta` and bytes but not `trFile`'s facts:
  `ZfGe`, `cut = none` after the writes), for no consumer. Producers: `walAreaRes` (`areaCls`: each
  tagged claim with `tmpClTouch`, the `.touch` of a whole claim under a WAL name's `nm.tmp`;
  `area_takeTmp`/`area_give`), `RemoveAll`'s wrapper (`rmAllOut_tmpDirH`: the file if `.touch` is still
  there), `TouchDirAll`'s error arms (`IsDirWriteable.spec`'s error post now gives the probe's file back,
  over `os.WriteFile.specEmptyS`'s `crTr False o`), `Create`'s exits (the directory has no `.touch`:
  `segClaim_back`, `create_Jback` keep the fact), and at boot the crash's `osFileStart`
  (`osFileStart_trFile`, `Crash.lean`; the area's establishment is C6's).

## 2026-11-14: `decoder.Decode.spec`/`proto.UnmarshalWalRecord.spec` (internal, the part's) -- an empty metadata read back as `nil`

- **Spec.** `LinuxFs/Spec/google_golang_org/protobuf/proto/UnmarshalWalRecord.lean` (its success is `ownRec l r`,
  `walpb/Defs.lean`), and through it `decoder.decodeRecord.spec`/`Decode.spec` (`decPost`); `walHandleIn`'s
  `recBytes mds (some h.md)` (`Handle.lean`), which `ReadAll` must establish for the slice it read
  (`wal-readall26`, obligation (c) of `walOpenWF`).
- **Defect.** `ownRec` says `v.Data' ↦* r.data` only: with an empty metadata (`d.metadata = []`) the slice the
  loop keeps (`metadata = rec.Data`, S/wal.go) may be `nil` for all the spec says, and then the handle's `cut`
  would write a metadata record without the data field (`Record{Data: nil}`), not the model's `recOf` bytes (the
  field present, empty), so `walHandleIn`'s `recBytes … (some md)` (`ds ≠ nil`) is unprovable. Not a Go bug:
  protobuf-go decodes a present bytes field to a non-nil slice (`internal/impl/codec_gen.go`, `consumeBytes`:
  `*p.Bytes() = append(emptyBuf[:], v...)`), and `TestRecordEncoder` measured `proto.Unmarshal(recEnc c)` giving
  back exactly `c`, `Data`'s presence included. The specs drop it: `proto.UnmarshalPb.spec` gives the exact
  content (`c = c₀` when `bs = pbEncC I c₀`), `UnmarshalWalRecord.wp_proof` forgets it (`recOwnC_ownRec`).
  With a non-empty metadata the slice is non-nil from its points-to (its length), so only `[]` is affected.
- **Evidence.** The proof of `ReadAll`'s success arm (`ReadAllWFPure.lean`: `readAll_md_some` gives `st.md = some
  md`, not the slice's non-nilness); `Create.spec` takes the metadata non-nil but may take `[]`; `walInv_alloc`
  admits a WAL found at boot with any metadata below `2 ^ 41`.
- **Proposed change.** Either (A, no client change) the decoder keeps the content's presence: `ownRec l r`
  gains `⌜∀ r₀, bs = walRecEnc r₀ → (recOf r₀).data.isSome → v.Data' ≠ slice.nil⌝` over the frame's bytes
  `bs` (from `UnmarshalPb`'s exactness), carried by `decodeRecord`/`Decode` and the reader's model (`goDecode`'s
  accepted frames are the encoder's for the WAL's files, `walReadFiles_running` at the byte level); or (B) the
  metadata non-empty: `Create.spec` takes `md ≠ []` (the server's is a marshalled `etcdserverpb.Metadata` with
  both ids set, never empty) and `WalsBounded` carries `0 < |d.metadata|` (and `walInv_alloc` takes it of the
  WALs found at boot), so the slice's length gives `≠ nil`. (B) is a few lines; (A) is the faithful one.
- **Decision.** Open: (B) adds a client premise to `Create` and an assumption on the WALs found at boot; the
  coordinator's call. Until then `ReadAll`'s `walOpenWF` takes it as a marked `sorry` (`hmdnn`).
  **Decided 2026-11-14 (coordinator; `wal-readall27`): (B).** The coordinator's first choice, relaxing
  `walHandleIn` to accept a `nil` slice at `md = []`, is not sound: `cut` encodes `Record{Type: …, Data:
  w.metadata}` as is (S/wal.go:842) and `record.proto`'s `data` is a proto2 `optional bytes`, so protobuf-go
  omits the field for a `nil` slice and writes it, empty, for `[]byte{}` (`recEnc`'s `optBytesField`, measured by
  `TestRecordEncoder`); a handle with a `nil` metadata would write a metadata record other than the model's
  `walRecEnc (recOf ⟨metadataType, _, []⟩)` (the field present), which the segments' byte model (`tailStream`,
  `WalAbsD`'s streams, the reader) fixes. Accepting it would need that model to admit both encodings of an empty
  metadata record, or (A). Made: `Create.spec` takes `md ≠ []` (beside `mp ≠ nil`; the server's metadata is a
  marshalled `etcdserverpb.Metadata` with both ids set); `WalsBounded` keeps `d.metadata ≠ []` (`Create`'s
  commit from the premise; no other step changes a metadata; `walInv_alloc`'s caller for the WALs at boot,
  none at the run's start); `ReadAll` gets the slice non-nil from its points-to's length.

## 2026-11-14: `walHandleIn`'s index bound (internal, the part's) -- `ReadAll` cannot bound `max(enti, snapi) + 1`

- **Spec.** `walHandleIn`'s `max (uint.nat h.enti) (uint.nat h.snapi) + 1 < 2 ^ 64` (`Handle.lean`), which
  `ReadAll` must establish (`wal-readall26`, obligation (d) of `walOpenWF`).
- **Defect.** `w.enti`/`w.snapi` after the loop are indices read from the WAL; nothing bounds them below
  `2 ^ 64 - 1`: `Save`/`SaveSnapshot` take `< 2 ^ 64 - 1` of what they write (their premises), but the
  invariant does not record it, so a WAL read back (or found at boot) may hold index `2 ^ 64 - 1` for all
  `ReadAll` knows, and `cut` would then name its next segment with a wrapped index.
- **Evidence.** `WalsBounded` (`Inv.lean`) bounds only the metadata; `WalAbsD.nameBound` bounds the indices
  before each segment by its name's `ix < 2 ^ 64`, not those of the last segment.
- **Proposed change.** An invariant fact, framed as `WalsBounded` (or a conjunct of it): `∀ dir d, s.wal !! dir
  = some d → ¬ walHasMaxIdx (histM d)`; kept by `Save`/`SaveSnapshot` from their premises, by `Create` (index 0),
  by crashes and cuts (histories' prefixes / unchanged), taken by `walInv_alloc` of the WALs found at boot. No
  client-visible change but the boot assumption.
- **Decision.** Open (an invariant change touching `Save`'s commit steps, which `wal-save*` owns): the
  coordinator's call. Until then `ReadAll`'s `walOpenWF` takes it as a marked `sorry`.
  **Decided 2026-11-14 (coordinator; `wal-readall27`): as proposed**, as a conjunct of `WalsBounded`
  (`¬ walHasMaxIdx (histM d)`): `walInvBody_append` (and `walTail_append`, `walHandleIn_append`) take
  `¬ walHasMaxIdx [o.toM]` of the appended operation, which `Save` and `SaveSnapshot` give from their index
  premises; `Create` starts empty; the other steps keep the history. `ReadAll` bounds `max(enti, snapi) + 1`
  by it (`readAll_idxD`: every index the loop writes is one of the history's, or 0).

## 2026-11-14: `walDirH`'s sequence bound (internal, the part's) -- `ReadAll` cannot bound the tail's sequence

- **Spec.** `walDirH`'s `∃ sq ix, nm0 = walFileName sq ix ∧ sq < 2 ^ 63 + k` (`Handle.lean`), `k` the files
  the handle's pipeline handed over (0 at `ReadAll`), which `ReadAll` must establish for the tail's name
  (`wal-readall26`, obligation (f) of `walOpenWF`).
- **Defect.** Nothing bounds a read-back tail's sequence: `WalAbsD.nameBound` gives the name's form and
  `ix < 2 ^ 64`, not `sq`. `Create` starts at 0 and each `cut` adds one under the handle's receipt bound
  (`walPc_bound`), but receipts do not survive a crash, so across generations the sequence is bounded by
  nothing the invariant keeps (a WAL found at boot, or cut `2 ^ 62` times per generation over two
  generations, may hold `sq ≥ 2 ^ 63`). Then `cut`'s `seq + 1` could wrap (`w.seq()` is a `uint64`).
- **Evidence.** The assembly of `walOpenWF` in `ReadAll` (`wal-readall26`).
- **Proposed change.** Either an invariant fact (every `.wal` segment's sequence `< 2 ^ 63`, kept by `cut`
  with a premise `sq + 1 < 2 ^ 63` that its caller takes from a bound the invariant then must keep: no
  natural source) or, simpler, `walDirH`'s bound weakened to what `cut` needs, `sq + k < 2 ^ 64 - 1`-style
  against `uint64` wrap, with the tail's `sq < 2 ^ 64` from the name's 16 hex digits and the remaining room
  as a premise on `ReadAll` (the same shape as the index bound above: `sq < 2 ^ 63` of the tail an
  assumption on the WALs found at boot, kept by `cut` only while receipts bound it). Needs the coordinator's
  design: no option is free.
- **Decision.** Open: the coordinator's call. Until then `ReadAll`'s `walOpenWF` takes it as a marked `sorry`.
  **2026-11-14 (`wal-readall27`): the coordinator chose a receipts budget; designed, not made.** The sketch (a boot
  premise `sq < 2^63` on `walInv_alloc`, each cut consuming an exclusive receipt) does not close across generations
  (the handle's `⧗` vanish at a crash; the next boot's premise is not implied). Design (`notes/bounds-plan.md`, "The
  WAL's segment sequence"): crash-stable persistent receipts `⧖` of the global step counter, `WalAbsD.nameBound` with
  sequence `first + k`, the invariant holding `⧖ |lay.cuts|` per WAL (deposited by `cut` after a counted step), or `⧖
  |d.H|` (deposited at `Save`'s commit; a crash keeps a prefix). No statement of `walDirH` changes. `ReadAll`'s `hsq`
  stays a marked `sorry` until it is made.
  **2026-11-14 (`wal-readall28`): made, the alternative** (`⧖` of every history's length in the invariant's ghost
  state, `walStepsLb`; `WalAbsD.seqName`; `notes/bounds-plan.md`, "Made"). No client-visible statement changed; the
  `sorry` is gone.

## 2026-11-14: the resize supplies' `P` (internal, the part's) -- a growth's supply cannot bound the crash size

- **Spec.** `os.truncSup K p tg P` (`LinuxFs/Spec/os/File__TruncateAu.lean`) told `m0.lo ≤ tg ∨ P m0`;
  `fallocSup K i tg` (`Proof/syscall/FallocateAu.lean`) told only `m0.size ≤ tg`; `preallocExtend(Trunc).specAu`,
  `Preallocate.specAu`, `ZeroToEnd.specAu` passing supplies with the default `P`.
- **Defect.** The WAL's growth supplies (`ZeroToEnd`'s growth of the lent tail back to its size, `wal-tc19`)
  need `min lo tg ≤ wr` of the state they start from (`rzGrow_pure`: the growth's crash sizes from `lo` on are
  the window's), and the truncate's also `size ≤ tg`; `lo ≤ tg` (the old second disjunct) is too weak for a
  growth (`tg` the size), and the default `P` says nothing. The supplies see only the state's `OsMeta`.
- **Evidence.** `walTail_fallocSup`/`walTail_truncSupG` (`GrowSup.lean`).
- **Change (made, `wal-tc19`).** `os.truncSup` told `⌜P m0⌝`; `os.File.Truncate.specAu` takes `P m` and `∀ m',
  m'.lo ≤ min m.lo sz → m'.size ≤ max m.size sz → P m'` (every later attempt starts from an announced or landed
  state, `lo := min lo tg`); `fallocSup … P` told `⌜P m0⌝`; `preGrownH` carries `m'.lo ≤ m.lo`; the
  `preallocExtend(Trunc)`/`Preallocate` specAu take `P` with `∀ m', m'.lo ≤ m.lo → m'.size ≤ sz → P m'`;
  `ZeroToEnd.specAu` takes `P` (the truncate to `o`) and `Q` (the growth) with `P m` and `∀ m', m'.lo ≤ min m.lo
  o → m'.size ≤ m.size → P m' ∧ Q m'`, and its success post gains `m'.lo ≤ min m.lo o` (the handle's `LoWr`).
  The WAL passes `LoWr · wr` (truncate, as before) and `lo ≤ wr ∧ size ≤ tg` (growth). Lean-first specs,
  proved; no trusted change.
- **Decision.** Made (internal; the only instances are the WAL's).

## 2026-11-14: `ZeroToEnd.specWalTail` and `TailMetaZ` (internal, the part's)

- **Spec.** `ZeroToEnd.specWalTail` (`ReadAllTailCallees.lean`, a hypothesis of `WAL.ReadAll.wp_proof`):
  post `TailMetaZ` (`TailMetaW` without `PastZ`, so `TailZ` of the zeroed tail); pre without `isPkgInit errors`.
- **Defect.** `TailZ` of the zeroed tail is not provable: a crashed tail (`initMeta`: `zf = pageEnd size`,
  `cz = 0`) or a synced one need not know the candidates of its last page past the size, and `ZeroToEnd`
  (`ZteMeta`) does not make them known; what the fdatasync after it needs is only the page cache known zero to
  the end of the size's page (`TailZ.synced_of`), which `ZeroToEnd.specAu` gives. `ZeroToEnd.specAu` needs
  `isPkgInit errors`.
- **Change (made, `wal-tc19`).** `TailMetaZ m bs := |bs| = size ∧ maps = ∅ ∧ pageEnd size ≤ max size cz`;
  `specWalTail`'s pre gains `isPkgInit errors` (`ReadAll`: `iPkgInit`, adapted), its post `sz' = sz`. Proved:
  `ZeroToEnd.wp_specWalTail` (`ZteWalTail.lean`, over `ZeroToEnd.specAu`).
- **Decision.** Made (internal).

## 2026-11-14: `wal.Create.spec` (the part's) -- the success arm is false when the parent's fsync fails and its close succeeds

- **Spec.** `wal.Create.spec`'s first arm: `err = nil` gives `walOpenWF P Mr w dir`, `walNamed dir`, `Q`, ...
- **Defect.** Not the spec's: the code's. After a failed `fileutil.Fsync(pdir)`, `Create` calls `dirCloser()`,
  which assigns `pdir.Close()`'s result to `perr`; a successful close makes `Create` return `(nil, nil)` and skip
  its deferred `cleanupWAL`. Over `fsExt` the fsync may fail (`Fsync.specDirS`) and the close succeed, so no
  spec with an honest success arm holds (`nonissues/etcd-wal-create-parent-fsync-nil-nil.md`; etcd's
  `bootstrapNewWAL` would dereference the nil WAL).
- **Evidence.** The continuation after `renameWAL` (`wal-create22`).
- **Proposed change.** None to the spec: the fork fix `notes/wal-fsext-fork/0005-...diff` (`pdir.Close()` on
  that path), then retranslate; the spec stays as it is.
- **Decision.** Pending the user (a fork change). Until then `Create.wp_proof` keeps a marked `sorry` on that
  path only.

## 2026-11-14: `wal.Repair.spec` (the part's, over `fsExt`) -- the `false` arm after a failed `Truncate` or `Fsync` cannot return the lock token

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Repair.lean` (`wal.Repair.spec`): every arm's post
  returns `walUnlockedTok` (framed, the entry "the lock token taken" above).
- **Defect.** Unprovable on two of the `false` arms. `walUnlockedTok`'s `walTailsFrag ∅` makes `Repair` unregister
  the tail it registered (the pending token, kind `true`, for its truncate at `wr`), which needs the tail idle
  (`WalTailIdle`: exact). After a failed `f.Truncate(lastOffset)` (`os.ftUndoneH`: the truncate's window open,
  `lo = wr`) or a failed `fileutil.Fsync(f.File)` after it (the window open, landed or not), the Go code returns
  `false` with no sync, and nothing the program can do closes the window. The state is crash-safe
  (`crashOkA_tailRep`: the window of a `RepOld` tail); only the unregistration fails.
- **Evidence.** The W7-W12 log, twelfth session ("Finding", option (b)); S/repair.go:83-97. Every client stops
  on `false`: the WAL tester's `restartRead` returns `readFail` (examples/etcd/wal/wal.go:200-202), etcd's
  `openWALFromSnapshot` calls `lg.Fatal` (server/etcdserver/bootstrap.go). Plan §6 Q6 (honest error posts: a
  client stops on these errors; `Sync`'s error arm already loses the handle).
- **Proposed change.** The post's token becomes `walUnlockedTok ∨ ⌜b = false⌝`: on `true` the token comes back;
  on `false` it may not (the proof returns it on every `false` arm but the two above). Nothing else moves
  (`∃ o, Q o`, the area's resources and the call permission are returned on every arm). The tester's proof
  (`restartRead`) uses `Repair`'s token only on `true` (the retried `Open`).
- **Decision.** Accepted (the coordinator, under plan §6 Q6, 2026-11-14: option (b) of the twelfth session's
  finding); applied by `wal-repair24` (the W7-W12 log, thirteenth session).

## 2026-11-14: `wal.WAL.sync.specC` (internal, the part's) -- the error arm keeps the lock token; `WAL.Close.specU`

- **Spec.** `WAL.sync.specC`'s error arm `⌜err ≠ nil⌝` (the handle and the lock token lost).
- **Defect.** `Create`'s cleanup (`cleanupWAL` after a committed rename whose parent fsync failed) runs `w.Close()`;
  when its `sync` fails, `Close` returns before unlocking, and `Create` must still merge `nm.tmp`'s claim back to
  the area (`create_areaBack`, which needs a token excluding the free one): `walLockedTok`, which the failed
  `sync` still holds (`walOpenW`: its flush failure leaves it, the fdatasync returns the pending-cut flag).
- **Evidence.** `cleanupWAL`'s design (W4 log, twenty-fourth session, (b)); `wal-create23`.
- **Change (made, `wal-create23`).** `sync.wp_core`'s error arm returns `walOpenW w dir`; `specC`'s error arm
  `⌜err ≠ nil⌝ ∗ walLockedTok` (`walOpenW_lockedTok`); `sync.spec`/`specCut` unchanged (they drop it). New:
  `WAL.Close.specU` (the cleanup's `Close`: over `walOpenWFU`, no update, the commit-free put-back
  `walCloseLawU`), post `(walUnlockedTok ∗ osCallPerm 1) ∨ (⌜err ≠ nil⌝ ∗ walLockedTok)` (the left arm whatever
  `err`: the directory's close failed after everything else).
- *Obligation, not made*: `Create`'s deferred `f.Close()` after the cleanup needs the segment's lock file: closed
  (`os.ownFile f (-1)`) when `Close` succeeded, open when its `sync` failed. Both need the handle's tail lock to be
  `Create`'s `f` (`walOpenWFU` hides it: a parameter `lt`, from a copy of `walHandleIn` with `lt` free), and the
  failed arm needs the tail file back from `sync`'s error arms (through `wp_tailWriteAtW`, `wp_tailWriteW`,
  `wal.tailWriterW`'s `B`, `flush`), and `renameWALPost`'s arm 2 must return `walLockLeft f …` (the retry's
  `w.Close()` closed it, or its `sync` failed and left it open).
- **Decision.** Made (internal).

## 2026-11-14: `time.Time.Format.spec` (trusted, an axiom) -- its result unconstrained; `cleanupWAL`'s rename

- **Spec.** `time.Time.Format.spec` (`Spec/time/Time__Format.lean`, axiom `Proof/time/Time__Format.lean`): post `True`.
- **Defect.** `cleanupWAL` renames the WAL to `fmt.Sprintf("%s.broken.%v", w.dir, time.Now().Format("20060102.150405.999999"))`;
  with nothing known of the timestamp the target may hold `/` (a path under some other directory) or be any length,
  and no `os.Rename` spec (nor ownership) covers an arbitrary target.
- **Evidence.** `cleanupWAL`'s proof (`wal-create23`; W4 log, twenty-fifth session).
- **Proposed change.** A spec of `Format` for that layout: the result's characters are digits and `.`, its length at
  most 22 (Go's layout: `yyyymmdd.hhmmss` and a fraction of up to six digits, trailing zeros and a bare `.` dropped).
  Until then `cleanupWAL`'s proof takes it as a callee hypothesis. Separately an `os.Rename` spec over `fsExt` for a
  target name past 255 bytes (`ENAMETOOLONG`, nothing changed).
- **Decision.** Pending the user (a trust-boundary change).

## 2026-11-14: `os.File.WriteAt.specLong` (the part's) -- the failure arm's `OsMeta` and page cut are false past 1 GiB

- **Spec.** `LinuxFs/Spec/os/WriteLong.lean`, `os.File.WriteAt.specLong` (no `SpecPlan` counterpart); its
  callers' error posts restate it: `os.File.Write.wp_long` (`LinuxFs/Proof/os/OffLong.lean`) and `os.fileB`
  (`LinuxFs/Proof/os/WriterStream.lean`).
- **Defect.** Unprovable past `maxRW` (1 GiB), failure arm. (1) The `OsMeta` `pwPost m off A j`: an attempt
  that lands its whole chunk `[nn, E)` raises `cz` to `pageEnd (off + E)` (`pwCz`, when the zeros known start
  at or below `off + E`); if a later chunk is then announced (`A > E`) and the write fails before reaching `A`,
  the file's `cz` keeps that raise, but `pwPost m off A j`'s is `m.cz` (`j ≠ A`), and no other `A`, `j` gives
  the announcement (dirty range, `zf`, `tc`, `hi`) the later chunk made. (2) `PwCut off len j`: a whole chunk
  of `2^30` bytes from an offset off a page boundary lands and the next attempt fails with nothing written:
  `j = 2^30`, `off + j` is not on a page boundary.
- **Evidence.** The Löb step of `os.File.WriteAt.wp_proof_long` (`LinuxFs/Proof/os/WriteLong.lean`): the
  `cz` of `pwPost (pwPost m off A A) (off + A) c 0` is `pwCz m off A A`, not `pwCz m off (A + c) A = m.cz`;
  the page cut: `PWriteFinish`'s `PwCut (off + nn) c k` with `k = c` says nothing of `off + nn + c`'s page.
- **Proposed change.** The post gains the end `E` of the last chunk that landed whole (`E ≤ j`, `j = A → E = A`;
  `0` if none): the `OsMeta` is `os.pwPostE m off A j E` (`pwPost m off A j` with `cz := pwCz m off E E`), the
  cut `os.PwCutE off len j E` (`PwCut off len j`, or `j = E` within `maxBytes`). Up to `maxRW` (`E = 0` or
  `E = j = A`) and on success (`E = j = A = len`) both are `pwPost`'s and `PwCut`, definitionally or by a
  lemma; the callers' error posts take the same change (both callers drop that arm's resources).
- **Decision.** Made (internal to the part: only the failure arm of a write past 1 GiB moves; no client-visible
  ghost state; the success arm unchanged). `wal-wlong1`.
## 2026-11-14: `wal.ValidSnapshotEntries.spec` (the part's, W8) -- restated over `fsExt`

- **Spec.** The main tree's axiom `Spec/.../wal/ValidSnapshotEntries.lean` (`walUnlockedTok` framed, the AU over
  `walDirIs` unchanged, success `walSnapsAt ps (walValidSnaps (d.H.map toM) d.cut)`), restated over `fsExt`:
  `LinuxFs/Spec/.../wal/ValidSnapshotEntries.lean`.
- **Defect.** None of the main tree's statement: only plan §3's binders change (`walAreaOk walCodec Mr`, the
  area's spine `osPathS R r qp jr` and `walAreaRes jr` framed, `osCallPerm 1` framed, the update at
  `walAuMask`; premises `InArea r dir nm`, `NameOk nm`, `cleanAbsPath r`, `dir.length < 2^59`), as `Repair`'s
  and `OpenForRead`'s, which read the same directory the same way.
- **Evidence.** `Repair.spec`, `OpenForRead.spec` (the same binders); S/wal.go:698-791.
- **Change (made, `wal-vsnap1`).** The restated spec; the update commits unchanged where the proof pins the
  segments (before the retry loop: every attempt reads the same pinned files, so the retry needs no second
  commit).
- **Decision.** Made (the restatement plan §3 prescribes).

## 2026-11-14: `decoder.Decode.spec` (the part's) -- no `errors.Is(err, io.ErrUnexpectedEOF)` answer on an I/O error

- **Spec.** `decPost`'s I/O arm (`⌜IoE err⌝`, `DecDefs.lean`) and `decAns` (only `errors.Is(err, io.EOF)`).
- **Defect.** Too weak for read mode's callers: `validSnapshotEntries` (W8) and `ReadAll` in read mode accept
  `errors.Is(err, io.ErrUnexpectedEOF)` as the end; on an `IoE` error the proof knows no answer, so a `true` would
  make a partial read a success. In Go the readers' errors are `*PathError`s of an errno, for which it is `false`.
- **Evidence.** S/wal.go:772-776 (VSE's exit test); `ReadBridge.lean` (the readers' errors are `errnoPathErr`).
- **Proposed change.** Carry the `io.ErrUnexpectedEOF` answer as the `io.EOF` one: `decRdE` and `decAns` gain
  `isEofAns e ueof` (with `e ≠ ueof` for an `IoE` error, as `¬ IoE eof`), `walDecFiles_mk` proves it from an
  `errors.IsPathErrnoEof`-style spec for `ueof`.
- **Decision.** Pending (internal; `validSnapshotEntries.specPinned` stays a hypothesis of VSE until it is made).
  **2026-11-14 (`wal-vsnap2`): adopted, refined.** A general `decide (e = ueof)` answer is false of `Decode`'s
  own errors (a `fmt.Errorf("%w ...", io.ErrUnexpectedEOF)` is not `ueof` but `errors.Is` finds it), so the
  answer is carried only on the I/O errors, which are the ones `Decode` passes on: `notUeof e` (`errors.Is(e,
  io.ErrUnexpectedEOF)` returns `false`, for the value the global holds; no new parameter), `ioUeof IoE e`
  (`e` nil or not `IoE`, or `notUeof e`) in `decRdE` and in `decFile`'s and `ownFbr`'s `FileInfo` result,
  and `notUeof err` in `decPostB`'s I/O arm. The readers' evidence: `errors.IsPathErrnoEof.spec` (a
  hypothesis) now also covers `io.ErrUnexpectedEOF`'s value (the same argument: a fifth `errors.New`
  allocation), `walPathErr_ueof` (`ReadBridge.lean`).

## 2026-11-14: `openWALFiles.spec` (internal, the part's) -- the closer not specified

- **Spec.** `LinuxFs/Spec/.../wal/openWALFiles.lean`: the success arm said nothing of the closer `cl`.
- **Defect.** Too weak for `validSnapshotEntries`/`Verify` (`defer func() { if closer != nil { closer() } }()`):
  the call needs a triple.
- **Evidence.** S/wal.go:494 (`closer := func() error { return closeAll(lg, rcs...) }`); W8 session's gap 2.
- **Change (made, `wal-vsnap2`).** The success arm adds `wal.walCloser write frs lfs cl` (`CloseDefs.lean`):
  `cl` non-nil, and `□` a triple of `cl()` over each reader's file again closable (`wal.walClosable write fr
  lf`: the `*fileReader`'s file, its fd whole, in write mode the lock's `lockedFile`), returning some error.
  Write mode (`openAtIndex`) drops it.
- **Decision.** Made (internal; no ghost state).


## 2026-11-14: `decoder.Decode.spec`/`decodeRecord.spec` (internal, the part's) -- the I/O arm loses the files' streams

- **Spec.** `decPostB`'s I/O arm (`LinuxFs/Proof/.../wal/DecDefs.lean`): `⌜IoE err⌝ ∗ ownRecAny rp ∗ ∃ fs' off' c',
  ownDecoder d IoE eof fs' off' c' false`.
- **Defect.** Too weak for `wal.Repair` (S/repair.go:30-106): on a reader's I/O error its `default` arm returns `false`
  and the deferred `f.Close()` runs, which needs the segment's `*os.File` (`os.File.Close.spec`: `os.ownFile`, `osFd`),
  held in the segment's stream (`walFileS`) inside the decoder; the arm's decoder is over unknown files `fs'`, so
  the stream cannot be taken out (`ownDecoder_streams`).
- **Evidence.** `RepairLoop.lean`'s `repair_decNorm` (the I/O arm, `sorry`); the decoder only ever leaves files at
  their end (`d.brs = d.brs[1:]`), so its files are always a suffix of `fs` (as the record and stop arms say).
- **Proposed change.** The I/O arm as the first arm's files: `∃ k off' c', ([∗list] F ∈ fs.take k, ∃ q, F.S q) ∗
  ownDecoder d IoE eof (fs.drop k) off' c' false` (`decodeRecord`'s I/O exits build it with `k = 0`,
  `decPost_cons_eof` adds one). Implies the old arm; `ReadAll` (the only other caller) drops it.
- **Decision.** Pending (internal; to be made after `wal-vsnap2`'s change of the same arm lands, to avoid a conflict).
  **2026-11-14 (`wal-vsnap2`): adopted** (the coordinator's decision), as proposed: the I/O arm is `⌜IoE err⌝ ∗
  notUeof err ∗ ownRecAny rp ∗ ∃ k off' c', ([∗list] F ∈ fs.take k, ∃ q, F.S q) ∗ ownDecoder d IoE eof (fs.drop k)
  off' c' false`.

## 2026-11-14: `decoder.Decode.spec`/`decodeRecord.spec` (internal, the part's) -- no `errors.Is(_, io.ErrUnexpectedEOF)` termination on `Decode`'s own errors

- **Spec.** `decPost` (`LinuxFs/Proof/.../wal/DecDefs.lean`): `decPostB ∗ decAns eof err`; only the I/O arm carries
  `errors.Is(err, io.ErrUnexpectedEOF)`'s answer (`notUeof`).
- **Defect.** Too weak for `wal.Repair` (S/repair.go:64: `errors.Is(err, io.ErrUnexpectedEOF)` on every non-`EOF`
  error) and `validSnapshotEntries`/`ReadAll` read mode: on a stop's or a failed `Unmarshal`'s error the call has no
  spec (`RepairLoop.lean`'s `errUeAns_end`, `sorry`).
- **Evidence.** The stop errors are `io.EOF`, `io.ErrUnexpectedEOF`, `fmt.Errorf("%w ...", io.ErrUnexpectedEOF|err)`
  (decoder.go:110-150) and `proto.Unmarshal`'s; `errors.Is` terminates on each in Go.
- **Change (made, `wal-vsnap3`).** `decPost := decPostB ∗ decAns eof err ∗ decUe err`, `decUe err := ⌜err = nil⌝ ∨
  errIsTerm err ∨ notUeof err`, `errIsTerm e` (`LinuxFs/Spec/fmt/ErrorfErrsNot.lean`): `errors.Is(e, u)` returns for
  every pointer target `u`. The hypotheses it comes from carry it: `fmt.ErrorfErrsNot.spec` (pre: each error argument's
  `errIsTerm`; post: the result's), `walpb.Record.Validate.spec` (pre: `ErrCRCMismatch`'s; post: its error's),
  `proto.UnmarshalWalRecordE.spec` (post: its error's), `decEnv` (`ErrCRCMismatch`'s; a part of the hypothesis
  `WalDecEnvSupply`); `io.EOF`'s and `io.ErrUnexpectedEOF`'s are proved (`*errorString` leaves, `errors.wp_Is_leaf`).
  **Deviation from the coordinator's wording** ("the `%w`-wrapped `io.ErrUnexpectedEOF`: true; `io.EOF`: false"):
  only termination is given, no answer. `true` on `fmt.Errorf("%w ...", io.ErrUnexpectedEOF)` is Go's answer but false of
  Perennial's `fmt.Errorf` model (`errors.New(format)`, a fresh leaf), so the hypothesis `ErrorfErrsNot` could not be
  discharged from the model if it claimed it; and no caller needs an answer (`Repair` needs `true` only at the end of the
  frames, where the stop is, `RepairAt`; `validSnapshotEntries`' error arm takes any error). `io.EOF`'s `false` follows
  from `wp_Is_leaf` where a caller needs it.
- **Decision.** Made (internal; no ghost state; the hypotheses' strengthening is true of Go and of the models).

## 2026-11-14: `openLast.spec` (internal, the part's) -- the last segment's name not known valid

- **Spec.** `walLastOpen` (`LinuxFs/Proof/.../wal/OpenLastDefs.lean`), `openLast.spec`'s success arm: the pin of the
  last segment `gL`, its file open at `child dir gL.name`, with pure facts on the layout.
- **Defect.** Too weak for `wal.Repair`'s `createNewWALFile(f.Name() + ".broken", true)` (S/repair.go:62): the open
  specs take `NameOk` of the created name, `repBroken gL.name`, which follows from `NameOk gL.name`; nothing in
  `walLastOpen` gives it (the segments' facts say `.wal` suffix and the entries, not validity).
- **Evidence.** `openLast.wp_proof` has it (`hbok`, from `ReadDir`'s output) and drops it; `Repair.wp_proof`'s
  `io.ErrUnexpectedEOF` arm (`wal-repair26`).
- **Change (made, `wal-repair26`).** `walLastOpen`'s pure facts add `NameOk gL.name` (last). A strengthening;
  `Repair` is the only client.
- **Decision.** Made (internal; no ghost state).

## 2026-11-14: the WAL's raftpb laws (`WalPbIn.*Law`, `WalHsOwn`) -- unprovable for real raftpb as stated (W4c U4)

- **Spec.** The model laws the WAL's `Link.lean` results take of the client's `P : WalPbIn GF`, `U`, `HsO`
  (`LinuxFs/Spec/.../wal/{WAL__Save,WAL__cutPre,WAL__saveEntry,ReadAllCallees}.lean`,
  `LinuxFs/Proof/.../wal/HandleUnnamed.lean`), to be discharged by the raftpb instance (U4).
- **Defects** (the laws are true of Go; they are not provable from this repository's trusted facts):
  1. **No package initialization in the pre.** `WalPbIn.UnmarshalEntLaw` and `WalHsOwn.unmarshal` (pre
     `d ↦*{dq} bs` only) call `pbutil.MustUnmarshalMessage`, whose specs (`MustUnmarshalMessagePb.spec`,
     `specWalSnap`) and `proto.UnmarshalPb.spec` take `isPkgInit pbutil`/`proto`; `WalPbIn.CloneHsLaw` calls
     `proto.Clone` (`ClonePb.spec`: `isPkgInit proto`) on any `P.hsIn` object, including a fresh zero one
     that `WalPbIn.ZeroLaw` makes from nothing; `WalPbIn.IsEmptyLaw` runs `raft.IsEmptyHardState`, which
     reads raft's package variable `emptyState` (node.go:32, :122-124), known only from `isPkgInit raft`,
     again on a fresh zero object. `P.hsIn` cannot carry the initialization: `WalPbIn.NilLaw` (`⊢ P.hsIn null
     hsZero`) and `ZeroLaw` produce it from no resource. (`MarshalEntLaw`/`MarshalHsLaw` can be met by
     putting `isPkgInit pbutil` into `P.entIn` and into the non-empty arm of `P.hsIn`, a workaround.)
  2. **`raftpb.HardState` has no trusted wire model.** It is not a registered `PbTypeC` (its schema is `[]`,
     `Proof/google_golang_org/protobuf/proto/PbSchema.lean`, "a type not listed here"), so no `proto` spec
     says what `pbutil.MustMarshalMessage`, `pbutil.MustUnmarshalMessage` or `proto.Clone` do on a
     `*raftpb.HardState`: `MarshalHsLaw`, `CloneHsLaw`, `WalHsOwn.unmarshal` are unprovable without a new
     registration (two axioms, as `walpb.Snapshot`'s `snapEncC_ok`/`pbSnapC_reg`).
  3. **`HardState.Reset` has no body.** raftpb's `Reset` is names-only (`Code/go_etcd_io/raft/v3/raftpb.toml`:
     `!*.Reset`), with no spec: `WalHsOwn.reset` needs a trusted model (as walpb's `Record.Reset.impl`).
  4. (Minor, worked around.) `WalUnmarshal.Ok.entry` is a round trip for **every** entry, but the entry
     encoder's trusted fact (`entryEncC_ok`) says nothing at sizes `≥ 2^63`; the instance uses stand-in bytes
     for entries of `2^48` bytes or more (`RaftModel/EntCodec.lean`), which no `Save` writes (its premise is
     `< 2^40`).
- **Evidence.** W4c U4 log (`notes/wal-fsext-w4c-plan.md`); the instance `walRaftMr`/`walRaftU` and its pure
  laws (`LinuxFs/Proof/.../wal/RaftModel/Marshal.lean`).
- **Proposed change.** (1) Add `isPkgInit pbutil` to the pres of `UnmarshalEntLaw`, `WalHsOwn.unmarshal`,
  `MarshalEntLaw`, `MarshalHsLaw`; `isPkgInit proto` to `CloneHsLaw`'s; `isPkgInit raft` (the part's
  `go_etcd_io.raft.v3`) to `IsEmptyLaw`'s. Their callers (`ReadAll`, `saveEntry`, `saveState`, `Save`, `cut`) hold
  `isPkgInit wal`, which gives the three (the WAL imports pbutil, proto and raft). (2)+(3) [user]: register
  `raftpb.HardState` in the part (`WalHsC`, `hsEnc` as in `RaftModel/Codec.lean`, a schema
  `[(1,[0]),(2,[0]),(3,[0])]`, `hsEncC_ok`, `pbHsC_reg`; Go-tested as `walpb.Snapshot`'s) and give
  `HardState.Reset` a trusted model -- or keep the three laws as hypotheses of the closed result.
- **Decision.** (1) taken (coordinator, 2026-11-14, branch `wal-u4b`): `isPkgInit pbutil` in the pres of
  `MarshalEntLaw`, `MarshalHsLaw`; `isPkgInit proto` in `CloneHsLaw`'s; `isPkgInit raft` (the part's root
  package) in `IsEmptyLaw`'s; **`isPkgInit wal`** (not pbutil) in `UnmarshalEntLaw`'s and `WalHsOwn.unmarshal`'s,
  as every spec of a `wal` function (`MustUnmarshalEntry`/`MustUnmarshalState` are `wal`'s; wal's
  initialization gives pbutil's). `WAL.saveState.specPre` (`cut`'s) gains `isPkgInit wal` in its pre (it had
  none, and its two laws now need raft's and pbutil's). The part's raft root fact gains `emptyState` (the
  main tree's conjunct, word for word), which `IsEmptyLaw`'s proof reads. (2)+(3) stay out (the user's call,
  W4c U4 task 3): `MarshalHsLaw`, `CloneHsLaw`, `WalHsOwn.unmarshal`, `WalHsOwn.reset` remain hypotheses of
  the closed result, listed in §10 of `notes/wal-fsext-plan.md` as pending the user.

## 2026-11-14: `fileutil.ReadDir.spec`/`specAbsent`, `readWALNames.spec`/`specAbsent`, `openWALFiles.spec` (internal, the part's) -- no `errors.Is` termination on their errors

- **Spec.** Their error arms give only `fmtErrorOkOrNil`/`errOk`: `errors.Is` on the error has no spec.
- **Defect.** Too weak for `validSnapshotEntries` (`specPinned`/`specAbsent`), whose errors must carry `wal.vseErrIs`
  (`ValidSnapshotEntries`' retry test `errors.Is(err, os.ErrNotExist)`, S/wal.go:639, on every error the attempt
  returns: `readWALNames`', `openWALFiles`', the decoder's, `ErrCRCMismatch`). Found in `wal-vsnap3` (W8, third
  session).
- **Evidence.** The errors are `*PathError`s of an errno (`os.errnoPathErr`, the part's `os` models: `ReadDir`'s
  every error, `os.OpenFile`'s), `fmt.Errorf("...: %w", e)` of them, and `errors.New` leaves (`ErrFileNotFound`,
  `ErrCRCMismatch`); `errors.Is` terminates on each in Go (`*PathError` has no `Is`; its `Unwrap` gives the `Errno`,
  whose `Is` compares the target with four pointer errors; `*wrapError` unwraps to its argument).
- **Change (made, `wal-vsnap4`).** `errIsTerm` (`errors.Is(e, u)` returns for every pointer target `u`) on: the
  error arms of `ReadDir.spec`/`specAbsent`, `readWALNames.spec`/`specAbsent`, `openWALFiles.spec` (read mode: write
  mode's `TryLockFile` errors are not needed), `notUeof` (the decoder's I/O errors); the wal package's error
  variables (`wal.errVar`) and `walpbInit`'s `ErrCRCMismatch` (`*errorString` leaves, proved). The `os`/`io/fs`
  package facts record `ErrNotExist` as an `*errorString` (proved from `internal/oserror`'s `errors.New`), so that
  `vseErrIs` follows from `errIsTerm`. Two new hypotheses, true of Go (as `errors.IsErrno.spec`,
  `fmt.ErrorfErrsNot.spec`): `errors.IsPathErrnoTerm.spec` (`errIsTerm` of an `os.errnoPathErr`) and
  `fmt.ErrorfErrsTerm.spec` (`fmt.ErrorfErrs.spec` passing `errIsTerm` from the error arguments to the result).
- **Decision.** Made (internal; no ghost state).

## 2026-11-14: `walInvBody` (internal, the part's) -- the crash boot's files-only fact `hfo` not derivable (W4c U3)

- **Spec.** `walInvBody` (`LinuxFs/Proof/.../wal/Inv.lean`) and what `walInv_crash` returns of the crashed tree.
- **Defect.** The crash boot (`walBootCrash`) must give the next generation `walTmpsRes J` (`0.tmp`/`1.tmp` absent or
  files), `walOthersL` (a WAL directory's non-segment entries files), `walAreaRes`'s `TmpOk` (a leftover `nm.tmp` holds
  only files, for `os.RemoveAll.specDirS`) and `tmpClTouch` (its `.touch` no directory). A crash leaves at a name what
  one of its claim's versions held (`RegionCrashed`), and only for the claims the invariant holds when the crash comes;
  the pipeline's names (while a write handle holds them), `Repair`'s lent names, `Create`'s `nm.tmp` directory and its
  contents are under claims the program holds whole, and the invariant's own WAL-directory claims record no fact about
  their past versions. So the fact is the crash boot's premise `hfo` (U3 log, second session), true of the Go code (the
  WAL creates no directory there) but dischargeable by no one.
- **Evidence.** U3 log, second session, (d); `BootFilesOnly.lean` (the crash-side lemma, proved).
- **Proposed change (decided by the coordinator, 2026-11-14).** A new framed conjunct of `walInvBody` (its own
  predicate, `walFoRes`): a list `fl` of claims held at half, and pure facts: every claim of `fl`, and every
  WAL-directory claim of `cl`, has a history holding no directory at its names (`HistNoDir`, all versions); and every
  version of an area claim of `cl` holding a directory `J` at a WAL name or at `nm.tmp` has every name of `J` covered by
  such a claim. Then `RegionCrashed (cl ++ fl) n V'.now` gives `hfo` (`regionCrashed_filesOnly`), narrowed to WAL names
  and `nm.tmp` (the `nm.broken.<t>` directories need only `SubCover`, which the boot's whole claims give). Every update
  under a claim of `fl` becomes an invariant step (`osAU`/`osAUnc` with the invariant's half: the os specs are already
  shaped for it). Condition checked: `walAreaRes` is unpacked by no client (outside the WAL's proofs only comments and
  the WAL's own specs name it; its body is exposed, not `@[no_expose]`-sealed). No client-visible ghost state: `fl` is
  inside the invariant.
- **Decision.** Adopted (internal), in progress: the design's open points are in the U3 log, third session.

## 2026-11-14: the part's WAL handle specs (`wal.Create.spec`, `WAL.ReadAll.spec`, `walOpenWF`) -- the client keeps no call permission while a WAL is open (W4c U5)

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Create.lean` (success arm: `walOpenWF` alone, no
  `osCallPerm` back), `Open.lean` (`walOpeningF` holds the client's `½`), `WAL__ReadAll.lean` (moves it into the
  handle's `walDirH`), `WAL__Close.lean` (gives back `osCallPerm 1`); `Handle.lean:457` (`walDirH` holds `osCallPerm ½`)
  and the pipeline (`walPipeH`) the other half.
- **Defect.** While a WAL is open the handle and its pipeline hold the whole call permission, so the client can make
  no `os` call until `Close`. The tester (`examples/etcd/wal/wal.go`) calls `storeOracle` (`durable.Write`: `os`
  calls, `osCallPerm qc` with `qc > 0`) between WAL calls with its WAL open (`save`, `saveSnap`, `sync`, `opOwnSnap`,
  `restartRead`'s `Open` loop, `Boot` after `Create`), and so would etcd (its snapshotter and backend write files
  while the WAL is open). The W4c U0 audit assumed the client kept `osCallPerm ½` while a WAL is open (plan §2, the
  table's `Open` row); the two ledger entries of 2026-11-14 that moved the halves into the handle and the pipeline
  (`Create`'s, `Open`'s "the call permission counted twice") left the client none.
- **Evidence.** `member.sync`'s proof (W4c U5, second session): after `Create`/`ReadAll` nothing supplies
  `storeOracle.spec`'s `osCallPerm qc`.
- **Proposed change.** The handle and its pipeline hold a quarter each and `Create`'s success arm (and `ReadAll`'s)
  gives the client `osCallPerm ½` back (`Open` keeps taking `1`: it hands `¼` to the pipeline, `¼` in
  `walOpeningF`, `½` back); `Close` gives back the handle's and the pipeline's `½`, the client recombining to `1`.
  A resource placement (fractions only, no new ghost state); the WAL's own proofs change only where they split or
  join the permission (`openAtIndex`, `Create`'s commit, `ReadAll`, `Close`). Interim (made): the tester's member
  state (`TP/Member.lean`) holds the client's `osCallPerm qc` as a parameter, so the member operations' proofs stand
  once the WAL's arms give it back; only `Boot`/`restart` (which take it from `Create`/`ReadAll`) wait.
- **Decision.** Adopted (the coordinator's decision of 2026-11-14; made on branch `wal-u5c`, W4c U5 third
  session). As proposed, with `Open`'s fractions placed thus: `openAtIndex`'s write arm returns `osCallPerm ¼ ∗
  osCallPerm ½` (the pipeline's `pipeRes` the other quarter), `Open` puts the quarter in `walOpeningF` and
  returns the half (`walOpeningF w dir s ∗ osCallPerm ½`); `ReadAll` moves `walOpeningF`'s quarter into the
  handle's `walDirH` (no change to its spec: the client's half came from `Open`). `Create`'s success arm (and
  `renameWAL`'s two committed arms, so `renameWALUnlock`'s hypothesis too) carries `osCallPerm ½`. `Close`,
  `Close.specU` and `Close.specOpening` return the half the handle and its pipeline held (`osCallPerm ½`;
  `specOpening` takes the quarter of `walOpeningF`); the client recombines with `osCallPerm_halfJoin`
  (`Pipe.lean`). Every error arm unchanged (`Create`'s after-rename arm `Q ∗ osCallPerm ½`). The tester's
  `member.close.spec` returns `Close`'s `osCallPerm ½`.

## 2026-11-14: `decoder.Decode.spec`/`decodeRecord.spec` (internal, the part's) -- the failed-`Unmarshal` arm loses the files' streams (W4c U5, fourth session)

- **Spec.** `decPostB`'s third arm (`GoFail`, `LinuxFs/Proof/.../wal/DecDefs.lean`): `∃ k s off' c', ⌜GoFail … ∧
  stopErr …⌝ ∗ ownDecoder d IoE eof (fs.drop k) off' c' false`.
- **Defect.** The streams of the `k` files the decoder left before the frame `proto.Unmarshal` rejected are dropped
  (`decPost_cons_eof` frames them away), as the I/O arm's were before the entry above. `Close` of the handle a failed
  `ReadAll` leaves (`WAL.Close.specFailed`, this session) closes every file (`l.Close()`, `os.File.Close.spec`: the
  file's `os.ownFile`/`osFd`, in its stream `walFileS`) and puts the segments' halves back (`walInvBody_unpin`), so
  `ReadAll`'s decoder-error exit must keep every file's stream.
- **Evidence.** `decPost_cons_eof`'s third case (`DecLemmas.lean`): `HF` unused.
- **Proposed change.** The arm as the other two: `∃ k s off' c', ([∗list] F ∈ fs.take k, ∃ q, F.S q) ∗ ⌜…⌝ ∗
  ownDecoder d IoE eof (fs.drop k) off' c' false` (`decPost_fail` with `k = 0`, `decPost_cons_eof` adds one).
  Implies the old arm (its users drop the new conjunct).
- **Decision.** Adopted (internal, the agent's; the same change as the I/O arm's, already adopted).

## 2026-11-14: `ZeroToEnd.specWalTail`/`Fdatasync.specWalPend` (internal, the part's) -- the error arms lose the tail (W4c U5, fourth session)

- **Spec.** `LinuxFs/Spec/.../wal/ReadAllTailCallees.lean`: both posts' error arm is `⌜err ≠ nil⌝` (resp. `⌜e ≠
  0⌝`) alone.
- **Defect.** `ReadAll`'s two exits after these errors (S/wal.go, the `ZeroToEnd` and the fdatasync after it) leave a
  handle whose `Close` (`WAL.Close.specFailed`, stated this session) runs `w.sync()`, i.e. `fileutil.Fdatasync` of the
  tail, and closes its lock's file: it needs the tail's `os.ownFile`/`osFd` and halves, and the generation's lock
  token comes back only if the tail can be put back into `walInv`. With the tail lost, `Close.specFailed` is
  unprovable on those exits.
- **Evidence.** `ZeroToEnd.wp_specWalTail` (`ZteWalTail.lean`): `ZeroToEnd.specAu`'s error arm returns the file, the
  fd, the key and record (`growTie`), the `OsMeta` and the bytes past the offset; the proof drops them.
- **Proposed change.** (a) The error arms return the tail (`∃ o' m' bs`, file, fd, offset `o'`, the lent token, the
  halves, the record), with a law putting back a tail left in a resize window or after a failed fdatasync (none
  exists: the same gap as `Repair`'s failure arms); or (b) leave them, and `Close.specFailed`'s post may lose the
  lock token after these two exits (as `Repair.spec`'s `false` arm), which the tester's `restartRead` (it calls
  `Repair` after a `nil` `Close`) cannot meet.
- **Decision.** (a), the coordinator's (2026-11-14, W4c U5 fifth session). Made (branch `wal-u5e`): the error arm
  of `specWalTail` returns `walTailPE` (`HandlePend.lean`: file, fd, some offset, the lent token of kind
  `false` (`ZeroToEnd`'s first step made it), the halves of some `OsMeta` and bytes with `TailMetaE o0`: all the
  bytes, no mappings, at least `o0` long, the length word at `o0` zero; and the record), over the entry below on
  `ZeroToEnd.specAu`; `specWalPend`'s error arm returns its `walTailP` unchanged (`wp_tailFsyncP` already gave
  it back). `ReadAll` still drops both (the ten exits' `walReadFailedF` body is task 4). The invariant steps
  for `Close` to put such a tail back are not made yet (W4c U5 log, fifth session: the lent tail's fdatasync in
  a window with no zeros past `wr`, `TailPend`).
  And `specWalPend`'s success arm gives `walTailW … TailMetaS` (was `TailMeta`; the synced bytes are durable),
  for the put-back of the exits after it (`walInvBody_untail` takes `TailMetaS`); `ReadAll` weakens it at once
  (`walTailW_mono`). Internal, the agent's.

## 2026-11-14: `ZeroToEnd.specAu` (`fileutil`, the part's) -- the error arm says nothing of the bytes (W4c U5, fifth session)

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/ZeroToEndAu.lean`, the error arm: some offset,
  `OsMeta` `m'` (`o ≤ m'.size`, the mappings) and `m'.size - o` bytes `ys` from `o`, nothing of their values.
- **Defect.** `Close` of the handle `ReadAll` leaves after a failed `ZeroToEnd` (entry above, option (a)) must
  sync the tail and put it back; the tail's layout may have no F-Z (`TailPend`: a torn frame past `wr`), and the
  synced layout's `tailStop` then needs the length word at `wr` zero, which only the handle's bytes show.
- **Evidence.** `ZeroToEnd.wp_proofAu`'s four error exits: the seek's (bytes unchanged), the truncate's not
  landed (`ftUndoneH`: `xs'.map Prod.fst = xs.map Prod.fst`), the truncate's landed (no bytes past `o`), the
  growth's (`osZerosA`).
- **Proposed change.** The arm's pure part gains `ys.map Prod.fst = xs.map Prod.fst ∨ ∀ y ∈ ys, y.1 = 0`.
- **Decision.** Adopted (internal, the agent's: a proved spec, its only user `ZeroToEnd.wp_specWalTail`); made.

## 2026-11-14: `WAL.Close.specFailed` (the part's, stated W4c U5 fourth session) -- the token back whatever `Close` answers (W4c U5, fifth session)

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__CloseFailed.lean`: post `walUnlockedTok ∗
  osCallPerm ½` for every `err`, as `Close.specOpening`.
- **Defect.** With option (a) above, a failed `ReadAll` may leave its tail in a resize window (`ZeroToEnd`'s
  truncate or growth failed) or unsynced (the fdatasync after it failed); `Close`'s `w.sync()` is then the only
  step that can make it exact, and the unregistration needs the WAL's `TailIdle` (`walTailsRes`'s
  `WalTailIdle`). When that fdatasync fails, `Close` returns its error before the locks and the tail stays lent
  in its window: the token cannot come back. Unprovable as stated.
- **Evidence.** `walTailsRes_close`/`walTailsRes_closeL` (`CloseLaw.lean`, `UnregLent.lean`) take `TailIdle`;
  `WAL.Close.spec` loses the token on `sync`'s error for the same reason.
- **Proposed change.** Post `(walUnlockedTok ∗ osCallPerm ½) ∨ ⌜err ≠ nil⌝`. Its client, the tester's
  `restartRead` (`examples/etcd/wal/wal.go:195-197`), fails the read on a non-nil `Close` and calls `Repair`
  (which takes the token) only after a nil one, so it needs only the left arm on `nil`.
- **Decision.** Adopted (the agent's: the spec is stated, unproved, not in the Link; no client proved over it);
  made.

## 2026-11-14: `walOpenWFU`, `WAL.Close.specU`, `WAL.sync.specC`, `renameWALPost` arm 2 (internal, the part's) -- `Create`'s name registered only at success (design P; unit `create`)

- **Spec.** `walOpenWFU` (`Handle.lean`, sealed), `LinuxFs/Spec/.../wal/WAL__CloseU.lean`, `WAL__syncC.lean`'s
  error arm, `WAL__renameWAL.lean`'s `renameWALPost` arm 2 (so `renameWALUnlock.spec`'s too).
- **Defect.** `Create`'s cleanup renames `nm` aside, which `os.Rename.specDirAnySnc` allows only with the whole
  claim on `nm`; but `walOpenWFU` held the name registered (`walNamesFrag none`), whose registration lent a
  fraction to `nameShare` that is never given back whole (borrowers drop what they borrow): no state after
  `Close.specU` lets `Create` call the rename (W4 log, twenty-sixth and twenty-seventh sessions).
- **Evidence.** `nameShare`'s `∃ q`, `walInv_dirPath`; `Close.specU`'s proof dropping the handle's and the
  pipeline's paths.
- **Change (made).** Design P (`notes/wal-units/create.md`): the handle before naming carries the pending
  registration (`walDirH`'s new names-fragment parameter `nf := some dir`) and its two paths to `dir` pinned at
  `Create`'s spine-law roots and fraction (`walOpenWFU P Mr w dir Rp qp`; `walDirH`'s naming fact a function of
  the path's roots and fraction, `walPipeH`'s new pin `pp`; all defaulted, so every other handle is unchanged).
  `Close.specU` returns `walUnlockedTokX` (the free token less its names fragment), `walNamesFrag (some dir)`
  and the two pinned paths (error arm: `walLockedTok ∗ walNamesFrag (some dir)`); `sync.specC`'s error arm
  returns the handle's names fragment `nf` too; `renameWALPost` arm 2 returns the pinned pending handle
  (`∃ x qd, ⌜dq = own qd⌝ ∗ UH x ∗ walOpenWFU P Mr w' dir R qd`). `Create` registers the name at its success
  exit, after the parent's close (`walInv_named`, `walInv_register`, `walOpenWFU_seal`).
- **Decision.** Made (internal: no client spec moves; `Create.spec` unchanged).
## 2026-11-14: `member.save.spec` (the tester's, W4c U5) -- the post drops the handle's written length, which `sync` takes (W4c U5, ops)

- **Spec.** `LinuxFs/Spec/github_com/mit_pdos/etcd_grove/examples/etcd/wal/member__save.lean` (and `MemberRep`'s
  `memSaveRes`/`memSavePost`): the true arm gives the handle, `tMemOk`/`tMemHs` of the new WAL state `d'` and
  the candidate's synced mark, not `walLenLb w dir |d'.H|`.
- **Defect.** `member.sync.spec` and `WAL.Sync.spec` take `walLenLb w dir |d.H|` of the current state, so no
  member operation after a `save` can call `sync` (`opRecvSnap`'s last call; `step`'s `sync`).
- **Evidence.** `WAL.Save.spec`'s success arm returns `walLenLb w dir (|d.H| + 1)` (`Hlen1` in
  `member.save.wp_proof`), which the proof dropped; the empty save keeps `d`, for which no length was in the
  precondition.
- **Proposed change.** The precondition (and `memSaveRes`) gains `walLenLb w dir |d.H|`, the true arm (and
  `memSavePost`) `walLenLb w dir |d'.H|`. Its provider at a restart or `Create` is the open handle's
  (`Open`/`ReadAll`, `Create`): an obligation of `restart`/`Boot`.
- **Decision.** Adopted (internal, the agent's: a strengthening of a proved spec of our own example, its only
  clients `opTerm`/`opCommit`/`opEntries`/`opResend`/`opRecvSnap`, all re-proved); made.

## 2026-11-14: `tOpWf` and `member.save.spec` (the tester's, W4c U5) -- a save's hard-state term unbounded, so a restart cannot re-establish the member's fields (W4c U5, restart)

- **Spec.** `LinuxFs/Proof/github_com/mit_pdos/etcd_grove/examples/etcd/wal/Defs.lean`'s `tOpWf` (a save's entries
  `tEntWf`, a snapshot's index and term below `2^63`; nothing on a save's hard state) and
  `TS/member__save.lean` (premises `tMemOk`, `tMemHs`, the entries' `tEntWf`, the sizes).
- **Defect.** After a restart the member's term is the read hard state's (`resume`), and `memLive` (`MemberInv`,
  the form the operations take) asks it below `2^63` (`tMemFields`); the read's hard state is the history's last
  save's, whose term nothing bounds, so `restart` could not give `memLive`.
- **Evidence.** `notes/wal-units/ops.md`, "For `restart`'s author"; `tMemFields_read` (`RestartLive.lean`) needs
  the bound (`tLastHS_term`).
- **Proposed change.** `tOpWf` gains a third clause, `o.snap = false → uint.nat o.hs.term' < 2 ^ 63`;
  `member.save.spec` the premise `uint.nat h.term' < 2 ^ 63`; its callers supply it: `opEntries` (its `t <
  2^63`), `opRecvSnap` (`memLive`'s `tMemFields`), and new premises `uint.nat t < 2 ^ 63` of `opTerm`/`opCommit`
  and `tMemFields t M` of `opResend` (all three implied by `memLive`, the form `step` will take).
- **Decision.** Adopted (internal: the tester's own definitions and specs, recommended by the ops agent and
  delegated to the restart path by the coordinator); made, every client re-proved.

## 2026-11-15: `WAL.cleanupWAL.spec` (new, internal, the part's) and `wal.Create.wp_proof`'s callees (unit `create`, session 3)

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__cleanupWAL.lean` (new); the binders of
  `wal.Create.wp_proof` (`LinuxFs/Proof/.../wal/Create.lean`).
- **Defect.** `Create`'s error exits after its commit run the deferred `cleanupWAL`, which had no spec.
- **Evidence.** S/wal.go `cleanupWAL` (the fork's fix: it returns its error); `Create`'s deferred closure.
- **Change (made).** `cleanupWAL.spec` over the handle before naming (`walOpenWFU`), with a caller law
  (`cleanupLaw`) for the rename (`os.Rename.specDirAnySnc`'s precondition at the timestamp, and a continuation
  from its post, both with `notCrashed`); three outcomes (sync failed; `Close` returned an error; the law's
  `Fin err`). Proved over `Close.specU`, `time.Now`, `time.Time.Format.specBroken`, `fmt.SprintfBroken.spec`,
  `os.Rename.specDirAnySnc`, zap. `wal.Create.wp_proof` takes `cleanupWAL.spec` and `fmt.ErrorfAny.spec` (both
  proved; in the Link `wal.wp_Create` now reaches the pending hypotheses `h_fmt_SprintfBroken` and
  `h_time_Time_FormatBroken`). `Create.spec` unchanged.
- **Decision.** Made (internal). The law's proof (`create_cleanupLaw`, `sorry`) is blocked on two invariant
  changes (a pin for the rename's area claim; the moved-aside step with the pending WAL known unnamed):
  `notes/wal-units/create.md`, session 3; left to the coordinator.

## Proposed by specgap (2026-11-15; unit `specgap`, `notes/wal-units/specgap.md`; nothing made)

Draft entries, in priority order, from comparing the part's `fsExt` WAL specs with what etcd's server needs
(SpecPlan's storage and boot specs, `examples/specreq/etcdserverboot/`, the Go at `0b50f0426`). Each waits for the
coordinator, and those marked [user] for the user. `Sp/` = `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/`,
`S/` = `LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/`, `SP/` = `SpecPlan/Spec/go_etcd_io/etcd/server/v3/`,
`RI` = `notes/wal-crash-handoff/restart-wal-interface.md`; Go paths are in the fork's server module.

## 2026-11-15: the server's storage specs (`SP/storage/storage__{Save,SaveSnap,Sync,Release,Close}.lean`) and etcd's `lg.Panic` on WAL errors -- `diskOk` cannot refute an `fsExt` error arm (P1)

- **Spec.** `SP/storage/storage__*.lean` (`RET #GoInterface.nil` under `⌜diskOk⌝`); the part's `wal.Create.spec`,
  `WAL.{Save,SaveSnapshot,Close,ReleaseLockTo}.spec` (honest error arms).
- **Defect.** SpecPlan too strong over `fsExt`: every system call may fail with any errno (`GooseLang/Ext/Fs/Impl.lean`,
  "Environmental failure"), so the WAL's error arms are reachable and a pure premise `⌜diskOk⌝` refutes none of them.
  Where the server `Fatal`s (raft loop `etcdserver/raft.go:257,264,279`; `openWALFromSnapshot`) honest arms are
  enough. Where it `lg.Panic`s, a no-panic theorem is false in the model: `bootstrapNewWAL`'s `Create`
  (`bootstrap.go:719`), `snapshot()`'s `SaveSnap`/`Release` (`server.go:2147,2151`), `applySnapshot`'s `Release`
  (`:1111`), `onStop`'s `Close` (`raft.go:441`), and `Reopen` (`storage/wal/wal.go:284`).
- **Evidence.** The Go sites above; `notes/wal-fsext-plan.md` §5 Q6 ("the server keeps `walSaveOk` as its own premise
  at C6"), which no Iris proof can use against an error the spec returns.
- **Proposed change.** [user] One of: (a) a failure ledger in `fsExt` (a ghost flag set by any failing call; the
  adequacy theorem conditioned on it staying unset), a trusted change; (b) fork changes `lg.Panic` → `lg.Fatal` at the
  five sites; (c) a closed theorem that exempts a panic after an I/O error. Then SpecPlan's storage specs get error
  arms (handle lost) and `diskOk` keeps only what (a) makes checkable.
- **Decision.** Proposed.

## 2026-11-15: the part's `WAL.{Save,SaveSnapshot,ReleaseLockTo,Sync}.spec` -- an exclusive handle, but the server calls them concurrently under a read lock (P2)

- **Spec.** `Sp/WAL__{Save,SaveSnapshot,ReleaseLockTo,Sync}.lean` (each takes `walOpenWF P Mr w dir`, exclusive);
  `SP/storage/Api.lean` (`isStorage` persistent, `storageOpen` fractional).
- **Defect.** Too weak for the server. `storage`'s methods take `st.mux.RLock` (`storage/storage.go`). The raft loop
  (`Save`, `SaveSnap`, `Sync`) and the apply thread (`snapshot()`'s `SaveSnap`/`Release`, `applySnapshot`'s
  `Release`) call them concurrently, and the WAL serializes them with `w.mu`. No client can thread an exclusive
  handle through read locks. `WAL.Sync` takes no lock at all (`wal.go:994`), and races with `ReleaseLockTo`'s write
  of `w.locks` (`wal.go:1039`), which `sync()`'s `tail()` reads: a candidate Go data race (specgap §3.1).
- **Evidence.** `etcdserver/raft.go:257-279`, `server.go:1111,2147-2151`, `server.go:990-1002` (the apply thread
  snapshots after `raftAdvancedC`, while the raft loop moves on to the next `Ready`).
- **Proposed change.** A shared-handle layer: `walOpenS w dir q` (fractional), with the handle in `w.mu`'s invariant.
  `Save`/`SaveSnapshot`/`ReleaseLockTo` take a fraction (their AUs already commit right after `w.mu.Lock()`), and
  `Close` takes all. For `Sync`: a fork fix (`Sync` takes `w.mu`) [user: the fork], after a `-race` test; or
  `storage.Sync` takes the write lock (also a Go change).
- **Decision.** Proposed.

## 2026-11-15: `walAreaOk`/`walAreaRes`/`AreaSlot`/`walBoot0`/`walBootCrash` (the part's) -- the area's slots and root do not fit etcd's member directory (P3)

- **Spec.** `S/Inv.lean:518` (`AreaSlot`: every `walNameOk` name and `nm.<sfx>`), `S/CreateDefs.lean:146`
  (`walAreaRes`), `S/Boot0.lean:89` (`hr`: the area a root; `hslots`), `S/BootCrash.lean:395` (`bootWals`),
  `DirsRoots`.
- **Defect.** Too strong for the server (W4c U1 mismatches 1 and 4):
  - `snap` is a slot, so `member/snap` (created by `bootstrapSnapshot`'s `TouchDirAll`, `bootstrap.go:211`, before
    the WAL) breaks `hslots`; `walBootCrash` would take it for a WAL; and the invariant holds half the area's claim
    on it.
  - The area must be an existing root, yet the first start creates `member/` (`bootstrap.go:68`) and probes
    `DataDir` above it (`:64`).
  - Durable directories must be roots, so `member/snap` cannot be durable.
  - `IsDirWriteable(WALDir)` (`:85`) writes `member/wal/.touch`, whose claim the invariant owns (`walOthersL`).
- **Evidence.** The definitions above; `GooseLang/Ext/AbsDisk/Paths.lean:34` (`walNameOk`); `notes/wal-fsext-w4c-plan.md`
  U1 log, mismatches 1 and 4; U3 log, premise 3.
- **Proposed change.** `AreaSlot` and `walAreaRes` take the WAL's name `nm` (slots `nm`, `nm.<sfx>`); every other
  name of the area goes to the client at boot. Allow a durable directory below a root through spine claims (or make
  the data directory the root, the area below it). Add a law lending a WAL directory's `.touch` to a client probe.
  World premises of the server's closed theorem: the data directory exists, clean and absolute; `DedicatedWALDir = ""`.
- **Decision.** Proposed (statement changes to the WAL's client vocabulary: the coordinator's; the boot premises: the
  user's at C6's closed theorem).

## 2026-11-15: the part's `wal.{Exist,ValidSnapshotEntries,Open,OpenForRead,Repair}.spec` -- `osCallPerm 1` with no directory operation (P4)

- **Spec.** `Sp/{Exist,ValidSnapshotEntries,Open,OpenForRead,Repair}.lean` (each takes `osCallPerm 1`).
- **Defect.** Too strong for the server. Once bbolt runs over `fsExt`, the backend's commit goroutine holds a share
  of the permission from `bootstrapBackend` on, and the server calls VSE (`recoverSnapshot`, inside
  `bootstrapBackend`), `Open`, `Repair` and `Create` after the backend is open. Only `Create` does a directory
  operation (a rename, `mkdir`, `RemoveAll`).
- **Evidence.** `bootstrap.go:77-89, 451, 675, 689, 717`; `LinuxFs/Spec/os/{Rename,Mkdir,RemoveAll}.lean` (the
  operations that need `osCallPerm 1`).
- **Proposed change.** The five take `osCallPerm q` for any `q` (`Open`: a third or a quarter each to the pipeline
  and the handle, the rest back). `Create` keeps `1`: the server must make the backend quiescent at
  `bootstrapNewWAL`, by a backend-side protocol returning its share, or by a fork reordering [user].
- **Decision.** Proposed.

## 2026-11-15: the part's `WAL.Save.spec`/`WAL.SaveSnapshot.spec` (through `walEntsIn`, `walSnapAt`, `Mr`) -- canonical contents only; raft's entries and the restarted server's conf state are not canonical (P5)

- **Spec.** `Sp/WAL__Save.lean` (`walEntsIn P`, `Mr.encEntry`), `Sp/WAL__SaveSnapshot.lean` (`walSnapAt Mr sp md cs`:
  bytes `= Mr.encSnap md`), U4's instance `S/RaftModel/{Codec,Pb}.lean` (`walCsCanon`: `AutoLeave` set).
- **Defect.** Too strong for the server:
  - Entries: already recorded by U4b (`notes/wal-fsext-w4c-plan.md`, U4 b log, task 4). Raft's entries keep the
    proposal's presence.
  - New here, the conf state: after a restart `ep.confState` is `buildConfStateFromV3store`'s
    `ConfState{Voters, Learners}`, with `AutoLeave` nil (`bootstrap.go:145`, `server.go:804`). The apply thread's
    first `snapshot()` before any conf change saves it (`CreateSnapshot(…, ep.confState, …)`, `storage.SaveSnap`
    → `walpb.Snapshot{ConfState: …}`). Its bytes are not `walCsCanon`'s, so `walSnapAt` fails.
- **Evidence.** The Go above; `walSnapCanon`/`walCsCanon` (`S/RaftModel/Codec.lean:42`).
- **Proposed change.** [user: the representation] `Mr.encEntry`/`Mr.encSnap` (or `P.entIn` and `walSnapAt`) over
  wire contents (`EntryC`, `WalSnapC`), the history keeping only what readers decode (the index and term for
  snapshots). Narrow alternative for the conf state: a fork fix setting `AutoLeave` in `buildConfStateFromV3store`.
- **Decision.** Proposed.

## 2026-11-15: the part's `wal.Create.spec` (with `wal.Exist.spec`) -- `Exist`'s `false` does not give `Create`'s `walAbsent` (P6)

- **Spec.** `Sp/Create.lean` (AU from `walAbsent dir`), `Sp/Exist.lean` (`b = false → ExistFalseOk o`: none, or fresh
  and unnamed).
- **Defect.** Too weak, composed: `bootstrap` calls `Create` exactly when `Exist` returned `false`
  (`bootstrap.go:77` → `bootstrapNewWAL`). A fresh unnamed WAL survives a crash (`walCrash` keeps `named = false`
  images), so `ExistFalseOk`'s second case cannot be excluded at a boot, and `Create`'s AU cannot be fired.
- **Evidence.** `GooseLang/Ext/AbsDisk/Impl.lean:223` (`walCrash`); the two specs.
- **Proposed change.** `Create`'s AU starts from `walDirIs dir o ∗ ⌜ExistFalseOk o⌝` (an existing fresh WAL at `dir`
  makes `Create`'s own `Exist` check return `ErrExist`, uncommitted; a moved-aside one is replaced). Alternatively,
  `Exist`'s `false` gives `o = none` once the ENOENT model fix lands and the moved-aside state is in the invariant
  (the `create` unit's cleanup design).
- **Decision.** Proposed.

## 2026-11-15: the part's `WAL.Close.specFailed` with `wal.Repair.spec` -- `openWALFromSnapshot` ignores `Close`'s error, then needs the token (P7)

- **Spec.** `Sp/WAL__CloseFailed.lean` (`(walUnlockedTok ∗ osCallPerm ½) ∨ ⌜err ≠ nil⌝`), `Sp/Repair.lean` (takes the
  token).
- **Defect.** The server's restart cannot be proved on this path: after a failed `ReadAll` it calls `w.Close()`,
  ignores the error, and calls `wal.Repair` (`bootstrap.go:683-689`). On `err ≠ nil` the token is lost. In Go,
  `Close` returns before unlocking (`wal.go:1053-1066`) and `Repair`'s blocking `LockFile` hangs: a hang, which
  only a lock model could show.
- **Evidence.** The Go above; ledger 2026-11-14, "`WAL.Close.specFailed` … the token back whatever `Close` answers".
- **Proposed change.** [user] Either the lock model (Q1), with `Repair` not needing the token; or a fork fix:
  `openWALFromSnapshot` `Fatal`s on `Close`'s error (specgap §3.2, to report).
- **Decision.** Proposed.

## 2026-11-15: the server's purge (`SP/etcdserver/EtcdServer__purgeFile.lean`) and `storage.MinimalEtcdVersion` -- no `fsExt` statement without locks (P8)

- **Spec.** `SP/etcdserver/EtcdServer__purgeFile.lean`, `SP/storage/storage__MinimalEtcdVersion.lean`; the part's
  `WAL.ReleaseLockTo.spec` (`unl` bookkeeping).
- **Defect.** `purgeFile` (`fileutil.PurgeFileWithDoneNotify`, `server.go:608`) deletes the oldest unlocked
  segments. `fsExt` has no lock state, so neither the purge nor `ReleaseLockTo`'s `unl` has content (`RI` gate 8).
  `Reopen` (`MinimalEtcdVersion`) releases every lock while the purge runs (suspected window, specgap §3.3).
- **Proposed change.** [user, `notes/wal-fsext-plan.md` §5 Q1] The lock model. Until then C6 states the purge as a
  hypothesis or drops it from the closed theorem.
- **Decision.** Proposed.

## 2026-11-15: the part's `WAL.ReleaseLockTo.spec` -- the post does not exclude an error, and the server panics on one (P9)

- **Spec.** `Sp/WAL__ReleaseLockTo.lean` (post `walOpenWF ∗ ∃ d, Q d` for every `err`).
- **Defect.** Too weak: `storage.Release`'s callers `lg.Panic` on any error (`server.go:1111,2151`). The only error
  is `parseWALName` rejecting a lock's file name, which the invariant rules out (every lock is a segment at a
  `walNameStr` name).
- **Proposed change.** Post `⌜err = GoInterface.nil⌝ ∗ walOpenWF ∗ ∃ d, Q d` (the proof's error exit refuted by
  `WalDirClaim`).
- **Decision.** Proposed (internal strengthening; no client yet).

## 2026-11-15: the part's `WAL.ReadAll.spec` -- the hard state and the entries come back read-only, and `ForceNewCluster` mutates them (P10)

- **Spec.** `Sp/WAL__ReadAll.lean` (`P.hsIn hp σ.hs`, `sl ↦*□ esL`).
- **Defect.** Too weak for `bootstrapWALFromSnapshot`'s `ForceNewCluster` path: `bwal.st.Commit = …`
  (`bootstrap.go:640,787`), and `append(wal.ents, ents...)` (`:781`) may write into the slice's capacity. `ReadAll`'s
  `state` is a fresh unmarshalled object (`w.state` is a clone, `wal.go:649`), so the client may own it.
- **Proposed change.** The success arm gives `HsO hp σ.hs` (owned; `WalHsOwn.freeze` turns it into `P.hsIn`) and the
  slice's ownership with its capacity.
- **Decision.** Proposed (low priority: `ForceNewCluster` only).

## 2026-11-15: `SP/storage/wal/Api.lean` (`Wal.Recs`, `walRecs`, `walWriting`, `walCreating`, `walPurgeRight`) and `SP/storage/storage__Close.lean` -- the trusted record model against the proved WAL (P11)

- **Spec.** SpecPlan's WAL vocabulary and its crash laws (`walRecs_crash`, `walWriting_crash`, `walCreating_crash`);
  `storage.Close.spec` (returns `walPurgeRight`).
- **Defect.** The model is trusted, yet the WAL is now proved. Its σ-level `Recs` updated by `save` is not
  compositional for the real read (`RI` §2: `walKeep` uses the history's final commit). `walWriting` and
  `walCreating` are two-step shapes that `fsExt`'s single commit replaces. `Close` returning the purge right is
  stronger than any user needs, and `fsExt` consumes it.
- **Proposed change.** `walRecs wd R := ∃ d, walDiskAt wd d ∗ ⌜view d = R⌝`, `walWriting` a mark below `|H|`, and
  `walCreating md := walDiskAt wd (walDurFresh md)` (`named = false`). The crash laws become lemmas: `walImg` with
  the invariant "every op past the mark is a commit-only `Save` or the write in flight" gives `Recs.crashed` and
  `crashedMid`. `storage.Close` consumes `walPurgeRight`. Coordinated with P1 (error arms).
- **Decision.** Proposed.

## 2026-11-15: `SP/storage/storage__Save.lean`, `storage__SaveSnap.lean` -- missing the WAL's premises (P12)

- **Spec.** As named, against `Sp/WAL__Save.lean`, `WAL__SaveSnapshot.lean`.
- **Defect.** SpecPlan too weak in its premises: the WAL needs every entry index `< 2^64-1`, every encoding
  `< 2^40`, the snapshot's index `< 2^64-1`, and its conf state set unless the index is 0. Raft's room fact and
  proposal limits must supply them, and a received snapshot's index has no bound yet (`RI` gate 5).
- **Proposed change.** Add them as premises of `storage.Save`/`SaveSnap`, discharged in `raftNode.start` from raft's
  invariants.
- **Decision.** Proposed.

## 2026-11-15: the part's WAL -- no specs of `WAL.LatestSnapshotEntry`, `WAL.Reopen`, `wal.MinimalEtcdVersion` (P13)

- **Spec.** None yet; `SP/storage/storage__MinimalEtcdVersion.lean` is the user.
- **Defect.** `storage.MinimalEtcdVersion` (downgrade, `schema.UnsafeMigrate`) calls them. `LatestSnapshotEntry`
  calls `ValidSnapshotEntries`, whose spec takes `walUnlockedTok`, which the open handle holds.
- **Proposed change.** A VSE spec over an open handle (the handle pins the segments), then the three. Low priority.
- **Decision.** Proposed.
## 2026-11-15: `os.File.WriteAt.specExt` (lean's chunked `WriteAt`) -- its post's `OsMeta` is false under the WAL track's page cache known zero (`OsMeta.cz`) (the `lean`/`wal-int` merge, branch `wal-lean`)

- **Spec.** `Spec/os/File__WriteAt.lean`'s `specExt` (lean `6342dfeb5d`, for the bbolt port): the post's
  `osMeta d.ino 1 (pwPost m off a j)`.
- **Defect.** `wal-int`'s change to the per-byte extension's program logic (P1 of
  `notes/axiom-review/eof-page.md`, pending the user's review: the page cache known zero `OsMeta.cz`, raised by a
  `pwrite` that lands all its data, `pwCz`) makes the `OsMeta` a chunked write
  leaves remember the last chunk that landed whole: after a first chunk landed whole and a later one short,
  the ghost `cz` is the first chunk's raise, not `pwPost`'s (`pwCz m off a j`, no raise unless the whole write
  landed). Lean's `specExt` was proved over the base semantics, without `cz`.
- **Evidence.** `Proof/os/WriteChunks.lean`'s `pwPost_chunk` leaves the goals
  `(pwPost (pwPost m off a j) (off + nn) cs k).cz = (pwPost m off (nn + cs) (max j (nn + k))).cz` (false when
  `j = a < nn + cs` and the first write raised `cz`) and the same for `rz`; the WAL track met the same in its own
  chunked spec and states it with `os.pwPostE m off A j E` (`Spec/os/WriteLong.lean`, `specLong`: `cz :=
  pwCz m off E E`, `E` the last whole chunk's end).
- **Proposed change.** `specExt`'s post as `specLong`'s: `∃ E, E ≤ j ∧ (j = a → E = a) ∧ ...` and
  `osMeta d.ino 1 (os.pwPostE m off.toNat a j E)` (and `rz` likewise, to check); `WriteChunks`' chunk lemma
  as `WriteLongStep.pwPostE_step` over `pwrite` anywhere; the bbolt port's six users of `specExt`
  (`Proof/go_etcd_io/bbolt/{Tx__write,Tx__write_ext,Commit/WriteRun,Commit/PwMeta,Commit/WriteExtRun,
  Commit/MetaBytes}.lean`) re-proved over `pwPostE`. Meanwhile `specExt`'s proof is split to
  `Proof/os/File__WriteAtExt.lean` (it does not build) so that the WAL does not wait on it.
- **Decision.** Restated as specLong's post; coordinator, 2026-11-15. Done on `wal-lean`: `specExt`'s post is
  `∃ j a E ys, ... E ≤ j ∧ (j = a → E = a) ∧ ...` with `osMeta d.ino 1 (os.pwPostE m off a j E)` (`rz` needed
  nothing: `pwPost` keeps it); `WriteChunks.pwPost_chunk` (false) is gone, replaced by
  `File__WriteAtExt.pwPostE_chunk` (with `pwCzE_stepG`, `pwCzE_step` for a write anywhere); the bbolt
  port's users (`Tx__write`, `Commit/WriteExtRun`, `Commit/PwMeta`'s `pwPostE_inside`) take the `E`; the
  others (`Tx__write_ext`, `Commit/WriteRun`, `Commit/MetaBytes`) needed nothing.

## 2026-11-15: `SP/storage/storage__MinimalEtcdVersion.lean` -- no panic under `diskOk`, false while the purge runs

- **Spec.** `storage.MinimalEtcdVersion.spec` (SpecPlan): returns without panicking under `diskOk`.
- **Defect.** `MinimalEtcdVersion` reopens the WAL (`w.Reopen`), releasing every segment lock, while the server's
  purge (`fileutil.PurgeFileWithDoneNotify`, `--max-wals`) may delete or lock segments the reopen needs; the
  reopen then panics.
- **Evidence.** `issues/etcd-storage-downgrade-reopen-purge-panic.md` (test reproduces the panic 5/5 at upstream
  main `260e4e0457aa`, 3/3 at the fork `3df9b265f`).
- **Proposed change.** Either the spec takes "no purge runs" (a premise the server's downgrade path would have
  to establish), or the fork reads the entries through `wal.OpenForRead` instead of reopening (the issue's
  proposed fix, untested), after which the spec stands.
- **Decision.** Proposed (with specgap's P8, the lock model, and P13).

## 2026-11-15: `LinuxFs/Spec/.../examples/etcd/wal/restartRead.lean`, `member__restart.lean` -- `m` not known non-nil

- **Spec.** `restartRead.spec`, `member.restart.spec` (the WAL tester).
- **Defect.** Unprovable: `restartRead` tests `m != nil`, and the field points-tos `m.[member, f] ↦ _` do not
  give `m ≠ null`.
- **Evidence.** `restartRead.wp_proof` (branch `wal-c-tester2`) needs it at the `if m != nil`.
- **Proposed change.** Premise `m ≠ null` on both (every caller allocated `m`: `Boot`'s `&member{...}`).
- **Decision.** Made (branch `wal-c-tester2`, `notes/wal-units/tester.md`, ninth session).
## 2026-11-15: the WAL invariant for `Create`'s cleanup (unit `create`, session 4; the coordinator's decisions)

- **Spec.** `LinuxFs/Proof/.../wal/Inv.lean` (`walNamesRes` takes `s`, the pending WAL unnamed; `WalsAt`
  weakened; `CreatingOk`'s `CreatingNew` guarded by `dir ≠ cleanKey`), `Ghost.lean` (`walCreatingAuth`'s
  cleanup pin, `walCreating` carrying `dir ≠ cleanKey`, `walCleanPin`), `CreateDefs.lean`/`CreateArea.lean`
  (`walAreaRes`/`AreaOk` exempt `BrokenSlot` names); the internal step lemmas `walInvBody_named`/`walInv_named`,
  `walInvBody_namedBy`/`walInv_namedBy` (take and return `walNamesFrag none`), `walInvBody_register`/
  `walInv_register` (premise `∃ J, hn.cur !! nm = some (.dir J)`), `walInvBody_mint`/`walInv_mint`
  (`dir ≠ cleanKey`), the area steps' `hT` (against `walUnlockedTokX`).
- **Defect.** `create_cleanupLaw` could not be proved: the rename's update could not find the invariant's half
  of its area claim (no pin), and a rename that took effect broke `WalsAt`, `walAreaRes`'s `SubCover` and, with
  the WAL possibly named, `CrashTo`.
- **Evidence.** `notes/wal-units/create.md`, sessions 3 and 4.
- **Change (made).** As listed; `Create` registers before it names. No client-facing spec changed.
- **Decision.** The coordinator's (decisions 1 and 2 of session 3); made, every importer rebuilt, both `sorry`s
  proved.

## 2026-11-15: the conf-state half of "canonical contents only (P5)" above -- withdrawn: the restarted server's `ep.confState` has `AutoLeave` set

- **Spec.** The entry above (`WAL.SaveSnapshot.spec`'s `walSnapAt`/`walCsCanon`), and the SpecPlan's
  `confStateFull` for `ep.confState` (`ApiApply.lean`'s `applyThread`, `raftNode__ApplyConfChange`,
  `EtcdServer__createMergedSnapshotMessage`, `EtcdServer__snapshot`).
- **Defect.** None: the reported one does not exist. `buildConfStateFromV3store`'s `ConfState` (`AutoLeave` nil)
  reaches the apply thread only through the `MemoryStorage`: `bwal.MemoryStorage()` → `ApplySnapshot`
  (`EnsureSnapshot`, then `proto.Clone`), and `run`'s `ep.confState` is `raftStorage.Snapshot()`'s
  (`EnsureSnapshot` again, a clone). `CreateSnapshot` clones it, so `SaveSnap` hands the WAL a full conf state.
- **Evidence.** `bootstrap.go:107-115, 571, 741-753`; raft `storage.go:119-126, 208-214, 218-237, 243-262`;
  `server.go:755, 803-809, 1175, 2053, 2132`. Measured against the pinned raft (`565c2bd`): bootstrap's `cs`
  has `AutoLeave` nil, `MemoryStorage.Snapshot()`'s and `CreateSnapshot`'s have it set
  (`notes/wal-units/autoleave.md`).
- **Proposed change.** None to the specs. P5 stays for entries only. The user's decision of 2026-11-15
  (generalize, do not insist on `AutoLeave`) was taken on the false reading: reopened as options in
  `notes/wal-units/autoleave.md` (recommended: keep the specs).
- **Decision.** Proposed (unit `autoleave`).

## 2026-11-15: `applyInit_ep.spec` (`SpecPlan/.../etcdserver/ApiApply.lean:724`) -- `ep.confState` from nowhere

- **Spec.** `applyInit_ep.spec`: `applyInit s γ p c ∗ ep's five fields ↦ … ∗ ep.confState ↦ cs ⊢ |==> applyThread s γ ep p`.
- **Defect.** Unprovable: `applyThread`'s realization holds `ep.confState` as a `RaftPb.confStateFull` listing the
  configuration at the consistent index (`confAt γ.raft ci m`), but `cs` is arbitrary and nothing is given about
  it. `run` has the `MemoryStorage` snapshot's `snapshotPts` (step 1) and drops it (step 5).
- **Evidence.** `ApiApply.lean:51, 97, 724-732`; `EtcdServer__run.lean` steps 1 and 5; Go `server.go:755, 803-809`.
  That the snapshot's conf state lists the configuration at `c` is bootstrap's doing (rebuilt from the backend,
  at `c`; `bootstrap.go:107-115`), which no SpecPlan statement carries to `run`.
- **Proposed change.** `applyInit_ep` also takes the conf state's holding, `RaftPb.confStateFull cs dq csm`
  (from `MemoryStorage.Snapshot`'s `snapshotPts` by `snapshotPts_unfold`), and a tie of `csm` to the configuration
  at `c`: either `applyInit` gains the membership (`applyInit s γ p c m`, with `⌜csm.Is m⌝` here; `start`'s
  `srvRunTok_intro` and `NewServer` supply `m` from bootstrap), or `applyInit` holds the `MemoryStorage`
  snapshot's model and the law takes `snapshotPts` itself. For batch 2d/2e's owners.
- **Decision.** Proposed (unit `autoleave`, found while answering where `ep.confState` comes from).
## 2026-11-15: error-free WAL specs under `NoIoErr` (unit `noioerr`) -- three obstacles

- **Spec.** The planned `WAL.SaveSnapshot`/`ReleaseLockTo`/`Close`/`Create` `.specNoErr` variants (none
  stated yet); `encoder.flush.specP`, `encoder.encode.specG`; `os.File.Write.wp_empty`.
- **Defect.** (1) `flush.specP`'s error arm is `B out pend` for any `pend`: with nothing pending (no write
  made, Go's `PageWriter.flush` returns `0, nil`) the spec still allows an error, so an error-free `sync`
  cannot be derived from it; `encode.specG`'s error arm likewise allows `b = []`. (2) An empty
  `(*os.File).Write`'s errno is arbitrary with no `fsExt` step (trusted model), which `NoIoErr` cannot
  exclude. (3) `ReleaseLockTo`'s only error is `parseWALName` on a lock's name, which the handle does not
  record as a WAL name: not an I/O error.
- **Evidence.** `notes/wal-units/noioerr.md`, "What is left".
- **Proposed change.** (1) Add "`pend = [] → err = nil`" to `flush.specP` (and "nothing written → `nil`" to
  `encode.specG`), proved from the page writer. (2) For the user (trusted model). (3) A handle fact: each
  lock's name is `walName seq idx`.
- **Decision.** Proposed.
- **Resolved (2026-11-15, unit `noioerr`, second session, `wal-c-noioerr2`).** (1) and (2) together, without
  changing a statement: new specs over a writer called only with bytes (`io.writerStreamPNE`;
  `PageWriter.flush/Flush/Write.specNE`, `encoder.flush.specPNE`, `write.specNE`, `encode.specGNE`,
  `saveCrc.specNE`), the old ones their instances. The page writer never writes an empty slice (Go:
  pagewriter.go:107-111, 86-88), so the trusted empty-`Write` branch is never reached on the WAL's paths: (2)
  needs no model change. (3) open (after `wal-c-locks`, which rewrites `walLockH`).

## 2026-11-15: `wal.Create.spec` (`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Create.lean`) -- the update from `walAbsent` only

- **Spec.** `Create(lg, dir, md)`: `AU <{ walAbsent dir }> … <{ walDiskAt dir (walDurFresh md), COMM Q }>`.
- **Defect.** Too strong a precondition for its clients: after `Exist` answers `false`, the state is
  `ExistFalseOk` (none, or a fresh unnamed WAL), and a generation may start with a fresh unnamed WAL (the
  trusted `walCrash` keeps `named = false`; `Create` failed after its rename, `cleanupWAL`'s move aside not
  fsynced). The tester's `Boot` then calls `Create` and cannot give `walAbsent` (the tenth session's B3, whose
  premise "a crash maps an unnamed WAL to absent" is false).
- **Evidence.** `LinuxFs/GooseLang/Ext/AbsDisk/Impl.lean:230-236` (`walCrash`); `Exist.lean`'s `ExistFalseOk`;
  `examples/etcd/wal/wal.go` `Boot`; S/wal.go `Create` (its `Exist` check before any effect, `renameWAL`'s
  `RemoveAll`).
- **Proposed change.** The update from `∃∃ o, walDirIs dir o ∗ ⌜wal.ExistFalseOk o⌝` (`wal.Create.specFresh`,
  stated as a hypothesis in `CreateFresh.lean`, taken by `Boot.wp_proof`); `Create.spec` is its `o = none` case.
  Proved by the WAL layer (the creating update generalized; the invariant lets the commit replace an unnamed,
  empty WAL whose directory is not at its name). Alternatives in `notes/wal-units/tester.md`, eleventh session.
- **Decision.** Proposed (unit `tester`); until then a hypothesis of `Boot`.

## 2026-11-15: `wal.Create.spec` generalized (`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Create.lean`) -- the update from any view

- **Spec.** `Create(lg, dir, md)`; follows the entry "the update from `walAbsent` only" above.
- **Defect.** The update from `walAbsent dir` only was stronger than needed; and `wal.Exist.spec`'s
  `false` arm, `ExistFalseOk o` (none or a fresh unnamed WAL), is weaker than what its proof shows
  (`o = none`: with the lock token held every present WAL is registered and `Exist` finds its segment).
- **Evidence.** `wal.Exist.wp_core`'s `b = false → od = none` (real state); `existFalseOk_of_le` only
  produces `o = none`; `notes/wal-units/fresh.md`.
- **Change made.** `Create.spec` takes `Pv : Option WalDur → Prop` and its update is from `∃∃ o,
  walDirIs dir o ∗ ⌜Pv o⌝` (given back by the error arm that commits nothing); `Create` finds the real
  state empty from its own `Exist` (`walAreaResFree`) and the lock token (`walCreating_absent`).
  `Create.specFresh` is its instance at `ExistFalseOk`, proved (`wal.Create.wp_specFresh`), no longer a
  hypothesis of `Boot`. Proposed, not made: `Exist.spec`'s `false` arm strengthened to `o = none`
  (closes specgap P6).
- **Decision.** Made (unit `fresh`, coordinator's option (a)); the `Exist` strengthening proposed.

## 2026-11-15: the WAL's internal file predicates and callee specs -- the lock semantics (unit `locks`, session 2)

- **Spec.** Internal to the part's WAL: the tail (`walTailW`, `walTailP`, `RepairTailDefs`, `tailWB`, `WAL.sync`'s
  error post), `walLockH`, `wal.rcFile`, `walClosable`, `walFileS`, `walOpenedFile`, `pipeFile`, `walLastOpen`,
  `walLockLeft`/`walLockIn` (`WAL__renameWAL`), the leftover-file posts of `WAL__syncC`, `WAL__cleanupWAL`,
  `WAL__CloseU`, and `RepairCallees` (`Truncate.specRepTail`, `Fsync.specRepTail`).
- **Defect.** Stated over 3-field descriptions and unlocked fds: false once `fsExt` has lock state (a locked
  segment's description has a lock field; `os.File.Close` takes its tokens).
- **Evidence.** The lock semantics (`notes/wal-units/locks.md` §2); the WAL did not build after it.
- **Change.** Each file a WAL predicate holds carries `fdLocks fd d` (its tokens, `lockToks`, and `fdKindOk d`:
  each lock it holds is of `fileutil`'s kind); the tail's description is `⟨i, rd, true, lo, lk⟩`; a segment opened
  by `openWALFiles` is `walSegFd write lo lk i`. No client-facing WAL spec changed.
- **Decision.** Made (unit `locks`, session 2).

## 2026-11-15: `WAL.Close.specFailed`'s error arm for the boot path's `Repair` (P7, continued)

- **Spec.** `Sp/WAL__CloseFailed.lean` (error arm `⌜err ≠ nil⌝`), `wal.Repair.specHeld` (new, proved).
- **Defect.** With the lock model, `Repair` on the held lock is provable (`Repair.specHeld`: `false`, nothing
  changed), but it needs what the failed handle still holds: the directory claim's share at the layout's names
  and the last segment's lock token (`osLock k gL.ino fd`, `fileutil.lockKind k`). `Close.specFailed`'s error
  arm gives nothing, and the spec is itself unproved (`walReadFailedF` is a stub).
- **Proposed change.** `Close.specFailed`'s error arm gives those resources (a `walCloseLeft`); with it, the server's
  restart (C6) composes `Close.specFailed` and `Repair.specHeld` on this path.
- **Decision.** Made (unit `locks`, session 3; the coordinator's approval, internal): the post is
  `(walUnlockedTok ∗ osCallPerm ½) ∨ (⌜err ≠ nil⌝ ∗ walCloseLeft R dir)` (`CloseLeft.lean`: the shared invariant
  and a path to `dir`, the claim's half at the layout's names with `Repair.specHeld`'s facts, the last segment's
  lock and `lockKind`, the call permission's half); the composition `wal.Repair.wp_afterCloseFailed`
  (`CloseFailedRepair.lean`, proved over `Repair.specHeld`). The tester's `restartRead` drops the new resources.
  `Close.specFailed` itself is still unproved (`walReadFailedF` a stub).

## 2026-11-15: the no-error WAL specs (unit `noioerr`, second session) -- `EFBIG` at `maxBytes` needs room

- **Spec.** The new `WAL.sync.specNoErr`/`specCNoErr`, `encoder.encode.specTailNoErr`, `WAL.Close.specNoErr`,
  `WAL.SaveSnapshot.specNoErr` (`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/*NoErr.lean`).
- **Defect (of the first statement tried: `Close.specNoErr` from `walOpenWF`).** False: a flush whose bytes
  reach `maxBytes` (ext4's `s_maxbytes`, `fsExt`'s file size bound) fails with `EFBIG`, which `NoIoErr` keeps
  (no success exists at that offset), and `walOpenWF` bounds only `o0 + |out| ≤ sz ≤ maxBytes`, not the
  pending bytes; `SaveSnapshot` adds a frame.
- **Evidence.** `GooseLang/Ext/Fs/Premises.lean` (`NoIoErr`: a covered call succeeds when a success exists);
  `examples/osfs/semantics/data_maxbytes.go`; the ledger's 2026-11-14 entries (the stream-end fact withdrawn).
- **Change (made).** The no-error specs that write take a sealed handle with room, `walOpenWFR P Mr w dir k`
  (`HandleRoom.lean`: `o0 + |out| + |pend| + k ≤ maxBytes`; `walOpenWFR_wf`); `sync`'s internal no-error
  specs take `o0 + |out| + |pend| ≤ maxBytes`. Existing specs unchanged.
- **Decision.** Open, for the user: how a client obtains the room (`notes/wal-units/noioerr.md`, second
  session: room from `Create`'s and `Save`'s posts, a public measure of the tail, or a history-size premise).

## 2026-11-15: `WAL.Close.specFailed`'s proof (unit `closefailed`) -- `walCloseLeft`'s roots and `dir` bound, the lent tail's lock

- **Spec.** `walCloseLeft R dir` (`CloseLeft.lean`, `Close.specFailed`'s error arm), `CloseLeftOk`; the internal
  `walReadFailedF w dir` (sealed), `walTailP`/`walTailPE`/`walOpenedFile`/`walFileS`/`walLastOpen` (internal).
- **Defect.** (1) The path to `dir` the failed handle can give is the area's (`walInv_dirPath`, roots `R` of
  `walAreaOk`) only through an invariant look; the pipeline's path has its own roots and an arbitrary fraction,
  so `walCloseLeft R dir` with the spec's `R` is provable but only by that look, and nothing needs `R` fixed
  (`Repair.specHeld` is generic in it). (2) `CloseLeftOk`'s `dir.length < 2^59` is `Open`'s premise, which
  `walOpeningF`/`walReadFailedF` do not record: `ReadAll` cannot supply it. (3) The lock `walCloseLeft` hands
  over is the tail's, but no WAL file predicate recorded that a writable description holds a lock (`fdLocks`
  keeps the tokens of the locks it has, possibly none).
- **Evidence.** `WAL__CloseFailed.lean`'s error arm; `Spec/.../Repair.lean` (`specHeld` generic in `R`, takes
  the bound as a premise); `openWALFiles`/`openLast` (every writable WAL file is a `TryLockFile`/`LockFile`
  success, `lkFd_lk`).
- **Change (made).** (1) `walCloseLeft dir`: the roots existential (`Close.specFailed`'s post `walCloseLeft
  dir`). (2) The bound out of `CloseLeftOk`; `wal.Repair.wp_afterCloseFailed` takes it as a premise (its caller
  called `Open` with it). (3) `fdLocksW fd d := fdLocks fd d ∗ ⌜d.writable → d.ofd = some true ∨ d.flk = some
  true⌝` (`LockLemmas.lean`) in `walOpenedFile`, `walOpenedRc`, `walFileS`, `walLastOpen`, `walTailP`,
  `walTailPE` (`lkFd_openW`, `fdLocksW_held`); internal predicates only. Also: `walReadFailedF Mr w dir` (the
  marshaller, for the lent tail's write position), the ReadAll/Close.specFailed statements updated with it.
- **Decision.** Made (internal; the client-facing change is the error arm's `walCloseLeft dir`, which only
  `restartRead` (drops it) and `wp_afterCloseFailed` use).

## 2026-11-15: the WAL's trusted protobuf specs under `lean`'s trust gates (unit `lean-integration`, session 4)

- **Spec.** `proto.MarshalAppendCachedRecord.spec` (trust boundary); `pbSchemaOf` (`PbSchema.lean`, trusted);
  `WalEnc.recSchema`, `WalEnc.walSnapSchema`, the WAL's `walCsSchema`; `pbRecordC_reg`, `pbSnapC_reg`.
- **Defect.** None of substance: the WAL's registrations and trusted specs were written in the part `LinuxFs/`,
  outside the model-param, pbschema and axiom-tok gates. (1) `MarshalAppendCachedRecord.spec` keyed the
  registration premise by the constant `walpb.Record.ty`, which rule 1 does not read as tying the model `I` to a
  Go type (it wants `pbModelOf GF I.data.ty = some I`). (2) The WAL's schemas were not in `pbSchemaOf`'s table
  (the descriptor check could not read them), and `walCsSchema` duplicated raft's `csSchema` word for word.
  (3) No `Sat` theorem for `pbRecordM`/`pbSnapM` (rule 7).
- **Evidence.** `etc/model-param-check.py` (6 findings), `etc/pbschema-check.py`, at `033a5eafda`
  (`notes/wal-units/lean-integration.md`, session 3).
- **Change (made).** (1) `∀ I, pbModelOf GF I.data.ty = some I → I.data.ty = walpb.Record.ty → ...`: the same
  statement (its one user passes `pbRecordC_reg rfl`). (2) `pbSchemaOf` gains `walpb.Record ↦ recSchema`,
  `walpb.Snapshot ↦ walSnapSchema` (both moved into `PbSchema.lean`, same names and lists; `record.proto` at the
  pin), `walCsSchema` replaced by `csSchema`; `pbMsg` of a walpb type (none exists) now reads the real schema
  instead of `[]`. The descriptor check reads both roots (and `raftpb.ConfState` through `Snapshot.conf_state`)
  and runs `examples/stdlib/walpb`'s encoder and schema tests. (3) `pbRecordM_sat`, `pbSnapM_sat` proved.
- **Decision.** Made (no statement weakened or strengthened; the schema table's two entries are trusted text,
  for the user's review with the WAL's other trusted specs).

## 2026-11-15: the handle's half of the lock tie (unit `locks`, session 5) -- `WAL.ReadAll.spec`'s premise, the handle's locks

- **Spec.** `WAL.ReadAll.spec` (client-facing: the atomic precondition); internal: `walDirH` (new arguments: the
  non-tail lock list and the cuts), `walHandleIn`/`walHandleC` (the lock slot moved into `walDirH`), `walTailW`,
  `walLockIn` (`renameWAL.spec`), `wp_createSeg`, `walTailReg`, `walInv_readCommitReg`, `readAll_splitLeft`,
  `walInv_untailPend`/`walInv_untailKey`/`readAll_failPend`/`readAll_failSynced`/`walInv_readGive` (any range).
- **Defect.** `ReleaseLockTo`'s `unl` raise was bookkeeping (nothing tied the handle's locks to it), so the purge
  could not be proved: a purger must know that a segment it can lock ends at or before `unl`. The handle has to
  register its locked range (`walLksAuth`'s `b ≤ unl`, session 4) at the point it can show the range is within
  `unl`. For a restarted handle that point is `ReadAll`: `Open(s)` raised `unl` to `walOpenPos H s`, but nothing
  the proof holds between `Open` and `ReadAll` records it (`unl` is not in `absLe`, the history is not frozen by
  anything until the tail record is registered); only the client, which did that `Open`, knows it.
- **Evidence.** `OpenAtPin.lean` (`walInv_openAt` raises `unl` and keeps no witness); `ReadAllRegCommit.lean`
  (the registration's look sees the client's `d`); the tester's `restartRead` holds `tWalOwn γ (some
  (walOpenRaise pr dc))`, i.e. exactly `Open`'s raised state, at `ReadAll`.
- **Change (made).** (1) `WAL.ReadAll.spec`'s atomic precondition: `some s = walNewestPair … ∧ walOpenPos (d.H)
  s.1 ≤ d.unl` (the tester proves it from `walOpenRaise`, `restartRead.lean`). (2) Internal: `walDirLks` /
  `LkRel` / `walLockHI` (`Handle.lean`): the handle's non-tail locks with their segment names and inodes,
  exclusively locked, and its registered range; `walTailW` (and `walLockIn`, `wp_createSeg`'s post) carry
  `fdLocksW` (the tail's description is locked); the registration laws above. `WAL.ReleaseLockTo.spec{,NoErr}`
  unchanged: now proved with the raise meaning what its docstring said (the released locks' segments end at or
  before `walReleasePos`, `cutStart_le_releasePos`).
- **Decision.** Made (the client-facing change is a premise every caller meets by calling `Open` first; the
  server's `openWALFromSnapshot` does the same, not translated in the part).

## 2026-11-16: `purgeRound` restored in the tester (unit `locks`, session 10) -- `member.opOwnSnap.spec` takes the `lg`/`walDir` fields

- **Spec.** `etcd_wal.member.opOwnSnap.spec` (the tester's; `LinuxFs/Spec/.../examples/etcd/wal/member__opOwnSnap.lean`).
- **Defect.** With `purgeRound` restored (the user's approval, `notes/decisions.md` "WAL tester over fsExt: `purgeRound`
  restored"), `opOwnSnap` calls `purgeRound(m.lg, m.walDir, …)`, which loads the member's `lg` and `walDir` fields;
  `memLive` does not hold them (as for `member.restart`, whose spec takes them), so the old precondition does not
  allow the call.
- **Evidence.** `wal.go`'s `opOwnSnap`; `member.step.spec`, its only caller, holds both fields
  (`m.[member, "lg"] ↦ lg ∗ m.[member, "walDir"] ↦ tWalDir e.area`).
- **Change (made).** A binder `lg`; the precondition and the postcondition (both outcomes) take
  `m.[member, "lg"] ↦ lg ∗ m.[member, "walDir"] ↦ tWalDir e.area`, as `member.restart.spec`'s. `member.step`'s proof
  passes them through. New spec: `etcd_wal.purgeRound.spec` (the handle `walOpenWF`, the caller's repeatable commit
  `walPurgeAcc dir Pc` and its token `Pc`, `max < 2^63`; back the handle and `Pc`).
- **Decision.** Made (the tester's internal spec; the call needs the fields).

## 2026-11-15: the auth-on KV results at `kvStateOf log` -- unprovable once `kvInvOn` carries the lease table (auth-lease S3a)

- **Spec.** `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__Put.lean:63`,
  `EtcdServer__DeleteRange.lean:59` (`Q (kvStateOf x.log)`), `EtcdServer__Txn.lean`'s writing post (through
  `txnQhOn_res`), and the read side's conversion `client/v3/Results.lean:1052` (`readQ_of_ansM`: `kvStM true`
  is `kvStateOf (kvModelM true …)`, so a range's `□ Q (kvStateOf log)`), at `E.authOn = true`.
- **Defect.** S3a (Draft rev 5 §2, frozen) puts the lease table in `kvInvOn`'s state and keeps the clients'
  half in every lease mode, so a client's update fires at `kvStateOf (kvModelOn L) (kvLeasesOn L)`. These
  posts give `Q` of `kvStateOf x.log` (the table `[]`), true only while no lease is granted. The off mode
  proves its text by refuting a granting cluster from the client's half (`kvSt_client_lg`: `kvStQ` owns the
  whole variable at `γk.lg`), which S3a removes with auth on by design. Nothing on the request side
  (`isServerReqM true`, `putPermitM true`, `reqPropOkOn`) ties the mode to `none`.
- **Evidence.** The S3a port: `ReqOn.grantedRes_applied` (`kvRes γc Q (kvStateOf lb)` from `grantedRes` at
  `kvStateOf (kvModelOn L) (kvLeasesOn L)`), `ReadOn`'s `kvStOn` (must equal the invariant's state for the
  read deposits' firing, `ReadOn.lean:666`), `readQ_of_ansM`'s `by cases on <;> rfl`.
- **Proposed change.** (A) the posts give `Q` of the state with its table: `∃ lt, ⌜E.authOn = false → lt =
  []⌝ ∗ Q (kvStateOf x.log lt)` (or the model's table named through `modelOutM`), and the read side's
  `□ Q (kvStateOf log lt)`, followed through v3rpc (`ServerKVOn`) and the client's KV results; (C) a
  transitional tie of the auth-on request side to the lease mode `none` until S3b. Not in Draft rev 5 §7.
- **Decision.** (A), with the stronger guard `⌜E.authOn = false ∨ γ.kv.lm = .none → lt = []⌝` (etcd-grove-81, 2026-11-15): S3a Draft rev 6, §14 (recorded here 2026-11-15, S3a2 review r2 S7).

## 2026-11-15: the latest track's certificate premise for a leased put or transaction -- unprovable at a dead lease (auth-lease S3a §6)

- **Spec.** `apply.Apply.kvSpecL`, `apply.uberKVC`, `apply.uberApplier.Apply.kvSpecL`
  (`apply/ApplyFnKVL.lean:73,110`, `apply/ApplyKVL.lean:54`; exported as `apply_*_kv_latest`): the premise
  `certPreVW v3 E x.chain rq x.log (kvOutL …)`; through `certPreW_inner` (`apply/AuthApplyLatest.lean:238`, used by
  the latest Put/Txn/Revoke) it becomes the class track's `certPre E c rq log` (`apply/Chain.lean:1532`): a
  certificate `E.Nx` of the log after EVERY `chainStep backendStep` outcome.
- **Defect.** `backendStep`'s put case (`apply/Chain.lean:209`, kept unchanged by S3a's N1 (ii′)) admits
  `applied (log ++ [putChangeOf op …])` whatever the lease, and its transaction case an applied commit without
  `PathsLeaseOk`. The model (`backendLog`) keeps the log for a put of a lease not live (`leaseMissingIn`) and for a
  transaction whose path names one. With auth on, `E.Nx = kvNxOn` certifies only the models of committed raft logs,
  so the server cannot give the certificate of that outcome: Draft §6's KV branch ("as today, S2's latest triple
  ... no more `plainCover` discharge") is unprovable for an admitted leased put or leased transaction at the
  revocable mode, which a concurrent revocation makes reachable (a put proposed with a lease revoked before it
  applies). §3a's `leaseExactL` reaches the posts, not this premise. The backend's Put gets the certificate before
  its lease check (`applierV3backend__Put.lean:88-95`) and uses it only in the live branch.
- **Evidence.** `certPreW_inner`'s hypothesis `∀ oc, chainStep backendStep c rq log oc → X oc`; `kvNxOn`
  (`KVApplyOn.lean`); `kv_certPreW_on` (`ApplyEntryOn.lean`), which needs every admitted outcome to be the model's
  (`outcomeOn_of_kvOutLL` needs `leaseExactL` at the model's table, not available for the premise).
- **Proposed change.** (1) Restrict the class track's certificate to lease-exact outcomes at the live set `T`
  (`certPre` -> `certPreT … T`, outcomes with `leaseExactL T`; the class track's `leasesLive` at `T`, i.e. `kvOwnAt E
  log T`, split at the top from the two `ltHalf`s; the backend Put/Txn take `E.Nx` in their live branch), and the
  latest track's `X` with `leaseExactL T`; (2) `backendStep` over the live set (wider); (3) narrow S3a: no leased put
  or transaction admitted (`plainReqL lm := plainReq`), leased puts moved to a later stage with (1).
- **Decision.** (3) now, then (1) as its own stage S3a2 (etcd-grove-81, 2026-11-15): Draft rev 7, §15; `plainReqL lm :=
  plainReq`.

## 2026-11-15: txn.Txn's write wand is not told the lease check (auth-lease S3a2 §2)

- **Spec.** `txn.Txn.specSole` (`Spec/go_etcd_io/etcd/server/v3/etcdserver/txn/Txn.lean:62-65`; frozen text,
  `notes/mvcc-api-clients/clients-txn.md` §8): the caller's write wand is told `PathsIgnOk (stateAfter log) br` only.
- **Defect.** Too weak for a caller whose commit certificate depends on the leases: `applierV3backend.Txn` builds
  the commit's witness `E.Nx` inside that wand, and S3a2's certificate at the live set (`certPreT … L`, ledger
  2026-11-15 option (1)) covers an applied transaction only with `PathsLeaseOk (stateAfter log) L br`.
- **Evidence.** Go: `checkTxn` (with `checkPut` → `checkLease`) runs before `kv.Write` (`server/etcdserver/txn/txn.go:54-67`,
  `put.go:71-72`). Proof: `Hlok : PathsLeaseOk L` is in scope at `Proof/…/txn/Txn.lean:182`, the wand called at
  `:256`. Probe: `Scratch/S3a2Probe.lean` (`Txn_wp_T` over a local copy of the strengthened spec).
- **Proposed change.** The wand's premise `⌜PathsIgnOk … br ∧ PathsLeaseOk (stateAfter log) L br⌝` (a weaker
  obligation on the caller); `txn.Txn`'s proof passes `⟨Hign, Hlok⟩`; `TxnSpecs.lean`/`clients-txn.md` §8 updated.
- **Decision.** Approved (etcd-grove-81, 2026-11-15, the S3a2 Freeze, decision 2): the wand gains
  `PathsLeaseOk (stateAfter log) L br`; `clients-txn.md` §8's frozen text noted as changed by this entry.

## 2026-11-15: authTie at a leased request -- false in the refused-implies-not-permitted direction (auth-lease S3a2 §4a)

- **Spec.** `authTie` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/ReqOn.lean:89-91`), in `resultIsWOn` and
  `modelOutM` (`:151`, `:221`), read by `EtcdServer.processInternalRaftRequestOnce`'s spec.
- **Defect.** `o = .rejected .auth ↔ ¬ kvGranted st rq`: `kvGranted` is the permission check only; the auth layer
  also refuses a leased put whose lease carries a key the principal may not write (`checkLeasePuts`,
  `apply/auth.go:198-219`; the model's `¬ kvGrantedL`). Once S3a2 admits leased puts with auth on, the `→` direction
  is false.
- **Evidence.** S3a2 review r3 F1 (`/shared/tmp/auth-lease-s3a2/review-r3.md`); the example: key `a` permitted, the
  lease carrying `b` not.
- **Proposed change.** (b) the iff at `kvGrantedL st (leaseItemsOf (stateAfter lb)) rq`, `authTie` gaining the log
  `lb` (recommended since S3a2 Draft rev 5, review r4; probed `Scratch/S3a2ProbeTie.lean`); alternatives (a) one
  direction, (c) the iff for requests without a leased put: S3a2 Draft §4a.
- **Decision.** (b) (etcd-grove-81, 2026-11-15, the S3a2 Freeze, decision 3): the iff at the model's `kvGrantedL`,
  `authTie` gaining `lb`.

## 2026-11-15: the 7f-5a Draft's store watch (independent re-review: M1, M2, m1, m2)

- **Spec.** `Draft.store.Watch.spec` and its vocabulary (`Proof/k8s_io/apiserver/pkg/storage/etcd3/Draft7f5a.lean`,
  unlinked; `notes/k8s-7f5a-draft.md` §10), before 7f-5a-P moves it to `Spec/`.
- **Defects.** (M1) the client may deliver a progress notification at the watch's start, `hdrRev = c` with
  `c + 1 = rev`, with no bound by a fired state (`watchStateRespOk`, `WatchStateDefs.lean:125-128`); the producer
  queues it as a bookmark, which `KRawTail.bm`/`KTail.bm` (`p ≤ σ.rev`) cannot hold. (M2) `kCancelPD` lacked the
  processing goroutine's own cancel (its `sendError`'s deferred `wc.cancel()`, watcher.go:559-562, 796).
  (m1) the post's error arm said only `err ≠ nil`. (m2) `kStartOk`'s `max m.req 1 ≤ st` needs `1 ≤ σ0.rev` in
  the legacy case, which neither `kvWf` nor a firing gives.
- **Evidence.** The re-review (etcd-grove-81, 2026-11-15); Go: watcher.go as cited; for M1, the driver check
  `watchOkL` rejects any event above the configuration's revision (`KWatch.lean:209`), and 7f-6's traffic draws
  future resource versions for legacy watches (`notes/k8s-7f-scope.md` §1), so a bookmark at a future start is
  one the consumer cannot accept; etcd does not send one (`progressIfSync` returns unless `rev ≥ w.startRev`,
  `server/storage/mvcc/watchable_store.go:539`): the client spec is looser than etcd.
- **Changes.** (M2) `kProcExited` set before the processor's `sendError`; `kCancelPD` gains it; `kInElem`'s no-gap
  fact gains it as a third disjunct (the processor refutes it). (m1) error arm `err ≠ nil ∧ sie = some false ∧
  uint.nat n = 0`. (m2) `kStartOk`'s watch-list arm `st = σ0.rev ∧ m.req ≤ st` (the `1` from the caller's `Q`).
  (M1) see the next entry. Was OPEN: the Draft-local fix (`bm` admitting `p = c` unbounded) does not serve the consumer (above); the
  alternative is the client's `watchStateRespOk` start disjunct gaining `hdrRev ≤ σ.rev` (an exported client
  spec), a stop for etcd-grove-81.
- **Decision.** M2, m1, m2: decided by etcd-grove-81 (2026-11-15; m2's form chosen by the agent). M1: open.

## 2026-11-15: the client watch's progress notification at the watch's start has no state bound (7f-5a M1)

- **Spec.** `client.watchStateRespOk` (`Proof/go_etcd_io/etcd/client/v3/WatchStateDefs.lean:125-128`), the element
  of `watcher.Watch.spec`'s channel (`watchStateElemP`), and the server-level `client.rawRespOk` (same file).
- **Defect.** Too weak: a progress notification at the cursor when the cursor is the watch's start
  (`hdrRev = c`, `c + 1 = rev`) carries no bound by the state `σ` (`watchStateRespOk`) nor a certified log
  (`rawRespOk`'s `c = hdrRev` arm). A consumer cannot exclude a progress notification at a revision etcd has not
  reached: the etcd3 store's watch queues it as a bookmark (`KTail.bm` needs `p ≤ σ.rev`), and 7f-6's driver check
  rejects a bookmark above the configuration's revision while its traffic watches from future revisions.
- **Evidence.** etcd sends a progress notification to a watcher only once the store reached its start
  (`progressIfSync`: `if rev < w.startRev { return false }`, `server/storage/mvcc/watchable_store.go:539` at
  `673da07c8f`). Proof: the server-level fact already has the log (`progCovd`: `sint.nat x.rev < L.length`;
  `cmpl_cov` gives `dd ≤ Lc.length` outright), which `cmpl_prog`'s at-the-cursor case drops.
- **Proposed change.** `rawRespOk`'s progress arm always carries `∃ L, □ W.histLb L ∗ ⌜hdrRev < L.length ∧
  rangeLogEvents L o (c+1) (hdrRev+1) = []⌝` (the `c = hdrRev` arm without a log removed); `watchStateRespOk`'s
  progress arm always `hdrRev ≤ σ.rev ∧ rangeEvents σ o (c+1) (hdrRev+1) = [] ∧ kvLogOkTo σ hdrRev` (the start
  disjunct removed: at `c = hdrRev` the range is empty). A stronger post of the exported client spec; `cmpl_cov`/
  `cmpl_prog` keep the log; `raw_to_state` fires at a state through it; the readers lose a case.
- **Decision.** Approved (etcd-grove-81, 2026-11-15): strengthen, land as its own unit before 7f-5a-P; no closed
  theorem statement changes, tcb stays 870/4; upstream's traffic kept.

## 2026-11-15: the server's lease requests with auth on (auth-lease S3b; Draft `notes/auth-lease-s3b-draft.md` rev 3)

One entry for the frozen texts S3b changes (Draft §6's table); the evidence of each is the Draft's section.

- **Spec.** `EtcdServer.LeaseGrant.spec`, `EtcdServer.LeaseRevoke.spec` (`Spec/go_etcd_io/etcd/server/v3/etcdserver/`),
  `srvGrantsLeases`/`srvRevokesLeases`, `reqPropOkOn`, `putPermitOn`/`txnPermitOn`/`txnPermitM` (`ProposeOn`, `ReqOn`).
- **Defect.** No proposer of a grant, a revocation, a leased put or a leased transaction with auth on: the two lease
  specs and `srvGrants/RevokesLeases` require auth off, `reqPropOkOn` has no lease form, `putPermitOn` requires lease 0
  and `txnPermitM` `txnPlain`, though Go serves all four with auth on (`v3_server.go` `LeaseGrant`/`LeaseRevoke`,
  `requireAuthInfo` at `:447`; the apply side admits them since S3a/S3a2).
- **Proposed change.** Draft §1, §2, §4.2, §4.3: the auth-off conjuncts dropped; the specs at `isServerReqM E.authOn`
  with the client's update (`leaseGrantPermitM`/`leaseRevokePermitM`) and, on success, `authedOutB` and
  `leaseGrantResM`/`leaseRevokeResM`; `reqPropOkOn`'s write disjunct at `plainReqL lm ∨ grantPropOk lm ∨ revokePropOk lm`,
  `rqShape lm`, `grantIdOwn`; the permits' lease disjuncts at the revocable mode.
- **Decision.** Approved (etcd-grove-81, 2026-11-15, the S3b Freeze); D6: the v3rpc lease handlers' contracts and
  etcdstart's registrations at the mode in S3c.

## 2026-11-15: authTie says nothing of revocations or of a leased put's lease (auth-lease S3b D1)

- **Spec.** `authTie` and its carriers `resultIsWOn`, `entryWitOn`, `resultΨOn`, `modelOutM` (`ReqOn.lean`; frozen at
  S3a2 rev 6), read by `processInternalRaftRequestOnce.spec`/`raftRequest.spec` through `appliedOkM`.
- **Defect.** Guarded by `isKVKind` (excludes `.leaseRevoke`): a successful revocation cannot be shown granted. It
  carries no liveness: a successful leased put cannot be shown to have met a live lease (`backendStep` admits an
  applied put of a dead lease; the lease exactness is dropped at the KV arm).
- **Evidence.** Draft §3; probe `Scratch/S3bProbe.lean` (`authTieB_of_kvOutL`, `kvGrantedL_of_tieB`, `leaseLive_of_tieB`).
- **Proposed change.** Guard `authKVKind`; the post gains `plainCover rq ∨ apply.leaseExactL lt.ids rq lb o`; `authTie`
  gains the model's table `lt`, threaded through the carriers.
- **Decision.** D1 approved (etcd-grove-81, 2026-11-15).

## 2026-11-15: grantedAt is the permission check only (auth-lease S3b D2)

- **Spec.** `grantedAt`, `grantedAt_iff` (`ProposeOn.lean`), hence `writeGrantG`/`grantedRes` and the posts of
  `Put`/`DeleteRange`/`Txn.spec`.
- **Defect.** `kvGranted` omits the lease part of the model's verdict (`kvEntryOn`'s guard is `kvGrantedL`): a client's
  update cannot be refuted for a put permitted on its key but refused for its lease's keys (`etcd_authlease_safe`
  checks 2, 3, 5).
- **Proposed change.** `grantedAt` at `kvGrantedL … (leaseItemsOf (stateAfter (kvModelOn …)))`; `grantedAt_plain` keeps
  the old meaning for every request without a lease part.
- **Decision.** D2 approved (etcd-grove-81, 2026-11-15).

## 2026-11-15: Put.spec's success does not say the lease was live (auth-lease S3b D3)

- **Spec.** `EtcdServer.Put.spec` (frozen `Spec/` text), with the exported `put_applied`.
- **Defect.** The success's client result `Q (kvStateOf x.log lt)` does not exclude the state where `kvOpStep (.put op)`
  is `leaseMissing`'s identity, though Go's success means the lease was found (`checkLease`, `put.go:71`).
- **Proposed change.** The success post's pure conjunct gains `¬ (kvStateOf x.log lt).leaseMissing op.leaseID`.
- **Decision.** D3 approved (etcd-grove-81, 2026-11-15).

## 2026-11-15: txnAppliedOk does not say a leased transaction's leases were live (auth-lease S3b D7)

- **Spec.** `txnAppliedOk` (`InvRead.lean`, the writing post of `EtcdServer.Txn.spec`; frozen).
- **Defect.** As D3's for a transaction: a committed transaction's executed path's leases were live (`checkTxn`), the
  post does not say so.
- **Proposed change.** The pure conjunct gains `l ≠ x.log → txn.PathsLeaseOk (stateAfter x.log) lt.ids (t'.branch …)`.
- **Decision.** D7 approved (etcd-grove-81, 2026-11-15).

## 2026-11-15: a delivered watch event's pointers are not known to be non-nil (k8s 7f-5a-P, B)

- **Spec.** `EtcdGrove.eventAt` (`Proof/go_etcd_io/etcd/cache/v3/InvStore.lean`, exported through the client's
  `eventsAt`/`respAt`/`watchStateElemP`).
- **Defect.** It drops `ev ≠ null ∧ e.kv ≠ null`, which its producer has (`mvcc.evRd`), so the etcd3 watcher's
  `parseEvent` cannot be called on a delivered event: its `e.IsCreate()` reads the type and revisions through the
  getters, which answer defaults on a nil pointer (with `p = null` the model's `IsCreate` is `true`).
- **Proposed change.** `eventAt ev e` gains `⌜ev ≠ null ∧ e.kv ≠ null⌝`; produced by `WatchContent.evIs_facts`;
  `eventAt_elim` keeps its statement (a weakening).
- **Decision.** Approved (etcd-grove-81, 2026-11-15, (B)).

## 2026-11-15: a codec's decoding of empty data (k8s 7f-5a-P, C)

- **Spec.** `ObjCodec` (`Proof/k8s_io/apiserver/pkg/storage/etcd3/Contract.lean`), hence `kvWfHist`'s `dec v ≠ none`.
- **Defect.** Nothing excludes an empty stored value that decodes; for one, the watcher's `prepareObjs` drops the
  previous object (`len(e.prevValue) > 0` fails) and `transform` calls `filter(nil)`, where `kEvOfL` decodes it.
- **Proposed change.** A field `dec_nil : ObjCodec.dec [] = none` (Kubernetes codecs reject empty data), discharged
  for the examples' codec.
- **Decision.** Approved (etcd-grove-81, 2026-11-15, (C)).

## 2026-11-15: the client watch's close error has no known dynamic type (k8s 7f-5a-P, E2)

- **Spec.** `WatchResponse.Err.spec` (`Spec/go_etcd_io/etcd/client/v3/WatchResponse__Err.lean`; proved).
- **Defect.** Its post gives a non-nil error only nil-iff and `errStrOk`; the etcd3 watcher's `sendError` needs
  its type facts (`kErrOk`: `etcdError`/`grpcError`/`APIStatus` assertions, comparability).
- **Evidence.** `client/v3/watch.go:123-135`: `v3rpc.Error(closeErr)`, `ErrCompacted`, `v3rpc.Error(status.Error(
  FailedPrecondition, reason))`, `ErrFutureRev`; `rpctypes.Error`'s post keeps `clientErr`; the close error's
  sources carry it (`cliStreamErr`, `errorsNewOk`, `ctxErrClientAllW`), but for `io.EOF` (`eofIs` only) and
  `*status.Error`'s `isLeafError` (gaps). Review: `notes/k8s-7f5a-draft.md` §11.1.
- **Proposed change.** The post gains `clientErr err ∗ statusErrOk err` of a non-nil result (only conjuncts added;
  its six callers untouched; no `Results`/`Adequacy*`/`MainLinked` names it).
- **Decision.** Approved (etcd-grove-81, 2026-11-15, E2).

## 2026-11-15: GetCurrentResourceVersion's error arm is bare (k8s 7f-5a-P, E4)

- **Spec.** `store.GetCurrentResourceVersion.spec` (proved).
- **Defect.** Its error arm is `err ≠ nil` only; `startWatching` hands it to `sendError` (`watcher.go:456-460`, when
  `initialRev > 0 ∧ forceInitialEvents`), which needs `kErrOk`.
- **Evidence.** `store.go:741-742`: the client `Get`'s error, or `fmt.Errorf("the current resource version must be
  greater than 0")`; both branches in the proof.
- **Proposed change.** The arm gains `(clientErr err ∗ statusErrOk err) ∨ kFmtErr err` (the E3 form, an
  `*errors.errorString`, once E3's text is approved).
- **Decision.** Approved (etcd-grove-81, 2026-11-15, E4).

## 2026-11-15: interpretListError is specified only when not paging (k8s 7f-5a-P, E5)

- **Spec.** `interpretListError.spec` (proved; `paging` fixed to `false`).
- **Defect.** `syncPaginated` calls it with `paging = true`.
- **Evidence.** `errors.go:66-89`: paging and `ErrCompacted` go to `handleCompactedErrorForPaging` (`EncodeContinue`,
  whose error branch calls the untranslated `HandleError`, avoided when the caller shows `encOkL`).
- **Proposed change.** One triple over any `paging` (premise `paging = true → encOkL …` of the keys), post `listErr c e`.
- **Decision.** Approved (etcd-grove-81, 2026-11-15, E5).

## 2026-11-15: auth on implies no lease granted (auth-lease S3c; Draft `notes/auth-lease-s3c-draft.md` rev 6)

One entry for the frozen, exported and hub texts S3c changes (Draft §10's table); the evidence of each is the Draft's section.

- **Spec.** `srvGrantGuard` (+ `_expired`), `lease.bootCfg` (hub) and its laws, `lease.srvInvAt`'s body, `srvUberOn`,
  `srv_uberKVL(_on)` and the exported `server_uber_kvl(_on)`, the apply specs' `srvLessorNilM` premise, the auth component's
  `acLessor` (frozen, 2026-11-04) in `Start`/`start`/`applyAll.spec`, `isServerRunC`, `isServerBuilt_offC`;
  `EtcdServer.revokeExpiredLeases.spec`; `srvClusterBootOn_alloc` (+ exported restatement); etcdstart's `grpcUpOn`; the v3rpc
  lease handlers' specs and `quotaLeaseServer.LeaseGrant.spec`.
- **Defect.** Four couplings make "auth on" imply "no lease granted" (the guard `False` at auth on, `bootCfg`'s `on → m =
  none`, `srvInvAt`'s `srvLessorNil`, the apply specs' `srvLessorNilM`), though Go serves grants with auth on and the apply
  layer no longer reads `srvLessorNil` since S2 (`UberOn.lean:134`); the gRPC lease contracts are auth off only (S3b D6).
- **Proposed change.** Draft §1–§7: C1 guard `⌜lg = true ∧ (on = true → leasesNoExpiry)⌝`; `bootCfg`'s row `on = true → m =
  revocable → leasesNoExpiry`; `srvLessorNil(M)`, `acLessor` and their conjuncts deleted; `revokeExpiredLeases.spec` takes
  `E.authOn = false`; the auth-on allocation at a lease mode (C6); the `…M` contracts beside today's (C5′) and the auth-on
  `Md` registrations (C4, C7, C8).
- **Decision.** Approved (etcd-grove-81, 2026-11-15, the S3c Freeze, conditional on review round 5, which found no
  first-tier problem).

## 2026-11-15: store.Watch's revision bound (k8s 7f-5a-P step 5)

- **Spec.** The Draft's `store.Watch.spec` (`Proof/k8s_io/apiserver/pkg/storage/etcd3/Draft7f5a.lean`, not yet in `Spec/`).
- **Defect.** Its premise `uint.Z n < 2^63` admits `n = 2^63 - 1` for a watch without initial events, whose
  `startWatching` asks the client for `WithRev(n + 1)`, which wraps negative; the client's `Watch` spec needs `1 ≤ rev`
  (in Go etcd then answers a compacted or invalid watch: no panic, but the proof's start point is not a revision).
- **Evidence.** `watcher.go` `startWatching` (`clientv3.WithRev(wc.initialRev + 1)`); `kStartPre` (`WatchProd.lean`) asks
  `uint.Z r0 + 1 < 2^63` in that case.
- **Proposed change.** `uint.Z n < 2^63 - 1`; the Draft (§3) updated.
- **Decision.** Approved (etcd-grove-81, 2026-11-15).

## 2026-11-16: store.Watch without `concurrentDecodeOff` (k8s 7f-5b)

- **Spec.** `k8s.store.Watch.spec` (`Spec/k8s_io/apiserver/pkg/storage/etcd3/store__Watch.lean`; a hypothesis of the 7f-6 lines).
- **Defect.** Its premise `concurrentDecodeOff` (the default gate has `ConcurrentWatchObjectDecode` off) was the temporary
  premise of Q6 (`notes/k8s-7f5-scope.md`): only the serial branch of `processEvents` was planned for 7f-5a.
- **Evidence.** 7f-5b proves both branches of `processEvents` (`notes/k8s-7f5b-draft.md` §§2-4); `Enabled` of a queried
  feature returns some `b` under `featureGateOk` with no gate fact.
- **Second defect (found drafting 7f-5b, both branches).** The read laws (`kvWf`, `kvWfHist`, `kvKeysShort`) do not
  give `transform`'s premise `kRawDecOk`: an etcd event's value is the value right after its own change, so a value
  put and overwritten within one revision is in no state `kvWfHist` covers (etcd admits such revisions:
  `issues/etcd-txn-delete-then-ignore-put.md`, `issues/etcd-txn-check-intervals-sibling.md`). `notes/k8s-7f5b-draft.md` §7.
- **Proposed change.** (1) The precondition's `watchListOn ∗ rangeStreamOff ∗ concurrentDecodeOff ∗` becomes
  `watchListOn ∗ rangeStreamOff ∗`. (2) The first read law `Q lb σ ⊢ ⌜lb ≤ σ.rev ∧ kvWf c σ ∧ kvWfHist c σ ∧
  kvKeysShort σ⌝` gains `∧ kvWritesDec c σ` (every value a revision up to `σ.rev` puts under the store's prefix
  decodes). Nothing else. Uses of the spec as a hypothesis drop the gate argument and prove the new law.
- **Decision.** (1) planned by the Scope (Q6); (2) option (A), decided by etcd-grove-02, 2026-11-16; producer 7f-6
  (stage C's `KvOne` in `KvNext`). Both reported again at the land stop.
- **Third defect (found at 7f-5b step 1).** `transform` needs `0 ≤ sint.Z modRev` of each raw event (its proof uses
  `W64 (sint.nat modRev) = modRev`); nothing in the spec bounds `σ.rev` (`kvWfHist` bounds the unsigned `modRev`
  only, the client watch gives no `kvRevFits`). Without it the stream facts are false at `σ.rev ≥ 2^63` (`kEvOfL`'s
  `rv = sint.nat modRev = 0`; Go's `UpdateObject(obj, uint64(rev))` the wrapped value).
- **Proposed change (3).** The first read law also gains `∧ kvRevFits σ.rev` (`σ.rev + 3 < 2^63`).
- **Decision (3).** Decided by etcd-grove-02, 2026-11-16; producer 7f-6 (the reads its `Q` fires at give `kvRevFits`).

## 2026-11-16: the store's update report gains "one change per step" (k8s 7f-6 C, F1)

- **Spec.** `KvNext` (`Proof/k8s_io/apiserver/pkg/storage/etcd3/Updates.lean`), in the posts of `k8sAu1` and `k8sAuRW`
  (what a write's firing tells its caller); `kvNext_step`, `k8sAu1_kvAu1`, `k8sAuRW_kvAu1`, `k8sAusRW_kvAu1`.
- **Defect.** `KvNext` tells the caller only the next state, so its history (`oneKeyRevs`, over state differences) cannot
  exclude a revision of two changes of one key, where the store's watch (`kStreamOk`, over etcd's events, one per change)
  delivers two events and the driver's check one: the bridge to `StreamOkL` is false without it.
- **Evidence.** `notes/k8s-7f6c-plan.md` §2 (the counterexample); the store sends single-operation transactions
  (`putTxn`, `delTxn`, `OptimisticPut`/`OptimisticDelete`).
- **Proposed change.** `KvNext`'s step disjunct gains `KvOne σ σ'` (every revision the step adds has at most one change);
  `kvNext_step` takes it of the operation's step, `kvOne_optPut`/`kvOne_optDel`/`seedOp_one` prove it of every producer.
- **Decision.** Approved (etcd-grove-02, 2026-11-16, F1 option 1).

## 2026-11-16: auth-lease S4 Freeze rev 2 (review r2): D-h and the lessor law's threshold

- **Spec.** Freeze drafts (not yet in `Spec/`): `etcdLeaseGrantSpecOn`/`etcdLeaseRevokeSpecOn`'s D-h reply fact;
  `lessor_keys_of_read`'s threshold; `EtcdServer.LeaseTimeToLive.spec`'s no-keys arm (R1).
- **Defect.** D-h's `□ (E.authOn = true → ∃ info, principalBoundT …)` is false of Go (with auth disabled in the store,
  `requireAuthInfo` returns `nil` and a token-less grant succeeds; `E.authOn` is the component, not the flag). The law's
  threshold `log.length` over `readLogOk γr c log` is false (`log` may extend what the member applied; also off by one).
  R1's no-keys arm has no server spec to come from (`authedOutB`'s disabled arm is unanchored).
- **Evidence.** `/shared/tmp/auth-lease-s4/freeze-review-r2.md` (H1, S1, T1); `v3_server.go:1277-1280`;
  `kvStateOf_rev` (`KVModelDefs.lean:988`).
- **Proposed change.** Freeze rev 3 (§10 of `notes/auth-lease-s4-freeze.md`): `n`-relative `leaseCheckT … n` replies
  with a new `authedFrom` on `requireAuthInfo.specC`/`LeaseGrant.spec`/`LeaseRevoke.spec`; the law over the member's
  store floor `kvLogLb E.γs F`, threshold `F.length - 1`.
- **Decision.** Pending (Freeze review by etcd-grove-02 and the user).

## 2026-11-16: auth-lease S4 item 7b: the lessor window token threaded in place (thaw approved)

- **Spec.** The write chain from the apply loop to `lease.lessor.Attach`/`Detach` (the list, old → new, in
  `notes/auth-lease-handoff.md`, "7b plan").
- **Defect.** The per-member lessor law (`lessor_keys_of_read`, Freeze §5) cannot be proved for a snapshot pushed by
  the entry still being applied. Its fact must be stored in the lessor's invariant at push time, and `Attach`/`Detach`
  can prove it only with the entry's target item map (`questions.md`, "Item 7b").
- **Evidence.** The design review of 2026-11-16 (read only). Each encoding that skips a push-site premise fails: a
  frozen-item set, per-key tokens, a self-dropping window hidden in `leaseOwn`, epoch tags.
- **Proposed change.** Every statement of the chain takes `lease.leaseOwnW γl L I w` (`w : Option LWin`) in place of
  `lease.leaseOwn γl L I`, plus the premise `winStep w I I'`, which is trivial at `none`. `leaseOwn γl L I` becomes
  `leaseOwnW γl L I none`, so a client that holds `leaseOwn` discharges the new premise trivially: no client's
  statement gets weaker.
- **Decision.** Approved by the user, 2026-11-16, via etcd-grove-02: option 2 (in place; no `…specW` siblings). Limits:
  STOP if the change reaches a closed theorem's statement, needs an axiom, `sorry` or trusted text, or makes a thawed
  statement weaker for an existing client. `lessorLawMask` gains `lessorRdN` (the form approved with the Freeze).
- **Landed (step 1-2, lease, 2026-11-17).** Vocabulary: `lease.LWin`, `LWinRec`, `lastWin`, `winStep`, `winStable`,
  `winEnd`, `winsOk`, `itemsLive`, `winOwn`, `lessorWinTie`, `leaseOwnW γl L I w` (`leaseOwn γl L I` is now the
  abbreviation `leaseOwnW γl L I none`, as are `lessorUser`/`leaseOwnOpen`/`lessorUserOpen`/`lookupView`/
  `lookupViewAfter` of their `W` forms), `win_push` (open a window or a free marker). The `NewLessor` axiom's ghost
  allocation extended (decided by etcd-grove-03, soundness note in `questions.md`, "Item 7b step 1"); its post gains
  `lessorWinTie γl []`. Thawed, old → new:
  - `lease.lessor.Attach.spec`: `leaseOwn γl L I` → `leaseOwnW γl L I w ∗ ⌜winStep w I (insertAll I xs id)⌝`, post
    `leaseOwn γl L (insertAll I xs id)` → `leaseOwnW γl L (insertAll I xs id) w` (∀ `w`; at `none` the old spec).
  - `lease.lessor.Detach.spec`: the same with `deleteAll I xs`.
  - `lease.lessor.GetLease.spec`, `Grant.spec`: `leaseOwn γl L I` → `leaseOwnW γl L I w` in pre and post (`w` passed
    through; at `none` the old spec). `Lookup.spec`: `lookupView γl U`/`lookupViewAfter γl id l U` →
    `lookupViewW γl w U`/`lookupViewAfterW γl id l w U` (the same).
  - `Revoke.spec` unchanged so far (its deletes need `mvccDeleter`'s window form, step 3).
  - Closed results whose text is unchanged and whose meaning gets stronger (decided fine by etcd-grove-03,
    2026-11-17): `txn/Results.lean` `txn_runTxn` (`lessorUser`), `etcdserver/Results.lean` `server_kv_backend`
    (post `mvccDeleter`), `lessor_apply_contract` (`isApplyLessor`).
- **Step 3 (mvcc, 2026-11-17).** Decided by etcd-grove-03 (option (a) of `questions.md`, "Item 7b step 3"):
  **premise strengthened, discharged by every client.** Old → new:
  - `mvcc.isLessor le γl` (`InvStore.lean`): the `GetLease`/`Attach`/`Detach` clauses over `leaseOwn γl L I` →
    `∀ w`, over `leaseOwnW γl L I w` (`Attach`/`Detach` with `⌜winStep w I I'⌝`); `SetRangeDeleter` unchanged.
  - `txn.isTxnLessor le γl` (`txn/Defs.lean`): `isLessor` as above, and the `Lookup` clause over `lessorUser γl L I`
    / `lessorUserOpen …` → `∀ w`, over `lessorUserW γl L I w` / `lessorUserOpenW … w`.
  - Closed results whose premise text is unchanged and whose premise gets stronger: `etcdserver/Results.lean`
    `server_kv_backend` and its two siblings (lines 939, 1010, 1155: `mvcc.isLessor le γl`), `txn/Results.lean`
    `txn_runTxn` (`isTxnLessor`). Every client discharges them from the real lessor (`isLessor_of_lessorInv`,
    `isTxnLessor_of_lessorInv`, which the window-generic lessor specs prove at any `w`).
  - Form: `winStep w I I'` is now monotone (`I k = T k → I' k = T k`: an item at its target stays there), weaker than
    the step-1 form (an item changed goes to its target), so that `put`'s `Detach` then `Attach` of a key moving to its
    target are both steps; `Attach`/`Detach`'s premise gets weaker (their specs stronger). Above the lessor the callers
    take `winMove w I I'` (the step-1 form) for the whole write, which gives each lessor call's `winStep`
    (`winStep_pre`/`winStep_post`/`winStep_of_move`).
  - `mvcc.storeTxnWrite.{put,delete,deleteRange,Put,DeleteRange}.spec`, `metricsTxnWrite.{Put,DeleteRange}.spec`:
    `leaseOwn γ.leases L (pendItems ilog pend)` → `leaseOwnW … w` in pre and post (∀ `w`, last binder), plus the
    premise `⌜winMove w (pendItems ilog pend) (pendItems ilog (pend ++ ops))⌝` (`True` at `none`).
  - `mvcc.api.Txn.Put.contract`: the same (`leaseOwnW … w`, `winMove w (pendItems σ.log pend) (pendItems σ.log (pend
    ++ [.put k vv leaseID]))`). `Txn.DeleteRange.contract`: `leaseOwnW … w` and `⌜winDrops w (pendItems σ.log pend)
    (fun it => delSel (decide (endk = slice.nil)) k e it.Key')⌝` (the window drops the range's items: stated over the
    range, since the caller learns the keys found, `delKeys`, only after the call).
  - `lease.lessor.Revoke.spec`: `leaseOwn γl L I₀` → `leaseOwnW γl L I₀ w` in pre and both posts (∀ `w`, last
    binder), plus `⌜winDrops w I₀ (fun it => I₀.lookup it = some id)⌝` (the window drops the lease's items).
  - Not thawed (left at `leaseOwn`): `KV.Put/DeleteRange.contract`, `writeView.{Put,DeleteRange}.spec` (no apply-loop
    caller), `mvccDeleter` (the window is in the owner's resource, not in the deleter's transaction).
- **Step 4 (server txn, 2026-11-17).** Form accepted by etcd-grove-03 (`questions.md`, "Item 7b step 3 forms: reviewed").
  New vocabulary (`txn/ApiVocab.lean`): `txn.delSelOf o` (the items a delete's range selects), `txn.putItemsOf I o` (the
  item map after a put request), `txn.WinOp`/`txn.WinOps w s0 r s ops` (built as `OpsOk`: a put's `winMove` to the
  state its change leaves, a delete's `winDrops` over its range, a nested transaction's chosen branch); lemmas
  `winOps_none`, `winOps_append`/`_drop`/`_drop'`, `winOp_txn`, `winOps_gets`, `winOp_put_et`, `pendItems_putChangeOf`
  (`ApiLemmas.lean`). Thawed, old → new (each `∀ w`, last binder; at `none` the old spec):
  - `txn.put.spec`: `leaseOwn γl L (pendItems σ.log pend)` → `leaseOwnW … w` in pre and post, plus
    `⌜winMove w (pendItems σ.log pend) (pendItems σ.log (pend ++ [putChangeOf o …]))⌝`.
  - `txn.deleteRange.spec`: the same with `⌜winDrops w (pendItems σ.log pend) (txn.delSelOf o)⌝`.
  - `txn.executeTxn.spec`: `(⌜isRead k⌝ ∨ leaseOwn …)` → `(⌜isRead k⌝ ∨ leaseOwnW … w)` in pre and post, plus the pure
    conjunct `isRead k = true ∨ WinOps w s0 r (mstate k) ops`.
  - `txn.txn.spec`: `(⌜ro⌝ ∨ leaseOwn …)` → `(⌜ro⌝ ∨ leaseOwnW … w)`, plus `ro = true ∨ WinOps w s0 r s0 branch`.
  - `txn.Txn.specSole`: `lessorUser γl L I` → `lessorUserW γl L I w` in pre and both posts, plus
    `⌜WinOps w (stateAfter log) (W64 log.length) (stateAfter log) (t.branch …)⌝`. `specRead` unchanged.
  - `txn.Put.spec`: `lessorUser` → `lessorUserW … w` (pre, three posts), plus `⌜winMove w I (txn.putItemsOf I o)⌝`.
  - `txn.DeleteRange.spec`: `leaseOwn γl L I` → `leaseOwnW … w` (pre, both posts), plus
    `⌜winDrops w I (txn.delSelOf o)⌝`.
  - `txn.checkLease.spec`, `checkPut.spec`, `checkTxn.spec`: `lessorUser γl L I` → `lessorUserW γl L I w` (passed
    through; `isTxnLessor`'s `Lookup` is at any window since step 3).
  - Callers: `txn/Results.lean` `txn_runTxn` (statement unchanged, at `none`: `winOps_none`); the applier's
    `applierV3backend.{Put,DeleteRange,Txn}` at `none` until step 6.
- **Step 5 (2026-11-17).** `txn/WinLemmas.lean`: `winOps_of_nodup`, `winOps_txn_of_nodup` (a run whose changes have
  distinct keys is within the window targeting the items after it). No statement thawed.
- **Step 6, the permits (2026-11-17).** Decided by etcd-grove-03 (`questions.md`, "Item 7b step 6 decision"): **premise
  strengthened; every client (the v3rpc handlers) discharges it by `check_gives_nodup` from `siblingSafeL`/
  `noFromKeyDelL`.** New `txn.txnKeysNodup t` (`WorkloadDefs.lean`: the run's change keys distinct at every sorted
  start state, as `txnShape`), with `txn.delsPresent_srvOps` and `v3rpc.txnKeysNodup_of_check` (`CheckShape.lean`; no
  new client premise: the handler's `checkIntervals`, `txnNoZeroEnd` and `siblingSafeL`). Old → new:
  `txnPermit` (`InvRequest.lean`), `txnPermitOn`, `txnPermitM` (`ReqOn.lean`): `… ∧ txn.txnShape t⌝` →
  `… ∧ txn.txnShape t ∧ txn.txnKeysNodup t⌝`. Closed result whose premise text is unchanged and gets stronger:
  `etcdserver/Results.lean` `txn_applied` (`txnPermit`). `ServerKVOn.txnPermitM_of_dep`'s shape hypothesis gains it.
- **Step 6, the apply thread's premise (2026-11-17).** Form (agent; `questions.md`, "rqShape's conjunct: forms"):
  `apply.rqOk`'s transaction arm `txn.TxnPreA log t ∧ putOk log` → `… ∧ txn.txnKeysNodup t` (internal: no `Results`
  statement mentions `rqOk`; producers `rqShape_txnL`/`rqShape_of_txn` discharge it from the permits).
  `txn.txnKeysNodup` moved to `txn/TxnRun.lean`.
- **F1-F3, F2 (2026-11-17).** Accepted by etcd-grove-03: `txn.isTxnLessor` gains the window-witness clause (now named
  `lease.winWitOk`): premise of the closed `txn_runTxn` and of `server_kv_backend`'s chain strengthened, text unchanged,
  discharged by `isTxnLessor_of_lessorInv` (`lease.win_wit`). `lessor.Revoke.spec`'s begin payload `winWit … -∗ auEnd`.
  F2: `txn.putAU/delAU/txnBeginAU` = `…W none`, the commit under `lease.winWit … w (pendItems σ₀.log pend) -∗`;
  `txn.Put/DeleteRange/Txn.spec` take the `W` forms; `txn.DeleteRange.spec` gains `lease.winWitOk (mvccLeases γ)`; the
  `winMove`/`WinOps` premises of `txn.Put.spec`/`Txn.specSole` move into the begin payloads (forms in `questions.md`).
- **The applier at a window (2026-11-17, in progress).** `AEnv.win`/`AEnv.Wt` (defaulted fields), `winTgt` in
  `putPre`/`deletePre`/`txnPre`/`revokePre`, `envAus`' end builder at `∀ w` with the token, `revokeClause` and
  `isApplyLessor`'s `Grant` at `∀ w` (forms in `questions.md`, "Item 7b F2 and the applier at a window: forms").

## 2026-11-16: the auth read contract per bucket, the write contract's sessions (auth-schema-srv A0)

- **Spec.** `auth.authReadTxOk` (trusted: given by `authSchemaSrv`, `authSchemaSnap`, `authSchemaBoot` through
  `authBackendOk`), `authReadTxLocked`, `authReadTxLockedFrom`, `auth.passwordChecked` (`CheckPassword.spec`'s post);
  `authBatchTxLk`/`authBatchTxLkR` (trusted likewise, through `authWBackendOkR`), `commitRevision.spec`.
- **Defect.** The read contract promised every `RLock` one recorded auth state; Go's `batchTxBuffered.Unlock` writes a
  step's puts back and releases the read lock before it commits the step's deletes, so a reader sees a step half
  applied (`notes/auth-schema-srv-refuted.md`, "Second refutation"). `passwordChecked` ("the revision of a recorded
  state that has the user") is false of Go for the same reason.
- **Evidence.** `nonissues/etcd-auth-readtx-delete-window-mixed-state/zz_authschema_window_test.go` (fails);
  `zz_authschema_perbucket_test.go`: `TestAuthSchemaReadPerBucket` (the store's admin steps; 0 per-bucket violations in
  three runs of ~10-13k steps and ~1.1-1.5M reads, ~13-17k reads of no single state, the old text's control) and
  `TestAuthSchemaReadMixedBucketSession` (a batch that puts and deletes in one bucket: readers see the bucket in
  neither state, ~33k times in 20 s: the per-bucket reading needs the write side's discipline).
- **Proposed change.** Q1 (a): `RLock` gives a view `BkView` (a state per bucket: `auth`, `authUsers`, `authRoles`),
  `authViewSnap(From)`: each recorded (at an index ≥ the lower bound), the users' index ≤ the `auth` bucket's; each
  read at its bucket's state (`authReaderOkV`); the latest clause (with the write token) one state, `BkView.uni st`.
  `passwordChecked`: the user in a recorded state and `rev` the revision of a recorded state not earlier. The write
  contract gains a session token `Sw : AuthSess → IProp` (puts and deletes never in one bucket in one session).
- **Decision.** Q1 (a) approved by the user 2026-11-16 via etcd-grove-02; the session discipline is what makes Q1 (a)
  true (reported at the A0 stop).

## 2026-11-16: the watch's annotated object is not expressible for the driver (k8s 7f-6 D)

- **Spec.** `store.Watch.spec`'s vocabulary (`Proof/k8s_io/apiserver/pkg/storage/etcd3/WatchDefs.lean`):
  `WatchSpec.annotate : Obj → Obj`, `watchContractOk`'s second conjunct (`AnnotateInitialEventsEndBookmark`'s post
  `S.objAt x (W.annotate o) rv`), `wevAt` (`S.objAt v.Object' (if e.ann then W.annotate e.o else e.o) …`); through
  them `New.spec`'s `storeWatchOk` (given `watchContractOk S W codec`).
- **Defect.** No `W : WatchSpec DObj` satisfies `watchContractOk driverSpec W codec`, so the driver can never produce
  the `storeWatchOk` that `store.Watch.spec` takes (the 7f-6 closed theorems could not be linked). The driver's
  `driverSpec.objAt` is `objAtD x o rv := ∃ p n, … ∗ p ↦ o.toObj n`, and `DObj.toObj` sets `Annotated' := false`
  (`DObj` has no annotation; every stored object is unannotated). Go's `AnnotateInitialEventsEndBookmark` on the
  driver's `*Obj` calls `SetAnnotations`, which sets `Annotated = true` (`examples/k8s/etcd3/k8setcd3.go:306-314`):
  the post `objAtD x (W.annotate o) rv` is false for every `annotate`. For the same reason `toWEvent` cannot give the
  bridge's `kWEvRel e w` (`KWatchBridge.lean`, `kToWEv`: `Annotated' := e.ann`) from `wevAt` for the annotated bookmark,
  the event `watchOk` checks the annotation of (`watchListOk`).
- **Evidence.** Code reading of the three definitions and the Go driver; found writing stage D's `toWEvent` spec.
- **Proposed change.** `WatchSpec` describes the annotated object by an ownership predicate instead of a function on
  bodies: `structure WatchSpec (GF) (Obj) where annAt : GoInterface → Obj → GoString → IProp GF` ("`x` holds the body
  `o`, annotated, at `rv`"); `watchContractOk`'s annotate conjunct posts `W.annAt x o rv`; `wevAt` reads
  `if e.ann then W.annAt v.Object' e.o rv' else S.objAt v.Object' e.o rv'`. The driver's `W`: `annAt x o rv := ∃ p n,
  ⌜x = mkOk (*Obj) p ∧ p ≠ null ∧ rv = rvStr n⌝ ∗ p ↦ { o.toObj n with Annotated' := true }`. Users: `WatchDefs`
  (3 places), `watchChan__transform`'s spec and proof (the bookmark), `New.spec` (the `W` binder's type);
  `store.Watch.spec`'s statement changes only in `W`'s type. No trust-base change.
- **Decision.** Accepted as proposed, decided by etcd-grove-02, 2026-11-16; made by the 7f-6 stage D agent on `k8s-7f6`
  (7f-5's landed proofs: bodies only).

## 2026-11-16: three more closed theorems over the file extension (decision A, landing `wal-lean`)

- **Specs.** `etcd_leaseN_adequate`/`etcd_leaseN_safe`, `etcd_leaseexpiryN_adequate`/`etcd_leaseexpiryN_safe`,
  `etcd_authN_adequate`/`etcd_authN_safe` (new on `lean` since the last merge, `523c2a5495`).
- **Defect.** As the 25 earlier ones: the bodied `fileutil`'s package initializer probes `F_OFD_GETLK` over
  `fsExt`, so `[idIssueExt]` (`TrivialExt.lean`) no longer has the extension the server's initialization needs.
- **Change.** As `putgetN`'s: the extensions are `[idIssueExt, fsExt]` (`lib/etcdstart/FsExts.lean`), one new
  premise `Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world)`; every other premise and the conclusion unchanged.
- **Decision.** The user's decision (A) of 2026-11-15 for this class of change; listed for the user's review
  with the earlier 25.

## 2026-11-17: the backend's hook step keeps the tracked buckets' write buffer and kinds (auth-schema-srv A1)

- **Spec.** `backend.hookStep` (`Model2.lean`): in the hooks' contract `hooksSpec`/`hookFnSpec` (inside `isBackend`),
  in `BackendHooks.OnPreCommitUnsafe.spec`'s post and the exported `cindex_hook_backend`
  (`etcdserver/Results.lean:1068`, post `⌜backend.hookStep P st st'⌝`).
- **Defect.** None of Go; a gap of the model: the hook step left the tracked buckets' contents (`rbData`) but not what
  the write buffer holds for them, so a hook could buffer a put there (one it then deletes) that a later write-back
  shows readers; A1's read model over the tracked buckets (`notes/auth-schema-srv-a1-scope.md`, D2) needs it excluded.
- **Evidence.** The server's hook (`BackendHooks.OnPreCommitUnsafe`) writes `meta` only (`storage/hooks.go`), not a
  tracked bucket (`mvcc.KBReal.P`'s `RB`: the rest buckets).
- **Change.** Old: `... ∧ dlR P st'.dl = dlR P st.dl ∧ st'.win = st.win`. New: the same `∧ (∀ n i, P.BT.lookup n =
  some i → P.RB n = true → bkOf st'.W.bks i = bkOf st.W.bks i) ∧ (∀ n, P.RB n = true → st'.tk n = st.tk n)` (`tk` the
  new ghost field `BSess.tk`, the session's bucket kinds). Stronger only: as a post (`cindex_hook_backend`,
  `OnPreCommitUnsafe`) it says more; as the hook's obligation it asks more of the hook, which the server's meets.
- **Decision.** Accepted by etcd-grove-03 (2026-11-17, A1 Scope decision 4); the user to be told by etcd-grove-03.
- **Addendum (A1.4, 2026-11-17, form decided by the agent, reviewed at checkpoint).** One more conjunct in `trkKept`:
  `∧ st'.cw = st.cw` (`cw` the new ghost field `BSess.cw`, the claimed buckets written through a claimed part). Same
  direction (stronger as a post, more asked of a hook: the server's writes `meta` through an unclaimed part, which
  keeps `cw`). Needed by `unsafeCommit`: the commit after the hook needs every claimed bucket still idle (or, from
  A1.5, handed to `Unlock`'s accessor), and the hook's batch lock is in the client-facing mode, which allows claimed
  writes inside the hook's window (`cwOk`).

## 2026-11-17: a nested auth message's size cache in an invariant, its `state` not held (auth-schema-srv A3)

- **Specs.** The predicates `auth.userOptsIs` (and through it `auth.userOptsAt`), `auth.ownPermW`, `auth.ownPermS`
  (`auth/Buckets.lean`); through them the trusted `proto.UnmarshalUser`, `proto.MarshalIRR`,
  `pbutil.MustUnmarshalMessage`, the gRPC models of `AuthUserAddRequest`/`AuthRoleGrantPermissionRequest`
  (`PerTypeAuth.lean`), and the exported `v3rpc.userAdd_end_to_end_on` (`api/v3rpc/Results.lean:794`, premise
  `auth.userOptsAt o b`; its only linked caller, `Results.lean:959`, still goes through).
- **Defect.** The predicates held the nested message's whole struct `↦□`, its `sizeCache` and `state` included: false
  of Go (`proto.Marshal` of a message holding it stores the nested size caches; `String()` and any `ProtoReflect` store
  a nested `state`), so no spec of `Marshal` (`proto.MarshalUser`/`MarshalRole`, A3) could be stated over them, and
  `MarshalIRR`'s precondition held read-only cells the call writes.
- **Evidence.** `examples/authpbmarshal/` (`TestMarshalWritesNestedSizeCache`, `TestStateWrites`,
  `TestConcurrentSharedNested`; the attack's `TestNestedOnlySizeCache`, `TestConcurrentEverything`); review
  `notes/axiom-review/auth-a3-marshal.md`; Draft `notes/auth-schema-srv-a3-draft.md` §1-§4.
- **Change.** Old: `o ↦□ {state' := st, NoPassword' := b, unknownFields' := uf, sizeCache' := sc} ∗ uf ↦*□ u` (and
  likewise the `Permission` of `ownPermW`/`ownPermS`, `ownPermW`'s unknown-field bytes not held). New: each wire field
  `↦□` (`NoPassword`, `unknownFields` with its bytes; `PermType`, `Key`, `RangeEnd`, `unknownFields`, with
  `ownPermW` now holding `∃ ub, uf ↦*□ ub`), `inv pbSizeCacheN (∃ sc, sizeCache ↦ sc)`, no `state`.
  `userAdd_end_to_end_on`'s premise text is unchanged; its meaning moves: old, the request's `Options` whole struct
  read-only; new, its wire fields read-only and its size cache in an invariant. Incomparable; both follow from a
  freshly allocated or decoded message, which is what gRPC's decoder and a client's literal give.
- **Decision.** Accepted by etcd-grove-03 (2026-11-17, A3 decisions 1-3, after the independent attack).

## 2026-11-17: the auth realization's premise hands out one reader ticket fewer (auth-schema-srv A6.1b)

- **Spec.** `authSchemaSrv` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/AuthSrv.lean`; trusted text, the closed
  auth theorems' named hypothesis `hD22`, discharged at A7).
- **Defect.** Not realizable as stated over the backend's specs: its write contract's reads (`authBackendReads`:
  `GetUser`, `GetRole`, `GetAllUsers`, `{{ T ∗ authOwn M hs }}`) take no reader ticket, while schema's code runs
  `ReadTx().RLock()`, which takes a reader slot (`backend.readTx.RLock.spec`'s `rdTok`); the realization's slots are
  the store's share `authRdSlots` (`backend.authRdN` of them) and the premise handed out `authRdN` tickets, each of
  which may be in use concurrently with the apply thread's read: `authRdN + 1` readers on `authRdN` slots.
- **Evidence.** questions.md "A6.1b" (the count); `RdPool.lean` (`rdAuth`: exactly `authRdN` `rdTok`s); the server
  never used the `authRdN`-th ticket (`AuthSrv.lean`, `srv_auth_tp_on`'s proof dropped it: `authRdSupply` is
  `authRdN - 1` copies, the auth applier reading with the write token).
- **Change.** Old: `([∗list] _x ∈ List.replicate backend.authRdN (), R)`. New: `([∗list] _x ∈ List.replicate
  (backend.authRdN - 1) (), R)`; the realization keeps one slot for the write token's reads (exchanged against `T`,
  exclusive). The premise promises less, so the closed theorems taking it are stronger; their text is unchanged.
  `authSchemaSnap`'s text has no ticket count (the boot's tickets work on every later backend): unchanged.
- **Decision.** Option (b), decided by etcd-grove-03 (2026-11-17), after the supply check: `authRdSupply`
  (`authRdN - 1` plain copies), `newAuthStore_on` (`N = authRdN - 1`), the server's 66: no consumer short.

## 2026-11-18: the auth realization's boot write contract takes the unset hook (auth-schema-srv A6, fix (A))

- **Spec.** `authSchemaSrv` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/AuthSrv.lean`; trusted text, the closed
  auth theorems' named hypothesis `hD22`, discharged at A7).
- **Defect.** False (`notes/auth-schema-srv-refuted.md`, third refutation): the boot write contract (persistent, at
  `authWTok γc`, hook `P f` chosen at boot) outlives the unset hook, which the constructor's wand gave back; a
  client that sets a panicking hook and calls the contract's `Lock` (schema: `LockInsideApply`, which runs the
  hook) gets a no-panic triple of a panicking call.
- **Evidence.** `batch_tx.go:113-120` (`LockInsideApply` runs `txPostLockInsideApplyHook`);
  `backend.batchTxBuffered.LockInsideApply.spec` takes `plHookAt γ dq f`; questions.md "A6 STOP".
- **Change.** Old: `authWBackendOkR … P f (authWTok γc) Wb`; `{{ authWTok γc ∗ Wb }} CreateAuthBuckets {{ authWTok γc
  }}`; the token `authWTok γc` handed out; `(Post -∗ bOpen d.γB qo ∗ plHook d.γB func.nil)`. New: at `T_b :=
  authWTok γc ∗ plHook d.γB func.nil` (the contract, the triple, the token handed out); `(Post -∗ bOpen d.γB qo)`.
  The premise is unchanged (still takes `plHook d.γB func.nil`). The contract now promises its `Lock` only to the
  holder of the unset hook; the hook comes back with the token rather than after `Post`. Server: passes `T_b` to
  `newAuthStore_on` and splits the token it gets back; `authApplyResPre` (internal) names the schema auth backend
  (`ablOn`) in place of the boot contract, `authApplyResB_of_pre` taking the contract at the frozen hook.
- **Decision.** Fix (A), decided by etcd-grove-03 (2026-11-18); for the A7 trusted-text list.

## 2026-11-18: the auth lend takes a revision of at least 1; the snapshot clause takes `permKeysOk` (auth-schema-srv A6, STOP 2)

- **Spec.** `authBkLend` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/AuthBkHook.lean`; trusted text, in both
  `authSchemaSrv` and `authSchemaSnap`) and `authSchemaSnap` (`AuthSnapKit.lean`; trusted text).
- **Defect.** (L) False (`notes/auth-schema-srv-refuted.md`, fourth refutation): `authSchemaSrv` hands out the lend at
  boot, before the auth buckets exist or hold a revision; its law promises `authBucketsAt bootState r` (which needs the
  `authRevision` key) of empty buckets; a client lends at `[bootState]` and runs `backend.Snapshot` with the lend's
  `RL`, whose post then claims it of the real data. (P) `authSchemaSnap` is not realizable as stated: the read
  contract's views need `authStateAt` (with `permKeysOk`) of the snapshot's state, which neither `authLockI st` nor
  `authBucketsAt st r` gives.
- **Evidence.** `backend.backend.Snapshot.spec` (the observation's `Q` of the committed data); a fresh backend has
  no auth bucket before `CreateAuthBuckets`; `auth.authStateAt` (`Model.lean`); questions.md "A6 STOP 2".
- **Change.** (L) `authBkLend`'s clause takes `⌜1 ≤ st.revision⌝` after `⌜hs.getLast? = some st⌝`; the consumer
  (`srvAuthApplyResB_lend`) discharges it from `bump bootState` and the monotone revision. (P) `authSchemaSnap` takes
  `⌜auth.permKeysOk st⌝` after `⌜authBucketsAt st r⌝`; its caller discharges it from `SnapAuthRecover.histWf`. Both
  ask less of the realization (weaker hypotheses).
- **Decision.** (L-rev) and (P2) approved by etcd-grove-03 (2026-11-18); for the A7 trusted-text list with fix (A).

## 2026-11-17: `proto.Marshal.spec` (KeyValue) -- the encoding's length unstated (S1b)

- **Spec.** `Spec/google_golang_org/protobuf/proto/Marshal.lean` (`proto.Marshal.spec`, a trust-boundary axiom).
- **Defect.** `mvcc.kvEncode` is opaque and the spec said nothing of its length, so no proof could show an
  entry mvcc writes (`revBytes`, `kvEncode kv`) within bbolt's `bboltEntryMax`, which the proved
  `Bucket.Put` takes (stage S1b of `notes/bbolt-integration-plan.md`).
- **Evidence.** `storeTxnWrite.put`/`delete`'s `UnsafeSeqPut` (`keyPutOk`'s new entry bound).
- **Change.** The post gains `⌜(mvcc.kvEncode kv).length ≤ kv.key.length + kv.value.length + 128⌝`: protobuf's
  wire format, six fields each a one-byte tag and a varint of at most 10 bytes (66 bytes of framing).
- **Decision.** Approved by the coordinator (2026-11-17, a true length fact); applied on `bbolt-putbound`.

## 2026-11-17: `schema.MustUnsafeSaveConfStateToBackend.spec` -- the JSON's length unstated (S1b)

- **Spec.** `Spec/go_etcd_io/etcd/server/v3/storage/schema/MustUnsafeSaveConfStateToBackend.lean` (axiom).
- **Defect.** Its callback took any bytes, so the hook's put of the conf state could not be shown within
  `bboltEntryMax`.
- **Evidence.** `BackendHooks.OnPreCommitUnsafe`'s put (`batchTxBuffered.UnsafePut`'s new entry bound).
- **Change.** Premise `storage.csOkN n cs` (nil, or read-only with at most `n` ids); the callback gets
  `⌜vb.length ≤ 25 * n + 128⌝` (JSON of a `ConfState`: `null`, or four `omitempty` id lists and `auto_leave`,
  at most 86 bytes of names and punctuation, each id at most 20 digits and a comma). The hooks keep the
  bound (`csInv`: `csOkN csIdMax`, `csIdMax = 2 ^ 20`, the server's voters' bound `srvMemOk`).
- **Decision.** Approved by the coordinator (2026-11-17); applied on `bbolt-putbound`.

## 2026-11-17: `etcdKeyMax` -- `2 ^ 27` let a key and a value pass a bbolt entry (S1b)

- **Spec.** `Proof/go_etcd_io/etcd/cache/v3/EtcdModel.lean` (`etcdKeyMax`, in the statements of the client
  model's laws `etcdState_keys`/`etcdState_vals` and of k8s's and the client's specs).
- **Defect.** A key and a value of `2 ^ 27` bytes each, encoded, pass `bboltEntryMax = 2 ^ 28`.
- **Evidence.** mvcc's put (`storeTxnWrite.put`'s entry bound).
- **Change.** `2 ^ 27 - 2 ^ 19`, the bound the request check gives (`etcdMaxRequestBytesOk`:
  `MaxRequestBytes + 2 ^ 19 < 2 ^ 27`). Stronger client-side facts, the same proofs; the coordinator had
  proposed sum bounds (`k + v ≤ n`) in `ChPutsLe`/`irrPutsLe`/`TxnOp.putsLe` and `MarshalIRR`'s statement,
  which this replaces: no axiom statement and no definition but this constant changes.
- **Decision.** Applied on `bbolt-putbound` (2026-11-17); for the coordinator's review.

## 2026-11-17: `zap.Logger.Panic.spec` (and the mvcc `keyIndex` panics) -- a panic value no Go program raises

- **Spec.** `Spec/go_uber_org/zap/Logger__Panic.lean` (`zap.Logger.Panic.spec`, the axiom
  `zap.Logger.Panic.wp_proof`) and the plan's `SpecPlan/Spec/go_uber_org/zap/Logger__Panic.lean`; through
  it, the panics of `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/keyIndex__{put,get,tombstone,restore,
  restoreTombstone}.lean`.
- **Defect.** False of the Go code: the post `r = PanicV #msg` is a panic with the bare string. Go's
  `panic(x)` (Perennial's `go.panic`, `wp_panic`) panics with the interface value,
  `PanicV #(interface.mkOk go.string #msg)`; zap's `WriteThenPanic.OnWrite` does `panic(ce.Message)`. The
  `keyIndex` specs inherit the bare string from it.
- **Evidence.** The reference implementation of zap in mit-pdos/etcd-refimpl (`Refimpl/go_uber_org/zap/`,
  `36ef0d5`) can meet the spec only with GooseLang's `Raise msg`, which no Go source translates to; with
  `panic(msg)` the proof fails at the final equality. `wp_panic` (Perennial, `Golang/Theory/Defer.lean`).
- **Second defect (same spec).** Its premise `⌜l ≠ null⌝` (kept by premise fixes 6, D4) admits loggers
  for which the axiom is false of zap v1.28.0 (`logger.go:283-357`, `terminalHookOverride`): a zero
  `&zap.Logger{}` panics with a nil-dereference runtime error (`log.core.Check` on a nil core), not
  `msg`; a logger built with `WithPanicHook(h)` for an `h` that returns makes `Panic` return normally.
  D4's reason (only a `recover` that inspects the value tells the panics apart) does not cover the
  second.
- **Proposed change.** `⌜r = PanicV #(interface.mkOk go.string #msg)⌝` in both zap specs; the same value
  at each `keyIndex` panic (`PanicV #(interface.mkOk go.string #(go!"…"))`). The premise `zapLoggerOk l`
  (as `Debug`/`Info`/`Warn`/`Error`/`Check`/`Fatal` have since premise fixes 6), and `zapLoggerOk lg` in
  place of `⌜lg ≠ null⌝` in `keyIndex.{put,get,tombstone,restore,restoreTombstone}` and
  `treeIndex.unsafeGet`; their callers have it from `isTreeIndex` (`#Hlgnn`). No trust-base change (the
  same axiom, restated). The plan's spec already has the premise (`isLogger l`).
- **Decision.** Accepted (the user, 2026-11-17: "fix the axioms ... and the proofs above that axiom");
  made on branch `zap-panic-iface`.
## 2026-11-17: raft's `Ready` hands out a canonical hard state (wal-link L1b, option (a))
- **Specs.** `raft.hardState.spec`; `RawNode.readyWithoutAccept.spec`, `RawNode.Ready.spec` (and its traced triple);
  the node API's `readyRest` (the post of `node.Ready`'s and `isReadyChan_recvAu`'s `Ready`), and the internal
  predicates carrying a `Ready`'s hard state (`ownRawNodeReady`, `readyData`, `freshOk`, `staleOk`,
  `ownRawNodeReady_abandon_keep`'s post).
- **Defect.** The WAL's state records hold protobuf-go's bytes of the hard state's wire content; `hsRO` leaves the
  unknown fields and the cells' presence free, so the bytes are not a function of the model and the WAL's crash
  invariant (over a model marshaller) cannot hold the server's records (`notes/wal-link-handoff.md`, "L1b by (iii)").
  Go's `r.hardState()` builds all three cells and no unknown fields (raft.go:504-510; its proof already showed it,
  `raft__hardState.lean`), and a `Ready`'s `HardState` is that pointer or `nil`.
- **Change (stronger posts only, no premise added).** `raft.hardState.spec`: post `hsRO p hs` → `hsROC p hs` (new,
  `InvPb.lean`: `hsRO` with the cells set and no unknown fields; `hsROC_hsRO`). `RawNode.readyWithoutAccept.spec`,
  `RawNode.Ready.spec`: post `"#Hhard" ∷ hsOpt rd.HardState' h` → `"#Hhard" ∷ hsOptC rd.HardState' h` (new,
  `InvPbLog.lean`: `nil` and zero, or `hsROC`; `hsOptC_hsOpt`). `readyRest` (`InvNode.lean`, `InvApi.lean`):
  conjunct `hsOpt rd.HardState' h` → `hsOptC rd.HardState' h`. Clients convert with `hsOptC_hsOpt` (kv, kvreconf,
  kvdurable, the server's `InvRaftNode`); premises unchanged (`acceptReady`, `IsEmptyHardState`, `MustSync`,
  `SetHardState` still take `hsOpt`). No closed statement's text changes; no trust-base change.
- **Decision.** Decided by etcd-grove-03, 2026-11-17 (conditions: no premise added, no closed etcd/k8s statement text
  changed, RaftTla regenerated); made by the wal-link agent on `wal-link`.
## 2026-11-19: the snapshotter's directory per execution (`isSnapshotter ss sd`; wal-link)
- **Specs.** `snap.Snapshotter.{DBFilePath,SaveDBFrom,ReleaseSnapDBs}.spec` (axioms), `storage.storage.Release.spec`,
  `isWalStorage`'s Release law and `rnNewStorageOk`, `storage.OpenSnapshotBackend.spec`, `EtcdServer.applySnapshot`'s
  `specSnapM`, `rafthttp.{Transport.Start,newSnapshotHandler}.spec`, `snapHandlerOk`, `bootstrappedRaft.newRaftNode.spec`;
  the vocabulary `snap.isSnapshotter`, `snap.snapDBPath`, `snapDirInv`; the bootstrap contracts' `bootOk`/`bootOkR`.
- **Defect.** `snap.snapDBPath : Loc → w64 → GoString` was opaque and pinned per run by `bootOk`'s `Hssp`: across runs
  every member's paths had to be one function, so the members' exclusive name claims (`Hsfree`, S5; `Hpath`, B1)
  collided and the multi-member boot premise was unsatisfiable (`notes/snapdir-crossworld.md`).
- **Evidence.** /shared/tmp/wallink/attack-b1.md §3 (the B1 attack).
- **Change.** `isSnapshotter ss sd` holds the `dir` field's cell `snapDirAddr ss ↦□ sd` and `⌜∃ dd, sd = snapDirOf dd⌝`;
  `snapDBPath sd i := sd ++ "/" ++ snapDBName i` (a definition); every spec over `sd`. Converges with `SpecPlan`'s
  `snap/Api.lean` (`isSnapshotter ss sd`, paths `dbPathOf sd i` over the directory).
- **Decision.** Approved by the user, 2026-11-19, via etcd-grove-03; made on `wal-link`.

## 2026-11-18: the batch lock's share of the auth history carries the states' permission keys (auth-schema-srv A6, STOP 3)

- **Spec.** `auth.authLockQ` (Model.lean), through `authLockI`: `authSchemaSrv`'s premise `authLockI (.on γa) bootState`,
  the write contract `authBatchTxLkR`'s `Lock` (gives it) and `Unlock` (takes it), `authSchemaSnap`'s lock share.
- **Defect.** Unprovable as stated, not false: at the write contract's `Unlock` the realization holds only the lock's
  quarter of the history; the write-back moves the auth buckets to the session's state `st`, which the invariant must
  record (`authStateAt`, which includes `permKeysOk st`, as the read contract's views hand it to readers), and nothing
  gives `permKeysOk st` (the quarter carried none; `roleEncode` opaque; `UnsafePutRole` allows an empty key).
- **Evidence.** `questions.md` "A6 STOP 3"; the store's history carries the fact (`authHist`, `authHistHalf`).
- **Proposed change.** `authLockQ γa hs := monoListAuthOwn γa.hist ¼ hs ∗ ⌜∀ st ∈ hs, permKeysOk st⌝` (P1'). Every
  producer goes through `authHist_split`; independent read-only check: no producer lacks the fact, nothing new for a
  client against the four forbidden laws. P2 kept (now redundant).
- **Decision.** Approved by etcd-grove-03, 2026-11-18 (on the A7 list); made on branch `auth-schema-srv`.

## 2026-11-19: `GetAllRoles` lists every role only below the range's implicit limit (auth-schema-srv A6, STOP 4, F-roles)

- **Spec.** `auth.rolesOut` (InvAuth.lean; the trusted write contract's `GetAllRoles` clause, `auth.authBackendReads`) and
  `auth.roleListOut` (Reads.lean; the post of the exported `auth.authStore.RoleList.spec`).
- **Defect.** Unprovable as stated: both listed every role of the state (`n ∈ names ↔ role ∧ roleListed n`). schema's
  `unsafeGetAllRoles` ranges with limit `-1`, which the backend's cursor reads as at most `2^63 - 1` entries
  (`backend.cursorRange`), and nothing bounds a recorded state's roles (the snapshot clause installs any state).
- **Evidence.** `questions.md` "A6 STOP 4"; `schema.rolesRangeEnts`, `mvcc.cursorRange_window`.
- **Proposed change.** `auth.rolesListed names st`: the names each once, each a role of `st` that `roleListed`, and every
  such role when `names.length < 2^63 - 1` (R-c); both texts use it. Weaker only in states with `2^63 - 1` or more roles.
- **SpecPlan.** W0's model answers `.roleList` with every role (`SpecPlan/Spec/go_etcd_io/etcd/api/v3/Model.lean`, ~l.1262),
  stronger than the code in two ways (F3's `0xff` names, this cap); not changed here (a SpecPlan entry for convergence).
- **Decision.** Approved by etcd-grove-03, 2026-11-19 (on the A7 list for the user); made on branch `auth-schema-srv`.

## 2026-11-19: `schema.authBucketsAre` holds a role's permissions in the state's order (auth-schema-srv A6, STOP 5, F-order)

- **Spec.** `schema.authBucketsAre` (etcdserver/InvAuthBackend.lean), through `authBucketsAt` (ImageOn.lean) in the trusted
  `authBkLend` (AuthBkHook.lean), `authSchemaSnap`'s premise (AuthSnapKit.lean) and the image certificates.
- **Defect.** False of ordinary runs: its roles clause said `st.roles.lookup n = some rr.toRole`, the bucket's record exactly
  the recorded state's role. Go's `RoleGrantPermission` appends and `sort.Sort`s by key (`server/auth/store.go:844-845`), the
  model's `grantPerms` (Steps.lean:222) appends: grant key `b` then `a`, the history says `[b, a]`, the bucket `[a, b]`. The
  write contract (`UnsafePutRole`) already allows a permutation; so the realization cannot prove `authBkLend` (the fifth
  refutation of `authSchemaSrv`'s text, `notes/auth-schema-srv-refuted.md`).
- **Evidence.** `questions.md` "A6 STOP 5" and its survey.
- **Proposed change.** (O-a) up to permutation: `∃ ps, st.roles.lookup n = some ps ∧ rr.toRole.Perm ps` (as `rolesAt`).
  (O-b, a sorting model) is not viable (Go's sort is unstable, equal keys); (O-c, a nondeterministic model order) is larger.
- **Decision.** (O-a), decided by etcd-grove-03, 2026-11-19 (on the A7 list for the user); made on branch `auth-schema-srv`.

## 2026-11-19: the auth records' size: the realization cannot meet `UnsafePut`'s entry bound (auth-schema-srv port, P5)

- **Spec.** The schema write contract's `UnsafePutUser`/`UnsafePutRole` clauses (`auth.authBatchTxLk`, `auth.authBatchTxLkR`,
  InvAuth.lean; inside `authSchemaSrv`'s text) and `authRecordsFit` (InvBoot.lean, opaque; a premise of
  `NewAuthStore`'s axiom, `NewServer.spec`, `NewServerR.spec` and the closed theorems' `Haf`).
- **Defect.** Since bbolt-integrate, `backend.batchTxBuffered.UnsafePut.spec` takes `kb.length + vb.length ≤
  bbolt.bboltEntryMax` (2^28). The realization's `lk_put` (AuthRealWr) puts `userEncode ur`/`roleEncode rr`, whose size
  neither the contract (key bounds only) nor `authSmall` (roles and permissions at most the revision, ≤ 2^61 + 2^48)
  bounds; `authRecordsFit` is opaque (no law). Known runtime finding: `nonissues/etcd-auth-record-too-large-fatal.md`.
- **Evidence.** Full timed build 20261119-190055-1577997 (`AuthRealWr.lean` l.1209, 1260); `questions.md` "BLOCKER
  (2026-11-19 h)".
- **Proposed change.** The user's option (1): the put clauses take `⌜name.length + enc.length ≤ bboltEntryMax⌝`;
  `authRecordsFit` gets content as a bound on the auth state the store keeps (a size field in `authSmall`, kept by every
  writer). Its concrete form: pending (questions.md "Option (1): concrete form").
- **Decision.** Option (1) chosen by the user, 2026-11-19, via etcd-grove-03.
- **Decision, revised.** Route (d') chosen by the user, 2026-11-19, via etcd-grove-03 (in place of option (1), whose
  parameterless content would have been false): the goosed bbolt fork's `Put` refuses an entry above `2^28` bytes
  (3f8520bd, branch `goose-lean-entrymax`, with a Go test); `bbolt.Bucket.Put.spec` in place (the size premise dropped,
  an oversized-error branch); `backend.batchTx.unsafePut`/`UnsafePut`/`UnsafeSeqPut` drop the premise and their posts
  say the entry was within the bound (else `lg.Fatal`); `batchTxBuffered.UnsafePut`/`UnsafeSeqPut` drop the premise.
  `authRecordsFit` and the schema contracts unchanged; A7 stays "only `hD22` removed".

## 2026-11-20: the error-free open/rename specs need the paths to fit (wal-fsfix merge of lean 94ea36b029)

- **Spec.** `Fs.wp_osOpenCreateSNE`, `wp_osOpenFileSNE`, `open_failure_eintr`, `wp_osRenameFileSNE`
  (`GooseLang/Ext/Fs/NoErrSpecs{OpenFile,Rename}.lean`) and the specs above them (`os.OpenFile.specCreateS`,
  `os.Rename.spec`, bbolt's `Open.spec`, the backend's glue, the server's snapshot backend).
- **Defect.** They build `IoCovers "Open"/"Rename"` for any path; since the user's A1 decision (2026-11-19)
  `NoIoErr` covers only paths that fit (`PathFits`: under 4096 bytes, no component over 255), so the specs are
  unprovable on wal-fsfix: a path call on an over-long path may fail with `ENAMETOOLONG` (`TestNoIoErrNameTooLong`).
- **Evidence.** The merge's build (2026-11-20): `NoErrSpecsRename.lean:214`, `NoErrSpecsOpenFile.lean`.
- **Proposed change.** `PathFits` premises on the four lemmas; the shared-mode name claims carry `PathFits path`;
  error arms `¬ FsNoErr ∨ ¬ PathFits p`; a bound on the member's data directory in `bootCfgFresh`, discharged in
  the examples from the member name (≤ 200 bytes).
- **Decision.** Option 2, the user, 2026-11-20, via etcd-grove-03; flock left to `NoMapLockErr` the same day.

## 2026-11-20: `checkMembershipOperationPermission` says nothing of its error's message (auth-mediation M2)

- **Spec.** `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__checkMembershipOperationPermission.lean`
  (post `adminOutC`); the membership contracts' handler answers `memChkAns`, `memCfgAns`
  (`MemberContracts.lean`).
- **Defect.** `PromoteMember` labels `learnerPromoteFailed` with `err.Error()`, which panics unless valid UTF-8;
  the guard's error carried no message fact (`adminWhy` is `True` with auth off), nor did the contracts' errors.
- **Evidence.** The proof of `EtcdServer.PromoteMember` (auth-mediation M2, 2026-11-20).
- **Proposed change.** The guard's post gains `authErrVarIs err` (its errors are `AuthInfoFromCtx`'s and
  `IsAdminPermitted`'s auth variables, `nil` with auth off; their messages are `auth.authErrMsgs` literals,
  `errMsgP_of_authErrVarIs`); the contracts' error answers gain `v3rpc.errMsgP err utf8Valid`.
- **Decision.** Decided by etcd-grove-03, 2026-11-20 (a stronger post on a proved spec).

## 2026-11-20: `EtcdServer.MemberList.spec` holds only with auth off (auth-mediation M2, found)

- **Spec.** `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__MemberList.lean` (and so
  `ClusterServer.MemberList.spec`), premise `isServerReq s E ρ`, which includes `⌜E.authOn = false⌝`.
- **Defect.** The client port's MemberList row (authenticated class) rests on it, but with auth on the spec
  says nothing: its guard's verdict (`authedRes`) is only stated for an auth-off server. `EtcdServer.Compact.spec`
  takes the same premise (its row's guard, `AuthAdmin.isPermitted`, is a separate spec, so that row is not
  affected the same way).
- **Evidence.** Reading the premise while writing the handler's spec (auth-mediation M2, 2026-11-20).
- **Proposed change.** Restate over `isServerReqM E.authOn`/`isServerReadM E.authOn` (as `EtcdServer.Range`),
  the proof taking the fields through `srvReqFieldsAtM`/`srvReadFieldsAtM`; then the row can be `e2e`.
- **Decision.** 2026-11-20, decided by etcd-grove-03 (a stronger proved spec: its premise generalized):
  restated IN PLACE (no twin) over `isServerReqM E.authOn`/`isServerReadM E.authOn`, the read's dependency
  at `kvStM E.authOn` (as `EtcdServer.Range`); `ClusterServer.MemberList.spec` the same; the row raised to
  `e2e` with the handler's spec in its specs.

## 2026-11-20: `grpclog.SetLoggerV2` panics on a component logger (prove-grpcsmall)

- **Spec.** `grpclog.SetLoggerV2.spec` (`Spec/google_golang_org/grpc/grpclog/SetLoggerV2.lean`), a trust-boundary axiom.
- **Defect.** Precondition `True` for any `l`; grpc v1.84.0's `SetLoggerV2` (`grpclog/loggerv2.go:35-41`) panics when `l`
  is a `*componentData`, which the exported `grpclog.Component` returns.
- **Evidence.** Code reading of the pinned grpc; `notes/axiom-review/setloggerv2.md`.
- **Proposed change.** `l : GoInterface` with the premise that its dynamic type is not `*componentData`; the one caller
  (`etcd3`'s `init`) discharges it from the `klogWrapper` conversion, whose axiom now names the interface it returns.
- **Decision.** Applied (prove-grpcsmall, 2026-11-20; a weakening of the axiom, the caller's obligation discharged).

## 2026-11-20: `v3rpc.isClientCtxErr` calls `status.FromError` without its premise (prove-grpcsmall)

- **Spec.** `v3rpc.isClientCtxErr.spec` (`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/isClientCtxErr.lean`), an axiom.
- **Defect.** Holds for any `err`; with `ctxErr == nil` the body calls `status.FromError(err)`, which calls `err.Error()`:
  an error whose `Error()` panics makes it panic. `status.FromError.spec` requires `statusErrOk err` and a stable `Error()`.
- **Evidence.** Code reading (`util.go`); `notes/axiom-review/setloggerv2.md`.
- **Proposed change.** Premise `⌜ctxErr ≠ nil⌝ ∨ statusErrOk err`. The receive-error callers have `statusErrOk`; the
  send-error callers (`sendLoop`, `leaseKeepAlive`) have only `streamErr` from `srvStreamIs`'s `Send`, which would have to
  carry `statusErrOk` too (true of grpc, but an extension of the trusted server model's assumption).
- **Decision.** Open: recorded only (the brief's "skip if discharging is hard"). Then applied by prove-grpcext
  (2026-11-20, next entry), with the spec plan's unconditional form (`errView err` there, `statusErrOk err` here).

## 2026-11-20: `isClientCtxErr` proved; the server stream's `Send` errors are status errors (prove-grpcext)

- **Spec.** `v3rpc.isClientCtxErr.spec`; the trusted server stream `srvRawStreamIs` (`Proof/google_golang_org/grpc/
  InvGrpcStream.lean`), its `SendMsg` clause, and the derived `srvRawStreamIsW`, `srvStreamIs`.
- **Defect.** The previous entry: `isClientCtxErr` had no premise and `FromError` needs `statusErrOk`; a send error had
  only `streamErr`.
- **Evidence.** grpc v1.84.0 `stream.go:1808-1860`: `serverStream.SendMsg` returns `prepareMsg`'s errors (`encode`'s and
  `compress`'s `status.Errorf`), `status.Errorf(codes.ResourceExhausted, ...)` for an oversized message, or
  `toRPCErr(ss.s.Write(...))`, which passes `io.EOF` through and makes `*status.Error`s of the rest (`rpc_util.go`); the
  same errors `RecvMsg` returns, for which the model already promised `statusErrOk` (premise fixes 7,
  `examples/premisefix/ctxvalue` `TestRealStreamErrors`). grpc-prometheus's `monitoredServerStream.SendMsg` and etcd's
  `serverStreamWithCtx` return the wrapped stream's error unchanged.
- **Proposed change.** `statusErrOk err` in `srvRawStreamIs`'s `SendMsg` error branch (a strengthening of the trusted
  model's promise, justified above) and in the derived predicates; `isClientCtxErr` takes `statusErrOk err` (as the spec
  plan's `errView err`); its callers (`watchServer.Watch`, from `recvLoop`'s post; `sendLoop`, `leaseKeepAlive`, from
  `Send`'s and `Recv`'s) pass it. `isClientCtxErr` translated (`v3rpc.toml`) and proved over `status.FromError`'s spec and
  `strings.HasPrefix`/`HasSuffix`: its axiom goes.
- **Decision.** Applied (prove-grpcext, 2026-11-20).

## 2026-11-20: grpc's generic stream wrappers relate their Lean types to their Go types (prove-grpcext)

- **Spec.** `grpc.Generic{Client,Server}Stream.{Send,Recv,Context}.spec`, `GenericClientStream.CloseSend.spec`
  (`Spec/google_golang_org/grpc/Generic*Stream__*.lean`), axioms until this change.
- **Defect.** Each quantified over the Lean types `V`, `W` of the wrapper's points-to (`structFieldRef
  (GenericClientStream V W) ...`) with nothing relating them to the Go types `T`, `U` of the method: the body's field access
  (`StructFieldRef (GenericClientStream.ty T U)`) is at `structFieldRef` of the Lean type that represents the Go type
  (`TypeRepr`), so for unrelated `V`, `W` the precondition's cell is not the one the body reads. And `Send`'s premise was the
  wrapped `SendMsg`'s WP for any postcondition, while the body returns its result through its named `error` result (a typed
  store and load).
- **Evidence.** The proofs (`Proof/google_golang_org/grpc/Generic*Stream__*.lean`, over the bodies the pinned Goose now
  emits for the generic types' methods).
- **Proposed change.** `[TypeRepr T V] [TypeRepr U W]` (with their `ZeroVal`s); `Send`'s premise's postcondition
  `v, ∃ err : GoInterface, ⌜v = #err⌝ ∗ Φ v` (as `Recv`'s already was). The two users (`srvStreamIs_of_raw`,
  `cliBidiStreamIs_of_raw`) take the instances, which their callers (the generated handler, the watch and keep-alive stubs)
  have for the messages' types; their `SendMsg` triples give `error` values.
- **Decision.** Applied (prove-grpcext, 2026-11-20): the seven axioms are theorems.

## 2026-11-20: `snap.Message.GetTo` takes raftpb's initialization (prove-grpcsmall)

- **Spec.** `snap.Message.GetTo.spec`, an axiom until this change.
- **Defect.** Not false, but unprovable: the body is raftpb's promoted getter, whose spec needs `isPkgInit raftpb` and the
  raft message's content, neither of which `msgIs` held.
- **Evidence.** The proof (`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Message__GetTo.lean`).
- **Proposed change.** `isPkgInit raftpb` in the precondition (the one caller, `sendMergedSnap`, gets it by `iPkgInit`);
  `msgRO` keeps the raft message's read-only content (`∃ st, msgOwn ml □ st`), which `NewMessage`'s precondition gives.
- **Decision.** Applied (prove-grpcsmall, 2026-11-20).
## 2026-11-20: `cut.specNoErr` needs lock coverage and a WAL directory that fits (`WalH`)

- **Spec.** `WalH` (`Proof/go_etcd_io/etcd/server/v3/storage/WalRecs.lean`, the open WAL handed out by the assumed
  `bootstrapContract`'s `wal.bootOk`); `WAL.cut.specNoErr` (`Spec/.../storage/wal/WAL__cutNoErr.lean`).
- **Defect.** `cut.specNoErr` is not provable over `FsStepSat (NoIoErr Sio)` alone: `cut` locks its new segment
  (`fileutil.LockFile`: OFD lock, `flock` fallback, covered by `NoMapLockErr`, not `NoIoErr`), and its path calls
  (`dir/<seg>.wal`, `dir/<n>.tmp`) are covered only when they fit (`PathFits`, the user's A1 decision). `WalH`
  carries neither the `NoMapLockErr` instance nor the WAL directory's `DirFits`, so `Save`'s covered case cannot
  discharge them.
- **Evidence.** wal-fsfix's attack (noioerr.md session 10, item 1) and the `cut` proof's callees (`WAL__cut.lean`).
- **Proposed change.** `WalH` gains the `FsStepSat (NoMapLockErr Sio)` instance and `Fs.DirFits dir` (derived from
  the data directory's `DirFits`, `bootCfgFresh`); `cut.specNoErr` takes them. Old → new meaning of
  `bootstrapContract`: the open WAL it hands out was covered by `NoIoErr` only → also by `NoMapLockErr` (its lock
  calls succeed whenever they can), in a directory that fits.
- **Decision.** Approved by the user, 2026-11-20, via etcd-grove-03; an independent attack before relying on it.

## 2026-11-20: `cut.specNoErr` also needs the WAL directory's paths covered (`WalA.cov` is inodes only)

- **Spec.** `WalA`/`WalH` (`Proof/go_etcd_io/etcd/server/v3/storage/WalRecs.lean`), `WAL.cut.specNoErr`
  (`Spec/.../storage/wal/WAL__cutNoErr.lean`, premise `∀ st i, Sio.ino st i`).
- **Defect.** `NoIoErr Sio` covers a path call (`open`, `rename`, `mkdir`, `unlink`, `rmdir`) only when
  `Sio.path p ∧ PathFits p` (`IoCovers`, `Premises.lean`). `cut` makes three: the pipeline's `OpenFile(dir/<n>.tmp,
  O_CREATE)` (`filePipeline.alloc`), `os.Rename(dir/<n>.tmp, dir/<seq>-<idx>.wal)` and `LockFile`'s
  `OpenFile(dir/<seq>-<idx>.wal, O_WRONLY)`; the low-level no-error lemmas take it (`wp_osOpenCreateSNE`,
  `wp_osOpenFileSNE`: `Sio.path (child d b)`; `wp_osRenameFileSNE`: `∀ p, Sio.path p`). `WalA.cov` (`walCov Sio`)
  covers every inode and no path, so even with the approved `satL`/`fits` (entry above) an uncovered `open` may
  fail with any errno and `cut` return its error: `cut.specNoErr` stays unprovable in `Save`'s covered case. The
  entry above's `Fs.DirFits dir` is also not derivable from `bootCfgFresh`'s `DirFits DataDir` as written there
  (`srvWalDirOf d` is 3 bytes longer than `d`; `DirFits` bounds at 3800): implemented instead at the area's
  allocation, from the member's name of at most 200 bytes (`dirFits_srvWalDirOf_memberDataDir`), so `walAreaFresh`
  carries it (no change to `bootCfgFresh`).
- **Evidence.** wal-fsfix2's survey of `cut`'s callees (`WAL__cut.lean`, `NoErrSpecsOpenFile.lean`,
  `NoErrSpecsRename.lean`); no WAL spec over an open WAL names `Sio.path` (grep).
- **Proposed change.** `WalA` gains `covP : ∀ b, Sio.path (Fs.child dir b)` (the WAL directory's entries; the
  closed theorems' `allIo` covers every path, so the allocation gives it by `trivial`); `cut.specNoErr` takes it
  with `satL` and `fits`. Old → new meaning of `bootstrapContract`'s `wal.bootOk`: the open WAL's files covered by
  `NoIoErr`/`NoMapLockErr` by inode → also its directory's names by path (a covered `open`/`rename` there that can
  succeed does). Alternative: `covP : ∀ p, Sio.path p` (simpler, as `FsNoErr`; claims more than `cut` needs).
- **Decision.** Approved by the user, 2026-11-20, via etcd-grove-03: the narrow `WalA.covP : ∀ b, Sio.path (Fs.child
  dir b)`; the forms (the fields in `WalA`, `fits` from the name bound via `hmsL`) accepted. An independent attack on
  `covP` with `satL`/`fits` before relying on it.

## 2026-11-20: `cut` under `walCov` can still fail: a blocking lock request in conflict may fail (no premise excludes it)

- **Spec.** `WAL.cut.spec` in the decided one-spec form (error arm `err ≠ nil ∧ ¬ walCov Sio`), and through it `Save`/
  `SaveSnapshot`'s covered case and item 3 (`rnNewStorageOk_holds`).
- **Defect.** `cut` makes two blocking lock requests: the pipeline's `LockFile(dir/<n>.tmp, O_CREATE|O_WRONLY)` on the
  fresh temporary file and step 8's `LockFile(dir/<seq>-<idx>.wal, O_WRONLY)` after `newTail.Close()` released the
  lock (fileutil: `F_OFD_SETLKW`, or `flock(LOCK_EX)` without `LOCK_NB`). The lock rule (`LockStep`, `Impl.lean`) has a
  success only when no other description holds a conflicting lock (`LockConflict`); otherwise only failures (any
  errno: the model's "waits, or fails", `locks_blocking.go`, the user's 2026-11-15 choice, `locks.md` §2.4). `NoIoErr`'s
  `OfdLock` clause and `NoMapLockErr`'s `Flock` clause ask errno 0 only where a success exists, so in a conflict they
  allow every errno. Nothing in the logic excludes a conflict at those steps: the locks' ghost state (`lockCtx`,
  `Locks.lean`) tracks exclusive locks only, and only while held (step 8 runs after the close released the token);
  no resource says no other description on the inode exists or holds a shared lock. So the planned witness
  `e ≠ 0 → ¬ FsNoErrIno` on the lock calls is not provable, and `cut`'s error arm `¬ walCov Sio` is not either.
- **Evidence.** wal-fsfix2 a6 (reading `LockStep`, `IoCovers "OfdLock"`, `MapLockOk "Flock"`, `wp_osLockStep`,
  `fileutil.wp_ofdLockFile`/`wp_flockLockFile`, `WAL__cut.lean` step 8). On Linux a blocking request in conflict waits
  (measured, `TestLocksBlocking`); the model's failure there is what the premises leave open.
- **Proposed change.** (A, recommended; trusted) the semantics gives a blocking request in conflict a wait step (the
  call steps to itself, as `MmapStall`; `locks_blocking.go` updated: "waits" becomes a step), and the premises say a
  covered blocking request ends errno 0 or waits (`NoIoErr` "OfdLock", `NoMapLockErr` "Flock"; `StepKeeps` holds: the
  wait step is always there). The base semantics keeps its failures (§2.4 unchanged); only the covered case loses them,
  resting on `SA_RESTART` (measured) and no allocation failure at entry (already the premises' assumption). Then the
  lock witness is `e ≠ 0 → ¬ FsNoErrIno` and the decided plan goes on unchanged. (B, untrusted, large) a lock right per
  inode and kind in `lockCtx` (shared locks tracked too), a fraction needed for every lock request, the whole one kept
  by the WAL for its segments: changes every lock spec (fileutil `LockFile`/`TryLockFile`, bbolt's `flock`, the purge's
  `TryLockFile` on WAL files), and the purge's concurrent locks must fit it. (C) `cut`'s error arm keeps a lock
  disjunct: item 3 then stays unprovable.
- **Decision.** Option (A), approved by the user 2026-11-20 via etcd-grove-03. Done: `LockStep` takes the call itself
  (`self`) and has a third outcome, `nb = false ∧ LockConflict … ∧ st' = st ∧ e' = self`; `ErrnoZero "OfdLock"` and
  `MapLockOk "Flock"` count the wait as no error; `locks_blocking.go` and `doc.go` updated; the lock calls are no longer
  `FsRetOp` (not atomic: `CrashFile.lean`); `wp_osLockStep` handles the wait by Löb induction. Old → new meaning: a
  blocking lock request in conflict waited by failing or by taking no step → it may step to itself; under
  `NoIoErr`/`NoMapLockErr`, a covered blocking request ends with errno 0 or waits (was: any errno in a conflict).
  An independent attack before relying on it.

## 2026-11-20: `cut.spec` restated as one spec over `Sio`; `sync.specCut`, `Save`, `SaveSnapshot` and the storage specs follow

- **Spec.** `WAL.cut.spec` and `WAL.cut.specNoErr` (deleted), `WAL.sync.specCut`, `WAL.Save.spec`, `WAL.SaveSnapshot.spec`,
  `storage.storage.Save.spec`, `storage.storage.SaveSnap.spec`.
- **Defect.** Two specs for one function (`cut.spec`, any error; `cut.specNoErr`, unproved, its premises incomplete:
  the three entries above); `Save`/`SaveSnapshot` chose between them at the call (`CalleeCov.walCov_cut`).
- **Evidence.** wal-fsfix2 a5-a8; the decided form (etcd-grove-03, 2026-11-20, `questions.md`).
- **Proposed change.** One `cut.spec` parameterised by `Sio`, with `[FsStepSat (NoIoErr Sio)]` and
  `[FsStepSat (NoMapLockErr Sio)]`: premises `walCov Sio → DirFits dir ∧ ∀ b, Sio.path (child dir b)` and
  `walCov Sio → o0 + |out| + |pend| ≤ maxBytes`; error arm `err ≠ nil ∧ ¬ walCov Sio`. `sync.specCut` the same way
  (room premise, error `¬ walCov Sio`; proved from `sync.spec` and `sync.specNoErr`). `Save.spec` gains the instance
  and the premise `walCov Sio → DirFits dir ∧ ∀ b, Sio.path (child dir b)` (a Lean premise); `SaveSnapshot.spec`'s
  `shared` precondition the same premise as a pure assertion; the storage specs the same, discharged by
  `RnNewStorage` from `WalH.fits`/`covP` (`satL` the instance).
- **Decision.** Decided by etcd-grove-03 (the one-spec form, 2026-11-20). Done (wal-fsfix2 a8): `cut.spec` proved
  (`WAL__cut.lean`: every callee's error witnessed, `Fs.fsNoErrOn_of` refutes it under `walCov`), `cut.specNoErr`,
  `walCov_cut` and `WAL__cutNoErr.lean` deleted; the WAL Link's hypothesis `h_wal_WAL_cutNoErr` gone.

## 2026-11-20: `verify.Verify`'s callback and details are untyped `val`s (prove-etcdstorage)

- **Spec.** `verify.Verify.spec` (`Spec/go_etcd_io/etcd/client/pkg/v3/verify/Verify.lean`, an axiom until this change;
  `SpecPlan/Spec/go_etcd_io/etcd/client/pkg/v3/verify/Verify.lean`).
- **Defect.** Unprovable as stated: `f : val` may be a panic value (the call `Verify(msg, f)` then panics binding its
  argument), and the details `d : val` that `f` returns may be one (`Verify` stores them into its `map[string]any`
  variable, which only a typed map value can be). The Go `f` is a func value and its details a map, so no caller is
  affected.
- **Evidence.** The proof (`Proof/go_etcd_io/etcd/client/pkg/v3/verify/Verify.lean`): `wp_auto` cannot step either.
- **Proposed change.** `f : GoFunc` (`#f`) and `∃ d : Loc, r = PairV #true #d`; with it, the premise `envVerifyOff` as an
  alternative to `f`'s triple (SpecPlan already had it, as `verifyOff`), which `VerifyBackendConsistency` needs.
- **Decision.** Applied in both (prove-etcdstorage, 2026-11-20); the five callers' proofs unchanged but `ileft` and
  `iexists mref` (a `Loc`, was `#mref`).

## 2026-11-20: `verify.Verify` takes its function as any `val` (prove-etcdapi)

- **Spec.** `verify.Verify.spec` (`Spec/go_etcd_io/etcd/client/pkg/v3/verify/Verify.lean`), a trust-boundary axiom.
- **Defect.** Not false of Go, but unprovable over the real code: `f` ranges over every `val`, where Go's `f` is a
  `VerifyFunc` value. `Verify`'s body first stores `f` into a `VerifyFunc`-typed local (`GoAlloc VerifyFunc.ty f`), whose
  semantics Perennial gives only for a value of the type (`IntoValTyped`), not for an arbitrary `val`. (A panic outcome
  `f = PanicV p` alone is provable: `f()` and `Verify(msg, f)` both unwind to it, which `f`'s WP excludes; the attempt has
  the lemma, `wp_absurd_of_pure`, in `/tmp` only, not landed.)
- **Evidence.** The proof attempt (prove-etcdapi): `wp_auto` stops at the `GoAlloc` of `f`.
- **Proposed change.** `∀ (f : GoFunc)`, the call `(Val #f)` and `f`'s WP over `#f` (as bbolt's `common.Verify.spec`).
  The five callers (mvcc `restoreIntoIndex`, `watcher.send`; backend `txWriteBuffer.putSeq`; schema
  `unsafeUpdateConsistentIndex`; etcdserver `verifyConsistentIndexIsLatest`) pass function literals, so the change is
  only the quantifier's type at their `wp_apply`s. Formally a weakening of the axiom's statement (fewer `f`), so not
  applied without the user; with it, `verify.Verify` is provable as bbolt's (over `os.Getenv`, `strings.ToLower`).
- **Decision.** Open: recorded only.
## 2026-11-20: `http.ReadAll_spec` admits a reader's negative count (prove-http)

- **Spec.** `http.ReadAll_spec` (`Proof/net/http/Boundary.lean`, the axiom `http.ReadAll_ok`) over `http.prefixReaderOk`.
- **Defect.** `prefixReaderOk`'s `Read` post said `ys.length = sint.nat n`, met by a `Read` returning `(-1, nil)`;
  go1.27.3's `io.ReadAll` slices `b[:len(b)+n]` (`io/io.go:723`) and panics.
- **Evidence.** `examples/premisefix/negread`; `notes/axiom-review/http-readall-negread.md`.
- **Proposed change.** `sint.Z n = ys.length` in `prefixReaderOk` and in `http.bodyRead_spec` (its producer's axiom, whose
  post gets stronger: Go's body reader returns `0 <= n`); `NewLimitedBufferReader`'s proof passes it through.
- **Decision.** Applied (prove-http, 2026-11-20).

## 2026-11-20: semver's `Version.Major`/`Minor` read `*v` without owning it (prove-smalllibs)

- **Spec.** `semver.Version.Major.spec`, `semver.Version.Minor.spec` (`Spec/github_com/Masterminds/semver/v3/`),
  axioms until this change; also `Version.LessThan.spec` and `Version.String.spec` (still axioms). The plan's
  (`SpecPlan/Spec/github_com/Masterminds/semver/v3/`) take `verAt v a` (a read-only points-to).
- **Defect.** Too weak a premise: only `v ≠ null`. The methods load `*v` (value receivers), so a program writing
  `*v` concurrently races (Go: a data race, Perennial: stuck), and the axiom would still claim a return. Unprovable
  over the real code for the same reason.
- **Evidence.** The proofs (`Proof/github_com/Masterminds/semver/v3/Version__Major.lean`): the load needs `v ↦{dq} x`.
- **Proposed change.** `Major`/`Minor`: premise `v ↦{dq} x`, kept, post the exact field (`x.major'`, `x.minor'`).
  `MustParse` returns `v ↦□ x` (its version is `NewVersion`'s fresh allocation), `New` returns
  `v ↦□ ⟨ma, mi, pa, pre, md, orig⟩` (proved); rafthttp's `serverVersion`/`minClusterVersion` return it, and
  `compareMajorMinorVersion`, `checkStreamSupport`, `checkVersionCompatibility` take it (and the latter returns it).
  `LessThan` and `String` keep `v ≠ null`: their callers include `ClusterVersionSet` on the cluster's
  `Version()` result, which `apply.isCluster`'s contract (inside `bootstrapContract`, a top-level premise) gives with
  no points-to; strengthening them needs that contract to say `Version()` returns `nil` or a read-only version
  (true: `semver.MustParse(c.version.String())`, `cluster.go:580-587`), a premise change for the user.
- **Decision.** `Major`/`Minor`/`New`/`MustParse`/rafthttp applied (prove-smalllibs, 2026-11-20); `LessThan`/`String`
  open (the `isCluster` contract change needs the user).

## 2026-11-20: x/time/rate's `limiterOk`/`reservationOk` opaque (prove-smalllibs)

- **Spec.** `rate.limiterRaw`, `rate.reservationRaw` (`Spec/golang_org/x/time/rate/Limiter__{Wait,Reserve}.lean`),
  opaque until this change; `NewLimiter.spec`, `Reservation.Delay.spec` (axioms until this change), `Limiter.Reserve.spec`,
  `Limiter.Wait.spec` (axioms).
- **Defect.** Not false, but unprovable: an opaque predicate no proof can produce (`NewLimiter`) or read (`Delay`).
- **Evidence.** The proofs (`Proof/golang_org/x/time/rate/{NewLimiter,Reservation__Delay}.lean`).
- **Proposed change.** `limiterRaw rl`: `rl`'s mutex guards its other fields (`limiterFields`); `reservationRaw r`:
  read-only `ok` and `timeToAct`. Callers' statements unchanged (the predicates are only passed between the
  four specs). `Reserve`'s axiom now claims the read-only fields (true: `ReserveN` returns a fresh `&r` the
  limiter does not keep, and no method writes `ok`/`timeToAct`, x/time/rate v0.16.0 `rate.go:162-230`);
  `Wait`'s takes the mutex (true: every method takes `lim.mu` before touching the fields).
- **Decision.** Applied (prove-smalllibs, 2026-11-20).

## 2026-11-20: `fmt.SprintfClientPtr` admits any directive for a `*clientv3.Client` (prove-reflectfmt)

- **Spec.** `fmt.SprintfClientPtr.spec` (`Spec/fmt/SprintfClientPtr.lean`), a trust-boundary axiom.
- **Defect.** False as stated: any format, the client unowned. Under `%v`/`%s` (or as an `EXTRA`) Go prints a pointer to a
  struct by its fields (`fmt/print.go:902-911`), reading `*c` and calling the `String`/`Error` of its exported fields'
  values (`print.go:756-763`); only `%p` (`print.go:686-693`) reads nothing.
- **Evidence.** Code reading of go1.27.3; `examples/axiomcx/sprintfclientptr` (a real `Client` whose `KV` has a
  `String()`); `notes/axiom-review/sprintfclientptr.md`.
- **Proposed change.** A directive-aware premise, `fmt.SprintfClientArgsOk format xs`: the directives parse and a
  `*Client` argument is consumed by a `%p` (none left over as an `EXTRA`). The one caller (`Client.dial`, `"%s://%p/%s"`)
  discharges it.
- **Decision.** Applied (prove-reflectfmt, 2026-11-20; a strengthening of the premise, the caller's obligation discharged).

## 2026-11-20: `encoding.json.Unmarshal` gives back the caller's slices as fresh (prove-reflectfmt)

- **Spec.** `encoding.json.Unmarshal.spec` (`Spec/encoding/json/Unmarshal.lean`), a trust-boundary axiom.
- **Defect.** False as stated: for any `p ↦ v` the post owns the decoded `PeerURLs`/`ClientURLs` in full, but
  `encoding/json` decodes into the field's existing slice, reusing its backing array (`decode.go:553-556`): a non-nil
  `v.PeerURLs` the caller still owns comes back aliased, two full points-tos of one cell.
- **Evidence.** Code reading of go1.27.3; `examples/axiomcx/jsonunmarshalalias`; `notes/axiom-review/json-unmarshal-alias.md`.
- **Proposed change.** Premise: both URL slices of `v` are `nil`. Both callers decode into `new(ConfigChangeContext)`
  and discharge it by `rfl`.
- **Decision.** Applied (prove-reflectfmt, 2026-11-20; a strengthening of the premise, the callers' obligation discharged).

## 2026-11-21: `txn.Range` takes its request read-only; `rangeStream` rewrites it (auth-mediation M3)

- **Spec.** `txn.Range.spec` (`Spec/go_etcd_io/etcd/server/v3/etcdserver/txn/Range.lean`, frozen, Strict M1) and the
  response it gives (`txn.rangeResult`, `txn.rangeResponseIs`, `txn.kvIs`).
- **Defect.** Too weak for a caller that reuses its request: the request is `txn.rangeRequestIs r o`, persistent (every
  field `↦□`), so once passed it can never be written again. `EtcdServer.rangeStream` (`v3_server.go:198-274`) calls
  `txn.Range(ctx, lg, kv, r, false)` once per page on the same `r`, writing `r.Limit`, `r.Revision` and `r.Key` between
  pages. Second, the response's keys are `keySl ↦*□ v.key` with no `ownSliceCap`, and `rangeStream` computes the next
  page's key as `append(resp.Kvs[len(resp.Kvs)-1].Key, '\x00')`, which writes into that key's capacity when it has
  room (Perennial's `wp_slice_append*`, persistent variant included, needs `ownSliceCap`). Neither is a Go bug: the
  key's array is the unmarshalled copy mvcc made for this read, and the appended byte is past the key's length.
- **Evidence.** The M3 proof attempt (worktree `/shared/etcd-grove-authm3`, branch `auth-mediation-m3`); Perennial
  `Golang/Theory/Slice.lean:1146-1398`.
- **Proposed change.** (a) `txn.Range.spec` takes the request at a fraction, the four rewritten fields owned or at
  `dq`, and gives it back; (b) the response gives `ownSliceCap` of each key (down through mvcc's API spec, where the keys
  are unmarshalled). Alternatives in `notes/auth-mediation-handoff.md` (M3).
- **Decision.** (B), the user's choice (2026-11-21, via etcd-grove-03): `rangeStream` stays names only, with one
  trust-boundary spec (`Spec/.../etcdserver/EtcdServer__rangeStream.lean`: it sends only through `rs`, each chunk of
  the range under the check the caller gives it), independently attacked (`notes/axiom-review/rangestream.md`:
  survives, with F1 applied, the request's new key given back without its contents); `EtcdServer.RangeStream` and
  `kvServer.RangeStream` proved over it. (A), this entry's proposed change, is the later replacement; it needs the
  fork to carry upstream's `bytes.Clone` of the last key (etcd-io/etcd@9acc0ebe37,
  `nonissues/etcd-rangestream-keysonly-index-key-race.md`), without which the append races in Go and the body is
  not provable.

## 2026-11-21: `doSerialize`'s `get` is not told that `chk` passed (auth-mediation M3)

- **Spec.** `EtcdServer.doSerialize.spec` (`Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__doSerialize.lean`).
- **Defect.** Too weak for a `get` with effects that need the check: `get`'s precondition was `G` alone, so a `get`
  that sends (`RangeStream`'s pages, inside `get`) cannot show each send came after a passed check; and `chk` could
  read only its own arguments, not a request `get` later rewrites (owned in `G`).
- **Evidence.** The M3 proof of `EtcdServer.RangeStream` (worktree `/shared/etcd-grove-authm3`).
- **Proposed change.** `get`'s precondition adds `∃ info, C info ∗ infoBoundM E.authOn s E tok info` with `C`
  persistent (a Lean instance premise; every caller's is); `chk`'s triple frames `G`. A stronger spec; Range, Txn and
  `ModeSpecs.spec_off` adjust (`specOff` takes the same premise on `C`).
- **Decision.** Decided by etcd-grove-03 (2026-11-21: a stronger proved spec); the `G` frame on `chk`, the obvious
  filling (a weaker requirement on the caller's `chk`), decided by the M3 agent.

## 2026-11-21: the request's readers take it read-only; the streamed request is owned (auth-mediation M3)

- **Spec.** `RangeRequest.GetKey.spec`, `GetLimit.spec`, `GetRevision.spec` (`Spec/go_etcd_io/etcd/api/v3/etcdserverpb/`),
  `txn.HasRevisionFilters.spec`, `v3rpc.checkRangeRequest.spec`, `v3rpc.checkRangeStreamRequest.spec`.
- **Defect.** Too strong a precondition: each takes the request's `Key`/`Limit`/`Revision` fields read-only (`↦□`,
  `txn.rangeRequestIs`), though it only reads them; `EtcdServer.RangeStream` and `kvServer.RangeStream` own those three
  fields (`rangeRequestOwn`: `rangeStream` rewrites them between pages) and cannot call them.
- **Evidence.** The M3 proofs of `EtcdServer.RangeStream` and `kvServer.RangeStream` (worktree
  `/shared/etcd-grove-authm3fix`).
- **Proposed change.** The getters at any fraction `dq` of their field, given back; the three readers over
  `txn.rangeRequestAt r dq o` (`txn/RequestAt.lean`: `rangeRequestIs` with the three fields at `dq`;
  `rangeRequestIs_at`, `rangeRequestOwn_at` give the two ends by `rfl`), given back. Stronger specs; the callers at
  `DFrac.discard` (`Range`, `firstOpKey`, `kvServer.Range`, `checkRequestOp_of`, `rangeLimit`) convert.
  `SpecPlan`'s getters already take `↦{dq}` (`rangeReqOwn p dq r`).
- **Decision.** Decided by the M3 agent (a stronger internal proved spec, its callers in the branch; reported to
  etcd-grove-03 under "Forms decided").

## 2026-11-21: an admin request refused at apply names no reason at the proposer (auth-mediation M4)

- **Spec.** `adminTieAr` (`Proof/.../etcdserver/KVAuthModel.lean`), through `resultIsWOn`/`resPostM` (the waiter's and
  `processInternalRaftRequestOnce.spec`'s mode-`on` result) and `adminOutOn` (`AdminOn.lean`, the Auth entry points'
  mode-`on` answer); `EtcdServer.raftRequest.spec`'s error branch.
- **Defect.** A refused outcome (`.rejected`, `authApplierV3.Apply`'s `needAdminPermission` check) carried nothing, and
  the error branch of `raftRequest`/`adminOutOn` only `appliedErr` (the result's `Err`, no outcome, no prefix): a client
  could not tell why its admin request failed (refusal-completeness at the proposer, G4 left).
- **Evidence.** `adminOut_model` (`ApplyTieOn.lean`) already has `adminRejL` at the latest state (`hrej`) and dropped it.
- **Proposed change.** `adminTieAr`'s rejected case states `¬ auth.adminOk st (principal of rq)`; `raftRequest.spec`'s
  error branch gives `appliedErrM E.authOn` (`appliedErr`'s, at the committed prefix `L` before the entry, with the
  result, the step's outcome, `modelOutM` and `adminTieM` of that one outcome, `resultIsM`; one mode-uniform
  definition, no `match` on the mode), and `adminOutOn`'s error branch the same. Stronger posts; `appliedErr_of_M`
  forgets.
- **Decision.** Approved by the user (2026-11-21, via etcd-grove-03), as proposed in `notes/auth-mediation-handoff.md`
  ("M4 proposal"); the exact error-branch form (`appliedErrM`, the outcome bound in the same existential as the result,
  so the tie is not vacuous) decided by the M4 agent. It reaches the five admin kinds the mode-`on` proposer admits
  (`adminPropOk`: AuthEnable, UserAdd, RoleAdd, UserGrantRole, RoleGrantPermission), not the other seven Auth rows.

## 2026-11-21: `rnNewStorageOk` proved: `raftpb.HardState` registered (wal-item3; the premise stays, option (c))

- **Spec.** `bootstrappedRaft.newRaftNode.spec` (premise `#Hns : rnNewStorageOk`), `NodeStart`'s two boot statements,
  `NewServer.spec`, `NewServerR`'s spec, etcdstart's `commonPremises`, `OneMember.premises`, the auth, leaseexpiry
  and putget3 `Defs` (`rnNewStorageOk` a conjunct of each), hence every closed theorem over them.
- **Defect.** `rnNewStorageOk` (`NewStorage`'s contract) was a premise although wal-link L3 proved it from the storage
  specs (`rnNewStorageOk_holds`), whose WAL `Save`/`SaveSnapshot` took the unproved `WalPbIn.MarshalHsLaw`
  (`pbutil.MustMarshalMessage` of a `*raftpb.HardState`): `raftpb.HardState` was not a registered protobuf type, so
  no `proto` spec covered its encoding (ledger 2026-11-20, wal-fsfix2 item 3's stop).
- **Evidence.** wal-fsfix2 a8's survey; `etc/gen-link.py --walfs`'s Link (`h_WalPbIn_MarshalHsLaw`, 8 results).
- **Proposed change.** Option (a): register `raftpb.HardState` like `walpb.Snapshot` (trusted: `hsSchema` in
  `pbSchemaOf`, `hsEncC_ok`, `pbHsC_reg`; Go: `examples/stdlib/walpb/hardstate_test.go`, `etc/pbschema-check.py` with
  two negative tests on HardState), prove `MarshalHsLaw` over `proto.MarshalPb.spec` (`walSrvP_marshalHs`), link the
  storage proofs at every `WalH` (`RnNewStorageLinked.lean`: `walStorSpecs_holds`, `rnNewStorageOk_law_holds`), and
  take `rnNewStorageOk.law` in `newRaftNode`'s proof (an `=` callee) instead of the premise.
- **Decision.** Approved by the user, 2026-11-20, via etcd-grove-03 (option (a); the predecessor's form accepted).
  **Amended 2026-11-21 (etcd-grove-03, option (c)):** the WAL's linked results take the semantic hypothesis
  `[UntypedRuneSemantics]` (`filepath`), so taking the law in `newRaftNode` would add it to every closed statement.
  Landed: the registration, `walSrvP_marshalHs`, `walStorSpecs_holds`, `rnNewStorageOk_law_holds` (under the class);
  `rnNewStorageOk` stays the premise of the specs and closed theorems above, unchanged, until Perennial steps those
  operations (`notes/perennial-changes.md`, "Operations on untyped rune constants have no step").
## 2026-11-20: `proto.Size` and `proto.SizeMessage` claim `0 ≤ n` of messages with shared sub-messages (prove-protootel)

- **Spec.** `proto.Size.spec` (conjuncts 2 and 3: a range response, a read-only transaction's response) and
  `proto.SizeMessage.spec` (`Spec/google_golang_org/protobuf/proto/`), trust-boundary axioms.
- **Defect.** False as stated: protobuf-go sums sizes with wrapping `int` additions, and the premises hold their
  repeated sub-messages read-only (shared pointers allowed; `msgPtsC` says nothing of a message's responses), so a
  pointer repeated many times gives a true size above `2^63` in little memory and a negative result.
- **Evidence.** protobuf-go v1.36.12 `internal/impl/encode.go:63-117`, `codec_field.go`; `examples/axiomcx/protosizewrap`
  (three tests, negative results); `notes/axiom-review/proto-size-wrap.md`.
- **Proposed change.** `proto.Size`: drop `0 ≤ sint.Z n` from conjuncts 2 and 3 (no caller uses it). `proto.SizeMessage`:
  `proto.SizePb`'s statement at the content (`msgPtsCC`, no responses, `msgSize c < 2^63 → sint.Z n = msgSize c`) and a
  no-claim case over `msgPtsC`; `decodeLoop` needs the stream decoders' size facts without `N.Sz` first.
- **Decision.** `proto.Size`: applied (prove-protootel, 2026-11-20; a weaker post, unused by every caller).
  `proto.SizeMessage`: open (needs the rafthttp receiver's size facts unconditional; the note says why).

## 2026-11-20: `goose_adequacy_start` hands out the rights of names whose descriptor IDs collide (prove-promdeep)

- **Spec.** `EtcdGrove.goose_adequacy_start` (`Proof/runtime/Start.lean`, a trust-boundary axiom), with the meaning
  of `prometheus.nameFree` (`Proof/github_com/prometheus/client_golang/prometheus/Registry.lean`) that
  `prometheus.MustRegister.wp_proof` relies on.
- **Defect.** False. The axiom gave `nameFree n` for every name of any duplicate-free `Ns`; `nameFree n` promises that
  no one but its holder registers `n`'s label-free descriptor ID (`xxhash64(n ++ "\xff")`). Two distinct names can
  share that ID, and registering the first then registers the second's ID: a program registering counters of both
  was proved not to panic, and panics on the second `MustRegister` (`Registry.Register`: the collector ID is taken,
  `AlreadyRegisteredError`).
- **Evidence.** `m_b699caa269ad35ee` and `m_641c7bdac316dcb7` (both `nameOk`) have ID `0xfea999cc795d2229`:
  `examples/axiomcx/promidcollide` (Go, client_golang v1.24.1), `prometheus.descId_collision` (Lean, over the xxhash
  model `Proof/github_com/cespare/xxhash/v2/Model.lean`); `notes/axiom-review/prometheus-id-collision.md`.
- **Proposed change.** A premise `hNsIds : prometheus.descIdsDistinct Ns` (the names' `descId`s pairwise distinct),
  decidable, an auto-parameter (`decide +kernel`) of the axiom and of `etcd_adequate`, `etcd_adequate_alloc` and
  their `_members` forms, so that every program's names are checked by the kernel where its closed theorem is
  proved; the closed theorems' statements do not change.
- **Decision.** Applied (prove-promdeep, 2026-11-20; a strengthening of an axiom's premise, discharged at every use).

## 2026-11-20: `txn.ApplySecObserve` panics on a non-UTF-8 label (prove-etcdserver)

- **Spec.** `txn.ApplySecObserve.spec` (`Spec/go_etcd_io/etcd/server/v3/etcdserver/txn/ApplySecObserve.lean`), an axiom
  until this change.
- **Defect.** Held for any `version`, `op`; the body is `applySec.WithLabelValues(version, op, FormatBool(success))
  .Observe(...)` (`metrics.go:59-61`), and prometheus' `WithLabelValues` panics on a label value that is not valid UTF-8
  (client_golang v1.24.1 `histogram.go:1263`, `validateLabelValues`, `labels.go:166`).
- **Evidence.** Code reading; `notes/axiom-review/etcdserver-observers-v2stats.md`.
- **Proposed change.** Premise `⌜utf8Valid version ∧ utf8Valid op⌝`; the three `dispatch` proofs pass `"v3"` and a literal
  operation name (`by decide`).
- **Decision.** Applied (prove-etcdserver, 2026-11-20), and the function proved (its body translated).

## 2026-11-20: `v2stats.ServerStats.RecvAppendReq`/`SendAppendReq` panic on a zero `ServerStats` (prove-etcdserver)

- **Spec.** `v2stats.ServerStats.RecvAppendReq.spec`, `v2stats.ServerStats.SendAppendReq.spec` (axioms).
- **Defect.** Premise only `st ≠ null`; a zero `&v2stats.ServerStats{}` (exported type) has nil rate queues, and
  `statsQueue.Insert` (`queue.go:62-63`, `q.rwl.Lock()`) dereferences nil: Go panics, the axiom proves the call returns.
  Only `NewServerStats` allocates the queues.
- **Evidence.** Code reading (`v2stats/server.go:91-128`, `queue.go`); `notes/axiom-review/etcdserver-observers-v2stats.md`.
- **Proposed change.** A persistent `v2stats.isServerStats st` (the queues allocated, the stats' lock), given by
  `NewServerStats`' post and required by both methods (and `BecomeLeader`, for the lock); threaded through the server's
  and the transport's invariants to `EtcdServer.Process` and `Transport.Send`.
- **Decision.** Open: recorded only (the callers' invariants are rafthttp's, another group's files on 2026-11-20).

## 2026-11-20: `v2stats.ServerStats.RecvAppendReq`/`SendAppendReq` need `NewServerStats`' queues (prove-rafthttpfix)

- **Spec.** `v2stats.ServerStats.RecvAppendReq.spec`, `v2stats.ServerStats.SendAppendReq.spec`, `v2stats.NewServerStats.spec`
  (axioms), `rafthttp.Transport.Start.spec`, `srvProcOk`, `trFixed`.
- **Defect.** As recorded by prove-etcdserver the same day: the methods' premise was `st ≠ null` only, and a zero
  `&v2stats.ServerStats{}` has nil rate queues, which `statsQueue.Insert` dereferences (`server.go:91-128`, `queue.go:62-63`).
- **Evidence.** Code reading; `notes/axiom-review/v2stats-serverstats-queues.md`.
- **Proposed change.** A persistent `v2stats.isServerStats st` (opaque: `ServerStats`' anonymous struct field keeps its
  fields untranslated), in `NewServerStats`' post and the two methods' premises, threaded through `srvProcOk` (to
  `EtcdServer.Process`) and `Transport.Start`'s premise and `trFixed` (to `Transport.Send`). Converges to the spec plan's
  `v2stats.isServerStats`.
- **Decision.** Applied (prove-rafthttpfix, 2026-11-20).

## 2026-11-20: `proto.SizeMessage` claims `0 ≤ n` of a message with shared sub-messages (prove-rafthttpfix)

- **Spec.** `proto.SizeMessage.spec` (`Spec/google_golang_org/protobuf/proto/SizeMessage.lean`, a trust-boundary axiom);
  `rafthttp.msgAppV2Decoder.decode.spec`; the stream path's codec parameter.
- **Defect.** As recorded by prove-protootel the same day (`notes/axiom-review/proto-size-wrap.md`):
  protobuf-go's size sum wraps, and `msgPtsC` admits a repeated entry pointer and unowned responses, so `0 ≤ n` is false.
- **Evidence.** `examples/axiomcx/protosizewrap`; `notes/axiom-review/proto-sizemessage-fix.md`.
- **Proposed change.** Two forms: over `msgPtsC`, no claim on the result; over `msgPtsCC l … c` with `c.resps = []`,
  `msgSize c < 2^63 → sint.Z n = msgSize c` (as `proto.SizePb`). The two counting callers discharge the bound:
  `snapshotHandler.ServeHTTP` from `decodeLimit`'s 64 MiB and `MsgDecC`; `streamReader.decodeLoop` from `msgSizeOk`, now
  unconditional (the stream codec's `Sz` is `True`, every sender's bundle being bounded; the msgappv2 decoder's post
  `Sz → msgSizeOk c`, heartbeats included).
- **Decision.** Applied (prove-rafthttpfix, 2026-11-20).

## 2026-11-21: an error's description as the relation `descIs` (errdesc stage 2b)

- **Spec.** `status.Error.spec`, `status.FromError.spec`, `errors.IsStatusErr.spec`, `grpc.model.respond.spec`,
  `waitRetryBackoff.spec`, `toGRPCErrorMap_init` (axioms); `rpctypes.Error`/`ErrorDesc`, `ContextError`,
  `Client.shouldRefreshToken`, `isSafeRetry`, `isSafeRetryMutableRPC`, the handler specs, `fmt.ErrorfWrap`
  (proved); the contracts `grpcInvokerOk`, `grpcMethodOkMd`, `grpcDecOk`, `srvInterceptorOk`.
- **Defect.** The description was the pure `errDesc : GoInterface → GoString`, fixed by `status.Error`'s post at a
  pointer it allocates: unsatisfiable (`notes/errdesc-ghost-plan.md` §0).
- **Evidence.** `notes/axiom-review/ctx-descs.md`, etcd-refimpl `README.md` "Findings".
- **Proposed change.** `descIs err m` as in SpecPlan's direction (`errView`/`descIs`), the description a parameter
  `m` fixed in the precondition; posts `∃ m, descIs err m ∗ …`. Convergence: this tree keeps `statusCodeIs` and
  `descIs` separate where SpecPlan has one `errView err c m ok`; `IsStatusErr` takes the descriptions optionally
  (`isDescs`, `dm : Option`), SpecPlan's takes them always.
- **Decision.** Applied (prove-errdesc2b, 2026-11-21; `notes/decisions.md`, "An error's description as a per-run
  relation").

## 2026-11-21: `apierrors.NewInternalError` needs its error's `Error() string` in the method set (prove-k8s3)

- **Spec.** `apierrors.NewInternalError.spec` (`Spec/k8s_io/apimachinery/pkg/api/errors/NewInternalError.lean`;
  until this change a trust-boundary axiom).
- **Defect.** Not provable over the body: `fmt.Sprintf("Internal error occurred: %v", err)` is specified by
  Perennial's `fmt.argOk`, which asks the method-set entry `methodSet ei.ty !! "Error" = some fmt.noArgStringSig`
  (`fmt`'s `handleMethods` switches `case error:` by signature); the precondition gave `Error()`'s WP and no
  `Format`, not the entry. Go's type system gives the entry of every non-nil `error`; the model ties no interface
  value's type to its static interface. Not a defect of Go's behavior.
- **Evidence.** prove-k8s2's attempt (2026-11-21, `notes/STATUS.md`); the proof of this change.
- **Proposed change.** Add the entry to the precondition's pure conjunct. Callers: `transformErrorToEvent` (from
  `kErrOk`, which already has it) and the model API server's handlers (from `apimodelInit`, whose error clauses gain
  it: its errors are `errors.New`'s `*errorString`, which has it; the fact is not proved yet, no `Init.lean`).
- **Decision.** Applied (prove-k8s3, 2026-11-21); `apierrors.NewInternalError.wp_proof` is a theorem. Approved by the user (2026-11-21): the premise makes sense (`.claude/skills/spec/examples/newinternalerror-type-fact.md`).

## 2026-11-21: the HTTP header specs need net/http's package initialization (prove-http3)

- **Spec.** `http.HeaderSet_spec`, `HeaderSetPtr_spec`, `HeaderGet_spec`, `HeaderGetPtr_spec`, `HeaderGetOwnPtr_spec`
  (`Proof/net/http/Boundary.lean`; four of them trust-boundary axioms until now); the predicates `hdrOwn`, `hdrAtRaw`
  (opaque until now).
- **Defect.** Not provable as stated: `Header.Set`/`Get` call `textproto.CanonicalMIMEHeaderKey`, which (for a key it
  changes) runs `commonHeaderOnce.Do(initCommonHeader)` and reads the package map `commonHeader` (go1.27.3
  `net/textproto/reader.go:796`); without the package's initialization the specs know nothing of that `Once`.
- **Evidence.** The translation (`Code/net/textproto.lean`, `CanonicalMIMEHeaderKey.impl`, `canonicalMIMEHeaderKey.impl`).
- **Proposed change.** Each spec takes `isPkgInit pkg_id.net.http` (net/textproto's fact: `commonHeaderOnce` is the
  `Once` of `initCommonHeader`, `Proof/net/textproto/Base.lean`); `hdrOwn`/`hdrAtRaw` defined (`hdrMap`: a
  `map[string][]string` whose value at each key is a read-only slice of that key's values in order). Every caller has
  `isPkgInit` of rafthttp, which imports net/http: discharged there with no change to the callers' statements.
- **Decision.** Applied (prove-http3, 2026-11-21): the four axioms are theorems over net/http's and net/textproto's code.
## 2026-11-21: mvcc's hasher, `kvHasherOk` a resource (prove-etcdint3)

- **Spec.** `mvcc.newKVHasher.spec`, `mvcc.kvHasher.WriteKeyValue.spec`, `mvcc.kvHasher.Hash.spec` (axioms until
  this change), over `mvcc.kvHasherOk` (`HashDefs.lean`).
- **Defect.** `kvHasherOk` was an opaque `Prop`, so nothing owned the `crc32` digest that `Write` updates through
  `h.hash` (the axioms were not provable over the real code); and `WriteKeyValue`'s map `keep` (whose ownership it
  took) was any map, where Go reads `h.keep`.
- **Evidence.** `hash.go:49-94` (the digest a `*crc32.digest`, written through the interface), translated with
  `hash/crc32`'s `New`/`Write`/`Sum32` (`crc32.go:146-230`).
- **Proposed change.** `kvHasherOk h : IProp`: the digest's points-to and its Castagnoli table; `newKVHasher` returns
  it with the fields (`compactRevision`, `revision`, `keep` its arguments); `WriteKeyValue` takes `h.keep' = keep`
  and gives back `hp ↦ h ∗ kvHasherOk h` (the value unchanged, where it was some `h'`); `Hash` gives `kvHasherOk h`
  back. The one caller (`store.scheduleCompaction`) threads them.
- **Decision.** Applied (prove-etcdint3, 2026-11-21).

## 2026-11-21: k8s utils `trace.New` needs its package's initialization; `trace.fromNew` defined (prove-otel4)

- **Spec.** `trace.New.spec` (`Spec/k8s_io/utils/trace/New.lean`, a trust-boundary axiom until this change) and the
  predicate `trace.fromNew` (`Proof/k8s_io/utils/trace/Defs.lean`, opaque until now), which `Trace.Step`'s and
  `Trace.LogIfLong`'s specs take.
- **Defect.** Not provable as stated: `New` is `&Trace{name: name, startTime: time.Now(), fields: fields}`
  (`k8s.io/utils` `be93311217bd` `trace/trace.go:154-156`), and `time.Now`'s spec takes `isPkgInit time`, which the
  premise `True` does not give; and its post was the opaque `trace.fromNew t`, which no proof can establish.
- **Evidence.** The translation (`Code/k8s_io/utils/trace.lean`, `New.impl`, with `time` and `sync` imported so that
  `Trace` translates as a struct).
- **Proposed change.** The premise `isPkgInit pkg_id.k8s_io.utils.trace` (which gives `time`'s: `iPkgInit`);
  `trace.fromNew t := t ≠ null` (what `Step` and `LogIfLong` need: they lock `t.lock` first, a nil receiver panics;
  any non-nil `*Trace` of a Go program is a `Trace`, and both accept its zero value). The three callers
  (`RealFIFO.Pop`, `processorListener.run`, `Reflector.list`) have `isPkgInit` of client-go's `cache`, which imports
  the package: discharged there with no change to their statements.
- **Decision.** Applied (prove-otel4, 2026-11-21); `trace.New.wp_proof` is a theorem.

## 2026-11-21: the lessor's `scheduleCheckpointIfNeeded` reads the lease's `ID` (prove-pgaps)

- **Spec.** `lease.lessor.scheduleCheckpointIfNeeded.spec` (`Spec/go_etcd_io/etcd/server/v3/lease/`; a trust-boundary
  axiom until this change, when the method was names only for its float-to-integer conversion).
- **Defect.** Not provable over the real code: the push's item `&LeaseWithTime{id: lease.ID, ...}` and the debug line's
  `zap.Int64("leaseID", int64(lease.ID))` load `lease.ID` (`lessor.go:759-766`), and the premise gave no points-to for it.
- **Evidence.** The translation (`Code/go_etcd_io/etcd/server/v3/lease.lean`, `lessor.scheduleCheckpointIfNeeded.impl`).
- **Proposed change.** The premise takes `lsF "ID" l ↦□ id` (read-only once granted: `leaseMeta`'s and the lessor
  invariant's `ID`); its two callers (`Grant`, `Checkpoint`) hold it persistently and pass it. `SpecPlan`'s statement
  (`lessorFields` and a lease of the lessor's state) already covers it.
- **Decision.** Applied (prove-pgaps, 2026-11-21): the method is translated and proved, the axiom retired.

## 2026-11-21: the lessor's `Promote` lacks the resources its sort's `Remaining()` takes (prove-pgaps, triage)

- **Spec.** `lease.lessor.Promote.spec` (`Spec/go_etcd_io/etcd/server/v3/lease/lessor__Promote.lean`, a trust-boundary
  axiom).
- **Defect.** Not provable as stated over the real code (found triaging it for a proof; the float arithmetic and the
  float-to-integer conversion step since Perennial `08d191151`): with
  `leaseRevokeRate` or more leases it runs `sort.Sort(leasesByExpiry(leases))`, whose `Less` calls each lease's
  `Remaining()`, which read-locks the lease's `expiryMu` (`lease.go`), a reader slot of a bounded pool: `Leases`,
  which sorts the same way, takes `levelTok leaseLvl`'s pool access, `threadBound GF ≤ 2^30 - 1` and
  `receiptBound GF ≤ 2^62` (the sort's length bound) for it. `Promote.spec` takes only `lessorInv` and `lessorCfg`.
- **Evidence.** `lessor.go` (`Promote`: `sort.Sort(leasesByExpiry(leases))`, then `l.Remaining()` in the loop);
  `lessor__Leases.lean`'s `sorter_byExpiry`.
- **Proposed change.** `Promote.spec` takes the level-0 token (`levelTok lessorLvl`, given back) and the two bounds,
  as `Leases.spec` does; the server's callers (`LessorOk.lean`'s contract, `NewServer`'s promotion on becoming
  leader) supply them. Not applied: it changes the server's lessor contract.
- **Decision.** Open (the axiom stays).

## 2026-11-21: v2stats' `ServerStats.BecomeLeader` takes the stats' ownership (prove-ps2-v2stats)

- **Spec.** `v2stats.ServerStats.BecomeLeader.spec` (`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v2stats/`; a
  trust-boundary axiom until this change: `ServerStats`' type has an unnamed struct field with tags,
  `serverStats.LeaderInfo`, which Goose refused until mit-pdos/perennial#655).
- **Defect.** Not provable over the real code: the premise was `st ≠ null` only, and `BecomeLeader` locks the stats'
  mutex and writes its fields (`server.go:130-145`), which nothing in the premise owns.
- **Evidence.** The translation (`Code/go_etcd_io/etcd/server/v3/etcdserver/api/v2stats.lean`,
  `ServerStats.BecomeLeader.impl`, `ServerStats.becomeLeader.impl`).
- **Proposed change.** The premise adds `v2stats.isServerStats st` (persistent: the stats' mutex owning the embedded
  `serverStats`, the two rate queues with their `RWMutex`es), as `RecvAppendReq` and `SendAppendReq` already take
  (the user's rule of 2026-11-21: a persistent ownership premise in place of `≠ null` alone, when every caller
  discharges it). Its one caller, `EtcdServer.run`'s `updateLeadership` (`EtcdServer__run.lean`), has it from the
  server's stats facts (`srvStatsAddr s ↦□ st ∗ v2stats.isServerStats st`, as `InvNet.lean`'s `srvProcOk`).
  `SpecPlan`'s statement (`isServerStats p`) already has it. `isServerStats`, opaque until now, is defined
  (`v2stats/Defs.lean`).
- **Decision.** Applied (prove-ps2-v2stats, 2026-11-21): with `NewServerStats`, `RecvAppendReq`, `SendAppendReq`,
  the four axioms retired, pending the Perennial pin bump to #655.
- **Decision.** Applied (prove-ps2-promote, 2026-11-21; heads-up on #10, no objection): `Promote.spec` takes
  `levelTok lessorLvl` (given back) and the two bounds, and is proved over the real code (the axiom retired). The
  server's lessor contract (`lessorOk`, InvApplier.lean) has `Promote` take the caller's `threadTok` (given back; it
  lends level 0, `threadTok_level0`), and `lessorOk_of_lessorInv` takes the two bounds, which `NewServer`/`NewServerR`
  give from theirs (`threadBound GF ≤ 2^28`, `receiptBound GF ≤ 2^48`); the apply thread's `applyEntryNormal` pays
  the token from its `srvGoRes`. No spec of the server changes.

## 2026-11-21: the auth store's `selectPassword` reads `as.bcryptCost` (prove-authcrypto)

- **Spec.** `auth.authStore.selectPassword.spec` (`Spec/go_etcd_io/etcd/server/v3/auth/`; a trust-boundary axiom
  until this change, the method names only).
- **Defect.** Not provable over the real code: its bcrypt branch is `bcrypt.GenerateFromPassword([]byte(password),
  as.bcryptCost)` (`store.go:420-426`), a load of the store's `bcryptCost` field, and the premise gave only
  `st ≠ null`.
- **Evidence.** The translation (`Code/go_etcd_io/etcd/server/v3/auth.lean`, `authStore.selectPassword.impl`).
- **Proposed change.** The premise takes the field read-only (`∃ c, aF "bcryptCost" st ↦□ c`); `authInv` holds it
  (its last conjunct; `NewAuthStore`'s composite literal sets it and nothing writes it: `NewAuthStoreOn`'s proof
  already had it persistent), `authInv_bcryptCost` hands it out; the four callers (`UserAdd`, its two `sure`
  variants, `UserChangePassword`) pass it. `NewAuthStore`'s axiom is unchanged (its contracts do not mention
  `authInv`).
- **Decision.** Applied (prove-authcrypto, 2026-11-21).

## 2026-11-21: bcrypt's `GenerateFromPassword` returns `nil` with its error (prove-authcrypto)

- **Spec.** `bcrypt.GenerateFromPassword.spec` (a trust-boundary axiom).
- **Defect.** Too weak for `selectPassword`'s post (`∃ bs, b ↦*□ bs` on every path): the error disjunct said nothing
  of the returned slice.
- **Evidence.** `bcrypt.go:95-104` (x/crypto v0.57.0): both error returns are `return nil, err`.
- **Proposed change.** The error disjunct also states `h = slice.nil` (a strengthening of the axiom, true of the
  code; `EtcdServer.UserAdd`'s two uses drop it).
- **Decision.** Applied (prove-authcrypto, 2026-11-21).
## 2026-11-21: the lessor's `demotec` and stop channels get ghost state (prove-ps2-lease)

- **Spec.** `lease.lessor.Demote.spec`, `lease.lessor.Stop.spec`, `lease.lessorStopTok`
  (`Spec/go_etcd_io/etcd/server/v3/lease/`, `Proof/.../lease/LessorBackend.lean`; all three axioms), and what
  `lessorInv` says of `demotec` (`InvLessor.lean`'s `lessorExtra`).
- **Defect.** Not provable over the real code: `Demote`'s `close(le.demotec)` needs a close right the invariant did
  not keep (`demotec` sits in `le.mu`'s fractional guard); `Stop`'s `close(le.stopC); <-le.doneC` needs the channels,
  which the opaque `lessorStopTok` did not name.
- **Evidence.** `lessor.go:534-550`, `:615-618`; the translations (`lessor.Demote.impl`, `lessor.Stop.impl`, the
  latter translated by this change).
- **Proposed change.** `lessorStopTok` defined (the two fields read-only, `stopC`'s broadcast close right, `doneC`'s
  receive side); `demotec`'s state per channel in an invariant with a close token, the current token in a lessor
  invariant tied by a ghost variable (`LessorRdNames`' seventh name) half in `lessorExtra` (which takes the lessor's
  `γl`). `Demote.spec`'s statement is unchanged but stated at `HasLC.hasLC` (its only callers, the server's, are;
  the channel close needs it). The assumed `NewLessor`, `Promote` and `Renew` keep their statements; their claims about
  the ghost state are checked in `notes/axiom-review/lessor-demotec-stop.md`.
- **Decision.** Applied (prove-ps2-lease, 2026-11-21): `Demote`, `Stop` proved, `lessorStopTok` and its `Timeless`
  instance retired.
## 2026-11-21: `v3rpc.NewMaintenanceServer` lacks the watchable store's `isMvcc` (prove-ps2-nms)

- **Spec.** `v3rpc.NewMaintenanceServer.spec` (`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/`; a
  trust-boundary axiom until this change).
- **Defect.** Not provable over the real code: the body calls `s.KV().HashStorage()` (`maintenance.go:101`), and
  mvcc's `KV.HashStorage.contract` takes the store's `isMvcc`; the premise gave only `srvKVAddr s ↦□ wsIface wsl`,
  the field's value, which the type `*watchableStore` alone does not make a store.
- **Evidence.** The translation (`Code/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc.lean`,
  `NewMaintenanceServer.impl`); `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean`, `KV.HashStorage.contract`.
- **Proposed change.** The spec takes `∀ γ` and the persistent `□ mvcc.api.isMvcc (v3rpc.wsIface wsl) γ` (the
  user's rule of 2026-11-21: a persistent ownership premise every caller discharges). Its one caller, `v3rpc.Server`,
  gets it from `v3rpc.grpcCfgOk`, which gains `□ isMvcc (wsIface C.wsl) C.E.γ`; the two places building it
  (`client.grpcCfgOk_of_started`, `_ofStartedM`) have it from `srvWatchBuilt` (`isMvcc E.kv E.γ`, `E.kv = wsIface wsl`).
- **Decision.** Applied (prove-ps2-nms, 2026-11-21): the function is proved, the axiom retired.
## 2026-11-21 · the backend image can be ahead of the merged snapshot's apply cursor

- **Spec.** `EtcdServer.createMergedSnapshotMessage` and `MemoryStorage.Entries`.
- **Defect.** The old sender postcondition fixed the label at the apply cursor.
  A restarted leader may already have a later committed image. The storage
  read postcondition allowed a strict prefix even for an unlimited read.
- **Evidence.** The Go regression reopens an image at index 7 with entry
  term 2 and recovered commit 3. The Raft storage implementation returns
  the entire requested interval for an unlimited successful read.
- **Decision.** The implementation proof uses the image's index, its entry
  term, and its configuration. It reads the initial log from the actual
  MemoryStorage before RestartNode and maintains an immutable history per
  Ready. The public storage spec retains the bounded-read prefix guarantee
  and identifies the complete interval for the unlimited case.
  [Replay regression](../../issues/etcd-merged-snapshot-replay-failure.md).
## 2026-11-21: `types.URLs.StringSlice` owns nothing of the URLs it reads (prove-ps2-misc)

- **Spec.** `types.URLs.StringSlice.spec` (`Spec/go_etcd_io/etcd/client/pkg/v3/types/URLs__StringSlice.lean`; a
  trust-boundary axiom until this change, `client/pkg/v3/types` names-only but for `URLs.Len` and `ID.String`).
- **Defect.** Not provable over the real code: the premise was `p ≠ null` alone (true of Go by type safety), but the
  pointer wrapper loads `*p` and the body reads `us[i]` and calls `url.URL.String` on each element
  (`client/pkg/types/urls.go:79-86`), which needs the slice and the elements (`http.URLStringAny_spec` takes
  `p ↦{dq} u`). The post was `True`.
- **Evidence.** The translation (`Code/go_etcd_io/etcd/client/pkg/v3/types.lean`, `URLs.StringSlice.impl`).
- **Proposed change.** Under the approved ownership rule (2026-11-21): the premise takes `p ↦{dq} sl ∗ sl ↦*□ us`
  (the post gives `p ↦{dq} sl` back, and the fresh output slice of as many strings). Its one caller, `NewServer`
  (and `NewServerR`) on `cfg.ClientURLs`, holds the field and `cfg.ClientURLs' ↦*□ U.client` (`bootCfgRO`).
- **Decision.** Applied (prove-ps2-misc, 2026-11-21): `URLs.StringSlice` translated and proved, the axiom retired.
## 2026-11-21: `FollowerStats.Fail` takes the stats' mutex (prove-ps2)

- **Spec.** `v2stats.FollowerStats.Fail.spec` (`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v2stats/`; a
  trust-boundary axiom until this change, `leader.go` names-only).
- **Defect.** Not provable over the real code: `Fail` locks the stats' embedded `sync.Mutex` and increments
  `Counts.Fail` (`leader.go:131-135`), and the premise (`fs ≠ null`) gave no mutex and no points-to. True of Go by its
  type safety (every non-nil `*FollowerStats` points to a valid one), not provable in the logic.
- **Evidence.** The translation (`Code/go_etcd_io/etcd/server/v3/etcdserver/api/v2stats.lean`, `FollowerStats.Fail.impl`).
- **Proposed change.** A persistent `v2stats.isFollowerStats fs` (the mutex, guarding `Counts.Fail`), allocated by
  `LeaderStats.Follower` with the stats (`&FollowerStats{}`) and kept for the map's values by `lsFollowers`;
  `Follower`'s post gives it (a strengthening), `startPeer` takes it (its one caller, `Transport.AddPeer`, gets it
  from `Follower`), the pipeline keeps it (`pipeHandleOk`: `nil` or the mutex) and passes it to `Fail`. The user's
  decision (2026-11-21): an ownership premise every caller discharges may be added.
- **Decision.** Applied (prove-ps2, 2026-11-21): `Fail` translated and proved, the axiom retired.
- **Decision.** Applied (prove-k8s3, 2026-11-21); `apierrors.NewInternalError.wp_proof` is a theorem.

## 2026-11-20: `backend.Snapshot` proved; its pre lends a reader's token (backend-snapshot B3/B4)

- **Spec.** `backend.backend.Snapshot.spec` (`Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__Snapshot.lean`),
  and the statements that restate it: mvcc's `mvccImage_snapshot.law` (`Spec/.../storage/mvcc/EtcdBackend.lean`), the
  server's `senderImage.law` (`KVStoreApi.lean`).
- **Defect.** Unprovable as stated (an axiom until now): `Snapshot` read-locks `b.mu` around bbolt's `Begin(false)`, which
  takes the caller's `threadTok` for `mmaplock`'s slot; one thread token cannot also pay for `b.mu`'s slot (thread pools
  borrow the whole token), and the pre had no other reader resource.
- **Evidence.** `notes/backend-snapshot-plan.md`, "The reader slot of `b.mu`" (Perennial's `threadPool.borrow`,
  bbolt's `Begin.spec`).
- **Proposed change.** Every backend reader's token `rdTok` carries a read slot of `b.mu` (`bmSlot`; the constructor makes
  `actualMaxReaders - 1` tokens, the batch transaction keeping one of `b.mu`'s slots); the pre and post of the three
  statements add the caller's `rdTok`, lent (SpecPlan's `Snapshot` takes a counted reader slot too). The server's apply
  thread lends the one it holds (`apply.bkRT`). The observation `Q` and the rest are unchanged.
- **Decision.** Taken under the user's direction of 2026-11-20 ("make your own choice ... the top-level robustness theorems
  should have fewer axioms"): it retires the `backend.Snapshot` axiom from every collection that reaches it.

## 2026-11-21: `lessor.Renew` proved; `stopC` and `revokec` close-once channels (prove-ps2-renew)

- **Spec.** `lease.lessor.Renew.spec` (`Spec/go_etcd_io/etcd/server/v3/lease/lessor__Renew.lean`; a names-only
  trust-boundary axiom until this change), unchanged. The definitions under it: `lease.lessorStopTok`
  (`LessorBackend.lean`), `lessorExtra`, `leaseMeta`, `revokeCloser` (`InvLessor.lean`), `leaseInit` (`Base.lean`).
- **Defect.** Not provable over the real code with the invariant as it was: `Renew`'s `select` receives on the lease's
  `revokec` (whose whole channel state was the revoker's `revokeCloser`), on `stopC` (a broadcast channel whose receive
  side nothing in `lessorInv` held, and `ownBroadcastChan` is stated at `HasLC.hasLC` only, the lessor's invariant at any
  `hlc`), and `leaseRenewed.Inc()` calls a counter `leaseInit` did not describe.
- **Evidence.** `lessor.go:396-456`; the translation (`lessor.Renew.impl`).
- **Proposed change.** `revokec` and `stopC` close-once channels as `demotec` already was (`onceChanInv`, `onceRecv`,
  renamed from `demoteChanInv`/`demoteRecv`): `revokeCloser c` the channel's `onceRecv` and close token, `leaseMeta`'s
  `revokec` its `revokeRecv`; `lessorStopTok` `stopC`'s close token, `lessorExtra` its `lessorStopRecv`; `leaseInit` adds
  `leaseRenewed`'s `counterSpec` (grouped with `leaseRevoked`'s). No spec a caller sees changes; `NewLessor`'s axiom
  claims more of its result (checked: `notes/axiom-review/lessor-demotec-stop.md`, prove-ps2-renew section).
- **Decision.** Applied (prove-ps2-renew, 2026-11-21): `Renew` and `Lease.expired` translated and proved, the axiom
  retired; `NewLease`, `initAndRecover`, `Grant`, `Revoke`, `Stop` re-proved over the new definitions.

## 2026-11-21: `lease.NewLessor`'s reader slots (prove-ps2-newlessor)

- **Spec.** `lease.NewLessor.spec` (`Spec/go_etcd_io/etcd/server/v3/lease/NewLessor.lean`; a trust-boundary axiom).
- **Defect.** False of the model: the post gave the caller all `Int.toNat actualMaxReaders` reader slots of `le.mu`,
  while the `runLoop` goroutine `newLessor` forks read-locks `le.mu` in every iteration (`revokeExpiredLeases`,
  `lessor.go:640`); `init_RWMutex` makes exactly that many slots, so none is left for the loop.
- **Evidence.** `notes/axiom-review/newlessor-reader-slot.md`; `lessor.go:245,640`; Perennial's `RWMutexGuard.lean`.
- **Proposed change.** The post gives `Int.toNat actualMaxReaders - 1` slots (the loop keeps one); the rest unchanged.
- **Decision.** Approved by the user (2026-11-21), on the condition that every caller still proves: applied, the callers'
  slot arithmetic adjusted (`NewServer`, `NewServerR`, `mvccfull`'s `runner.open`, `mvccrand`'s `runChecks`).

## 2026-11-21: `wal.WAL.renameWALUnlock.spec` -- its call made unreachable (supersedes the open parts of the 2026-11-14 entries)

- **Spec.** `Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__renameWALUnlock.lean` (a hypothesis of
  `renameWAL.wp_proof`, and so of `wal.Create`'s and every result over it: the WAL tester's `wp_Boot`/`wp_Main`,
  `h_wal_WAL_renameWALUnlock`).
- **Defect.** False as stated (entries of 2026-11-14): (1) its `w.Close()` needs the encoder and the tail file,
  which `walPreIn` does not carry; (2) its `Open`/`ReadAll` need an atomic update on `walDirIs dir` that the client
  spent at the first rename's commit; (3) after a rename that committed with an error, the second
  `os.Rename(nm.tmp, nm)` has an absent source, which no `os.Rename` spec covers. A false hypothesis makes
  every result over it vacuous.
- **Evidence.** The 2026-11-14 entries; `renameWAL.wp_proof` (`WAL__renameWAL.lean:116-125`) reaches the call only
  when `os.Rename(nm.tmp, nm)` returned an error. The WAL's other specs already rule out such errors when the file
  system cannot fail on the path (`cut.spec`, `Save.spec`: `walCov Sio → DirFits dir ∧ …`; `os.Rename.specFileS`'s
  witness `err ≠ nil → ¬ (FsNoErrOn (· = target) ∧ PathFits src ∧ PathFits target)`, wal-fsfix2).
- **Proposed change.** (a) `os.Rename.specDirS`/`specDirSnc` (`Spec/os/RenameS.lean`) gain the same error witness
  as `specFileS` (a stronger post; proof over a new `wp_osRenameDirSW`/`wp_osRenameDirSNE` in
  `GooseLang/Ext/Fs/NoErrSpecsRename.lean`, as for files: `NoIoErr` gives a directory rename with a success, the
  source a directory, the target absent, the whole call permission held, errno 0). (b) `renameWAL.spec` and
  `wal.Create.spec`/`specFresh` take the premise `FsNoErrOn (· = dir) ∧ PathFits (child r tmp) ∧ PathFits dir`
  (the file system does not fail on the WAL's name, and both names fit). `renameWAL`'s rename-error branch is
  then refuted, and `renameWALUnlock.spec` leaves `renameWAL.wp_proof`'s hypotheses, so it leaves every Link. The spec
  file is deleted, and `renameWALPost`'s arm 2 (the reopened handle) can go, with its handling in `Create`.
  Clients: the WAL tester (premise from its semantics, `NoIoErr allIo`, and its area's path fitting); no
  etcdserver proof calls `wal.Create` (C6 unwritten).
- **Decision.** (a) and (b) decided by the coordinator (etcd-grove-03, 2026-11-21, issue #15): (b) as an internal
  spec premise. The user signs off at the closed statement, whose world premises will list "the area's `wal` and
  `wal.tmp` paths fit (`PathFits`)" explicitly.
- **Made (2026-11-21, `wal-safe` `15fb2e2e44`, `26904191fa`).** (a) `wp_osRenameDirSNE`/`wp_osRenameDirSW`
  (`GooseLang/Ext/Fs/NoErrSpecsRenameDir.lean`), `specDirS`/`specDirSnc`'s witness; (b) the premise on
  `renameWAL.spec`, `wal.Create.spec`/`specFresh`; the error branch refuted, `errors.As` no longer reached
  (`h_errors_AsLinkError` left the Links too); `WAL__renameWALUnlock.lean` deleted; the tester's `Boot`/`Main`
  take `tWalFsOk area`. `renameWALPost`'s arm 2 is now dead but kept (its removal is a cleanup).

## 2026-11-22: `wal.Create.spec`'s no-failure premise widened to `dir.tmp` and the area; `os.RemoveAll.specSubS` and `os.Stat` witness their errors (wal-safe, step 2 (D), design (FNE))
- **Spec.** `Spec/go_etcd_io/etcd/server/v3/storage/wal/{Create,CreateFresh}.lean` (premise
  `FsNoErrOn (· = dir) ∧ PathFits (dir ++ ".tmp") ∧ PathFits dir`, from the entry of 2026-11-21);
  `Spec/go_etcd_io/etcd/server/v3/storage/wal/CreateCallees.lean`'s `fileutil.CreateDirAll.specTmp`; the WAL tester's
  `tWalFsOk` (`WalTester/.../RestartOk.lean`); `Spec/os/RemoveAll.lean`'s `os.RemoveAll.specSubS`.
- **Defect.** `Create` must cope with any leftover `dir.tmp` (a crash's): `RemoveAll` may return `nil` with it still
  there (a spurious `ENOENT`, no effect) and `Exist` may miss it (a `Stat` error), so `CreateDirAll` can meet a
  `dir.tmp` holding anything (a file, a directory with directories, a directory `.touch`). `specTmp` covers only a
  directory of files, and the tester bridges the rest with the premise `BootFoNmTmp` on every crashed tree, which
  no premise on the initial state can discharge.
- **Evidence.** `TrustedCode/os.lean` (`RemoveAll.impl`, `model.removeAllFrom`, `model.stat`) and `NoIoErr`/`PathErrno`
  (`GooseLang/Ext/Fs/Premises.lean`): with `dir.tmp` and its parent covered and fitting, every `nil` exit of
  `RemoveAll(dir.tmp)` is an `unlink`/`rmdir` of `dir.tmp` answering 0 or `ENOENT`, the parent's `open`
  answering `ENOENT`, or a read of `dir.tmp` answering `ENOENT`, each only with `dir.tmp` gone; `Stat` of an
  existing covered path succeeds. Notes: `notes/wal-units/tester.md`, handoffs of sessions 5 and 6.
- **Proposed change.** (FNE) `wal.Create.spec`/`specFresh` and `tWalFsOk` take `FsNoErrOn (fun p => p = dir ∨ p =
  dir ++ ".tmp" ∨ p = r)` (`r` the area, `filepath.Dir dir`), `PathFits` unchanged; `specSubS`'s post gains
  `err = nil → FsNoErrAt (child d b) → FsNoErrAt d → b gone`; `os.Stat.wp_dirSW`/`wp_fileAnySW` (new) witness
  their error; `CreateDirAll.specTmp` is deleted (`Create` then calls `CreateDirAll` only on an absent `dir.tmp`:
  `CreateDirAll.spec`, proved), and with it `walAreaRes`'s `TmpOk`/`tmpClTouch` and the tester's `BootFoNmTmp`.
  The rejected alternative (G): make `TouchDirAll`/`CreateDirAll` cope with any leftover (3-4 sessions).
- **Decision.** (FNE), the coordinator (etcd-grove-03, 2026-11-22). At the closed theorem the widened premise is
  discharged by the semantics' `NoIoErr allIo` (every path), as `tWalFsOk` already is: no new closed premise.
- **Made (2026-11-22, `wal-safe`, session 6).** The `os` half: `specSubS`'s post, `os.Stat.wp_dirSW`/`wp_fileAnySW`
  (`Proof/os/StatNE.lean`), over `wp_fs_postSh` (`GooseLang/Ext/Fs/WpPostShared.lean`). The `wal.Create`/tester
  half (session 7, `57d9a044f0`): the premise widened on `wal.Create.spec`/`specFresh` and `tWalFsOk`;
  `CreateDirAll.specTmp` (and its proof, with `TouchDirAll.specDir`) deleted; `walAreaRes`'s `TmpOk` replaced by
  `ClRanked` of each `nm.tmp`'s claims, `tmpClTouch` gone; the tester's `BootFoNmTmp` gone.

## 2026-11-22: `WalPbIn.CloneHsLaw` narrowed to a non-nil source; `WalHsOwn.notNull` (wal-safe, session 9)
- **Spec.** `Spec/go_etcd_io/etcd/server/v3/storage/wal/ReadAllCallees.lean`: `WalPbIn.CloneHsLaw` (a hypothesis of
  `WAL.ReadAll.wp_proof`) and `structure WalHsOwn`.
- **Defect.** The law covered `proto.Clone` of a nil `*raftpb.HardState` (`P.hsIn` allows nil), which no trusted
  spec covers (`proto.ClonePb.spec` takes a frozen message, non-nil), so the law could not be derived for the raftpb
  instance without new trust.
- **Evidence.** In `ReadAll` (fork `d7c7f6434`, wal.go:717) `state` is `&raftpb.HardState{}` or
  `MustUnmarshalState`'s `&s`, never nil; the reviewer's `clone-hs-law.md` (`/shared/tmp/coord-03/review-wal4/`)
  suggested dropping the nil case.
- **Proposed change.** `CloneHsLaw` takes `p ≠ null`; `WalHsOwn` gains `notNull : HsO p h ⊢ ⌜p ≠ null⌝`, which
  `ReadAll` uses before freezing its `state` (`walRaftHsO_notNull`: `hsOwnC` holds it).
- **Decision.** Made (coordinator's task 2, "narrow the law that way if needed"). `walRaftP_cloneHs` and
  `walRaftHsO_unmarshal` (`RaftModel/LawsHsPb.lean`) discharge `CloneHsLaw walRaftP` and `WalHsOwn.unmarshal` over
  `proto.ClonePb.wp_proof`/`proto.UnmarshalPb.wp_proof` (axioms already reached); both leave `TOpen`.

## 2026-11-22: `io.CopyFiles.spec`'s size premise `m.size < 2^62` too weak (wal-safe, session 9)
- **Spec.** `Spec/io/CopyFiles.lean` (`io.CopyFiles.spec`, a hypothesis of `wal.Repair.wp_proof`).
- **Defect.** With a source of size in `[2^62 - 2^31, 2^62)` the triple is false of the model: the translated
  dispatch reaches `model.pollCopyFileRange`, whose first round asks `min(remain, 0x7ffff000)` bytes at the
  source's offset, and `model.copyFileRangeRound` panics when `offMax (= 2^62) ≤ soff + max`.
- **Evidence.** `TrustedCode/os.lean`, `model.copyFileRangeRound`'s third check; `remain = 2^63 - 1`
  (`tryLimitedReader` of a non-`LimitedReader`).
- **Proposed change.** `m.size < 2 ^ 61` (then every round's `soff + max < 2^62`, and the fallback's `Read`/`Write`
  of 32 KiB stay below `2^62`). `Repair` has `size ≤ Fs.maxBytes = 0xffffffff000`.
- **Decision.** Made (the premise's own statement; no client but `Repair`, which supplies it).

## 2026-11-22: `time.Time.Format.specBroken` weakened to what the WAL uses, and made an axiom (wal-safe, session 11)
- **Spec.** `Spec/time/Time__FormatBroken.lean` (a hypothesis of `wal.WAL.cleanupWAL.wp_proof`, through the WAL and
  tester Links); `cleanupLaw`'s timestamp premise (`Spec/.../wal/WAL__cleanupWAL.lean`).
- **Defect.** Stronger than the WAL needs: its post said every byte is a digit, `.` or `-`, but the WAL uses only that
  the broken name `nm.broken.<s>` is a name (`brokenName_nameOk`: no `/`, no NUL). As a trust-boundary axiom (the
  user's decision, 2026-11-22: "a minimal axiom claiming only what the WAL relies on") the extra claim would be
  trusted for nothing.
- **Evidence.** `brokenName_nameOk`'s proof uses only `/ ∉ s` and `NUL ∉ s`; `create_cleanupLaw` ignores the premise.
- **Proposed change.** Post `⌜timeStampOk s⌝` (`timeStampOk s := 47 ∉ s ∧ 0 ∉ s`); `cleanupLaw` takes the same;
  `timeStampChars` deleted. The axiom `time.Time.Format.wp_proofBroken` (`Proof/time/Time__FormatBroken.lean`),
  reviewed by the `axiom` skill (`notes/axiom-review/time-format-broken.md`: survives).
- **Decision.** Made (the user's approval of item (4), 2026-11-22). Closes the 2026-11-14 entry ("its result
  unconstrained").

## 2026-11-22: `fmt.ErrorfErrsNot.spec`/`fmt.ErrorfErrsTerm.spec` -- premises no proof can use (wal-safe, session 11)
- **Spec.** `Spec/fmt/ErrorfErrsNot.lean`, `Spec/fmt/ErrorfErrsTerm.lean` (hypotheses of the WAL's `decodeRecord`,
  `Record.Validate`, `readWALNames(Absent)`, `openWALFiles`; `TOpen`'s `errorfErrsNot`/`errorfErrsTerm`).
- **Defect.** The premises on each error argument `e` are `errIsNot e t`/`errIsTerm e`: triples of `errors.Is(e, _)`.
  But `errors.Is` on `Errorf`'s result never calls `errors.Is` on the argument: Go's `Is` runs `is(err, target, c)`, a
  loop that on a `*fmt.wrapError` calls `Unwrap()` and continues the loop at the child (and recurses through `is`,
  not `Is`, for `Unwrap() []error`). So a proof of the result's triple needs facts about every error of the
  argument's tree (its `==` with the target, its `Is` and `Unwrap` methods: Perennial's `errors.Is.spec` takes
  `errorWalkTree S I U target`), and a triple of `Is(e, _)` gives none of them. True of Go, unprovable from its
  premises: hypotheses that could never be discharged. Second gap: with no `%w`, `errIsNot`'s `err ≠ t` needs the
  result `*errorString` to differ from `t` (also an `*errorString`), and Perennial's `fmt.errorfErr` gives only
  `l.[errorString, "s"] ↦□ s` (persistent: no freshness against `t`'s pointer).
- **Evidence.** Go 1.27.3 `errors/wrap.go` (`Is`, `is`); Perennial `Spec/errors/Is.lean`, `Proof/fmt/Args.lean`
  (`errorfErr`); session 8's analysis (`notes/wal-units/tester.md`).
- **Proposed change.** State both over error trees, as `errors.Is.spec` takes them: `errTreeNot e t` (`e ≠ t`, and an
  `errorIsTree S M t` containing `e` in which no error is `t` and no `Is` method answers `true`, `TreeTyped S t`) and
  `errTreeTerm e` (for every pointer target `u`, an `errorIsTree S M u` containing `e`, `TreeTyped S u`), in
  `Spec/errors/ErrTree.lean`; `errIsNot`/`errIsTerm` follow from them (`errIsNot_of_tree`, `errIsTerm_of_tree`).
  Narrow both specs to what the WAL calls: a format with at most one `%w` argument (`ErrorfErrsTerm`), exactly one
  (`ErrorfErrsNot`, all five call sites), so that the result is a fresh `*fmt.wrapError` (or, for `Term`, a leaf
  `*errorString`); `ErrorfErrsNot` takes a target that is not a `*fmt.wrapError` (`io.EOF`, an `*errorString`), so
  `err ≠ t` follows from the types, without freshness. A `*fmt.wrapErrors` (two `%w`s) is left out: Perennial's
  `errorfErr` says nothing of its `errs` field, so its `Unwrap` cannot be stepped.
- **Decision.** Made (the user's approval of item (3), 2026-11-22).

## 2026-11-22: `time.Time.Format.specBroken` -- precondition `True` admits a writable `Location` (wal-safe, independent review)
- **Spec.** `Spec/time/Time__FormatBroken.lean` (the trust-boundary axiom `time.Time.Format.wp_proofBroken`), called by
  `wal.WAL.cleanupWAL.wp_proof` on `time.Now()`'s `Time`.
- **Defect.** Precondition `True` for every `t`. `Format` reads `*t.loc`; in Go a write to that `Location` racing with
  `Format` tears it and `Format` panics (`index out of range` in `Location.lookup`, `zoneinfo.go:200`). The axiom was
  sound only because no model program can yet get a `Time` whose `Location` it can write (`Local` read-only by `time`'s
  initializer, no specs of `In`/`Date`/`FixedZone`/`LoadLocation`): a fact outside the statement, which a future spec
  could break.
- **Evidence.** The independent review's `TestRacyLocation` and `TestRacyLocal` (go1.27.3, rerun 2026-11-22: both
  panic in `time.(*Location).lookup`), `notes/axiom-review/time-format-broken/review_*.txt`.
- **Proposed change.** `∀ t l, {{ globalAddr time.Local ↦□ l ∗ ⌜t.loc' = Loc.null ∨ t.loc' = l⌝ }}` (the location is
  `UTC`'s or the read-only `Local`'s, whose `Location`s `time`'s initializer leaves no one the points-to of); the post
  unchanged. `cleanupWAL` discharges it with the new `time.Now.specLoc` (`Spec/time/NowLoc.lean`, proved over
  Perennial's translation of `Now`: the result's `loc'` is `Local`'s value).
- **Decision.** Made (the independent review's recommendation, relayed by the coordinator, 2026-11-22).
## 2026-11-21: `resolver.EtcdManualResolver.Close` had no premise (prove-grpc3)

- **Spec.** `resolver.EtcdManualResolver.Close.spec` (an axiom until this change), `resolver.New.spec`.
- **Defect.** Premise `isPkgInit` only, for any `r : Loc`: `Close` is promoted from the embedded `*manual.Resolver`
  (grpc v1.84.0 `resolver/manual/manual.go:103-105`, `r.CloseCallback()`), so a nil `r` (or one whose `Resolver` is
  nil) panics on the field's load, and the axiom proved the call returns. False as stated; the package is
  `internal`, so only etcd's client calls it, always on `New`'s result.
- **Evidence.** Code reading (`client/v3/internal/resolver/resolver.go:31-41`, `manual.go:32-41,103-105`); the proof
  over the translated code needs the field and the callback; `notes/axiom-review/grpc3-resolver-close.md`.
- **Proposed change.** `Close` takes `etcdResolverCloser r` (half of `r.Resolver`, the manual resolver's
  `CloseCallback` and that it returns), which `New`'s post now also gives (a strengthening); `newClient` keeps it
  for the failed dial's `Close`. Converges to the spec plan's resolver predicates when they have a closing right.
- **Decision.** Applied (prove-grpc3, 2026-11-21), with `New`, `SetEndpoints` and `Close` proved over the translated
  code and `etcdResolverOwn` defined (no longer an axiom).

## 2026-11-21: `lease.NewLessor`'s write-back tokens and thread bound (prove-ps2-newlessor3)

- **Spec.** `lease.NewLessor.spec` (`Spec/go_etcd_io/etcd/server/v3/lease/NewLessor.lean`; a trust-boundary axiom).
- **Defect.** Not provable over the real code: its pre gave one write-back token (`backend.wbTok d.γB`), while the
  proved `lessor.initAndRecover.spec` takes two (`tx.Unlock()` after `UnsafeCreateLeaseBucket`, `lessor.go:814`, and
  `b.ForceCommit()`, `:834`, whose proved `backend.ForceCommit.spec` charges one); and the forked `runLoop`'s
  `findExpiredLeases` calls `l.expired()` → `Remaining()`, which read-locks the lease's `expiryMu` with a slot of the
  lease's pool, which exists only under `threadBound GF ≤ 2^30 - 1` (`isLeaseObj`), a bound the pre did not give.
- **Evidence.** `lessor.go:208-249, 640-750, 808-835`; `Spec/.../lease/lessor__initAndRecover.lean`;
  `isLeaseObj` (`InvLessor.lean`); `/shared/tmp/ps2/newlessor/plan.md` (items 2 and 4).
- **Proposed change.** The pre takes `ownToks d.γB.wb 2` (as `lessor.Recover.spec`) and `⌜threadBound GF ≤ 2^30 - 1⌝`
  (as `Renew`, `Promote`, `Leases`). Rejected alternative for the tokens: a `ForceCommit.spec` that charges none (#16's
  commit path).
- **Decision.** Approved by the user (2026-11-21), applied: `NewServer`/`NewServerR` mint the second token from the
  write budget's supply (`wbSupply_of_stock`, a receipt at `ReqTimeout()`'s resolution: no change to the boot's
  `bootLeft` or to any top-level premise) and discharge the bound from theirs (`2^28`); mvccrand's `runChecks` and
  mvccfull's `inc_open_backend` give one more token from their fresh backend's (proof-internal).

## 2026-11-21: a streamed request body's `Read` count and errors; `ReadFull` of it with `io`'s initialization (prove-http3)

- **Spec.** `http.bodyStreamRead_spec` (axiom `bodyStreamRead_ok`), `http.ReadFull_stream_spec` (axiom until now),
  `http.bodyStream` (opaque until now); `rafthttp.bodyStream_readFullAt`.
- **Defect.** `bodyStreamRead_spec` said `ys.length = sint.nat n`, which a `Read` returning `-1` met; `io.ReadFull`
  (`ReadAtLeast`'s `buf[n:]`) of such a reader panics, so the axiom `ReadFull_stream_ok` implicitly assumed `0 ≤ n`
  (the same flaw prove-http found in `prefixReaderOk`, `notes/axiom-review/http-readall-negread.md`). `ReadFull_stream_spec`
  had no `isPkgInit pkg_id.io`, which `io.ReadFull` needs (`io.EOF`, `io.ErrUnexpectedEOF`).
- **Evidence.** Perennial's `io.ReadFull.spec` (`Perennial/Spec/io/ReadFull.lean`), proved over the translated code.
- **Proposed change.** `bodyStreamRead_spec`'s post: `sint.Z n = ys.length`, and the error `errStrOk` and
  `io.ptrTyped` (what `ReadFull_stream_ok` claimed of the errors it passed on); `bodyStream` defined as its raw fact
  with `⌜Pre r ∧ rd ≠ nil⌝` (Go's server request bodies are never nil); `ReadFull_stream_spec` takes `isPkgInit io`,
  and `bodyStream_readFullAt` takes it (the snapshot handler has it).
- **Decision.** Applied (prove-http3, 2026-11-21): `ReadFull_stream_ok` is a theorem over Perennial's `io.ReadFull`.

## 2026-11-21: the etcd3 store's latency tracker: `Record` of any tracker and error, `NewEtcdMetricsTracker` of any labels (prove-metrics)

- **Spec.** `metrics.OperationLatencyTracker.Record.spec` and `metrics.NewEtcdMetricsTracker.spec`
  (`Spec/k8s_io/apiserver/pkg/storage/etcd3/metrics/`; trust-boundary axioms in `k8s_robust`'s base).
- **Defect.** Both false of Go. `Record` took any non-nil `t` and any `err`: a zero
  `OperationLatencyTracker` panics (`t.latency.Observe` on a nil interface), and for every tracker a
  typed-nil `*status.Error` panics in `errorReason` (`status.FromError` calls its `GRPCStatus`), whether
  the metrics are registered or not (`RecordEtcdRequest`'s defect of premise fixes 3).
  `NewEtcdMetricsTracker` took any group-resource: once `metrics.Register()` has run (the apiserver runs
  it), `NewOperationLatencyTracker`'s `WithLabelValues` panics on a label that is not valid UTF-8 (the
  recorders' R1, `nonissues/k8s-apiserver-metrics-negative-or-non-utf8-panic.md`).
- **Evidence.** apiserver `9c4ec15b8038` `metrics.go:360-398`; `examples/premisefix/latencytracker`
  (both panics, and the valid inputs' returns, registered and not).
- **Proposed change.** `NewEtcdMetricsTracker` takes `utf8Valid` of the group and the resource and posts
  `latencyTrackerOk lt` (opaque, `Proof/.../etcd3/metrics/Tracker.lean`: built by it) in place of
  `lt ≠ null`; `Record` takes `latencyTrackerOk t` and `statusErrOk err`. `isStore` keeps
  `latencyTrackerOk c.lt`; `New` passes its `utf8Valid` premises, `store.Get` `Client.Get`'s error
  (`statusErrOk_split`).
- **Decision.** Applied (prove-metrics, 2026-11-21): both stay trust-boundary axioms (`Record` observes
  a float latency, `sinceInSeconds`; both are names-only over component-base's metrics).
## 2026-11-21: `labels.Everything` needs `labels`' initialization (#25)

- **Spec.** `Spec/k8s_io/apimachinery/pkg/labels/Everything.lean`, `labels.Everything.spec` (the trust-boundary
  axiom `labels.Everything.wp_proof` until now).
- **Defect.** The pre is `True`, but `Everything` returns the package variable `sharedEverythingSelector`
  (`selector.go:93-98`), and its post's `MatchesNothing` triple reads `sharedNothingSelector`: no proof over the
  code can load them without `labels`' initialization, whose fact said nothing of them.
- **Evidence.** `Everything.impl` (`Code/k8s_io/apimachinery/pkg/labels.lean`, translated since #25): a `GoLoad` of
  `GlobalVarAddr sharedEverythingSelector`.
- **Proposed change.** The pre takes `isPkgInit pkg_id.k8s_io.apimachinery.pkg.labels`; `labels`' fact becomes
  `labelsInit` (`storage/etcd3/Base.lean`: both shared selectors read-only, the everything selector an empty
  `internalSelector`), established by its generated `Init.lean`. The post is unchanged. Callers
  (`daemonSetLister.GetPodDaemonSets`/`GetHistoryDaemonSets`, `storage`'s initializer) hold `labels`' `isPkgInit`
  through their own package's.
- **Decision.** Applied (#25, 2026-11-21): an initialization premise every caller holds; no client-visible change.
## 2026-11-21: `lessorApplyOk` at a backend that has `Lease`; one put per batch lock (prove-ps2-newlessor5)

- **Spec.** `lessorApplyOk` (`Proof/.../etcdserver/SnapRO.lean`, `lease.NewLessor.spec`'s post) and
  `lessorApplyOk_at` (`LessorApplyLaws.lean`); `lease.leaseBatchTx` (`Proof/.../lease/LessorBackend.lean`).
- **Defect.** Not provable of the real backend: `lessorApplyOk` quantified over every backend `d`, but the real
  backend's `UnsafePut` needs the bucket in its table (`batchTxBuffered.UnsafePut.spec`'s `P.has bi`; Go: a missing
  bucket is a `Fatal`), which nothing in its premises gives (`isBackend` pins only the batch limit of `d.P`); and
  `leaseBatchTx` allowed any number of puts under one lock at no cost, while each real `UnsafePut` counts a pending
  operation (`pend + 1 < 2 ^ 58`, `Unlock`'s `pend + hookMax < 2 ^ 58`).
- **Evidence.** `Spec/.../storage/backend/batchTxBuffered__UnsafePut.lean`, `batchTxBuffered__Unlock.lean`;
  `/shared/tmp/ps2/newlessor/plan.md` ("Fifth session", Q1).
- **Proposed change.** `lessorApplyOk` takes `⌜mvcc.leaseParams d.P⌝` (the bucket in the table, tracked, none of its
  keys a hook's); `leaseBatchTx`'s lock token is indexed by whether the session's one put is done (`Lk false` from
  `LockInsideApply`, `UnsafePut` from `Lk false` to `Lk true`, `Unlock` from either): all the lessor does
  (`persistTo`'s one `MustUnsafePutLease`). Alternative (a receipt per put, as auth's) rejected: more churn
  (`persistTo`, `Grant`, `Checkpoint` would take receipts).
- **Decision.** Main session's decision under the user's rule (everything still proves), applied: every use already
  has the fact (`snap_isApplyLessor`'s `hlp`, mvccrand's `rcP_lease`, mvccfull's `bkKeep` at `rcP`); the contract is
  proved of the real backend (`lessorApplyOk_real`, `LessorApplyReal.lean`).

## 2026-11-21: the token-free `Lookup` clause deleted (prove-ps2-newlessor5)

- **Spec.** `lease.NewLessor.spec`'s post (its last clause), `lessorLookupOk` (`SnapRO.lean`, in `srvSnapRO` and
  `EtcdServer.applySnapshot.spec`), `apply.isApplyLessor`'s last clause (`apply/Contracts.lean`), the last premise of
  `apply.isApplyLessor_of_lessorInv`.
- **Defect.** `{{ True }} lp.Lookup(id) {{ … }}` takes no reader slot and no token: `lessor.Lookup` read-locks `le.mu`,
  which the model's `RWMutex` bounds by reader slots, so no proof over the real code gives it (true of Go only because no
  process has `2 ^ 30` concurrent readers). Its `apply.leaseIs`'s `Keys()` likewise read-locks the lease's `mu`.
- **Evidence.** `lessor.go` `Lookup`; `lessor.Lookup.spec` (takes `lessorRd`); every destructuring of
  `isApplyLessor` dropped the clause (`-`): no proof used it; `/shared/tmp/ps2/newlessor/plan.md` ("Fifth session", Q2).
- **Proposed change.** Delete the clause (alternative: give it a reader slot `lessorRdOf γl` in and out).
- **Decision.** Main session's decision, applied: deleted from `NewLessor`'s post, `isApplyLessor`,
  `isApplyLessor_of_lessorInv`, `srvSnapRO`, `applySnapshot`'s spec; `lessorLookupOk` and `UberOn.lookupOk_of_guard`
  deleted. The exported `lessor_apply_contract` (`etcdserver/Results.lean`) keeps its statement text: its last premise
  (the triple) is kept, now unused, and its conclusion loses exactly the conjunct that premise restates. `apply.leaseIs`
  stays (that premise names it).

## 2026-11-21: `lease.NewLessor` proved; `Lease.expired` the expiry payload's trust boundary (prove-ps2-newlessor5)

- **Spec.** `lease.NewLessor.spec` (statement unchanged, now a theorem over `lease.newLessor.spec`, new);
  `lease.Lease.expired.spec` (now an axiom, `Proof/.../lease/Lease__expired.lean`); `lease.lessor.runLoop.spec`
  (post `True` to `levelTok leaseLvl`: the forked goroutine ends with its thread token).
- **Defect.** None in the statements; the constructor's axiom covered code that is now proved, except the
  expiry loop's payload `¬ leasesNoExpiry` (an opaque premise about the real clock; the model's `time.Now` is
  arbitrary).
- **Evidence.** `newLessor.lean`, `NewLessorAlloc.lean`, `NewLessorGhost.lean`, `etcdserver/LessorApplyReal.lean`;
  `notes/axiom-review/lease-expired-payload.md`.
- **Proposed change.** Replace `NewLessor`'s axiom by the narrower `Lease.expired` one (the user's choice (a),
  prove-ps2-newlessor).
- **Decision.** Approved (the user's (a); net 0 axioms), applied.

## 2026-11-22: `slices.Concat`'s axiom takes the total length `< 2 ^ 63` (claim #26, fix-slices-concat)

- **Spec.** `slices.Concat.spec` (`Spec/slices/Concat.lean`, the axiom `Proof/slices/Concat.lean`), and through its
  one caller the decision vocabulary of `k8s.io/apiserver/pkg/authorization` (`Proof/.../authorizer/Defs.lean`):
  `collectReasonsAndErrors.spec`, `ConditionsAwareDecisionUnion.Add/ToDecision.spec`,
  `PartiallyEvaluateConditionsAwareDecision.spec`, `ConditionsAwareDecisionConditionsMap.spec`,
  `partiallyEvaluateConditionsMapInternal.spec`, `AuthorizerFunc.ConditionsAwareAuthorize.spec`, `caaOk`,
  `ownBuilder`, `Dec.WF`, and the driver's `arbDecision.spec`, `arbAuthorizer.ConditionsAwareAuthorize.spec`.
- **Defect.** The axiom had no premise ("the address space bounds strings' total length"). Go's `Concat` sums
  `len(s)` and panics with "len out of range" once the sum is negative (go1.27.3 `slices/slices.go:491-498`), before
  `Grow`; aliased arguments reach it without the memory (`examples/premisefix/concatlen`: `TestBoundary`, 2^63-1
  returns and 2^63 panics; `TestStringsOverflow`; `TestStrings32` under `GOARCH=386`). In the model a slice of
  length `2 ^ 63 - 1` passed as `collectReasonsAndErrors`'s prefix made the axiom prove a slice of length `2 ^ 63`.
- **Evidence.** The Go source; Perennial PR #670 proves `slices.Concat.spec` over the translated code with the premise
  `(xss.map List.length).sum < 2 ^ 63` (its post adds that an empty result is `nil`).
- **Proposed change.** The premise, as PR #670 states it (our statement is its string instance, so the axiom becomes
  a theorem after the pin bump). The caller extends a path of names by one per union level, so it takes
  `pre.length + m.depth < 2 ^ 63` (`Dec.depth`, new); `Dec.WF`'s union case adds `Dec.depthL ks + 1 < 2 ^ 63`; the
  builder keeps its children below `2 ^ 63 - 1` (`ownBuilder`, `Add`'s premise), which `caaOk` gives
  (`isWFDecisionLe (2 ^ 63 - 2)`, new predicate); producers report depths (`ToDecision`: at most its union's;
  `PartiallyEvaluate...`: at most its input's; the leaf constructors and `AuthorizerFunc`: `0`); the driver's
  `arbDecision(depth)` takes `uint.nat depth < 2 ^ 63`, `arbAuthorizer.ConditionsAwareAuthorize` `z.depth < 2 ^ 63 - 1`
  (its closed program uses 2). A fixed bound in the invariant alone cannot work: a union of invariant decisions is
  one level deeper, so the authorizers' decisions (`caaOk`) carry the tighter one.
- **Decision.** Applied (fix-slices-concat/2026-11-22). `k8s_authz_robust`'s statement unchanged; no axiom added or
  removed.
## 2026-11-22: kvnet's answers' length bound weakened to what the reply frame needs (KvNet)

- **Spec.** `Replica.read.spec`, `Replica.propose.spec`, `Node.handle.spec` (KvNet, Lean-first; no SpecPlan
  counterpart): post `len(v) < 2^61` to `(len(v) : Int) + 9 < 2^63`. `Replica.install.spec`: new premises
  `MapFits K'`, `MapFits A'`.
- **Defect.** The `2^61` bound was not derivable (the store's `waitP`/`readAns` say nothing of lengths): the
  proofs took it as two seams (`ansLen.law`, `waitLen.law`). The only consumer (`serveClient`, its `writeFrame`)
  needs `len(v) + 9 < 2^63`.
- **Evidence.** `notes/kvnet-part.md`, "The answers' lengths"; `Node__serveClient.lean` unchanged.
- **Proposed change.** Weaken the posts; carry the bound in the replica's maps (`MapFits`, `Defs.lean`) and
  waiters; drop the seams.
- **Decision.** Applied (the coordinator's item 1: weaken locally before strengthening the store).

## 2026-11-22: `durable.Write`'s sync update may use the crash token (WalTester, copied into KvNet)

- **Spec.** `github_com.mit_pdos.etcd_grove.examples.lib.durable.Write.spec` (WalTester, Lean-first; no SpecPlan
  counterpart): the second update `durWriteSync γ Ψ` is now `notCrashed -∗ AU <{∃∃ s, durSt γ s}> <{ durSt γ
  ⟨s.cur, none⟩, COMM notCrashed ∗ Ψ }>`. This is weaker as the client's obligation: a plain update is one
  (`durWriteSync_of_au`).
- **Defect.** A client could not fire raft's *enter* (`readyEnter`, which takes `notCrashed`) at the sync, where
  decision C (`notes/kvnet-proof-plan.md`) places it. Yet the proof holds the token there (`durInv_commit`).
- **Evidence.** `notes/kvnet-part.md`, "`persist`" item 1; `WriteInv.lean`'s `durInv_commit`.
- **Proposed change.** As above. `durInv_commit` passes the token; the tester's `storeOracle` gives a plain update.
- **Decision.** Applied (needed for kvnet's `persist`, item 2 of the coordinator's 2026-11-22 decisions).

## 2026-11-22: raft's node API -- a crash could only discard a batch cut and not entered; `statusOwn` gave no read access

- **Spec.** `Proof/go_etcd_io/raft/v3/InvNode.lean`: `readyEnter` (in `node.Ready`'s post through `readyGot`),
  `nodeCrash`, `statusOwn` (`node.Status.spec`'s post). No SpecPlan counterpart: the plan has no crash law, and
  `node.Status` has no plan spec.
- **Defect.** (1) Too weak for a durable client whose write has two durability points (`durable.Write`: rename,
  then directory sync). After a crash between them the new file may survive. Then the restarted node's storage
  holds the batch's state, while raft's durable state (`raftState`) is the old one, because `nodeCrash` discards
  the batch. `RestartNode` cannot get `StorageHolds S σ`. (2) `statusOwn` gave heap ownership but no law to read
  it, so kvnet's `Node.status` could not call `GetTerm`/`GetCommit` on `st.HardState`.
- **Evidence.** kvnet's `persist`, `notes/kvnet-part.md` (branch `worktree-agent-a9b8a3f3fbe5852a9`),
  "persist" item 3 and "`Node.status` (open)".
- **Proposed change.** (1) `readyEnter := readyEnterLive ∧ readyEnterCrash`. The live half is the old wand.
  The crash half gives the law `readyCrashEnter`: `crashed -∗ nodeCrashTok γ id x -∗ nodeArm n γ x -∗
  nodeRunning n γ N q -∗ readyEnter … -∗ raftState γ id st.durable ={E}=∗ raftState γ id st'.durable ∗
  nodeVacant γ id`. This is kvnet's requested statement with `nodeRunning` and `nodeArm` added and `isCluster`
  dropped. Without the two additions the law is false: after a `node.Stop` the batch is of a dead generation
  (`notes/raft-crash-law-design.md` (k)). Live clients take the conjunction's left half. (2)
  `statusOwn_hardState : statusOwn st ⊢ statusOwn st ∗ ∃ hs, hsOpt st.BasicStatus'.HardState' hs`, read access
  only.
- **Decision.** Applied (branch `raft-crash-enter`; the coordinator's 2026-11-22 decision for (1), "raft adds a
  variant of `nodeCrash`"). kvnet must adapt its `readyCrashEnter.law` hypothesis to the two added premises.
## 2026-11-22: `durable.Write`/`tryWrite` and `os.File.ReadAt`: no 1 GiB bound (WalTester, main tree's `os`)

- **Spec.** New `os.File.ReadAt.specLong` (`Spec/os/File__ReadAt.lean`): `spec` without `len(b) <= 2^30`, proved
  (`wp_proof_long`; `wp_proof` is its instance, statement unchanged). WalTester's `durable.Write.spec` and
  `tryWrite.spec`: `len(data) <= 2^30` to `len(data) < 2^63`; `DCand.Ok` and `durFound` likewise.
- **Defect.** The bound came from using one `WriteAt`/`ReadAt` of at most `maxRW`. The model (and Go) loop in
  chunks, and kvnet's image has no size bound.
- **Evidence.** `notes/kvnet-part.md`, "`persist`" item 2. `tryWrite` now uses `WriteAt.specLong` (new lemmas
  `TrOk.pwA` and `pw_wholeA`), and `tryRead` uses `ReadAt.specLong`.
- **Proposed change.** As above. The tester's `storeOracle` keeps its own 1 GiB invariant (`tOrSmall`), which
  implies the new premise.
- **Decision.** Applied (the coordinator's item 2, 2026-11-22).

## 2026-11-22: kvnet's `writeFrame` refuses an oversized body; the answers' length bounds dropped (KvNet)

- **Spec.** `writeFrame.spec`: no premise on the body's length; new post conjunct `2^26 < len(xs) → w = []`.
  `Replica.read.spec`, `Replica.propose.spec`: the post's `len(v) + 9 < 2^63` dropped. `Node.handle.spec`: post
  `⌜good = true⌝` (was `∧ len(v) + 9 < 2^63`). `PutStatus.spec`: takes `s.Contents ↦${dq} M ∗ csOpt s.Conf □ c`
  and gives the map back; no length promise (was nothing taken, `< 2^61` promised: unprovable).
  `Node.status.spec`: post the fresh map and `csOpt` (was `True`), what `PutStatus` takes.
- **Defect.** `serveClient` needed `len(v) + 9 < 2^63` for `writeFrame`'s `make([]byte, 0, 8+len(body))`, and no
  invariant bounds a status encoding: `PutStatus` could not promise a bound.
- **Evidence.** Go change `ab79c782b8` (option (a)): `writeFrame` returns `false` and writes nothing past
  `maxFrame`, which `readFrame` refuses anyway; `notes/kvnet-part.md`, "`Replica.contents`, `PutStatus`,
  `Node.status`".
- **Proposed change.** As above. `serveClient` takes `len(v) < 2^63` (for `kvQ`) from the answer's slice.
  `MapFits` stays for now (the waiters' handoffs still carry it); it is removable.
- **Decision.** Applied (the coordinator's option (a), 2026-11-22). Unchecked: no `.lake` at the time.

## 2026-11-22: `EtcdServer.adjustTicks` proved with the tick advance off (prove-ps2-srv)

- **Spec.** `EtcdServer.adjustTicks.spec` (`Spec/.../etcdserver/EtcdServer__adjustTicks.lean`): two new premises,
  `srvMonitorsOff s` and `isRaftNode Er γn (srvRAddr s)` (for any `Er`, `γn`). `srvMonitorsOff` (`InvMonitors.lean`)
  gets one more conjunct, `Cfg.InitialElectionTickAdvance ↦□ false`, and `srvMonitorCfg` the field at the
  configuration's value (`NewServer`, `NewServerR` give it from the copied `Cfg`).
- **Defect.** The axiom held for any configuration; a proof over the real code with
  `InitialElectionTickAdvance` true needs the multi-member branch's wait loop, whose `transport.ActivePeers()` is
  not in `rafthttp.isTransporter` (rafthttp's `ActivePeers` read-locks `t.mu` with no reader token, the reason
  `Transport.ActiveSince` is itself an axiom: a narrower axiom on it would be 1-for-1). `advanceTicks` needs the
  raft wrapper's contract, which the premise did not give.
- **Evidence.** `server.go:468-530` (fork `goose-lean`): a single member fast-forwards (`advanceTicks(ElectionTicks
  - 1)`, proved); with several members and the advance off, `lg.Info` and return. No example sets
  `InitialElectionTickAdvance` (grep of `examples/`: the zero value, false); `Start`'s callers discharge it as they
  discharge the other monitors-off fields (`iExactEq …; rfl` on the literal). `Start` has `isRaftNode` in its
  construction premise (`isServerBuiltC_rn`, `AuthCompRows.lean`).
- **Proposed change.** As above; `Start.spec` unchanged in statement (its `srvMonitorsOff` premise widened).
- **Decision.** Applied (the user's standing rule: a trust-boundary spec may change when every caller still proves,
  memory `ownership-premise-ok`; same pattern as audit B4a's monitors-off premises).
## 2026-11-22: `credentials.NewPerRPCCredentialBundle` takes its package's initialization; `credTokInv` over the lock (prove-ps2-client)

- **Spec.** `credentials.NewPerRPCCredentialBundle.spec`: pre `True` to `isPkgInit
  pkg_id.go_etcd_io.etcd.client.v3.credentials`. `credTokInv rc P` (the definition `tokenBundleInv`,
  `UpdateAuthToken.spec` and `GetRequestMetadata.spec` are written in): a bare invariant over `rc.authToken` to
  `rc.authTokenMu`'s `isRWMutexGuard` over `credTokR rc P` (the field at a fraction, `""` or a `□ P` token), the
  lock's reader tokens in a thread pool, and `isPkgInit pkg_id.sync`; the bound `threadBound GF ≤ 2^30` kept.
- **Defect.** None in the old statements: `UpdateAuthToken` was a trust-boundary axiom because its lock had no
  ghost state; a writer needs only the persistent guard (`RWMutex.wp_Lock_guard`), and `Lock` needs `sync`'s
  initialization, which nothing on `UpdateAuthToken`'s path had.
- **Evidence.** `UpdateAuthToken.wp_proof` is now a theorem over its body. `GetRequestMetadata`'s axiom is as true
  of the new `credTokInv` (its reads are under `RLock`; every write is `UpdateAuthToken`'s, under `Lock`).
- **Proposed change.** As above. The one caller, `newClient`, has `client/v3`'s initialization, which gives the
  credentials package's.
- **Decision.** Applied (a premise every caller discharges; the user's rule of 2026-11-21).

## 2026-11-22: `remote.opMaybe`'s read form needs node 0 to know which firing answers (etcd-dist D8)

- **Spec.** `Net/Proof/.../lib/remote/Defs.lean`, `opMaybe R tok op`: the far side gets the one-shot
  update `lin R i Φ`; the proposed read form (the coordinator, the user's approval, 2026-11-22) gives it,
  for a read (`R.B.isWrite i = false`), a persistent read update instead, which it may fire zero or more
  times, returning `ov o` with `Φ o` of one firing.
- **Defect.** As proposed, node 0 cannot provide the read form. Node 0's `Φ o` must give lintest's
  continuation at `(i, ok o)`, which needs lintest's update committed at the firing whose output is `o`;
  lintest's update is one-shot, so only one firing may commit, and which one is decided by the output the
  far side *will* return (etcd may serve one read's update several times at different states, e.g. a
  read retried at another member, `read_ok_au`, and answer from any of them). Committing at the first
  firing leaves a later firing (whose output may differ) unable to produce its `Φ`; committing at the
  return is not a linearization point (other clients commit in between). "A read leaves the state
  unchanged" makes every firing a valid point, but the proof still has to pick the one whose output is
  returned. txnlin's `Apply` picks it with its revision prophecy (`callInv`), which `remote`'s design
  (`notes/remote-port-plan.md` §3/§7: node 0's `Do` makes the prophecy, the client's `op` is txnlin's call
  without its own) removes from the client machine. Also: `lin` (one-shot) cannot yield
  a persistent update, so "`lin` for a read yields the read form" holds only in the other direction (a
  read-form operation fired once meets the one-shot form).
- **Evidence.** The argument above; no proof attempted. Separately, txnlin's `Call.spec` cannot be stated
  against `remote`'s `opMaybe` yet: its import closure reaches the main tree's `Code.net` (through
  `cache/v3` and grpc's `peer`), which clashes with `Net/`'s `net` (D2).
- **Proposed change.** (A, recommended) node 0 prophesies the answered output: `remote.Do` resolves a
  second prophecy with the answering reply's bytes (a `ResolveU64` per byte, prophecy-only Go code); the
  answering attempt's slot for a read holds an invariant with lintest's update that commits at the first
  firing whose output's encoding is the prophesied one, and `Φ o := (encOut (ov o) = prophesied → lintest
  committed at o)`; with `codecOk` (decode of encode is the identity) the returned output's `Φ` is the
  commit. The slot body, `serveConn`, `attempt`, `Do`, `Pend` change; the counter's server (one firing) and
  client (a `Do`) meet the read form directly; `counter_remote_robust`'s statement is unchanged.
  (B) keep the one-shot form and give `Call` a prophecy at the client machine (against `remote-port-plan.md` §3/§7's design).
  (C) an etcd-specific revision prophecy at node 0 (not generic).
- **Decision.** 2026-11-22, kaashoek via etcd-grove-03: option A (the user's decision): `remote.Do` prophesies
  the answered reply's bytes; a read commits lintest's update at the first firing whose output encodes to them.
  Applied on `etcd-dist` (`Defs.slotUpd`, `Do.spec`'s choice over the bytes, `pend_choice`'s read commit
  invariant; `Run.spec`/`Check.spec` gain the premise that distinct outputs have distinct bytes).
## 2026-11-22: kvnet's `StartNode`: the start resource indexed by the configuration; the file invariant from the generation's boot (KvNet)

- **Spec.** `StartNode.spec`/`Run.spec`/`RunNode.spec` (KvNet): the start resource `S : IProp` becomes
  `S : w64 → GoString → Options → GMap w64 GoString → IProp` (id, directory, options, address map); `StartNode`
  takes `cfg.Addrs ↦$□ M ∗ S cfg.ID cfg.Dir cfg.Opts M`; `RunNode` gives `S id dir opts M` at every `M` with
  `addrMapOk (splitAddrs addrs) M`. `newReplica.spec`: the file's names are one record `fl : KdFileNames`
  (`durable`'s, the file, its roots, the writer's variable, the invariant's crash token, raft's arm), the file
  invariant `kdFileInvK γ id fl` (no node) and `nodeArm n γ fl.x` in its precondition. `Replica.persist`'s specs
  unchanged (the invariant's change is inside `isReplica`).
- **Defect.** A constant `S` cannot name what `StartNode` needs from the configuration: the directory and id
  (the file), the voters (`kdCluster γ vs`), every other address's protocol (`newTransport`). And the file
  invariant, allocated after `RestartNode` in the old design, cannot be emptied by the generation's crash
  obligation, which Perennial's crash adequacy takes at the generation's start (ledger 2026-11-22, raft's
  `RestartNode`).
- **Evidence.** `notes/kvnet-part.md`, "`StartNode` and the crash frame" and "The file invariant from the
  generation's boot". The pending batch's record names its node existentially (a `NodeH` is in `Type 1`, so it
  cannot be in the writer's ghost variable), recognized by the writer through a saved proposition; `persist`'s
  write lemma takes two later credits.
- **Proposed change.** As above.
- **Decision.** Applied (checked: `etc/lean-check.py` of every changed module, then `lake build KvNet`).

## 2026-11-22: kvnet's `ValidCluster` checks `MaxInflightMsgs < 2^62` (KvNet, Go and Lean)

- **Spec.** `ValidCluster.spec` (KvNet) through `validCluster` (`Addrs.lean`), and so `RunNode.spec`'s premise:
  `mif < 2^63` becomes `mif < 2^62`. The Go `ValidCluster` (`examples/raft/kvnet/addrs.go`) the same.
- **Defect.** Raft's `RestartNode` (and kvnet's `kvOptsOk`, `StartDefs.lean`) needs `MaxInflightMsgs < 2^62`;
  `ValidCluster` allowed up to `2^63`, so `RunNode`'s premise did not give what `StartNode` needs.
- **Evidence.** `notes/kvnet-part.md`, "The WIP checked and built", the gap noted with `kvOptsOk`.
- **Proposed change.** Tighten the Go check (the design: validity is a Lean premise, mirrored by Go panicking on
  an invalid configuration), retranslate, and the statement draft's `ClusterConfig.Ok` the same.
- **Decision.** Applied (the coordinator's decision, 2026-11-22).

## 2026-11-22: kvnet's transport takes no frame-length bound with a message; `newReplica` names its node (KvNet)

- **Spec.** `Transport.Send.spec`'s `sendElem F m` and the queue's `qElem F pid m` (`TransportDefs.lean`, so
  `Transport.enqueue.spec`, `isPeer`) lose the conjunct `(encMsg st).length + 8 < 2^63`. `newReplica.spec`'s
  post names the node it was given: `∃ st' sts' sq' ρ, isReplicaR γ vs dir id r n st' sts' sq' ρ` (was `∃ n' …`).
- **Defect.** The bound is not derivable where the messages come from (`run`'s send callback gets raft's
  `Ready` messages, with no size bound: `MaxSizePerMsg` is any `uint64`), so `StartNode` could not give
  `t.Send` as `run`'s callback. It is not needed either: `runPeer` encodes the message first (`putMsg`), and
  the encoding's slice gives `(encMsg st).length < 2^63` (`ownSlice_len`), all the protocol needs. And
  `StartNode`'s post (`isNodeS`) needs the replica's node to be the transport's: the old post forgot it.
- **Evidence.** `Transport__runPeer.lean` (the bound's two uses, `peer_send` and the frames' bound, now from
  the slice); `newReplica.lean`'s last step already named `n`.
- **Proposed change.** As above.
- **Decision.** Applied (weaker premises; a stronger post).

## 2026-11-22: kvnet's wire reads a message's entries of any type (`getMsgEntry`; `MsgWf` weakened) (KvNet, Go and Lean)

- **Spec.** `MsgWf` (`Wire.lean`, so `getMsg.spec`'s premise and `kvFacts`' `msgOkK`): a message's entries need
  only `MsgEntWf` (data of a Go slice's length), no longer `EntWf` (also a type `≤ 2`). New `getMsgEntry.spec`
  (wire.go's `getMsgEntry`, new): `getEntry.spec` with `MsgEntWf`.
- **Defect.** `StartNode` must give `run`'s send callback (raft's `Ready` messages, `sentMsg`) to the transport,
  whose protocol carries `MsgWf`. Nothing in raft's API says a sent message's entries are of raft's types (a
  forwarded `MsgProp`'s are whatever `Propose` was given; `readyRest_ents_type` covers only the `Ready`'s
  entries), so the type bound was not derivable. The Go decoder refused other types (`getEntry`'s `typ > 2`,
  right for the storage file, not needed on the wire: an `EntryType` is an `int32`, written sign-extended,
  truncated back).
- **Evidence.** `examples/raft/kvnet/wire_test.go` (entries of types `-5` and `2^30` round-trip); the proofs
  of `getMsgEntry` and `getMsg`.
- **Proposed change.** `getMsg` decodes entries with `getMsgEntry` (no type check); `MsgWf` as above.
  (Alternatively a raft API lemma `sentMsg ⊢ ∀ e ∈ st.ents, Type ≤ 2`, which needs raft's message invariant to
  track forwarded proposals' entries: not taken.)
- **Decision.** Applied.

## 2026-11-22: reader slots for the transport's persistent callers; `ActiveSince` proved, `adjustTicks` for both flags (rdslot)

- **Spec.**
  - `rafthttp.Transport.ActiveSince.spec`: its premise is `transportTok γn t c` (given back), where it was
    `trState γn t c`.
  - New `Transport.ActivePeers.spec`, `peer.activeSince.spec` and `peerStatus.activeSince.spec`.
  - `rafthttp.isTransporter tr Rd`: a new reader-resource parameter `Rd`. `ActiveSince` takes and returns `Rd`
    (it took `True`), and `ActivePeers` is new.
  - `isConnectedSince`, `numConnectedSince` and `isConnectedToQuorumSince` take `isTransporter tr Rd ∗ Rd` and
    return `Rd`. `srvPeersOk`'s conjunct becomes `∃ Rd, isTransporter tr Rd`.
  - `srvLeadTimeReader s` is redefined as `leadTimeMu`'s slot `∗ srvTrReader s`. The new
    `srvTrReader s := ∃ tr Rd, s.r.transport ↦□ tr ∗ isTransporter tr Rd ∗ Rd` is one transport reader slot.
    No spec text changes. Pool `I`'s items and the compactor's `srvCompactR` hold it, built by `NewServer`
    and `NewServerR` from the transport's reader tokens, which they used to drop.
  - `srvMonitorsOff` loses `InitialElectionTickAdvance ↦□ false`.
  - The new `srvMonitorRes s := srvLgReader s ∗ srvTrReader s ∗ ∃ b, InitialElectionTickAdvance ↦□ b`
    replaces `srvMonitorCfg`'s `srvLgReader s` and the switch's field. It also replaces `Start.spec`'s third
    `srvLgReader s` (monitorDowngrade's) and `memberBuilt`'s/`memberBuiltR`'s `srvLgReader s`.
  - `adjustTicks.spec` takes `srvGoAttachOk s γg`, `srvTrReader s` (given back) and the switch's field at any
    value, in place of `srvMonitorsOff s`.
- **Defect.**
  - `ActiveSince`'s axiom read-locked `t.mu` without a reader token. Its callers are on the request path
    (`parseProposeCtxErr`), any number at once, and the axiom's docstring rested on "physically at most
    `2^30 - 1`". The same blocked `ActivePeers`.
  - `adjustTicks` was therefore proved only under `InitialElectionTickAdvance = false` (ledger, the
    entry above). etcd's own default (`embed`) is true.
- **Evidence.**
  - The design: `/shared/tmp/ps2/rdslot/design.md`. It follows the bounds plan's rule 2: the server's pool
    `I` (level 2), which every gRPC run and revocation goroutine already borrows `leadTimeMu`'s slot from,
    now holds the transport's slot beside it. `parseProposeCtxErr` read-locks `leadTimeMu`, then, not
    nested, the transport.
  - `adjustTicks` and the compactor are one-off goroutines with counted slots (D2 (a)).
  - The count: `2^30 - 1` tokens hold 2 (Send key, `CutPeer`/`MendPeer`), `2^29` (the peer handler),
    `2^28 - 1` (`I`), 1 (the compactor) and 1 (`adjustTicks`).
  - No top-level statement changes. No new axiom, `threadBound` or `List.replicate` in a Spec file.
- **Proposed change.** As above.
- **Decision.** Applied. Every caller discharges the new resources: `Start.spec`'s `srvMonitorRes` (one more
  transport slot than the `lgMu` slot it replaces) comes from `NewServer`'s `srvMonitorCfg`, through the
  examples' `memberBuilt`. `Start.spec` no longer needs the switch to be false.
## 2026-11-22: `semver.Version.LessThan` takes its receivers' points-tos and returns `Compare(o) < 0`; the cluster's `Version()` returns a read-only version (prove-ps2-semver)

- **Spec.** `semver.Version.LessThan.spec` (`Spec/github_com/Masterminds/semver/v3/Version__LessThan.lean`): the
  premise `v ≠ null ∧ o ≠ null` becomes `v ↦{dv} x ∗ o ↦{dw} y` (any fractions, given back); the post, some
  boolean, becomes `decide (semver.lessThan x y)` (`CompareModel.lean`: semver v3.5.0's `Compare`, line for
  line). `apply.isCluster`'s `Version` law (`apply/Contracts.lean`, the names-only membership's trust
  boundary): the post `True` becomes `⌜v = null⌝ ∨ ∃ x, v ↦□ x`.
- **Defect.** The axiom was unprovable over the real code: `Compare` reads both structs, and a `≠ null` premise
  gives no points-to (a concurrent writer races). The ownership-premise rule (the user's, 2026-11-21) applies:
  `version.LessThan` passes its by-value copies (owned), `compareMajorMinorVersion` `New`'s results (`↦□`),
  `ClusterVersionSet` `MustParse`'s result (`↦□`) and the cluster's `Version()`, for which the contract now says
  what `cluster.go:580-587` does (nil, or `semver.MustParse(c.version.String())`: a fresh `NewVersion`
  allocation nothing else holds). That law is a premise of the top-level results (through `clusterApplyOk`,
  `bootOk`, `bootstrapContract`), so this is a stronger trusted premise, true of the Go code, in exchange for
  the retired axiom.
- **Evidence.** `Proof/github_com/Masterminds/semver/v3/{Version__LessThan,Version__Compare,comparePrerelease,
  comparePrePart,compareSegment,Version__Patch,Version__Prerelease}.lean`, over `strings.Split` and
  `strconv.ParseUint`; the callers' proofs (`version/LessThan`, `rafthttp/compareMajorMinorVersion`,
  `apply/applierV3backend__ClusterVersionSet`).
- **Proposed change.** As above. `SpecPlan`'s `Version.LessThan.spec` (`verAt`, `SemVer.ltb` with an opaque
  `preLtb`) is the same shape; its `preLtb` could now be defined as `CompareModel`'s `cmpPre … = -1`.
- **Decision.** Applied (the approved ownership-premise rule; the cluster contract's strengthening recorded
  here and in the report to #18).
## 2026-11-22: kvcheck's `randomChange` bounds its changes (KvNet)

- **Spec.** `checker.randomChange.spec`'s post (`kvcheck/checker__randomChange.lean`): `⌜ccTransOk o⌝` becomes
  `⌜ccTransOk o ∧ (ccToV2 o).changes.length ≤ 3⌝`.
- **Defect.** `reconfigure` sends `PutConfChange(nil, cc)` through `checker.request`, whose premise bounds the
  payload (`len + 17 < 2^63`, the frame's header); `encCC o` has at most `17 + 16 n` bytes (`encCC_length`),
  so the bound needs `n` bounded, and the post said nothing of it. The code makes at most three changes
  (`count` is `1` or `1 + below(3)`); the proof already tracked `cnt ≤ 3`.
- **Evidence.** `checker__randomChange.lean` (the loop's invariant), `ConfCodec.lean`.
- **Proposed change.** As above (a stronger post).
- **Decision.** Applied.

## 2026-11-22: prometheus's `NewGauge` returns a representation, not method triples (prove-ps2-metrics)

- **Spec.** `prometheus.NewGauge.spec`'s post: `metric.gaugeSpec g ∗ metric.gaugeSetSpec g` becomes
  `metric.isGauge g` (a `*gauge` whose `valBits` is in an invariant, `MetricRep.lean`). `GaugeVec.WithLabelValues.spec`'s
  post gains `metric.isGauge gi` (additive, before the slice's points-to: every caller's pattern ends in `-`).
  `mvccInit` gains `totalEventsCounter`'s `counterSpec` and `pendingEventsGauge`'s `isGauge` (in its last
  conjunct); `membershipInit` gains `isLearner`'s `gaugeSetSpec` and `knownPeers`' label names (two conjuncts
  at the end: `PromoteMember`'s and `ValidateConfigurationChange`'s patterns gain a `-`).
- **Defect.** None false: the posts claimed the methods' behaviour (trusted), and lacked what `Sub` (on
  `pendingEventsGauge`) and the vector gauge's `Set` (`knownPeers`) need, so `ReportEventReceived`,
  `setIsLearnerMetric` and `updateMembershipMetric` stayed axioms.
- **Evidence.** client_golang v1.24.1: `NewGauge` and `GaugeVec`'s `newMetric` return `&gauge{...}`,
  and `valBits` is only accessed through `sync/atomic`. The methods (`gauge.{Set,Add,Sub,Inc,Dec}`) are
  translated and proved over their bodies; `metric.gaugeSpec_of_isGauge`, `gaugeSetSpec_of_isGauge`
  (`MetricLaws.lean`) recover the old claims, applied by `etc/gen-init.py`'s `metric_steps`. (`NewCounter`
  unchanged: `counter`'s struct needs `timestamppb` translated, whose names-only initializer would add two
  trust-boundary axioms, more than `counter.Add`/`Inc`'s proofs would remove.)
- **Proposed change.** As above; agreed with kaashoek's prom-registry on #15 (2026-11-22).
- **Decision.** Applied. Trust: the constructors' axioms claim less (a representation instead of method
  triples); three etcd axioms retired, two added (`client_model/go`'s `opaqueInitsOk`/`initFuncsOk`: the
  package now imported for `gauge`'s `labelPairs`): net -1.
## 2026-11-22: bbolt's `(*Options).String` takes the package's `isPkgInit` (ps2 misc2)

- **Spec.** `Options.String.spec` (`Spec/go_etcd_io/bbolt/Options__String.lean`): the pre gains
  `isPkgInit pkg_id.go_etcd_io.bbolt`.
- **Defect.** The axiom is now proved over the real code, and its body calls `fmt.Sprintf`, whose
  spec takes `isPkgInit pkg_id.fmt`; the old pre (`optsAt` and `loggerPtrOk` only) had no package
  initialization to get it from.
- **Evidence.** `Proof/go_etcd_io/bbolt/Options__String.lean`. The only caller, `Open` (through
  `options_logArgOk`, `Open/LogFmt.lean`), holds the package's `isPkgInit` (its own pre's).
- **Proposed change.** As above (a premise every caller discharges). `SpecPlan`'s
  `Options.String.spec` should take it too (not edited here).
- **Decision.** Applied.
## 2026-11-22: kvcheck's `fresh`/`do`/`read` at the store; `read` gets a prophecy (KvNet, Go and Lean)

- **Spec.** kvcheck's checker (`kvcheck/Defs.lean`): `CheckerNames` (the ghost maps of issued numbers) and
  `issued` go; the lock's invariant `checkerInv c γ` holds, with the two counters `a`, `b`, a counter
  predicate `γ false a ∗ γ true b` (`γ : CheckerCnt GF := Bool → w64 → IProp GF`, the caller's: at the
  top, the store's op counter half and the read sequence numbers of every replica id, `kvCnt`).
  `checker.fresh.spec` takes a minting law `∀ a, ⌜uint.Z a + 1 < 2^64⌝ -∗ γ w a ={⊤}=∗ γ w (a + 1) ∗ L (a + 1)`
  and returns `L n` (no more `issued γ w n`). `checker.do.spec`/`checker.read.spec`: stated at the store
  (`kvFacts γ cf`, the checker's counters `kvCnt γ ls`, `rkvInv γ`), logically atomic as kvdurable's
  `Cluster.do`/`Read` (an `AU` over `rkvVal γ` in, `Φ` of the answer out), in place of the caller's minting
  laws and the answer's fact. The other kvcheck specs: `CheckerNames` becomes `CheckerCnt GF` (no other change).
  Raft: a new API module `ReadCtxLaws` (`readCtxAfter_agree`: a read context's log is unique).
- **Defect.** The old specs cannot be linked to the store (found writing `Check`): `do` fired its minting
  law outside the checker's lock on an `issued` token, but `kd_mint` mints at the store's op counter, in
  order (`ghostVar γ.r.opn ½ nop`, mints `nop + 1`); `do`'s post dropped the ticket `kd_collect` needs; and
  a linearizable read needs its answer prophesied (the linearization point is the first change after
  which the key has the answer: kvdurable's `Cluster.Read`), which kvcheck's `read` did not have. The
  replica's read answer names the context's committed log existentially (`ansReadK`), so the client needs
  the log it minted the context after to be that one: agreement on raft's `ctxs` map (`readCtxAfter`,
  sealed).
- **Evidence.** `notes/kvnet-part.md`, "kvcheck's decoders, `conf`, `reconfigure`; the plan for `Check`";
  kvdurable's `Cluster__do.lean`/`Cluster__Read.lean`.
- **Proposed change.** As above. Go: `checker.read` creates `primitive.NewProph()` and resolves it with the
  answer (`trusted_proph.ResolveBytes(p, v)`, gokv's, as kvdurable's `Cluster.Read`; no effect in Go),
  `examples/raft/kvnet/go.mod` requires gokv, project kvnet maps gokv to the main tree. Minting under the
  lock: `do`'s law is `kd_mint` (the counter is the op counter half); `read`'s mints, at every replica id
  at once, the context of the fresh number after the log of the read's start (`kd_mint_next`).
- **Decision.** Applied (the prophecy: the coordinator's decision, 2026-11-22).

## 2026-11-22: `storage.OpenBackend`'s axiom takes `New`'s receipt bound (step bounds, #30, step 2)

- **Spec.** `storage.OpenBackend.spec` (`Spec/go_etcd_io/etcd/server/v3/storage/OpenBackend.lean`), a
  trust-boundary axiom (`storage.OpenBackend.wp_proof`), and `OpenSnapshotBackend`'s, which takes it.
- **Defect.** The axiom gives `backend.New`'s post (`newPostK`) under `[ThreadBoundLe GF (2 ^ 29)]`
  alone, but `New` requires a receipt bound: `[ReceiptBoundLe GF (2 ^ 62)]` since S3e (2026-11-17;
  bbolt's core invariant keeps `receiptBound GF ≤ 2 ^ 62`, `Proof/go_etcd_io/bbolt/Inv/Bolt.lean:111`),
  `2 ^ 60` since step 2 (the buffers' receipt `bufRc` keeps `receiptBound GF ≤ 2 ^ 60` in the batch
  lock's ghost share). So the axiom is false at a larger receipt bound: from its post, lock the batch
  transaction and read `receiptBound ≤ 2 ^ 60` off the share (`batchGhostAt_bufRc`), refuting
  `receiptBound = 2 ^ 61`, and `WP (OpenBackend; Lock; panic) {True}` follows. Its docstring's "its
  post exactly what `New` gives" stopped being true at S3e. No closed theorem is affected: they fix
  `receiptBound ≤ 2 ^ 48`.
- **Evidence.** The step-2 review (fresh `spec-reviewer`, 2026-11-22), item 1.
- **Proposed change.** Add `[ReceiptBoundLe GF (2 ^ 60)]` to `storage.OpenBackend.spec` and to
  `OpenSnapshotBackend`'s use of it (only weakens the axiom: it now claims `New`'s post under `New`'s
  premises). Its one caller, `OpenSnapshotBackend` from the server's `applySnapshot` walk
  (`SnapApplyWalk.lean:338`), has no receipt bound in scope (`isServerM` holds only the thread
  bound), so the change threads a receipt-bound fact into the walk (from `isServerM`, as its thread
  bound, or a premise of `applySnapshot`'s spec).
- **Decision.** Deferred from step 2, then applied at the user's request (2026-11-22, branch
  `openbackend-receipt`, `notes/step-bounds-questions.md`, Q2): the axiom and `OpenSnapshotBackend`'s
  spec take `[ReceiptBoundLe GF (2 ^ 60)]`; `srvSnapRO`'s receipt conjunct and `applySnapshot`'s
  `hrbw` become `receiptBound GF ≤ 2 ^ 60` (implying the `wbInit - 6` they stated), which the walk
  passes as the instance.
## 2026-11-22: kvnet's top-level statement takes `os`'s two field-assumption instances (KvNet)

- **Spec.** `raft_kvnet_robust.spec` and `raft_kvnet_robust_example.spec`
  (`KvNet/Spec/.../kvnet/TopLevelRobustness.lean`): two instance binders added next to `net.FieldAssumptions`,
  `[os_file_sem : os.file.FieldAssumptions] [os_stat_sem : os.fileStat.FieldAssumptions]`; the header's list
  of trusted instances names them.
- **Defect.** `durable`'s proofs (`tryRead`, `tryWrite`, `WriteOpen`, through `StartNode` and `persist`) read
  files through `os`'s models, which take these trusted struct-field facts (`TrustedCode/os.lean`, of the kind
  of `net.FieldAssumptions`); `kvcheck.Assumptions` does not include them, so the agreed statement could not be
  proved without them (found linking kvnet, 2026-11-22: `kvnet/Link.lean`'s section variables).
- **Evidence.** `KvNet/Proof/.../lib/durable/{tryRead,tryWrite,WriteOpen}.lean`, `kvnet/Link.lean:196-197`;
  reported on mit-pdos/etcd-grove#22 (gap 3).
- **Proposed change.** As above.
- **Decision.** Applied: approved by the coordinator (zeldovich-agent's session, relaying the decision on
  #22), 2026-11-22.
## 2026-11-22: kvnet's top-level statement takes `[log.NewModel]` and `dir.length < 2 ^ 39` (KvNet)

- **Spec.** `raft_kvnet_robust.spec` and `raft_kvnet_robust_example.spec`
  (`KvNet/Spec/.../kvnet/TopLevelRobustness.lean`): an instance binder `[log_sem : log.NewModel]` next to the
  `os` ones (both statements); a premise `dir.length < 2 ^ 39` after `replicas.length < 2 ^ 32` (the main
  statement; the example's `/var/lib/kvnet` meets it by computation). The header lists both.
- **Defect.** (1) `kvnet.initialize'` initializes raft, whose initializer calls `log.New` (`defaultLogger`,
  `discardLogger`), which Perennial translates names-only: raft's `wp_initialize'` takes the trusted class
  `log.NewModel` (`Proof/log/NewModel.lean`), as kvdurable(-noax)'s closed theorem does. (2) Each replica's file
  is `durable`'s `DFile ⟨dir, J, "replica-<id>"⟩`, and `StartNode`'s start resource needs `DFile.Ok`, which has
  `f.d.length + f.tb.length < 2 ^ 40` (`WalTester/.../lib/durable/Defs.lean`, the path arithmetic of
  `filepath`/`os`); `tb` is at most 27 bytes, and nothing in `FsInit`/`RootsOk` bounds a root's length.
- **Evidence.** Reported on mit-pdos/etcd-grove#22 (gaps 4 and 5, with the exact texts).
- **Proposed change.** As above.
- **Decision.** Applied: approved by the coordinator (relayed to the kvnet-proof session, 2026-11-22).
## 2026-11-22: `BackendPath`, `OpenSnapshotBackend`, `applySnapshot` take a data directory shorter than `2 ^ 60` bytes (bkarea)

- **Spec.** `config.ServerConfig.BackendPath.spec`: a premise `d.length < 2 ^ 60` and `isPkgInit config` in
  the pre (until now an axiom, now proved). `storage.OpenSnapshotBackend.spec`: a premise
  `cfg.DataDir'.length < 2 ^ 60`. `EtcdServer.applySnapshot.specSnapM`: a premise `hdd` of the same text after
  `hmmap`. `srvSnapRO`'s pure part: the same conjunct, last.
- **Defect.** `BackendPath()` is `datadir.ToBackendFileName(c.DataDir)`, three `filepath.Join`s; `Join`'s spec
  (proved) needs its elements' lengths to sum below `2 ^ 62` (Go strings are shorter than `2 ^ 63`, GooseLang's
  are lists). `Clean` can shorten a path (`a/../a/../...`), so no bound on the backend path's length bounds the
  data directory's: the premise is on `DataDir` itself.
- **Evidence.** `Proof/go_etcd_io/etcd/server/v3/storage/datadir/*.lean`, `Proof/path/CleanIdem.lean`
  (`joinModel_triple_length`).
- **Proposed change.** As above. Every caller discharges it: `applySnapshot` from `srvSnapRO`; `srvSnapRO` at a
  first start from `bootCfgFresh`'s `Fs.DirFits cfg.DataDir'` (under 3800 bytes, `NewServer`), at a restart from
  the image's WAL area (`srvFiles_dataDir_len`: `WalA.fits` of `srvWalDirOf dd`, `NewServerR`), kept by
  `srvSnapRO_succ`. No top-level statement changes.
- **Decision.** Applied under the approved ownership-premise rule (an intermediate premise every caller
  discharges; the user's 2026-11-21 rule), bkarea, 2026-11-22.
## 2026-11-22: the bootstrap contracts give the membership buckets in the backend's table; `SetBackend`, `MustDeleteMemberFromBackend` take them (members)

- **Spec.** Top level (the user's approval, 2026-11-22): `bootOk`'s `%Hbe` (`InvBoot.lean`, the post of the trusted
  `bootstrapContract`) and `bootOkR`'s (`InvRestart.lean`, `bootstrapRestartContract`'s) gain three conjuncts,
  last, `d.P.has mvcc.membersBI ∧ d.P.has mvcc.membersRemovedBI ∧ d.P.has mvcc.clusterBI` (the new names: schema's
  `Members` id 10, `MembersRemoved` id 11, `Cluster` id 5, `InvStore.lean`). Intermediate: `srvSnapRO`'s pure part
  gains the same triple after the alarm/auth one; `EtcdServer.applySnapshot.specSnapM` and `applySnapshot_walk` a
  premise `hmbP` of that text after `halbi`; `membership.RaftCluster.SetBackend.spec` the three `d.P.has` premises and
  `isPkgInit schema` in its pre; `schema.membershipBackend.MustDeleteMemberFromBackend.spec` the two `d.P.has`
  premises of its buckets. `schemaInit` (schema's package fact) gives the three buckets' values (`bucketIs`).
- **Defect.** Both functions were trust-boundary axioms (names-only). Proved over the real code, their
  `UnsafeCreateBucket`/`UnsafeDelete`/`UnsafePut` calls need the bucket in the backend's table (`P.has`, a ghost
  parameter: the bucket among the backend's ghost names), which nothing carried for these three buckets (alarm/auth
  got theirs from item E of the 2026-11-02 approved restatements). `KBReal.BT` is free; nothing derives it from data.
- **Evidence.** `/shared/tmp/ps2/bkarea/triage.md` (the previous agent's); the proofs
  `Proof/.../schema/membershipBackend__{MustCreateBackendBuckets,MustDeleteMemberFromBackend}.lean`,
  `Proof/.../membership/RaftCluster__SetBackend.lean`.
- **Why true of the code.** As item E's for alarm/auth: `bootstrap`'s `cl.SetBackend(be)` creates the three
  buckets (`MustCreateBackendBuckets`, `schema/membership.go:168`), and the contract already states them present
  (`%HDr`: `D.lookup "members"/"members_removed"/"cluster" = some ∅`); the table is the ghost naming of the
  backend's buckets, which the contract picks.
- **Proposed change.** As above. Every intermediate premise is discharged: `srvSnapRO` from `bootOk`/`bootOkR`
  (`NewServer`, `NewServerR`), kept by `srvSnapRO_succ` (a new backend's parameters are the old one's);
  `applySnapshot`'s from `srvSnapRO` (`ApplyAllSnap`); `SetBackend`'s at the new backend `d'` (`d'.P = d.P`);
  `MustDeleteMemberFromBackend`'s spec has no caller that instantiates it (`applyConfChange` takes it unused).
- **Decision.** Applied: the two contract clauses approved by the user (2026-11-22, relayed by proving session 2);
  the intermediate premises under the approved ownership-premise rule (2026-11-21).

## 2026-11-23: `clientCodec.ReadResponseHeader.spec` bounds the header it read; `Client.send.spec` and `callRes` take the call's `Error` at `nil` (net/rpc model)

- **Spec.** `Net/Spec/net/rpc/clientCodec__ReadResponseHeader.lean`: the success case's pure part gains
  `(respHdr seq sm e).length ≤ maxFrameN` (as `ReadResponseBody`'s `pl.length ≤ maxFrameN`).
  `Net/Spec/net/rpc/Client__send.lean`: the pre's `structFieldRef Call "Error" pc ↦ e0` (any `e0`, a parameter)
  becomes `↦ interface.nil`; `callRes` (`Net/Proof/net/rpc/ClientDefs.lean`, a pending call in `mutex`'s
  invariant) likewise holds `Error ↦ interface.nil` (its `∃ e0` dropped).
- **Defect.** Found proving `Client.input`. (1) To identify the answer a header heads (`ans_next`, `respHdr_inj`)
  the reader needs the header's strings shorter than `2 ^ 62`; the spec gave no bound on what was read. (2) For a
  successful reply `input` calls `call.done()` without writing `call.Error`, so the outcome `done` carries is the
  field's old value; `callPost`'s `nil` case needs it `nil`, which an arbitrary `e0` does not give.
- **Evidence.** `Net/Proof/net/rpc/Client__input.lean` (`hdr_match`; the default case of the switch).
- **Why true of the code.** (1) `readFrame` refuses a frame over `maxFrameN` (its spec already says so), and the
  header is that frame's payload (`ReadResponseHeader`'s proof: `pl = respHdr ...`). (2) `Go` makes the call with
  `new(Call)`, `Error` `nil` (`Client.Go`'s proof passes the zero value); only `send`'s failure path and `input`
  write it, each after removing the entry from `pending`.
- **Proposed change.** As above; callers updated (`Client.send`'s, `Client.Go`'s, `ReadResponseHeader`'s proofs).
- **Decision.** Applied (callee strengthenings an existing proof discharges; no top-level statement changes).

## 2026-11-23: `violated.spec` says an empty result is `nil` (antithesis check, #33 S3b W7)

- **Spec.** `Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/check/violated.lean`.
- **Defect.** Its post held only `strsRO u (violated s)`; `Checker.Next` tests `v != nil` on the
  result, which a list `[]` held by a non-nil slice would not decide, so `Next`'s proof re-proved the
  call with the extra fact (`Checker.Next.violated_wp`).
- **Evidence.** `check.go`'s `violated` returns `nil` when no invariant is broken and the state's
  `Viol` is empty (`len(s.Viol) == 0`), else a non-empty slice.
- **Proposed change.** The post adds `⌜violated s = [] → u = slice.nil⌝`; `violated.wp_proof` is the
  re-proof's body, `Checker.Next.wp_proof` takes `violated.spec`, `violated_wp` goes.
- **Decision.** Applied (a callee strengthening its own proof discharges; no trust or top-level change).
## 2026-11-23: grpc's contracts take a resource parameter (#24's S2 signatures, item (c))

- **Spec.** `Proof/google_golang_org/grpc/InvGrpc.lean`, `InvGrpcStream.lean`, `InvGrpcRun.lean` and the axioms
  stated over them. Server: `srvChainWP R`, `grpcSrvChain R`, `srvStreamChainWP R`, `grpcSrvStreamChain R`
  (each call `R -∗ WP … {{ v, R ∗ Ψ v }}`); the Go facts a run is given (`grpcAccepted`, so `acceptRun`/
  `acceptRunConns`; the run and method contracts `grpcRunOkMd`, `grpcMethodOk(Md)`) at every resource
  (`grpcSrvChainAll`, `grpcSrvStreamChainAll`); the stream run contract's chain at `R := True` (the run keeps its
  `threadTok` in its own pre/post). Client: `grpcConn conn addrs ics dopts Ok` (the family `Ok` the credentials
  were dialed for), `perRPCCredsOk pc Ok Q` (`GetRequestMetadata` given `R` with `Ok R`, given back),
  `grpcInvokerOk conn addrs Ok inv` (each attempt given `R` with `Ok R`), `chainWP R`; `ClientConn.Invoke`,
  `ClientConn.NewStream` take `⌜Ok R⌝ ∗ R` and give `R` back; `cliStreamIs`/`cliBidiStreamIs … Ok`: `SendMsg`,
  `RecvMsg`, `CloseSend` (and the wrappers' `Send`/`Recv`/`CloseSend`) likewise; `NewClient` takes the
  credentials at `Ok` and returns `grpcConn … Ok`.
- **Defect.** None of grpc-go's: the contracts did not let a caller lend a resource (a reader slot of a pool) to
  the per-RPC credentials grpc calls, so `perRPCCredential.GetRequestMetadata`, `Client.Endpoints` (the retry
  interceptor) and `api.IsCapabilityEnabled` (the server's interceptors) could only be axioms reading under a
  lock without a reader token.
- **Evidence.** #24 ("draft signatures for the resource parameter (S2)", the per-call `R` / family `Ok`
  exchange, item (c)). Found while restating: the credentials also run inside a client stream's
  `SendMsg`/`RecvMsg`/`CloseSend` (a transparent retry before the stream commits, `stream.go:800-819,930`), so
  the agreed `NewStream` `R` alone was not enough: the stream's operations take one too.
- **Why true of the code.** grpc-go v1.84: the server's chain closures (`server.go:1227-1276`) and the client's
  (`chainUnaryInterceptors`, `getChainUnaryInvoker`) call the next interceptor synchronously and touch no
  program resource; the credentials are called only by `http2Client.createHeaderFields` → `getTrAuthData` when
  an attempt's transport stream is made, synchronously inside the caller's `Invoke`/`NewStream`/stream
  operation, transparent retries included.
- **Proposed change.** As above. etcd's client instantiates `Ok := anyRes` (every resource; its credentials'
  axiom needs none yet) and passes `R := True`; etcd's handlers use the chains at `R := True`.
- **Decision.** Applied (agreed on #24; reviewed there before landing). No top-level statement changes.

## 2026-11-23: `api.IsCapabilityEnabled.spec` takes a level-0 token; etcd's interceptors' resource is that token (prove-ps2-cap)

- **Spec.** `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/IsCapabilityEnabled.lean`: under
  `[ThreadBoundLe GF (2 ^ 30)]`, the pre gains `levelTok 0` and the post gives it back (the key `c : GoString`,
  `Capability`'s type, in place of any `val`). `v3rpc.newUnaryInterceptor.spec` (under the same instance):
  `srvInterceptorOk ic (levelTok 0) learnerReqOk` in place of `… iprop(True) …`; `v3rpc.newStreamInterceptor.spec`:
  `srvStreamInterceptorWOk ic (levelTok 0)` in place of `… iprop(True)`; `v3rpc.Server.spec`'s post likewise for
  `iu` and `is`. `etcdserver/api`'s package fact: `capInit` (`api/CapPool.lean`) in place of `True`.
  `client.etcdIcRs s` (the unary chain's lent resources) is `[srvLgReader s, True, levelTok 0]`, so
  `etcdGrpcSlot` holds the run's level 0 (`etcdGrpcSlot_bundle : srvRunBundle ⊣⊢ etcdGrpcSlot`, until then
  `⊣⊢ etcdGrpcSlot ∗ levelTok 0`) and the lease handlers take the level 0 the interceptors lend.
- **Defect.** The trust-boundary axiom `api.IsCapabilityEnabled.wp_proof` read-locked `enableMapMu` with no
  reader token (`{{ isPkgInit api }} … {{ b, True }}`): a reader slot of an `RWMutex` for free, which is
  false of Go without a bound on concurrent readers (`notes/bounds-plan.md`).
- **Evidence.** `IsCapabilityEnabled` translated with its body (`api.toml`) and proved
  (`Proof/.../api/IsCapabilityEnabled.lean`): the package's initializer builds `enableMapMu`'s reader slots into
  a level-0 thread pool (`capInit_alloc`, `sync.init_RWMutex_threadPoolL`), and a reader borrows one with a
  level-0 token. The callers are v3rpc's interceptors, run by grpc on a gRPC run's goroutine before the handler:
  the run's bundle holds its level 0 (`srvRunBundle`/`srvStreamBundle`), free during the interceptor's call
  (`RevokeCtx.lean`'s header).
- **Why true of the code.** `IsCapabilityEnabled` (`capability.go:85`) `RLock`s, reads `enabledMap` (nil or a
  map nothing writes after `init()`: `UpdateCapability` stores one of `capabilityMaps`' inner maps under the write
  lock; `EnableCapability`, the only writer of entries, is called by tests only) and `RUnlock`s by `defer`;
  `newUnaryInterceptor`'s and `newStreamInterceptor`'s closures call it first (`interceptor.go:49,220`), before
  the handler. The unary contract lends the token to the handler (`srvInterceptorOk`), so the lease handlers'
  level-0 pools use it after; the stream contract keeps it (`srvStreamInterceptorWOk`), and the watch handler,
  the one stream handler proved, does not use level 0.
- **Proposed change.** As above; callers updated (`v3rpc.Server`'s proof, the served theorems' slots: the KV,
  lease, auth and watch ones, `etcdstart`'s `grpcUp`).
- **Decision.** Applied: an axiom retired, callee contracts restated so that every caller proves on top; no
  top-level statement changes.

## 2026-11-23: `semver.Version.LessThan` back to the trust boundary; `apply.isCluster`'s `Version()` law back to `True` (prove-ps2-version)

- **Spec.** Reverts the 2026-11-22 entry (prove-ps2-semver). `semver.Version.LessThan.spec`
  (`Spec/github_com/Masterminds/semver/v3/Version__LessThan.lean`): again of any `v`, `o` not nil, some boolean;
  `semver.Version.LessThan.wp_proof` again an axiom. `apply.isCluster`'s `Version` law (`apply/Contracts.lean`):
  the post `⌜v = null⌝ ∨ ∃ x, v ↦□ x` again `True`. The callers' proofs (`version/LessThan`,
  `rafthttp/compareMajorMinorVersion`, `apply/applierV3backend__ClusterVersionSet`) as before 2026-11-22.
- **Defect.** The 2026-11-22 change was a stronger trusted premise, not a proved fact: `isCluster` reaches every
  top-level theorem through `clusterApplyOk`, `bootOk`, `bootstrapContract` and `bootPremise` (`bootstrap` and
  `RaftCluster.Version` are not verified: `membership` translates `Version` names-only, and the cluster's lock
  invariant `rcLockInv` holds nothing of `c.version`). Upamanyu's ruling on etcd-grove#18 (2026-11-23): no
  axiom is retired by growing a top-level premise.
- **Evidence.** `semver.Version.Compare` and its callees stay proved over the real code
  (`Proof/github_com/Masterminds/semver/v3/{Version__Compare,…}.lean`), linked but used by no proof until
  `LessThan` can take ownership; `LessThan` stays translated with its body (`v.Compare(o) < 0`).
- **Proposed change.** Retire the axiom again once `ClusterVersionSet`'s `prev` has a proved ownership: the
  cluster's version field in `rcLockInv` (`c.version` nil or read-only), `RaftCluster.Version`/`SetVersion`/
  `Recover` translated and proved over it, and the cluster's construction in `bootstrap` verified so that
  `bootOk`'s `isRaftCluster` is proved, not assumed.
- **Decision.** Applied (reverted).
## 2026-11-23: `Client.Call.spec` asks the codec to decode only the method's answers (net/rpc model)

- **Spec.** `Net/Spec/net/rpc/Client__Call.lean` (and `Client__Go.lean`, `Client__send.lean`): the decoding
  obligation `□ (D -∗ ∀ rep, C.dec rep reply (Θ rep))` becomes `□ (D -∗ ∀ rep, Φ rep [] -∗ C.dec rep reply
  (Θ rep))`; `Call`'s success post `Rargs ∗ ∃ rep, Φ rep [] ∗ Θ rep true` becomes `Rargs ∗ ∃ rep, Θ rep true`
  (the answer went into the decoding; `Θ` keeps what the caller needs of it), as `callPost`'s `nil` case
  (`ClientDefs.lean`). `callRes` holds `bodyDecG C reply D (fun rep => Φ rep []) Θ`.
  `Net/Spec/net/rpc/clientCodec__ReadResponseBody.lean`: `bodyDec C body D Θ` becomes `bodyDecG C body D G Θ`
  (`Codec.lean`: the `dec` of every payload `pl` with `G pl`), with a new premise `□ (∀ pl, ⌜pl.length ≤
  maxFrameN⌝ -∗ P (frameOf pl) -∗ ▷ (P (frameOf pl) ∗ G pl))` (the guard from the reader predicate, a step
  after the read; `guard_true` for a `nil` body). `decErr`'s docstring (`Codec.lean`): the generated `Decode`
  also panics `rpcNotModelled` on a tag naming another type (and on a `nil` or unlisted target), outside any
  `C.dec` a generated codec meets; `CodecSpec`'s: a decoding that fails partway leaves fields written, so
  `dec`'s `Ψ false` can only promise some value of the target's type.
- **Defect.** No program using rpcgen's codec with two types or more could meet `Call`'s premise: its
  `rpcDecode` (`models/net/rpc/rpcgen_core.py`) panics `rpcNotModelled("... decoding a <tag> into a <T> is not
  modelled")` when the tag parses but names another listed type (a documented deviation from gob), so
  `C.dec rep reply Ψ` is false of such `rep` and `∀ rep, C.dec rep reply _` unprovable: a kit cannot call
  `Call`.
- **Evidence.** kaashoek's craq port, report on etcd-grove#24. The new statement is proved:
  `Client.input`'s proof (`Net/Proof/net/rpc/Client__input.lean`) trades the call's collection token for the
  answer `Φ reply []` at the header (`resp_hdr`, `ans_trade`), before the body, and gives `ReadResponseBody`
  the guard `pl = reply` (`body_guard`: by `resp_body` and the `ans` element's agreement, the body frame is
  that answer's reply); `lake build Net.Proof.net.rpc.Results` green, every linked result Lean's three axioms.
- **Why true of the code.** A success response's body is the server's encoding of the handler's reply
  (`sendResponse`, `callRet`: `C.enc replyv (fun eb => Φ eb [])`), and `Φ rep []` reaches the client only
  through the run's answer (`answerRes`, `replyEscrow`), so a method spec that gives `Φ rep []` only for `rep`
  an encoding of the reply type (as a caller's `Φ` can require) makes the decoding provable. `decOk`'s failure
  branch claimed nothing about the target (it is `C.dec`'s `Ψ false`, the codec spec's choice); no concrete
  `CodecSpec` exists yet to overclaim.
- **Proposed change.** As above; callers updated (`Client.input`'s, `Client.send`'s, `Client.Call`'s,
  `ReadResponseBody`'s proofs). Open, same defect: the server's `methodOk` (`ServerDefs.lean`) gives
  `bodyDec C argv D Θ`, a decoding of every request body, which a generated codec with two types does not meet
  either (`serverCodec.ReadRequestBody`, `Server.readRequest`); the same guard from the deposit `S m args Φ`
  would fix it.
- **Decision.** Applied for the client (branch `models-rpc-server`); the server's request decoding closed the
  same day (next entry).

## 2026-11-23: `methodOk` asks the codec to decode only the arguments a client deposited (net/rpc model, server)

- **Spec.** `Net/Proof/net/rpc/ServerDefs.lean`: `methodOk`'s `NewArg` gave `bodyDec C argv D Θ`, i.e.
  `codecSet C ∗ □ (D -∗ ∀ pl, C.dec pl argv (Θ pl))`; it now gives `argDec C argv D Sm Θ :=
  codecSet C ∗ □ (D -∗ ∀ args Φ, Sm args Φ -∗ Sm args Φ ∗ C.dec args argv (Θ args))` (the method's deposit
  is the guard, and is kept: the call obligation `Sm args Φ -∗ Θ args true -∗ callObl …` and the error
  answers through `errOk` use it after the decoding, unchanged). `Net/Spec/net/rpc/serverCodec__ReadRequestBody.lean`:
  `bodyDec C body D Θ` becomes `bodyDecG C body D G Θ` with the guard premise `□ (∀ pl, ⌜pl.length ≤
  maxFrameN⌝ -∗ P (frameOf pl) -∗ ▷ (P (frameOf pl) ∗ G pl))`, as `clientCodec.ReadResponseBody.spec`'s.
  `bodyDec` (`Codec.lean`) is gone, no user left.
- **Defect.** The server twin of the previous entry's: a generated codec with two types or more panics
  `rpcNotModelled` decoding another listed type's value, so no kit could prove its methods' `methodOk` (the
  decoding of every request body into the argument).
- **Evidence.** Proved: `Server.readRequest`'s proof (`Net/Proof/net/rpc/Server__readRequest.lean`) applies
  `argDec` to the request's deposit `S m r.body Φ` (taken at the header, `take_req`) before the body read,
  getting the deposit back and `C.dec r.body argv (Θ r.body)` as `ReadRequestBody`'s decoding resource, with
  the guard `pl = r.body` (`req_guard`, `ServerGhost.lean`: by `req_body`, the body frame after request
  `k`'s header is its argument bytes). On a read failure the resource is dropped and the deposit pays the
  error answer, as before. `ServeCodec`'s proof unchanged. `lake build Net.Proof.net.rpc.Results` green,
  every linked result Lean's three axioms.
- **Why true of the code.** A request's body is the client's encoding of `args` (`Call`'s `C.enc args (fun bs
  => S M bs Φ ∗ …)`), so the deposit's bytes are what the method's spec says a client sends; a method spec that
  deposits only for `args` an encoding of the argument type (as a kit's can) makes the decoding provable. The
  guard does not consume the deposit: a decoding needs to know the bytes' type, not to spend the call.
- **Proposed change.** As above; callers updated (`readRequest`'s and `ReadRequestBody`'s proofs). The client
  is unchanged. At-most-once and the other guarantees unchanged.
- **Decision.** Applied (branch `models-rpc-server`); closes the previous entry's open item.
## 2026-11-23: `semver.Version.String.spec` takes a points-to and returns the exact rendering (prove-ps2-semstr)

- **Spec.** `Spec/github_com/Masterminds/semver/v3/Version__String.lean`: the pre gains `v ↦{dq} x` (any
  fraction, given back) in place of `⌜v ≠ null⌝`; the post is `RET #(semver.render x)` (`major.minor.patch` in
  decimal, Perennial's `fmt.decimal`, then `-pre`/`+metadata` if not empty: `Proof/.../semver/v3/Str.lean`) in
  place of some `s` with `semverStr s`, which `semver.semverStr_render` derives. SpecPlan's
  `Semver.Version.String.spec` (`verAt v a`, `render a`) is the same at `dq = DFrac.discard`.
- **Defect.** The trust-boundary axiom owned nothing of `*v` (only `v ≠ null`): unprovable of the real body,
  which reads the struct (`version.go:340`), and too weak against a concurrent writer.
- **Evidence.** `Version.String` translated with its body and proved over Perennial's `fmt.Fprintf` spec and
  `bytes.Buffer`'s `Write`/`String` (`Proof/.../semver/v3/Version__String.lean`; Perennial branch
  `bytes-buffer-string`: `Buffer.String` translated and proved, `bytes.Buffer.writeSpec`).
- **Proposed change.** As above, under the approved ownership-premise rule (2026-11-21). Callers: `New` (its fresh
  version), rafthttp's `checkVersionCompatibility`/`checkClusterCompatibilityFromHeader`/`checkStreamSupport` and
  `ClusterVersionSet` (their read-only `↦□`) discharge it. `EtcdServer.start` does not: `s.ClusterVersion()`'s
  contract (`clusterVersionOk`, from `bootstrap`'s `clusterVersionMono`, in `bootOk`) gives only `v ≠ null`.
  Proposed: that contract's non-`nil` result comes with `∃ x, v ↦ x` (owned; true of Go: `RaftCluster.Version()`
  returns `semver.MustParse(c.version.String())`, a fresh version, `cluster.go:580-587`).
- **Decision.** Pending the user: the `clusterVersionMono` change strengthens `bootstrapContract`, a premise
  of the top-level theorems (`bootPremise`), so it is a top-level statement change; prepared on the branch,
  not landed.
## 2026-11-23: the cluster's version slot; `Hcvm`, `Hclok` and `isCluster`'s `Version`/`ID` rows proved (prove-ps2-bootstage1, #34 stage 1)

- **Spec.** `membership.rcLockInv c γcv` (`Proof/.../api/membership/Defs.lean`) gains the version slot
  `rcVerSlot c γcv` (`notes/bootstrap-proof-plan.md` §7.1 I1): `c.version` is nil with the counter `γcv` at 0,
  or read-only (`vp ↦□ x`, its rendering parsing: `semverValid (semver.render x)`) with the counter at 1;
  `isRaftCluster c := ∃ γcv, isRaftClusterV c γcv` (the arity kept), `isRaftClusterG` likewise.
  `rcLockInv_boot` (I2) builds it from `c.version ↦ nil`. New: `RaftCluster.Version.spec` (proved). `bootOk`
  and `bootOkR` lose `Hclok` (`lease.clusterOk`) and `Hcvm` (`clusterVersionMono`), and `Hisc` becomes
  `clusterApplyRest` (`clusterApplyOk` without the `Version`/`ID` rows: `apply.isClusterRest`), all three
  proved of `Hrc`/`Hcid` (`ClusterLaws.lean`). `clusterVersionMono`/`clusterVersionOk`/`EtcdServer.ClusterVersion`'s
  non-nil result and `isCluster`'s `Version` row now give `∃ x, v ↦□ x`. `memBucketsOk`'s and
  `clusterImageOk_restModel`'s docstrings widened: the image's `cluster` bucket holds a version once the
  cluster's is set (what `Recover`'s axiom needs to keep the slot).
- **Defect.** The cluster's `Version()` contracts were trusted rows of the bootstrap contract, and gave no
  ownership of the result, so `semver.Version.String` and `LessThan` (which read it) could not take a
  points-to without growing the top-level premise (#18's ruling).
- **Evidence.** `RaftCluster.Version` translated with its body (`cluster.go:580-587`) and proved over
  `MustParse` and the proved `String` (`Proof/.../membership/RaftCluster__Version.lean`).
- **Proposed change.** As above. The top-level premise change: `bootPremise`'s `bootOk`/`bootOkR` lose `Hclok`,
  `Hcvm` and `Hisc`'s `Version`/`ID` rows (now lemmas); `Hrc`'s lock invariant gains the slot, nil at boot
  (the approved interim claim, #34 decision 2). `SetVersion`, `UpdateAttributes`, `SetDowngradeInfo` stay
  trusted rows (`isClusterRest`); `Recover` stays an axiom (JSON, #24).
- **Decision.** The interim claim approved by Upamanyu on #34 (decision 2); the deviations from §7.1 posted on
  #34 (D1-D3) before landing.

## 2026-11-23: `remote.ServeClient`'s `newClient` is a persistent triple, and no call budget reaches the far side (#28, #24)

- **Spec.** `Net/Spec/.../lib/remote/ServeClient.lean`: the premise `{{ True }} newClient(c) {{ sys, RET #sys;
  tok sys }}` (persistent). `Net/Proof/.../lib/remote/Defs.lean`: `reqP S`, `svcOp S tok op`, `opMaybe R tok op`
  carried no bound on the number of calls a node serves.
- **Defect.** (1) `ServeClient` calls `newClient` once, but the triple's `□` forbids it to consume anything, so the
  client machine's system cannot hold exclusive per-client state (VR's request numbers and ghost state; rabia's
  kit worked around it with a mutex). (2) The kits rely on a per-client operation budget (rabia's `SeqBudget`,
  VR's request numbers), but nothing told a client machine it serves at most `ops`-many calls.
- **Evidence.** `ServeClient`'s proof uses the premise once (`wp_apply HnewClient`). The orchestrator makes
  `ops` operations per client (`perclient.Run`), each at most `ReadTries` attempts (`Do`), one connection each.
- **Proposed change.** (a) The premise becomes the caller's one-shot WP `∀ Φ, ▷ (∀ sys, tok sys -∗ Φ #sys) -∗
  WP newClient(c) {{ Φ }}`. (b) Call budgets in ghost state (`notes/remote-port-plan.md`, "`ServeClient`'s
  one-shot `newClient` and call budgets"): `RemoteGS.bud`, a unit `budUnit a` per call in `reqP S a`'s slot,
  handed to `svcOp S a`/`opMaybe R a`; `budUsed_add` bounds the count; `Check`/`Run` take `nb ≥ ops * readTries`
  units per client address. Go unchanged.
- **Decision.** Approved by the user (Upamanyu agreed on #24); applied on branch `remote-serveclient` for review on #28.
## 2026-11-23: the TLS fallback and the lease-TTL row as parameters of the auth-on table specs (phase 7 S2, O2)

- **Spec.** The client-facing auth vocabulary took the server's location `s : Loc` only to state `srvTLSId s`
  (its config's `ClientCertAuthEnabled ↦□ true`) and, for `LeaseTimeToLive`, `leaseTTLRow s γl`. It now takes
  the facts themselves, `T : IProp GF` (TLS) and `R : IProp GF` (row): `v3rpc.infoBoundT`, `principalBound`,
  `v3rpc.{hdrBoundT, rangeAuthed, txnAuthed, writeGrantOn, opGrantT, kvOpAuOn, kvOpAuM, leaseGrantResT,
  leaseRevokeResT, adminReplied, userAddReplied, authHistAuT}`, `leaseCheckFrom`, `client.txnAuthOn`, and the
  table specs `client.etcd{Put,Delete,Range,Txn}Spec{On,M}`, `client.etcdLease{TTL,Leases}SpecMd`,
  `client.etcdLease{Grant,Revoke}SpecOn`, `v3rpc.etcd{UserAdd,UserGrantRole,RoleAdd,RoleGrantPermission,
  AuthEnable}Spec` (`T`) and `etcdLeaseTTLSpecLive`, `client.etcdLeaseTTLSpecMd` (`R`). Each table spec is a
  heap-free `…W` over the message models plus its old name at the message types (as the auth-off batch,
  `ae188a5c42`); every server-side statement passes `T := srvTLSId s`, `R := leaseTTLRow s γl`, so it says
  what it said.
- **Defect.** None in meaning: `srvTLSId s` and `leaseTTLRow s γl` name a machine's heap (the server's config
  struct, its raft node), so a service table, which holds no machine's heap (#24, O2), could not state the
  auth-on specs.
- **Evidence.** Mechanical: the definitions' bodies used `s` only through `srvTLSId s` (and `leaseTTLRow s γl`);
  every call site rewritten to `(srvTLSId s)`/`(leaseTTLRow s γl)`; `etc/heapfree-check.py` checks the `…W`s;
  full build green with no new axiom or `sorry`.
- **Proposed change.** As above, with one-way monotonicity laws for the bridge at `Serve`: each table spec
  `S T R` satisfies `□ (T1 -∗ T2) ∗ □ (R2 -∗ R1) ∗ S T2 R2 ⊢ S T1 R1` (`…W_mono`; a registration at the
  server's facts serves a caller at the table's, `isGrpcRpc_mono_with`), and `srvTLSId_iff`:
  `srvCfgFieldAddr s "ClientCertAuthEnabled" ↦□ tls ⊢ (srvTLSId s ∗-∗ ⌜tls = true⌝)`. A table takes
  `T := ⌜tls = true⌝`, `R := ⌜row = true⌝`.
- **Decision.** Applied (branch `prove-ps2-s2flags/2026-11-23`), as agreed with upamanyus-agent on #24
  (parameters, not a `Bool` through the server's specs).

## 2026-11-23: the client side of the auth-on KV and lease calls over the TLS fact `T` (phase 7 S2, O2, #24 item 3)

- **Spec.** Following the previous entry, the client's auth-on vocabulary and results take `T : IProp GF` for the
  server's `s : Loc`, which they used only as `srvTLSId s`: `client.clientGrant`, `clientOpAuOn`, `txnUpdAtOn`,
  `clientHistAu` and their lemmas (`clientOpAuOn_attempt`, `clientOpAuOn_of_au1`, `txnUpdAtOn_write`,
  `clientHistAu_attempt`, `txnAuthOn_write`, `kvOpAuM_of_au1`, `kvOpAuM_of_on`, `etcd{Put,Delete,Range,Txn}SpecM_
  {true,false}`, `etcdRangeSpecE_M`, `kvOpAuOn_lease{Grant,Revoke}`), and `ResultsOn`'s `client_put_on`,
  `client_put_on_nil`, `client_range_on`, `client_delete_on`, `client_txn_on`, `client_lease_{grant,revoke}_on`
  (each with `[Persistent T]`). Every use (the examples', the server's linking modules) passes `srvTLSId s`.
- **Defect.** None: the statements are generalized (at `T := srvTLSId s` they are the old ones), so that a client
  can take its registrations from a service table at `T := ⌜tls = true⌝`.
- **Evidence.** Mechanical; `kvOpAuM_of_au1`/`kvOpAuM_of_on` were proved through the server's `kvDepOwnM_*`
  (which take `s`) and are now proved directly. Full build green; no axiom or `sorry`.
- **Proposed change.** As above. The examples keep `□ (srvTLSId s -∗ False)` until they take registrations from
  the table.
- **Decision.** Applied (branch `prove-ps2-s2client/2026-11-23`).

## 2026-11-24: `RawNode.Step.form`'s scope premise, a sender among the voters (#33 S4, P-raft-3)

- **Spec.** `RawNode.Step.form` (`Proof/go_etcd_io/raft/v3/RawNodeAbsSpecs.lean`), the strengthened triple's
  scope premise `S → st.msg.Type' ∈ antStepTypes ∧ (st.msg.Type' = MsgHeartbeatResp → st.ctx = [])`, under which
  the post is the exact `RecvEnd ps m ps'`.
- **Defect.** False: a response (`MsgHeartbeatResp` with no context, a rejecting `MsgAppResp`/`MsgVoteResp`) from
  a sender not in the progress map (`From = 99`) at a term `t' > ps.term`, `t' ≤ rs.tc`: `NetMsgOk` and
  `isMessage` hold, but raft's `Step` guard `IsResponseMsg(m.Type) && !IsLocalMsgTarget(m.From) &&
  r.trk.Progress[m.From] == nil` returns `errStepPeer` without stepping, so `ps' = ps`, while `RecvEnd` at
  `m.term > ps.term` requires the step-down.
- **Evidence.** Found proving `RawNode.Step.wp_absProof` (helper of the S4 lead): raft v3.7 `rawnode.go`,
  `RawNode.Step`.
- **Proposed change.** Add `st.msg.From' ∈ γ.reCfg` to the scope premise: in the scope the progress map's domain
  is the configuration's ids, which contain the voters `γ.reCfg`, so the early return is refuted. The harness
  supplies it from `NetFacts` (`m.src = nodeId i`) and `reCfg = voters3`. Not a raft bug: etcd never steps a
  response from a non-member (its transport drops them), and the API form's `S := True` callers are the
  harness's only.
- **Decision.** Applied (branch `antithesis-s4`, the lead).

## 2026-11-24: `RawNode.Ready.form`'s post, a new hard state differs from the last one (#33 S4, P-raft-3)

- **Spec.** `RawNode.Ready.form` (`Proof/go_etcd_io/raft/v3/RawNodeAbsSpecs.lean`), the strengthened triple's
  `%Hout`; and `RawNode.readyWithoutAccept.spec` (`Spec/go_etcd_io/raft/v3/RawNode__readyWithoutAccept.lean`).
- **Defect.** Too weak for the Antithesis harness's drain: the `Ready`'s hard state `h` is related to the node's
  only through `phsNext rs.phs h`, so a client cannot tell a non-empty `h` that repeats the last hard state
  handed out from a new one. The TLA+ binding reports a hard-state change only when there is one.
- **Evidence.** raft v3.7 `rawnode.go`, `readyWithoutAccept`: `if hardSt := r.hardState();
  !isHardStateEqual(hardSt, rn.prevHardSt) { rd.HardState = hardSt }` (`prevHardSt`'s record is `rs.phs`,
  `prevHS`).
- **Proposed change.** Add, under the scope guard of `%Hout`, `¬ (h.Term' = 0 ∧ h.Vote' = 0 ∧ h.Commit' = 0) →
  h ≠ rs.phs`; `readyWithoutAccept.spec` gains it unguarded (`%Hhnew`), from its `isHardStateEqual` branch.
  A strengthening: the old specs (`RawNode.Ready.spec`, through `spec_of_abs`) are unchanged.
- **Decision.** Applied (branch `antithesis-s4`, the lead's decision; helper F).

## 2026-11-24: `TickEnd`'s heartbeats and `stepLeader`'s `MsgBeat` clause leave the heartbeat's context free (#33 S4, msgShape)

- **Spec.** `LeaderNonpropResultC`'s `MsgBeat` clause (`Spec/go_etcd_io/raft/v3/stepLeader.lean`, in
  `stepLeader.spec`), and the protocol end relation `TickEnd`'s heartbeat arm (`Proof/go_etcd_io/raft/v3/Protocol/
  InputEnd.lean`), lifted by `tickEnd_of_stepEnd_beat` (`InputEndLift.lean`).
- **Defect.** Too weak for the Antithesis harness: `stepLeader` says only `HbCtxOk s.rd.ro m'.ctx` of a
  heartbeat's context (nil or some position), `TickEnd` nothing, so `msgShape.stmt`'s "a heartbeat (and its
  response) carries no context" (`Sim/MsgShapeStmt.lean`, what `RawNode.Step`'s `NetFacts` needs at the
  receiver) is not derivable: a `TickEnd` with a heartbeat of context `[1]` satisfies every premise.
- **Evidence.** raft v3.7 `raft.go` `bcastHeartbeat`: `r.bcastHeartbeatWithCtx(r.readOnly.heartbeatCtx())`,
  nil with no read request pending (the fork's `heartbeatCtx`; `raft.bcastHeartbeat.spec` already gives
  `m.ctx = hbCtx s.rd.ro`, which `stepLeader/Rest.lean` weakened to `HbCtxOk`).
- **Proposed change.** (1) `stepLeader`'s clause: `m'.ctx = hbCtx s.rd.ro` in place of `HbCtxOk s.rd.ro m'.ctx`
  (stronger; `hbCtx_ok` recovers the old). (2) `TickEnd`'s heartbeat arm gains `x.ctx = []`; its lifting
  takes `s.role = .leader → s.rd.ro.pending = []`, which `RnScope` gains (appended last) and every absProof
  keeps (a win resets the read-only object, `pbecomeLeader`'s `rdNL`; no input of the harness's scope adds a
  read request). (3) `msgShape.stmt`'s cause premise gains `m.ty = .heartbeat → m.ctx = []` (`NetFacts`).
- **Decision.** Accepted (the lead, 2026-11-24). (1) and (3) applied by helper F; (2) to land with the
  `RnScope` scope change (the raft helper's successor), then `msgShape := msgShape_of tickHbCtx`.
  (2) applied with the scope change below (`tickEnd_of_stepEnd_beat` takes `(toPState s).rd.ro.pending = []`;
  `roEmpty_iff`, `tickEnd_ro`, `recvEnd_ro` keep it), and `Sim/MsgShape.lean` proves `tickHbCtx` and `msgShape`.

## 2026-11-24: `NewRawNode.emptyStartAbsSpec`'s precondition is unsatisfiable: the scope required the static mode (#33 S4)

- **Spec.** `RnScope` and `rnScopeAt` (`Proof/go_etcd_io/raft/v3/RawNodeAt.lean`), `NewRawNode.emptyStartForm`
  (`RawNodeAbsSpecs.lean`), `NewRawNode.restartAtSpec`'s scope premise (`RawNodeStart.lean`), `rawNode_scope.law`
  (`RawNodeApi.lean`).
- **Defect.** Vacuous: `RnScope`'s first conjunct was `rs.mode = .static` and `emptyStartForm` assumed
  `γ.rnMode = .static`, but `isCluster` (its pre) forces the cluster's nodes into the dynamic mode of the
  decoder that decides nothing (`UniNames`, `ModeDec`: `γ.mode = (RNMode.dyn noDec …).all`, `InvApi.lean`).
  No harness could meet the premise; every `absSpec` in the scope was usable only vacuously.
- **Evidence.** `InvApi.lean` `ModeDec`/`UniNames`; `RawNodeStart.lean` (the restart's `Hin` proof
  already refuted the static mode from `Hmd`).
- **Proposed change.** The scope admits the dynamic mode: `RnScope`'s first conjunct becomes
  `rs.mode.isDyn = true → rs.cfg.cfg.outgoing = ∅`; `rnScopeAt γ id` owns `RnCfgIn γ id rs` (the node among
  `γ.reCfg`, in the dynamic mode `rs.cfg.cfg.incoming = γ.reCfg`, and `γ.reTrace = none`); the proofs read the
  configuration by mode (`ownStepGhost_cfgScope`: static `CfgStatic`, dynamic `ghostRestM`'s `g.cfg.cfg = c`)
  into `CfgScope` (`cfgScope_of`). `emptyStartForm` drops `γ.rnMode = .static` for
  `γ.raftNames.reCfg = GMap.listToSet vs ∧ cv.ID' ∈ vs`; `restartAtSpec`'s premise for
  `m.voters = reCfg ∧ m.votersOutgoing = ∅ ∧ cv.ID' ∈ reCfg`. `rawNode_scope.law` states
  `id ∈ γ.reCfg ∧ γ.reTrace = none ∧ (isDyn → incoming = reCfg ∧ outgoing = ∅)` (was `rs.mode = .static`).
  `RnScope` also gains, last, `s.role = .leader → s.rd.ro.pending = []` (entry above).
- **Decision.** Applied (the lead's option (a), branch `antithesis-s4`; raft helper).

## 2026-11-24: `RawNode.Advance.form`'s in-progress boundary fact is false in general (#33 S4)

- **Spec.** `RawNode.Advance.form`'s exact effect (`Proof/go_etcd_io/raft/v3/RawNodeAbsSpecs.lean`), the
  conjunct `ip' = min ip (lcpLen ps.log ps'.log)`.
- **Defect.** False when the boundary is below the log's end: a `Ready` hands out `(2,b)`; a `MsgApp`
  truncates to `(2,c)` (`ip = 1`); a later leader's `MsgApp` writes `(2,b)` back (`ip` stays `1`); the
  `Advance` that steps the storage acknowledgement of `(2,b)` then finds it at the log (`ip' = 2`, not
  `min 1 2 = 1`).
- **Evidence.** The trace above (round 3 of the antithesis S4 plan); `unstable.stableTo` and
  `acceptInProgress` raise `offsetInProgress` to the acknowledged index when the entry still matches.
- **Proposed change.** The fact at a boundary at the log's end only:
  `ip = ps.log.length → ip' = min ip (lcpLen ps.log ps'.log)`. The harness meets it: after a `Ready`,
  `ip = |log|` (`Ready`'s `ip' = ps.log.length`), so an acknowledgement's index is at most `ip` and the
  `max` is a no-op (a self-vote's `becomeLeader` append leaves `inprogress` alone).
- **Decision.** Applied (the lead's round-3 decision; raft helper G). `drainAdvance` passes its `hip`.

## 2026-11-24: the antithesis harness's thread tokens: `RunCluster`, `Main`, `Cluster.run` (#33 S4)

- **Spec.** `Spec/.../raft/antithesis/RunCluster.lean`, `Main.lean` (precondition `isPkgInit` only)
  and `Cluster__run.lean` (post `True`).
- **Defect.** Unprovable: `RunCluster`'s boot drains call `Cluster.drain`, which takes a
  `threadTok`, and nothing in `RunCluster`'s precondition gives one; a goroutine forked with
  `wp_fork_tok_body` must end holding its token, and `Cluster.run`'s post gave none back.
- **Evidence.** `RunCluster`'s proof (the boot loop's `wp_drain`; the `go c.run(n)` loop).
- **Proposed change.** `RunCluster` and `Main` take `threadTok` (as other examples' `Main` specs:
  the adequacy gives the main thread its token); `RunCluster` returns it (`runOver c ∗ threadTok`);
  `Cluster.run`'s post `{{ RET #(); threadTok }}` (its proof holds the token throughout).
- **Decision.** Applied (the lead's decision; RunCluster helper F, round 3).

## 2026-11-24: `RawNode.Advance.form`'s exact effect needs no queued pre-vote response (#33 S4)

- **Spec.** `RawNode.Advance.form` (`Proof/go_etcd_io/raft/v3/RawNodeAbsSpecs.lean`), the conjunct
  `AdvanceEnd (rnCfg γ) id ps qs ps'` in the scope.
- **Defect.** Unprovable from `ownRawNodeAt`: a queued self-addressed `MsgPreVoteResp` of term
  `s.term + 1` (a pre-candidate's own vote, `campaign(campaignPreElection)`) has no `RecvEnd`. Go's
  `Step` keeps the term for a granted pre-vote response of a higher term (`m.Type == MsgPreVoteResp &&
  !m.Reject`), while `RecvEnd`'s preamble (`PreEnd`) raises it to the message's term. Nothing in
  `ownRawNodeAt` (`RnScope`: pre-vote off now) excludes such a message from the queue.
- **Evidence.** `RawNode__AdvanceAbs.lean`'s loop (`advStep_pure`): the self response's `RecvEnd` is
  `recvEnd_of_stepEnd_net`, for the harness's types only.
- **Proposed change.** A premise in the scope: `(S → ∀ q ∈ qs, q.ty ≠ .preVoteResp)`. The harness meets it:
  after a `Ready` the queue is the outbox's self-addressed messages, a self-acknowledgement or a
  self-vote (`SelfOut`, `qs_noPreVote`); `DrainIter.Ok` carries it.
- **Decision.** Applied (the lead's decision; Advance helper F).

## 2026-11-24: `RawNode.Ready`'s messages may be untyped (#33 S4)

- **Spec.** `RawNode.Ready.form`'s `%Hout` (`Proof/go_etcd_io/raft/v3/RawNodeAbsSpecs.lean`) and
  `RawNode.readyWithoutAccept.spec`'s post: nothing said every message handed out reads as a protocol
  message (`absMsgOf`), which `Cluster.drain` needs (its interim `readyMsgsOk.law`, `habs`).
- **Defect.** Not provable from the invariant: `XfOk` allowed untyped queued messages
  (`MsgTimeoutNow`, a forwarded `MsgTransferLeader`) at any untraced node, and nothing in the phys
  state told a node that has never stepped a transfer request apart.
- **Evidence.** The drain proof's `habs` (Cluster__drain.lean), and raft: the only untyped messages
  `send` queues are `sendTimeoutNow`'s and `stepFollower`'s forward, both under a transfer request's
  step or a transferee (`leadTransferee`, stored by `stepLeader`'s transfer arm).
- **Proposed change.** A ghost bit `NGhost.xs` (a transfer request was stepped), set by `raft.Step`'s
  transfer arm at a follower or a leader before the step (`ownRaftPhysC_set_xs`, `ownStepGhost_set_xs`,
  `stepGates_xw` generalized), never cleared; `XfOk`'s last clause `xs = false → lt = 0 ∧ every queued
  message typed`; `SendOk`'s transfer clause carries `xs = true`; `sendTimeoutNow`, `stepLeader` (transfer)
  and `stepFollower` (transfer at a node with a leader) take it; `raft.Step`'s `%Hxwframe` frames `xs`
  with `xw`; `RnScope` gains `xs = false`; `readyWithoutAccept` (in the scope) and `Ready`'s `%Hout` (under
  `S`) give `∀ q ∈ ms, (absMsgOf q.st).isSome`; `readyMsgsOk.law` keeps only the destinations (`hvot`). The flag-free alternative (state-only posts with `lt = 0`) was evaluated and is blocked: the physical queue is not in `NState` (`s.outbox` drops untyped messages), and `lt = 0` holds with a forwarded transfer or a surviving `MsgTimeoutNow` queued.
- **Decision.** Applied (the lead's approval: `SendOk`'s clause, `Ready`'s `%Hout`; raft helper H2).
