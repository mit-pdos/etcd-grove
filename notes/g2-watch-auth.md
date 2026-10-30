<!-- The approved G2 design (candidate 4, approved by the user 2026-10-30, after three spec-review rounds). Statements go in code over named stubs; no proofs before the freeze. -->

**In code (2026-10-30, branch `g2-stmts`).** The statements below are in code over named stubs
(`sorry -- G2: re-prove after freeze`). Three departures from the approved text, none of them a
trusted change:
- **The bound per create is a ghost field of the request model, `CreateReqM.bound`** (as
  `CreateReqM.sr` is), in place of `∃ γb n, agreeOwn γb n` in the up content. The approved
  mechanism could not say which create a server record belongs to: `ctrlWatcher` names the create
  by its request, and `γb` was existential in the up content, so two creates with the same key could
  not be told apart. The wire model reads fields one by one (`isWatchReq`), so a ghost field costs
  the Go code nothing. The client sets it to its `n` and keeps it on a resume (`initReq`, with only
  `rev` advanced). A create's up content carries `□ authPubLbM R.E.authMode c.bound` (`watchUp`), and
  `ctrlWatcher` records `watchAuthed γ s tok c.bound c.key c.rangeEnd`.
- **`classResFrom M n info perms`** (`apply/AuthClass.lean`) is `classRes` at a bound (each
  permission granted by a state recorded at an index `≥ n`). `watchClassFrom` is it at
  `watchPerms`, and `isWatchPermitted`'s post is `classResFrom … [(k, e, .read)]`. Laws:
  `classResFrom_zero`, `watchClassFrom_zero` and `watchClassFrom_on`, all proved.
- **F-W3's law in two pieces.** `attemptTokOk_of_watcher` (`InvClientAuth.lean`, a stub) is the
  agreement: the `Watcher` field and a `watcherConnAt w conn` with `clientTokAt` give
  `attemptTokOk conn P`. `watcher_of_clientTokAt` (`WatchCheck.lean`, the approved statement) is
  proved from it, `isNewClient_watcher` and `watcherConnAt_of_watcher`. `New`'s proof gives the new
  conjunct from `watcherConnAt_of_core`.
- `infoBoundT` moved from `v3rpc/ServerKVOn.lean` to `AuthReqDerive.lean` (no change of meaning),
  so that `InvWatchStream` can name it without importing the KV server's proofs.
- **(g) is not changed.** `etcd_kv_auth_served_on` serves the unary methods (`grpcServerAt`); the
  watch stream is served by `etcd_watch_served_chain` (`grpcStreamServerAt`), now md-indexed at
  `R.s` (row (l)), which authkv calls as linkv3p and watchkv do. One exported statement fewer moves.
- **`grpcStreamHandlerOk` is md-indexed too** (as `grpcStreamMethodOk`, row (b)): the watch server's
  handler spec (`watchServer.Watch.spec`) is at the run's token `auth.ctxTokenOf ci`, which a fixed
  `Spec` cannot say; `_Watch_Watch_Handler.spec` takes `Spec : GrpcMd → StreamSpec` with
  `Spec (incomingOf ci)`. A local predicate (`InvGrpcStream.lean`), not an axiom.
- **(d) also gives the token binding**: `watch_registered_authorized` (and `ctrlWatcher_authorized`,
  `watchAuthed_on`) conclude `infoBoundT s (.on γa) tok info` and `c.bound ≤ i`.
- **The client's internals**: the watcher's channel element (`outcElem`) keeps the row `True`, and
  `runCore`'s epoch token is existential, until `Watch` and `run` are re-proved. The internal specs
  `openWatchClient`, `newWatchClient` and `serveWatchClient` carry the stream's metadata `md` and
  its token, and `newWatcherGRPCStream`'s post the stream context's `outgoingOf` and key.
- **`srvAuthLb` in `watchSrvOk`** (after etcd-grove-56's review, 2026-10-30): the server's
  contract for the watch path carries the auth store at a reader's lower bound, so `recvLoop` has
  what `isWatchPermitted` takes, and `recvLoop`'s stubbed statement is final. The off-mode builders
  get it from `srvAuthLb_off`, the on-mode one (`grpcCfgOk_of_started_on_w`) from `Start.specOn`.
- **Bound 0 today**: the verified client builds its creates with `bound := 0` (`createOf`,
  `client/v3/InvWatch.lean`), so `c.bound ≤ i` in `watch_registered_authorized` is trivially true of
  every create the verified client sends until `Watch` and `run` are re-proved with `n`.
- **(h) makes a context spec depend on grpc**: `Spec/context/WithCancelValCtx.lean` imports
  `metadata/Outgoing.lean`, the stopgap until Perennial's `Value` contract
  (`notes/perennial-changes.md`, "Context model: `WithCancel` keeps its parent's values").
- **Stubs** (`sorry -- G2: re-prove after freeze`, each with the commit of the proof before G2):
  `watcher.Watch`, `watchGRPCStream.newWatchClient`, `serverWatchStream.recvLoop`,
  `serverWatchStream.isWatchPermitted` (the
  bound's reasoning at the store), and the law `attemptTokOk_of_watcher` (field agreement). The
  rest of the restated proofs are adapted.
# G2: the watch with auth on (candidate 4, 2026-10-30; after review round 3, the last)

**Changes from candidate 3** (review: `g2-review3.md`; round 3 is the last review round. The user
approved both repairs on 2026-10-30):
- S1: the stream interceptors' contract `srvStreamInterceptorOk` keeps the run's context: the
  handler continuation is at the same `ci`, as in the unary `srvInterceptorOk`.
  - grpc-prometheus's `StreamServerInterceptor` axiom is strengthened with it (trusted row (b′)).
  - `newStreamInterceptor` re-proves the contract under `runsNoRequireLeader`.
  - Layer 2's "`tok := none`" fallback is dropped: it was false with auth on.
- S2: `dialOk` requires an etcd stream interceptor to be present (trusted row (a′), `NewClient`'s
  axiom). `clientv3.New`'s dial supplies it.
- Second tier:
  - `outgoingOf`'s own docstring says it is `FromOutgoingContext`'s view (lower-case keys,
    `added` after `md`). A raw `MD` literal whose keys collide up to case is outside the model.
  - (c)'s docstring states the margin it inherits at a hostile `Value`.
  - The two `streamKeyOf` laws are new axiom names, so `tcb --check --update` is needed. authkv's
    collection joins once `Work` uses the watch.
  - F-W3's law takes `isNewClient_watcher`'s premises. `watchStubAt` is renamed `watcherConnAt`.
  - The forbidden bytes are written out.
  - `auth.ctxTokenOf_md` is moved, not copied.
  - (h)'s "why true" cites the recorded convention over `outgoingOf`, not freshness.

# (candidate 3's header follows)

**Changes from candidate 2** (review: `g2-review2.md`; the user's choices, 2026-10-30: R7 strengthen
the axioms **in place**; R2 a **local axiom** plus a Perennial proposal; R3 `streamKeyFromCtx`
**gains `isContext`**):
- R1: `NewStream`'s post gives `clientAttemptMd conn ctx md`, with `withVersion` inside, instead of
  `grpcAttemptMd conn ctx md`, which is false at the caller's `ctx`.
- R2: the stream's context is related to the watch's by strengthening the existing local axiom
  `context.WithCancelValCtx` in place. It is already the trust boundary for
  `WithCancel(&valCtx{inctx})`, and its post gains `outgoingOf ctx' = outgoingOf inctx`. Both
  halves, `valCtx` promotion and `cancelCtx` delegation, are inside it. `watchCheckOk` is stated
  over the metadata (`clientAttemptMdOf`), not a context.
- R3: `streamKeyOf : GrpcMd → GoString` is opaque. Its two laws are part of trusted change (c),
  with the full side condition (no ` `, `:`, `[`, `]`; lower-case key). `streamKeyFromCtx` takes
  `context.isContext`. The nil-context bug is recorded in `notes/audit.md` (`5c69d8649b`).
- R4: `Watch.spec` is over an explicit environment `V` (`isClientWatcher V w ∗ ⌜V.kst = γ.st⌝`).
  The gate is visible in the triple. F-W3's law concludes about the watcher's environment and its
  connection.
- R5: `watchAuthed` takes `tok : Option GoString`, not `md`. Its binding is gated on the mode being
  on. The `md ↦ tok` map is `auth.mdTokenOf`, moved to the auth package beside `ctxTokenOf`.
- R6: `Work`'s watch context (`authkv.go:268`) uses `WithTimeoutBackgroundMd` (no new axiom: it
  is already in authkv's collection). The plan's sentence is corrected.
- R7: the trusted table is split into axioms (old and new, why true, collections) and exported
  statements, and it is complete.
- Second tier:
  - The check is over the create's key and range end, which survive resumes.
  - The bound travels in `watchUp` through an agreement ghost the client allocates; grpc's `Up` is
    unchanged.
  - The pre's gate is `0 < n`, so `n = 0` needs nothing; there is no `watchBoundAt_zero` update.
  - The callers' restated lemmas are named.
  - The missing laws are listed.
  - `isGrpcStream` is an abbreviation of `isGrpcStreamMd`.
  - (b)'s "why true" is cited, including `runsNoRequireLeader`.

## What each of authkv's watches needs (unchanged)

| Watch | Needs |
|---|---|
| `Work`: `cli.Watcher.Watch(wctx, "c/", WithPrefix(), WithRev(1))` | **auth**: no response has events |
| `Main`: `root.Watcher.Watch(hctx, "", WithPrefix(), WithRev(1))` | the state's events of **every** key (F5, after the pin bump) |
| `Main`: `ucli.Watcher.Watch(uctx, lo, WithRange(hi), WithRev(1))` | events in `[lo, hi)` |

## Vocabulary

### Auth (the merge session's package; proposed)

- `auth.mdTokenOf : GrpcMd → Option GoString` moves from `client/v3/InvKVConn.lean:772` to
  `server/v3/auth/InvAuth.lean`, beside `ctxTokenOf`, with its existing law `auth.ctxTokenOf_md`
  (`client/v3/KVServiceOn.lean:35-37`, moved, not copied). This is a move with no change of
  meaning. v3rpc's proofs that rewrite with it (`v3rpc/Results.lean:835,879,918`) stop importing
  the client's module.

### Server (v3rpc; strengthened in place, proposed to the merge session)

```lean
/-- **A registered watcher's authorization** (A4; strengthened, G2): in the store's mode `M`, the
class of the create's read (`watchKey c.key`, the range end as checked) for an auth info `info`,
at auth states recorded at indices at least the create's bound `n` (`watchClassFrom`); with auth
on, `info` is bound to the stream's token `tok` (`infoBoundT`: the empty user, a token issued to
`info`'s user, or the server's TLS identity); and the request's shape. The binding is gated on
the mode being on (the margin of `NewAuthStore`'s axiom, as in `isWatchPermitted.spec`). -/
def v3rpc.watchAuthed (γ : mvcc.WsNames) (s : Loc) (tok : Option GoString) (n : Nat)
    (key rangeEnd : List w8) : IProp GF :=
  iprop(∃ (M : auth.AuthMode) (info : auth.AuthInfo),
    auth.modeTag γ.tag M ∗ apply.watchClassFrom M n info key rangeEnd ∗
    □ (⌜M.isOn = true⌝ → infoBoundT s M tok info) ∗
    ⌜auth.reqShape (apply.watchKey key) rangeEnd⌝)
```

- `apply.watchClassFrom M n info k e` is `apply.watchClass`'s range under
  `auth.permVerdictFrom M n info … .read GoInterface.nil`. It is new, next to `rangeClassFrom`.
  - Law `watchClassFrom_zero`: at `n = 0` it is today's `watchClass`.
  - Law `watchClassFrom_on`, as `watchClass_on` (`AuthClass.lean:436`): with the mode on, a state
    recorded at an index `≥ n` permitted the read of every key of the range for `info`.
- The current `watchAuthed γ c` is `watchAuthed γ s tok 0 c.key c.rangeEnd` with the binding
  dropped. Its users (`ctrlWatcher`, `watch_registered_authorized`) are restated.
- **The bound per create**: the create's up content carries `∃ γb n, agreeOwn γb n ∗ □ authPubLbM
  R.E.authMode n` (`watchUp R`, below). The client allocates `γb` per substream, keeps it, and
  resends the same `γb` on a resume. The server records `agreeOwn γb n` in `ctrlWatcher`.
  `agreeOwn` is persistent, and two copies agree (standard).

### Client (client/v3)

```lean
/-- **The key `streamKeyFromCtx` computes** from the outgoing metadata (`metadata.outgoingOf`, whose
own docstring now says it is `FromOutgoingContext`'s view: the context's metadata merged with its
appended pairs, keys lower-case; a raw `MD` literal whose keys collide up to case is outside the
model): Go's `fmt.Sprintf("%+v", map[string][]string(md))`, `""` with none. Opaque: a
faithful `%+v` needs the map's sorted finite key set, which a function-valued `GrpcMd` does not
carry. Its laws are trusted (part of (c)). -/
opaque streamKeyOf : GrpcMd → GoString

/-- (c, law 1) Only "no metadata" gives `""`: any map prints as `map[...]`. -/
axiom streamKeyOf_none (m : GrpcMd) : streamKeyOf m = streamKeyOf none → m = none

/-- (c, law 2) A one-entry map's key determines its entry's values, for a lower-case key and a
value free of ` `, `:`, `[`, `]`. The printed `map[k:[v]]` has one `:`, which splits off the key;
no space, so one entry; `[v]` joined without a space, so one value. -/
axiom streamKeyOf_single (m : GrpcMd) (k v : GoString) (hk : metadata.lowerKey k)
    (hs : ∀ b ∈ k ++ v, b ∉ [W8 32, W8 58, W8 91, W8 93]) :     -- ' ', ':', '[', ']'
    streamKeyOf m = streamKeyOf (metadata.mdAdd none k v) → metadata.mdVals m k = [v]

/-- `clientAttemptMd` over the metadata itself: it depends on the context only through
`outgoingOf` (law `clientAttemptMd_iff : clientAttemptMd conn ctx md ↔ clientAttemptMdOf conn
(metadata.outgoingOf ctx) md`, by definition). -/
def clientAttemptMdOf (conn : Loc) (m : GrpcMd) (md : GrpcMd) : Prop :=
  ∃ (c : GoInterface) (v : GoString),
    metadata.outgoingOf c = metadata.mdSet m go!"client-api-version" [v] ∧ grpcAttemptMd conn c md

/-- **A watch's check, as the client sees it** (persistent; G2): the gRPC stream the watch's create
went on was opened with outgoing metadata `m` of the same stream key as the watch's context; an
attempt of it on `conn` delivered `md`; and the server's check of a create of the watch's key and
range end passed for `md`'s token at the bound `n`. -/
def watchCheckOk (γ : mvcc.WsNames) (s conn : Loc) (ctx : GoInterface) (n : Nat)
    (key rangeEnd : List w8) : IProp GF :=
  iprop(∃ (m md : GrpcMd),
    ⌜streamKeyOf m = streamKeyOf (metadata.outgoingOf ctx) ∧ clientAttemptMdOf conn m md⌝ ∗
    v3rpc.watchAuthed γ s (auth.mdTokenOf md) n key rangeEnd)
```

- `attemptTokOk conn P` (`InvClientAuth.lean:391`) is restated over the metadata:
  `□ ∀ m md, ⌜clientAttemptMdOf conn m md⌝ -∗ (∃ t, ⌜auth.mdTokenOf md = some (trimPrefix t "Bearer
  ")⌝ ∗ □ P t) ∨ ⌜auth.mdTokenOf md = auth.mdTokenOf (mdNorm m)⌝`. Today's form is the instance
  `m := outgoingOf ctx`. Its proof (C1, the credentials' values first) does not use `ctx` beyond
  `outgoingOf ctx`.
- **Law `watchCheckOk_tok`**: `watchCheckOk γ s conn ctx n k e ∗ attemptTokOk conn P ⊢ ∃ m tok M
  info, ⌜streamKeyOf m = streamKeyOf (outgoingOf ctx)⌝ ∗ ((∃ t, ⌜tok = some (trimPrefix t
  "Bearer ")⌝ ∗ □ P t) ∨ ⌜tok = mdTokenOf (mdNorm m)⌝) ∗ modeTag γ.tag M ∗ watchClassFrom M n info
  k e ∗ □ (⌜M.isOn⌝ → infoBoundT s M tok info)`. authkv uses this and does not unfold.

## Layer 1: grpc streams, indexed by the stream's metadata

- `isGrpcStreamMd addr name (Up : Nat → Req.M → IProp) (Spec : GrpcMd → StreamSpec Rep)`. `Up` is
  unchanged (no `md`, no names).
  - `isGrpcStream addr name Up Spec := isGrpcStreamMd addr name Up (fun _ => Spec)` is an
    abbreviation, so there is one predicate. Likewise `isGrpcStreams`/`isGrpcStreamsMd`.
- **Server side, trusted (b)**: `grpcStreamMethodOkR` is md-indexed. A run with context `ci` is given
  `Spec (metadata.incomingOf (GoInterface.ok ci)) γ Dn`, as the unary `grpcHandlerOkMd` does.
  `grpc.serveStream` is restated over it, in place. Today's is the instance at a constant `Spec`.
- **Client side, trusted (a)**: `ClientConn.NewStream.spec` takes `isGrpcStreamsMd addrs method Up
  Spec`. Its success post is `∃ a γ Dn cd' md, ⌜a ∈ addrs ∧ clientAttemptMd conn (GoInterface.ok
  ctx) md⌝ ∗ cliStreamIs … ∗ … ∗ Spec a md γ Dn`, in place.
  - Each gRPC stream has one `md` for its life: grpc sends the headers once.
  - A `watchGRPCStream` spans many gRPC streams, one per reconnect. Each has its own `md`, since
    `getToken` re-runs; `watchCheckOk`'s `∃ md` covers this.

## Layer 2: the server's watch stream (v3rpc; proposed to the merge session)

One spec each, the mode in `E` (no `…On` beside the plain ones):
- `serverWatchStream.isWatchPermitted.spec`: at a bound `n` with `□ authPubLbM r.srv.E.authMode n`
  (and `srvAuthLb s E` in `WRun`, as `Range`'s `isAuthStoreRangeLb … n`), a passed check gives
  `watchClassFrom M n info (key, end)` and, gated on the mode being on, `principalBoundI`. Today's
  spec is its `n = 0`.
- `watchUp R i m`: today's (over `R.γ`), and a create also carries `∃ γb n, agreeOwn γb n ∗ □
  authPubLbM R.E.authMode n`. (Signature change: `R : WSrv` in place of `γ`.)
- `watchSpec R tok`: today's, and `ctrlWatcher` carries `agreeOwn γb n ∗ v3rpc.watchAuthed γ R.s
  tok n c.key c.rangeEnd` for the create at up position `i`. `recvLoop`'s proof supplies the
  passed check, the up content's `γb`/`n`, and `tok := auth.ctxTokenOf ci`. (Signature change:
  `tok`.)
- The registration is `isGrpcStreamMd addr "/etcdserverpb.Watch/Watch" (watchUp R) (fun md =>
  watchSpec R (auth.mdTokenOf md))`. The server's proof gets `tok = ctxTokenOf ci` through
  `ctxTokenOf_incoming` and (b).
  - This needs the handler's stream context to be grpc's run context. The interceptors'
    contract `srvStreamInterceptorOk` keeps it (S1, trusted (b′)). etcd's `newStreamInterceptor`
    meets it under `runsNoRequireLeader`, since otherwise its `serverStreamWithCtx` hands the
    handler another context (`v3rpc/interceptor.go:244-245`). That is already a premise of the
    serving results (authkv `Defs.lean:85`). In `off` the gate makes the binding vacuous, so no
    fallback is needed.
- `watch_registered_authorized` is restated over the strengthened `watchAuthed`.
- The auth-on export `etcd_kv_auth_served_on` also gives the md-indexed watch registration at the
  member's `s` and `E`, with `srvAuthLb` in `NewWatchServer`'s `WSrv`.

## Layer 3: the client's `Watch`, one restated spec

```lean
abbrev watcher.Watch.spec : Prop :=
  ∀ (w : Loc) (V : WEnv GF) (γ : KVNames) (ctx : GoInterfaceOk)            -- CHANGED: explicit V
    (ctx_desc : context.ContextDesc (IProp GF)) (key : GoString) (opts_sl : GoSlice)
    (opts : List (OpFull → OpFull)) (rev : w64) (Q : KVState → IProp GF) (n : Nat), -- NEW: n
  {{ isPkgInit … ∗ isClientWatcher V w ∗ ⌜V.kst = γ.st⌝ ∗                  -- was: isKvWatcher w γ
      context.isContext ctx ctx_desc ∗ optsAt opts_sl opts ∗
      ⌜(opWatchModel key opts).isRangeWatch rev = true ∧ ¬ opWatchPanics key opts ∧
        1 ≤ sint.Z rev⌝ ∗                                                   -- CHANGED: any range
                                                                            -- (F5, after the pin)
      □ (⌜V.nm = 1 ∧ 0 < n⌝ → authPubLbM (V.mem 0).2.E.authMode n) ∗        -- NEW: the gated bound
      □ (AU <{ ∃∃ σ, etcdKV γ σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅ <{ etcdKV γ σ, COMM □ Q σ }>) }}
    w.Watch ctx key opts_sl
  {{ (ch : Loc) (γw : EtcdWatchNames), RET #ch;
      isSpsc γw.spsc ch (watchStateElem γw (opWatchModel key opts) Q
        (□ (⌜V.nm = 1⌝ → watchCheckOk (V.mem 0).2.γ (V.mem 0).2.s V.conn   -- NEW: the gated row
          (GoInterface.ok ctx) n (opWatchModel key opts).key (opWatchModel key opts).rangeEnd)))
        (fun _ => True) ∗
      spscConsumer γw.spsc [] ∗ monoListIdxOwn γw.cur 0 (rev - W64 1) }}
```

- `watchStateElem γw o Q Au i v` is today's, plus `Au` when the response has events (a new last
  argument).
- **The gate** is a scope restriction, not an axiom's margin, and is filed in the plan (F6). With
  several members, a lagging member's store checks at its own older auth state, so the client's
  bound does not reach it. With one member, `γa`'s published index is that member's store's.
- **Margin**: the code also ends a refused watch with a canceled response carrying the refusal's
  error (`addSubstream`, `closeSubstream`). The spec says only that no response has events without
  the row.
- **The client's proof**:
  - `newWatcherGRPCStream`'s post gains `outgoingOf w.ctx = outgoingOf inctx` (from (h)) and
    `ctxKey = streamKeyOf (outgoingOf inctx)` (from (c)).
  - `Watch` joins the stream at `streamKeyOf (outgoingOf ctx)`, so the stream's `inctx` has the
    same key.
  - Each `NewStream` on `w.ctx` gives `clientAttemptMd conn w.ctx md`, which is
    `clientAttemptMdOf conn (outgoingOf inctx) md` (the `m` of `watchCheckOk`).
  - The substream's ghost keeps `γb`. On a resume, `nextResume` resends `initReq` with only `rev`
    advanced, so key and range end are unchanged.
- **Callers**:
  - The existing callers (watchkv, linkv3p `MainWatch`, cachekv, k8s `KMWatch`, the cache)
    destructure `isKvWatcher` (one line) and pass `n = 0`, so the bound's premise is vacuous.
  - `isSpsc` fixes the element predicate inside an invariant, so the callers' lemmas that abstract
    it are restated: `isRespChan_of_state` (`examples/common/RespChan.lean:144-160`),
    `KMWatch.lean:637`, and `WatchApiLemmas.lean:174` (the second cursor).
  - `isKvWatcher` stays, as the existing callers' form.

## F-W3: the watcher on the client's connection (local)

- `clientTokAt cl eps P` also names the `Watcher` field and its stub's connection: `∃ w, Watcher ↦□
  ok (watcherIfaceOf w) ∗ watcherConnAt w conn`, with `conn` the same `conn` as the KV's. Here
  `watcherConnAt w conn := ∃ wc, watcherF w "remote" ↦□ wcIface wc ∗ wc's "cc" ↦□ conn`. It is
  renamed from candidate 3's `watchStubAt`, which clashed with `v3rpc.watchStubAt`.
- Law `watcher_of_clientTokAt`, with `isNewClient_watcher`'s premises (`hV : eps = [V.addr]`, `hm :
  V.mem = fun _ => (V.addr, V.R)`, `hn : V.nm = 1`, the three `isPkgInit`s, `wp_ErrAny`, `hAs`,
  the instances): `isNewClient cl eps V ∗ watchAddrFacts V ∗ clientTokAt cl eps P ⊢ ∃ (w conn wc
  lg : Loc) ics, Watcher ↦□ … ∗ isClientWatcher {V with conn := conn, ics, wc, lg} w ∗
  attemptTokOk conn P`.
  - The two `conn`s agree through the `Watcher`, `remote` and `cc` fields: `↦□` agreement plus
    injectivity of `watcherIfaceOf`/`wcIface`/`interface.mkOk`. The connection is
    `isNewClient`'s existential, not `V.conn`.
- `New`'s and `newUserClient`'s posts (`clientTokAt`) change accordingly.

## Layer 4: authkv

- `Work.spec`'s watch premise: `watchAddrFacts V` tied to the KV's server, with `V.nm = 1` and
  `V.mem 0 = (addr, R)`, `R.s = s`, `R.E = E`. `V.nm = 1` and `V.mem` are authkv's choice of `V`,
  passed to `watcher_of_clientTokAt` as `hn`/`hm`.
- `M.isOn` for the row's mode: `auth.modeTag_agree` (`auth/ModeTag.lean:67`) with the server's tag
  at `.on γa`.
- `Work`'s watch context (`authkv.go:268`, `WithTimeout(Background(), …)`) uses
  `WithTimeoutBackgroundMd`: `outgoingOf wctx = none`. This adds no axiom: it is already in
  authkv's collection. `bad`'s context is `AppendToOutgoingContext(wctx, "token", "badtoken")`, so
  `outgoingOf = mdAdd none "token" "badtoken"`.
- `Work`'s refused watch:
  - `n` comes from `akAuthFixed` (`authPubLb γa n`).
  - A response with events gives the row, and through `watcher_of_clientTokAt` and
    `watchCheckOk_tok` a stream metadata `m` and a token:
    - **anon**: `streamKeyOf m = streamKeyOf none` gives `m = none` (law 1). So the token is
      `none` or anon's `P` token (none exists), hence the empty user.
    - **bad**: law 2 at `("token", "badtoken")` (lower-case, no forbidden byte) gives `mdVals m
      "token" = ["badtoken"]`. So the token is `"badtoken"`, refuted by `tokIssued_badToken`.
    - **u, v**: `m = none` as for anon. So the token is one issued to them, or none.
  - `srvTLSId s` is refuted by `Work.spec`'s premise.
  - `watchClassFrom_on` gives a permitted read of `c/…` at a state at index `≥ n`. By
    `akAuthFixed`'s read half (H5) that state is `setupSt _`, where `permittedK who "c/"` is false.
    Contradiction.
- Root's and u's watches use `n = 0`, the plain conjuncts.

## Trusted statements changed (each needs the user's approval)

### Axioms, strengthened in place (the user's choice, 2026-10-30)

| | Axiom | Old | New | Why true | Collections resting on it |
|---|---|---|---|---|---|
| (a) | `grpc.ClientConn.NewStream.wp_proof` | registration `isGrpcStreams`; post `Spec a γ Dn` | registration `isGrpcStreamsMd`; post `∃ md, ⌜clientAttemptMd conn ctx md⌝ ∗ Spec a md γ Dn` | etcd's stream interceptor opens on `withVersion(ctx)` (`retry_interceptor.go:120`), `getToken`'s credentials; grpc builds the headers once per stream: the credentials' data, then the outgoing metadata and `added`, reserved keys skipped (`internal/transport/http2_client.go:579-655`) | cachekv, watch, cache-client, watchkv, lease-served, linkv3p, client, lease |
| (b) | `grpc.serveStream` (over `grpcStreamMethodOkR`) | a run is given `Spec γ Dn` | md-indexed: `Spec (incomingOf ci) γ Dn` | grpc-go's server builds the stream context from the received headers (`internal/transport/http2_server.go:544`, `metadata.NewIncomingContext`; reserved headers skipped at `:467`) | cachekv, watch, linkv3p, v3rpc, cache-client, watchkv |
| (a′) | `grpc.NewClient.wp_proof` (through `dialOk`, `InvDial.lean:155`) | `dialOk`: every stream interceptor is etcd's | also: one is present (`∃ si, .streamInterceptor si ∈ ds ∧ etcdStreamInterceptor si`); the axiom accepts fewer dials | without it, (a)'s `withVersion` claim is false on a connection with no stream interceptor (round 3, S2); `clientv3.New`'s dial adds it (`Client__dialSetupOpts.lean:39`) | authkv, m2, k8s, client, putget3, linkvtxn, putget, k8setcd3, watchkv, cachekv, linkv3p |
| (b′) | `srvStreamInterceptorOk` (`InvGrpcStream.lean:715`), so `grpc_prometheus.ServerMetrics.StreamServerInterceptor.wp_proof` | the handler continuation at any `ci'` | at the run's own `ci`, as the unary `srvInterceptorOk` | prometheus wraps the stream in `monitoredServerStream`, whose `Context()` is `ss.Context()` unchanged (go-grpc-middleware v2.3.4 `interceptors/server.go:35,49-51`; providers/prometheus v1.1.0 `reporter.go:84-86,130`); etcd's `newStreamInterceptor` is proved, under `runsNoRequireLeader` (`interceptor.go:216-261`) | v3rpc, m2, putget, linkvtxn, putget3, k8setcd3, cachekv, watchkv, linkv3p |
| (c) | `streamKeyFromCtx.wp_proof`, and `streamKeyOf`'s laws 1 and 2 (new axioms) | pre `True`, any `ctx : GoInterface`; returns some string | pre `context.isContext ctx cd`, `ctx : GoInterfaceOk` (fixes the nil bug); returns `streamKeyOf (outgoingOf ctx)` | `watch.go:1102-1107`: `FromOutgoingContext` then `fmt.Sprintf("%+v", …)`, which sorts map keys; laws: the format of `%+v` of a `map[string][]string` (checked by a Go test, the scratch `skey/main.go`). Margins, in the docstring: like `FromOutgoingContext.wp_proof`, it assumes `Value(mdOutgoingKey{})` returns; it is a function of `outgoingOf`, so it excludes a raw `MD` whose keys collide up to case (where Go's result depends on map order). The old "two calls need not agree" sentence goes | cache-client, cachekv, watch, watchkv, linkv3p, client |
| (h) | `context.WithCancelValCtx.wp_proof` (local) | post `isContext ctx' …`, `cancelSpec` | also `⌜outgoingOf ctx' = outgoingOf inctx⌝` | `valCtx` embeds `inctx`, so its `Value` is `inctx`'s (Go's promotion); a `*cancelCtx`'s `Value` at a key other than `&cancelCtxKey` is its parent's (`context.go`, `cancelCtx.Value`); grpc's outgoing key is its own `mdOutgoingKey{}`. Consistency: the convention recorded for every `outgoingOf` axiom (`notes/axiom-review/withtimeout-outgoing.md`, "Remarks"): each returns an existential context, and no spec equates two of them; round 3 checked it against `AppendToOutgoingContext` | cachekv, watch, cache-client, linkv3p, watchkv, client |

- Each gets an `axiom`-skill review before it lands, recorded in `notes/axiom-review/` and
  `notes/audit.md`.
  - (c)'s laws: an attack on the format.
  - (h): consistency with `AppendToOutgoingContext`, under the recorded convention (above).
  - (a′), (b′): (b′) is a stronger contract for prometheus's interceptor; (a′) only narrows what
    `NewClient`'s axiom accepts.
- `tcb-report.py --check` flags only what a linked result reaches. The in-place strengthenings keep
  their names, so the audit rows list their collections. The two new laws of (c)
  (`streamKeyOf_none`, `streamKeyOf_single`; approved with the table, 2026-10-30) and the stub
  `attemptTokOk_of_watcher` are reached by no linked result yet, so `--check` does not list them
  (2026-10-30: it listed the five stubbed `wp_proof`s only). They enter the baseline, and authkv's
  collection gains (a), (b), (c), (h) and the laws, once `Work` uses the watch; the laws get the
  `axiom` skill all the same. (c)'s laws rest on `outgoingOf`'s reading (its docstring,
  `metadata/Outgoing.lean`): `FromOutgoingContext`'s view, keys lower-cased, no raw `MD` whose
  keys collide up to case.
- (h)'s general fix goes to `notes/perennial-changes.md`: Perennial's context model has no `Value`
  contract (`isContextDef`'s `Values` field is unused). The general change is a `Value` contract
  for `WithCancel`/`WithTimeout` (delegation to the parent at foreign keys), proposed on a
  Perennial branch by its own workflow. (h) is retired when it lands.

### Exported or shared statements changed (proved; listed for review)

| | Statement | Change |
|---|---|---|
| (d) | `v3rpc.watch_registered_authorized` (`v3rpc/Results.lean`) | over the strengthened `watchAuthed` (bound, gated token) |
| (e) | `watcher.Watch.spec` | as above (explicit `V`, `n`, gated bound and row, any range) |
| (f) | `clientTokAt`; `New`'s and `newUserClient`'s posts | the `Watcher` on the connection (F-W3) |
| (g) | `etcd_kv_auth_served_on` (merge session's export) | also the md-indexed watch registration at `s`, `E` |
| (i) | `watchUp`, `watchSpec` (v3rpc) | signatures: `R` (for the mode), `tok` |
| (j) | `watchAddrFacts` (`InvClientNewResult.lean:43-53`), `watchConnFacts` (`InvWatch.lean:443-450`) | the md-indexed registration |
| (k) | `New.spec`'s precondition (takes `watchAddrFacts`) | through (j) |
| (l) | the server's watch-registration exports (`v3rpc/Results.lean:1548-1667`) | md-indexed |
| (m) | the cache's restated result (`cache/v3/Results.lean:142`) | through (e)/(j), `n = 0` |
| (n) | `attemptTokOk` | over the metadata (`clientAttemptMdOf`); today's is an instance |
| (o) | `auth.mdTokenOf` | moved to the auth package (no change of meaning) |

## Scope choices (the user's, 2026-10-29)

- **F5, from-key ranges**: the Perennial lemma (an empty slice literal is non-nil, branch
  `slice-literal-nonnull`). Root's watch waits for the pin bump.
- **F6, several members**: a single-member gate (above). Multi-member auth watches are out of scope
  and filed in the plan.

## Dependencies

- H5 (`authStateAt_setup`, the merge session's) for `akAuthFixed`'s read half, so that
  `authPubLb γa n` with `n > 0` has a source.
- Layer 2, (g), (i), (l), (o) are the merge session's files: proposed to `etcd-grove-56`, not
  edited here.
