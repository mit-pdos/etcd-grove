# The watch path over mvcc's API, round 14: specs and invariants (draft, 2026-11-03)

The Lean is in `/home/ubuntu/.claude-D/jobs/e4ba2bf8/tmp/clients/watch/WatchSpecs.lean`. It
typechecks with `lake env lean` from the worktree `mvcc-api` against the round-14 `Api.lean`
(exit 0, about 10 s). Names sit under `v3rpc.W14` and `client.W14`; adopted, they drop the prefix
and replace today's. This draft builds on the assessment `assess-watch.md`. Its gaps G1-G3 are
closed by round 14's A1 (`wsSentLb`), A2 (`wsChan_tryRecv`) and A3 (compaction responses at
revision `0`).

The rule throughout: **v3rpc no longer hands mvcc's internal predicates to the client.** Each
message carries v3rpc's own ghost state (the registry, the received list), the server's certified
lower bound, and the API's pure guarantee `wsRecvOk`, taken at a snapshot.

## (a) The specs that change

### The models (§2)

**`WatchRespM2`.** A response's ghost source becomes `Option (Nat × WResp)`: the index `n` in the
send loop's received list, plus the response. It replaces `Option mvcc.RespM`, whose ghost fields
`w`, `cov`, `regs` and `idx` have no counterpart in the API.

- The wire fields are unchanged: `WatchRespM2.wire` drops the source.
- `pbWatchResponse2` reuses `watchRespMsg`/`watchRespRecv` on the wire fields.
- `mvccResp2`, `ctrlAnswers2`, `idLive2`, `sentEvsOf2`, `fwdEvs2` and `fwdIdx2` are today's, keyed
  by watch id instead of watcher location. Ids are never reused on a stream: `StreamState.cancel`
  keeps the entry.

**`RegInfo`** `{rg, lo, k}` is v3rpc's registry entry: `WInfo` without its filters (always `[]` on
the server) and without liveness.

### The per-message stream spec (§4, replacing `InvWatchStream.lean:532-700`)

**`rcvSnap r rs σ S`** (persistent) is the snapshot of the received list `rs`. It holds:
- `wsRecvOk σ S rs`, and every watcher is unfiltered;
- `histLb σ.notifiedLog` and `crevOk σ.crev` (the server's facts, part (c));
- for each watcher in `S`: `regIs γreg id (regInfoOf w)`, and live or `cancelQ γs id`.

**`mvccOk2 r j m`** replaces `mvccOk`, `mvccExtra` and `mvccCov`. For response `m` at down position
`j`, sourced from received entry `(n, x)` with `pre` received before it and `L` sent before it:
- the down list's lower bound at `L`, `rcvLb γr (pre ++ [x])`, and `rcvSnap r (pre ++ [x]) σ S`;
- the bookkeeping kept from today: `idLive`, the "no earlier copy" uniqueness, `fwdIdx`, `fwdEvs`,
  and "the id's responses with events sent are the id's responses with events received";
- **new:** for a `-1` response, every id live after `L` is in `S`. Every created response in `L`
  was sent before `x` was received (a `-1` is sent right after it is received), so that watcher
  registered before the snapshot.

**`ctrlWatcher2`** replaces `idAssigned`/`watcherIs`/`streamRegAt`/`streamSentLb`. It holds:
- `regIs γreg id i`, `createRangeOk c id i.rg`, and `idTok2 γtok id`;
- `wsSentLb ι i.k` (round 14's A1, which the drain consumes);
- `i.lo` as the start revision, or, for a start revision of `0`, the length of a certified log
  (`histLb Lr`, with `σ.log` at a registration where nothing is pending);
- `watchAuthed`, unchanged.

**`createdAfter2`** holds:
- `regIs γreg id i`, a received list `l` with `i.k ≤ |l|`, and the down list `L` of length `j`;
- every `-1` among `l` has already been sent within `L`.

**`ctrlOk2`, `watchDn2`, `watchStreamSpec2`.** The run `r : WRunA` is existential. It is published
through `streamAuxIs γs (auxOf2 r)`, with `auxOf2 = [γreg, γtok, γr, γa]`; `ι` is not a `GName`,
and no client needs it.

### `watchReqOk` / `upOk` (§5)

- `watchReqOk` is unchanged. The API's `Watch` is only for id `0` (`AutoWatchID`).
- `upOk2` keeps only the create's auth bound. It drops `mvcc.watchTok`, because the API's `Watch`
  takes no budget token.
- It also drops `mvcc.watchNoDup`. v3rpc forwards conjuncts 2 and 3 still conditioned on
  `onceUpTo`, and the client discharges that condition with `srvOnce`.
- `watchUp2` changes the same way.

### The run and the four specs (§6)

**`swsIs2`** replaces today's mvcc part of `swsIs` with:
- `isMvccWatchStream (wspIface wsp) γm ι` and `inv wsN (wsInv r)`;
- `srvWOk (wsIface wsl) W wsN`;
- the stream at `pbWatchResponse2`, `watchStreamSpec2`, and `upOk2`.

Gone: `watchChanInv`, the channel names, `savedProp`/`savedPred` (`progQ`, `cancelQ` as `Ψ`), and
the `γo`/`γc` equalities.

- **`recvLoop.spec`:** gains `threadTok` in its pre and post (`Watch`, `Cancel`, `Rev` and
  `RequestProgressAll` take one), and loses `recvRes`'s `watchReader`.
- **`sendLoop.spec`:** `wsRecv ι [] ∗ monoListAuthOwn γr 1 []` replaces `watchConsumer`. No reader
  slot; the thread bound stays (`GetProgressReportInterval`).
- **`close.spec`:** `closeTok γcl ∗ threadTok` replaces `watchStreamOpen`.
- **`watchServer.Watch.spec`:**
  - takes `srvWOk` and `threadTok`;
  - the stream and its spec are at the new model, with `upOk2`;
  - `watchRunSlot` becomes `R.E.RD ∗ ⌜threadBound …⌝`;
  - it allocates `γreg`/`γtok`/`γr`/`γcl` and `wsInv` from `NewWatchStream`'s
    `wsState ι wsStart ∗ wsRecv ι []`.
- **`NewWatchServer`/`watchSrvOk`:** `mvcc.isWatchableStore wsl E.s γ` becomes `srvWOk`.
  `watchTokPool` is dropped. `WSrv.γ : mvcc.WsNames` goes; `watchAuthed`'s `γ.tag` moves to the
  server's auth tag. The draft keeps `r.srv.γ` there, by reference.

### client/v3's bridges (§8)

These are statements, replacing the mvcc unfolds:

- **`srvEventIdsAssigned2.stmt`** (S3): from conjunct 1 and the snapshot's `regIs`. S2
  (`srvProgressAllAnswers`) is dropped; no proof uses it.
- **`recvEvents.stmt`** replaces `watchRecvOk` in `recv_unfiltered`/`dispatch_content` and
  `reg_pre*`. Given `srvOnce`, the events received for id `X` up to `x` are
  `watchEvents L i.rg i.lo hi`, for a certified `L` with `hi ≤ |L|`.
- **`progressCov.stmt`** replaces `respCov`, `covFact`, `respCompl`, `regsAt`, `chanRegAt` and
  `rsnW` (`WatchRun.lean` ~860-1980, `WatchCompl.lean` ~826, `watchGRPCStream__run.lean` ~2013).
  Its premises:
  - an event-less, non-compaction response at `j`, from received entry `n`;
  - a created response at `p < j`, still live in `L_j`;
  - the response's id is `X` itself or `-1`.

  Its conclusion: the events received for `X` up to `x` equal `watchEvents L rg lo (x.rev+1)`, or
  the response is a `-1` and `cancelQ γs X` holds.

  The argument:
  1. If `n < |l|` (createdAfter2's `l`), then `x = l[n]`, because two `rcvLb`s agree. That `-1`
     would then have been sent before `p`, contradicting `mvccOk2`'s uniqueness. So
     `n ≥ |l| ≥ i.k`.
  2. `X` is in `S` (mvccOk2's new clause), and its entry is `i`, because two `regIs` agree.
  3. If `X` is live, conjunct 3 applies at index `n`. If not, the snapshot gives `cancelQ`.
  4. `onceUpTo` follows from `srvOnce` applied to the snapshot's `histLb` and `crevOk`.
- **`compactResp.stmt`** replaces `mvccOk_cmpPerm`/`cmpOkOf_of_mvccOk` and `reg_pre_cmp`'s shape:
  no events, the watcher's id, revision `0` (A3), and `0 < compactRev ≤ c` with `crevOk c`.
- **`srvWL2 W L := histLb L ∗ ⌜LogSmall L⌝`** replaces `srvWL`'s `mvcc.evLog`. `watchLaws_srv` is
  re-proved over it.
- **`watchSrvFacts` (client InvWatch):** drop `watchTokPool` and S2. `srvNoDupKeys` and the
  examples' `watchNoDup` become `srvOnce W`. `srvLogsSmall` becomes `srvWOk`'s law.

## (b) v3rpc's invariant, and the proof obligations

### The invariant `wsInv r` (§3, at `wsN = nroot.@"v3rpc".@"ws"`)

```
∃ S R T, wsState ι S ∗ ghostMapAuth γreg 1 R ∗ ghostMapAuth γtok 1 T ∗
  ⌜∀ id, R !! id = (S.ws !! id).map regInfoOf ∧ ((T !! id).isSome ↔ (S.ws !! id).isSome)⌝ ∗
  ⌜every watcher's fs = []⌝ ∗ □ ([∗map] id ↦ i ∈ R, regIs γreg id i) ∗
  ([∗map] id ↦ w ∈ S.ws, ⌜w.live⌝ ∨ cancelQ γs id) ∗ (⌜S.closed = false⌝ ∨ closeTok γcl)
```

The send loop keeps `wsRecv ι rs ∗ monoListAuthOwn γr 1 rs` in its own loop invariant, not in
`wsInv`.

### Obligations (§7; statements, proofs still to write)

- **O1, `watch_au`.** recvLoop builds `Watch`'s update at `⊤ \ ↑mvccN` from `swsIs2`. Within one
  update, it opens `wsInv` and the server's peek (`srvPeek`); both namespaces lie inside
  `⊤ \ mvccN` (`srvWOk`'s side conditions), and everything is timeless, so there is no later
  modality to strip. At the commit, on an open stream:
  - insert `id` into `R`, which also gives `regIs` (fresh, because `S.ws !! id = none`), and into
    `T`, which gives `idTok2`;
  - the new watcher is live, so the cancel map is extended trivially.

  `COMM` returns the registry entry, the token, `wsSentLb ι k`, `histLb σ.log`, `σ.pending = none`,
  `lo = watchLo σ startRev` and the range. On a closed stream, the state is unchanged and `id = -1`.
- **O2, `cancel_au`.** recvLoop holds `cancelQ γs id` (from the received cancel request) when it
  calls `Cancel`. The commit applies `S.cancel id`. For the entry that loses liveness, the cancel
  map's disjunct becomes `cancelQ`; `R` is unchanged, since `regInfoOf` ignores `live`.
- **O3, `close_au`.** `close` owns `closeTok`, which is exclusive. So the invariant's disjunct must
  be `S.closed = false`, which is `Close`'s precondition. The commit closes the stream and deposits
  the token.
- **`Rev()` (headers).** The update is the peek with `Q := True`. Today nothing in `watchDn`
  constrains a control response's header revision.
- **O4, `snap_after_recv`.** This runs right after each `recvAu` commit:
  - a ghost step `|={⊤}=>` opens `wsInv` (giving `S`, the persistent `regIs` map and the cancel
    map) and the peek (giving `σ`, `histLb`, `crevOk`);
  - it applies `wsRecv_ok.law` to `isMvccWatchStream ∗ wsRecv ∗ wsState ∗ mvccState`, yielding
    `⌜wsRecvOk σ S rs⌝`;
  - it copies the registry and cancel facts for `S.ws`, using `R`'s relation to `S`;
  - it closes both invariants unchanged.

  The result is `rcvSnap r rs σ S`. The `-1` clause of `mvccOk2` (live ids of `L` are in `S`) comes
  from `regIs` of each created response in `L` (its `ctrlWatcher2`) agreeing with `R`'s authority.
  A watcher cancelled between the receive and the snapshot gets `cancelQ`, which matches
  `progressCov`'s second arm.
- **O5, `drain_empty`.** Before sending a created response for watcher `i`, the drain loops
  `wsChan_tryRecv` with `n := i.k`, using the `wsSentLb ι i.k` from `ctrlWatcher2`.
  - A received response is sent at once if it is a `-1`, and otherwise handled as today.
  - The empty case gives `⌜i.k ≤ |rs|⌝`, and every `-1` in `rs` has been sent.
  - Then `createdAfter2` follows from `rcvLb`, which is taken from the authority.

## (c) What the server must give the watch path (§1, `SrvW` / `srvWOk` / `srvOnce`)

The server's draft defines `γm`, `N`, `histLb` and `crevOk`; their laws are what v3rpc and
client/v3 use.

1. **`mvccState` in an Iris invariant at `N`.** `N` must lie outside `↑mvccN` and outside
   `wsN`.
   - It is exposed as the persistent **peek** `srvPeek`: at any `E ⊇ ↑N`, it gives `σ` with
     `mvccState γm σ`, `histLb σ.notifiedLog`, `crevOk σ.crev`, and a closer for the same `σ`.
     Every watch-path use leaves `σ` unchanged: `Watch`'s and `Rev`'s updates, and the snapshot.
   - The apply thread's writes (`Write`/`End`'s two updates) must also go through this invariant,
     so that `mvccState` is never held thread-locally.
2. **`histLb L`.** A persistent, certified lower bound of the *notified* log, including the pending
   revision. The server must mint its certificate before `End`'s `notify`, as `certOk` is today.
   Laws:
   - agreement: any two bounds are prefix-comparable;
   - prefix closure;
   - (round 16) `histLb L ⊢ ⌜LogWf' L ∧ L.length < 2^63 ∧ LogSmall L ∧ LogPutsLe etcdKeyMax L⌝`.
     `LogWf'` and the length come from `mvccState_reachable`. `LogSmall` comes from the receipt
     `⧖ (logCh σ.notifiedLog)` that the server keeps, which the notify steps now give, with
     `receiptBound ≤ 2^62`. `LogPutsLe` comes from the server's request checks.
   - `histLb [[],[]]` at boot (`watchkv/Served.lean`'s `cert0_of_server`);
   - the client model's laws that `watchLaws_srv` (`cli/InvWatch.lean:425`) takes today from
     `evLog`: `etcdReached` of its revisions (`etcdReached_of_certOk`), `srvEtcdState`/`srvStep`
     (`etcdState`/`EtcdStep`) over it, and `LogPutsLe` for its keys (`srvKVCoreM_keys`).
3. **`crevOk c`.** Persistent: `c = -1`, or `c > 0` permitted by the cluster, and downward closed
   to the client's `kvCmpPermit`. The API only bounds a compaction response by `compactRev ≤ crev`;
   today it gets the exact `crevPermAt compactRev`. `kvCmpPermit_le` makes `≤` enough.
4. **`srvOnce W`** (the client's premise; it replaces `watchNoDup`/`srvNoDupKeys` on the watch
   path): `histLb L ∗ crevOk c ={⊤}=∗ ⌜onceUpTo L lo c⌝`.
   - For a cluster that never compacts, the server must let it show `crevOk c → c = -1`: no
     compaction permit is ever issued. Today this is the store's mode `cm = false`; the API has no
     mode.
   - For `compactkv`, it comes from `srvNoDupKeys` restated over `histLb`.

## Gaps

- **W1 (open; affects every handler under the API): where the handler's `threadTok` comes from.**
  The API's `Close`, `Watch`, `Cancel`, `Rev` and `Read` take a thread token. recvLoop and sendLoop
  are forked, so they get one from `wp_fork_tok_body`. But `watchServer.Watch` (the gRPC handler,
  which calls `sws.close()`) has none in today's grpc handler contract: no `threadTok` anywhere in
  `Proof/google_golang_org/grpc`. Repair: grpc's stream and unary handler contracts lend the
  handler goroutine's token. This is a trusted-model change in `InvGrpcStream`, shared with the
  KV path. Alternatively, `close` could run in a goroutine that holds one, but the Go code is fixed.
- **W2: `WSrv.γ : mvcc.WsNames` disappears.** `watchAuthed`/`auth.modeTag γ.tag` must take the
  auth tag from the server's environment. This is mechanical; the draft keeps `r.srv.γ` by
  reference.
- **W3: the model type changes** (`WatchRespM` to `WatchRespM2`, `pbWatchResponse2`). Every
  `downLbW`, `watchRespMsg` and `src` use is touched in v3rpc's `WatchSendModel`/`WatchSendHist`
  and in the client's `WatchClientModel`. The change is mechanical.
- **W4: compaction through the watch path is now live.** `noCompactor` is gone, so v3rpc's sendLoop
  must handle compaction responses as today's D6 code does, for every server. What follows a
  compaction response for its watcher is unspecified by the API ("Open"); the client already treats
  it as the substream's end.
- **W5 (minor): no stated source for `-1` responses.** The API does not say that `-1` responses
  come only from `RequestProgressAll`. Nothing needs it, since S2 is dropped.
- **W6 (proof-side): agreement of the received-list bounds.** `rcvLb` agreement (two lower bounds
  of one mono list are prefix-comparable) and `regIs` agreement are needed in `progressCov`; both
  exist in Perennial (`monoListLbOwn` and `ghostMapElem` agreement).
- **Not drafted, by reference:** the other thirteen field points-to of `swsIs`, `ctrlP` over
  `ctrlOk2`, the send loop's internal `SendInv`/`sendSt` re-keyed by id, the examples' `Served`
  lemmas (`watchRunSlot` becomes `R.E.RD`, `watchNoDup` becomes `srvOnce`), and `Results.lean`'s
  restatement, which follows the server's.

## Update for API rounds 15-16 and the cross-review (`xreview-clients.md` §1, §6, §11)

The scratch file still typechecks: `lake env lean`, exit 0, against `mvcc-api` HEAD `01c2e43415`
(which contains `d810bc697a`; its `ApiState.olean` is round 16's). Three edits:
- `SrvW` gains `kv`;
- `srvWOk W wsl wsN` states `⌜W.kv = wsIface wsl⌝`, and its `LogSmall` law becomes the four-fact
  law below;
- `srvWL2 W L := W.histLb L`.

### 1. The watch path's `LogSmall` / `LogWf'` needs

**Per-result facts do not suffice.** Each place below states a fact about the log's *states*
(`stateAt L r`, every key-value at a revision), not only about the events delivered:

| Today | Fact used | Comes from |
|---|---|---|
| `cli/InvWatch.lean:248` `srvWL` (`LogSmall ∧ LogPutsLe`) | the client's `etcdState`/`EtcdStep` of the log | `stateAt_client_revs` (0 < createRev ≤ modRev ≤ r, 0 < version, for every key-value of a state) |
| `cli/InvWatch.lean:317` `srvLogsSmall` | `LogSmall` of a sealed log | used by `stepCert_of_watch` (`WatchCompl.lean:306`) and `sealed_logOk` (`WatchFire.lean:68`) |
| `v3rpc/HistoryModel.lean:57` `histLog` (`LogWf' ∧ length < 2^63 ∧ LogSmall ∧ LogPutsLe`) | the history's states | `stateAt_client_revs` at `:152` |
| `v3rpc/ClientModel.lean:96-99` `srvLog` (`idxSealed ∗ LogSmall ∧ LogPutsLe`) | the same | `:157-166`, `:203` |
| `WatchContent.lean:65` `evsOfRevM_state` | an event's key-value is in the state at its revision | `LogWf'`, the length (and no duplicate keys) |

Round 16 adds positivity to `wsRecvOk`: each event's `modRev`, and a put's `createRev` and
`version`. That covers only the delivered events' own values. It cannot give a progress response's
state (`histEtcdState` at a revision under a prefix includes key-values never delivered as events),
nor `createRev ≤ modRev ≤ r`, nor the cache's chain of steps.

**So the restatement is over `histLb` with its receipt.** The exact law I need from the server
(in the draft's `srvWOk`; the server can state it as part of `histLb_model.law`):

```
□ ∀ L, histLb L -∗ ⌜mvcc.LogWf' L ∧ L.length < 2 ^ 63 ∧ txn.LogSmall L ∧ mvcc.LogPutsLe etcdKeyMax L⌝
```

- The server keeps `⧖ (logCh σ.notifiedLog)` next to the bound (xreview §1's resolution, now the
  API's notify, `Put` and `DeleteRange` updates).
- `LogWf'` and the length come from `mvccState_reachable` at the peeked state: `MvccReachable σ`
  gives `LogWf σ.notifiedLog`. That is a pure induction; the cleanest home is the API, as a pure
  lemma in `ApiState` (`MvccReachable σ → LogWf σ.notifiedLog`), so that no client proves it.
- `LogPutsLe` is the server's own: its gRPC key-length checks (`srvKVCoreM_keys`).

With this law:
- `srvWL2 W L := W.histLb L`;
- `histLog` and `srvLog` become `histLb` (the receipt and the pure conjuncts follow from the law);
- `srvLogsSmall` and `sealed_logOk` go.

`watchLaws_srv` needs, besides this, the server's §6b `histLb_model.law`: `etcdReached`,
`srvEtcdState`/`srvStep`, over `histLb`.

### 2. §6c and §6d

- **§6c, the tie:** the server must state `⌜E.kv = interface.mkOk (go.GoType.PointerType
  watchableStore.ty) #wsl⌝` for the `wsl` it hands `NewWatchServer`. This goes in `watchSrvOk` /
  `srvKVInvsA`, or as `∃ wsl, ⌜E.kv = wsIface wsl⌝ ∗ srvKVAddr s ↦□ E.kv`, which matches
  `NewWatchServer`'s `srvKVAddr s ↦□ wsIface wsl` by agreement. It is needed because
  `shapes.law`'s first conjunct gives only `isKV` from `isMvcc`. `NewWatchStream`'s contract comes
  from its per-type conjunct, at `watchableStore`. In the draft this is `srvWOk`'s
  `⌜W.kv = wsIface wsl⌝`.
- **§6d, a dependency:** the peek strips no later modality, so every conjunct of the server's
  `kvStoreInv` must be timeless. This includes `kvNx`'s raft `isCommittedLogLb` (`InvNode.lean:89`,
  `@[no_expose]`). raft's API must export `Timeless (isCommittedLogLb ..)`, as an instance or a
  law. Otherwise `srvPeek` needs a `▷` and `£ 1` from its callers: `Watch`'s update, `Rev`'s
  update, and the snapshot after each receive. The snapshot is a ghost step with no credit at hand,
  so a `▷` there would need `wp_recv`'s credit plumbing.

### 3. §11: the mvcc-internal names the draft uses

- **In terms, in the draft:**
  - `mvcc.Log`, `mvcc.EvM`, `mvcc.WatchRange`;
  - `mvcc.watchRangeOf`, `mvcc.watchEvents`;
  - `mvcc.LogWf'`, `mvcc.LogPutsLe` (new in the law above);
  - `mvcc.Assumptions` (the package-semantics class);
  - `txn.LogSmall` (txn's, not mvcc's); `etcdKeyMax` (cache's model).
- **Through v3rpc definitions the draft reuses:**
  - `mvcc.evIs` (in `watchRespMsg`/`watchRespRecv`; also in the API's own `wrespIs`);
  - `mvcc.RespM`: today's `WatchRespM.src` type, which `WatchRespM2.wire` still builds. It goes
    when `WatchRespM2` replaces `WatchRespM`.
  - `mvcc.WsNames`: `WSrv.γ`, which `watchAuthed`'s `γ.tag` reads (W2: it goes once the auth tag
    moves to the server's environment).
- **In the client proofs the bridges feed (by reference; pure model, to re-export):**
  - `stateAt`, `applyChanges`, `findKey`, `Change`, `evsOfRevM`, `evType`;
  - `filtered` (with a `filtered [] = id` lemma, since the server's watchers are unfiltered);
  - `watchEvents_append`, `watchEvents_empty`, `logEvents`, `logEvents_prefix`;
  - `LogWf'` lemmas, `LogPutsLe`, `NoDupKeysPerRev` (txn);
  - `mvcc.kvPtrFixed`: an Iris predicate, the read-only key-value an event points to. Re-export it,
    or restate the client's use over `evIs`.
- **Gone from the watch path:** `evLog`, `idxSealed`, `idxCert`, `certOk`, `crevPermAt`,
  `watchNoDup`, `noDupKeys`, `watchTok(Pool)`, `watchReader`, `watcherIs`, `idAssigned`, `idTok`,
  `chanRegAt`, `respCov`, `covFact`, `respCompl`, `regsAt`, `rsnFor`, `progFact`.

### 4. W3-W5

None of them needs an API change:
- **W3**, the model type change, is internal to v3rpc and the client.
- **W4**, compaction responses being live: A3's revision `0` is the only API fact used.
- **W5**, no stated source for `-1` responses: nothing needs it.

**W1 is unchanged and outside the API:** the gRPC handler's `threadTok`.
