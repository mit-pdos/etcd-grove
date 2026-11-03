# The encoded-size bound at grpc's send side (2026-10-30, branch `invoke-size`)

The repair of `grpc.ClientConn.Invoke.wp_proof` and `grpc.ClientConn.NewStream.wp_proof`, which
the axiom review `axiom/txn-nested-wire` refuted. grpc v1.84's `codecV2.Marshal` allocates
`proto.Size` bytes before checking any size (`issues/grpc-codec-alloc-before-size-check.md`, on
`axiom/txn-nested-wire` `b157b99a97`). The design was approved by the user on 2026-10-30 (Q1-Q6); it
is recorded in `notes/decisions.md`, "The encoded-size bound at grpc's send side". This file
records the state of the change and what `txn-nested` must fold.

## State: partial (passes 1, 2, the cache's part of pass 3; concurrency: the prefix and value bounds, the STM)

**Done (builds: `Proof.go_etcd_io.etcd.client.v3.Link`, `Results`, `ResultsOn`, `ClientPutGet`,
the adapters `KMGet`, `KMPut`, `KMTxn`, `KMWatch`, `KMClient`, `ServerKVGet`, `ServerKVPut`,
`ServerKVTxn`, `ServerWatcher`; `Proof.go_etcd_io.etcd.cache.v3.Results`):**

- **Pass 1, the gRPC layer and the client** (`9cf7e979f1`).
  - `grpcMsgMax`, `ProtoMsg.wireLen` and `grpcInvokerOk`'s premise are in
    `Proof/google_golang_org/grpc/InvGrpc.lean`.
  - `StreamMsg.wireLen` and the `SendMsg`/`Send` premise are in `InvGrpcStream.lean`.
  - Each request instance has a `wireLen`, and the whole-struct sends pin
    `unknownFields' = slice.nil`. The instances are in `InvKVConn`, `InvAuthConn`,
    `InvClientAuth`, `InvLease`, `InvLessor` and `v3rpc.InvWatchStream`.
  - `reqOpAt`'s put case gains `o.ignoreValue = true → o.val = []` (W2).
  - The client's specs from the interceptor up gain the premise:
    - the stubs and the retry clients;
    - `kv.Do`/`Put`/`Get`/`Delete` and `txn.Commit` (`spec`, `specM`, `specG`);
    - the auth client (`strsSizeOk`, with the credentials' bound in `clientAuthAt`/`clientAuthPre`);
    - `watcher.Watch` (`watchSizeOk`).
  - The client results take `hsz`:
    - `client_*_any`, `_end_to_end`, `client_get_after_put`, `client_*_on`;
    - `client_{Put_own,Get_own,Get_st,Put_rep,Put_any,Put_st,Delete_st,Put_kv}`.
- **Pass 2, cache/v3's client contracts and their adapters** (`99650e0ced`).
  - Each operation of the contracts takes the size premise as a last pure conjunct:
    - the gets (`opSizeOk (opGetModel key gs)`): `isEtcdKV`, `isEtcdKVE`, `isEtcdKVTodo`;
    - the watches (`watchSizeOk (opWatchModel key gs)`): `isEtcdWatcher`, `isEtcdRangeWatcher`;
    - the deletes and puts (`opSizeOk`): `isEtcdDeleteKV`, `isEtcdDeleteKVTodo`, `isEtcdPutKVTodo`;
    - every builder's `Commit` (`txnSizeOk b.model`): `txnBuilderSpec`/`X`, `txnCommitErrTodo`,
      `txnBuilderSpecO`;
    - `readTxnBuilderSpec`'s `Commit` (`txnSizeOk (readTxn os)`, a new definition);
    - `isEtcdDoKV` (`opSizeOk o`).
  - The adapters pass it on; the client's `txnSizeOk_wireOf` takes the model's bound to the wire's.
  - Where the vocabulary lives:
    - the payload predicates, `opWireLen`, `wireSlack` and the option laws are in the client's `InvOp`
      (the contracts import it);
    - `cmpWireLen`, `TxnOp.wireLen`, `txnWireLen` and `txnSizeOk` are in `cache/v3/InvEtcdTxn`,
      beside `TxnModel`;
    - the laws against `grpcMsgMax` stay in `InvKVConn`.
  - The scalar options' keep laws are added to `InvOp`: `withLimitM_keep`, `withRevM_keep`, ...,
    `withSortM_keep`.
- **Pass 3, the cache.**
  - `New.spec` and `newCache.spec` take `pfx.length ≤ 2 ^ 28`.
  - `isCacheFields` keeps it (`"%Hpfx"`).
  - The cache's get, `serverRevision`'s get and `watchEvents`' watch discharge their premises by
    `cacheGet_size`, `cacheRev_size` and `cacheWatch_size` (`InvCache.lean`).
  - `cache_end_to_end_client` and `cache_end_to_end_new` take `hpl`.

**Left (the build is red from these on):**

1. **concurrency.**
   - The objects need the bound kept in their invariants: `isMutex`, the election, the session's
     users. The constructors `NewMutex`, `NewElection`, `ResumeElection` need a prefix bound;
     `Campaign`/`Proclaim` a value bound.
   - About 16 contract calls to discharge: `Mutex__{Lock,TryLock,Unlock,tryAcquire}`,
     `Election__{Campaign,Proclaim,Resign,Leader,observe}`, `waitDelete(s)`,
     `stm__{commit,fetch}`, `stmSerializable__commit`.
   - The STM needs per-call bounds (Q6), tracked through its read and write sets, so that `commit`'s
     transaction has `txnSizeOk`.
   - **A statement beyond the draft is needed here: stopped.** The servers
     `server/v3/etcdserver/api/v3lock` (`lockServer.Lock`, `Defs.lean:52`: `∀ pfx, isEtcdMutexClient
     c pfx`) and `v3election` build mutexes and elections on prefixes taken from the request they
     received (`req.Name`). Their proofs cannot meet `NewMutex`'s prefix bound unless one of these
     is decided:
     - (a) the received request's size is bounded, a new trusted fact about grpc's server receive
       (`MaxRecvMsgSize`);
     - (b) the servers' specs take a premise on `req.Name`, a new statement of registered
       handlers, which nothing can discharge for a request off the wire;
     - (c) the contract keeps no size premise for the uncovered case, and the size goes to an
       error branch.

     The draft's section 7 does not list these two servers.

     **Plan for concurrency (not started).** It does not build: 14 proofs broken since pass 2
     (`Mutex__{Unlock,TryLock,Lock,tryAcquire}`, `Election__{Leader,Resign,Proclaim,Campaign,observe}`,
     `waitDelete`, `waitDeletes`, `stm__commit`, `stm__fetch`, `stmSerializable__commit`). Bounds:
     - `NewMutex`/`NewElection`/`ResumeElection` take a prefix of `2 ^ 27` bytes or less, kept in
       `isMutex`/the election's predicate. `tryAcquire`'s transaction carries the key three times
       and the prefix's range four times: 7 · 2^27 plus slack is under `2 ^ 30`.
     - The held key (`pfx ++` the lease in hex, or `ResumeElection`'s `key`) needs a length bound
       in the mutex's and election's state, for `Unlock`/`Resign`/`Proclaim`.
     - `Campaign`/`Proclaim` take a value of `2 ^ 28` bytes or less.
     - STM: per-call key and value bounds (Q6).
     The receive-size fact gives the servers `< 2 ^ 27` for each field (`grpcRecvBytesOk.lt`), which
     meets all of these.

     **Decided (2026-10-30): (a)**, stated in code ("Receive-size fact" below); the servers' proofs
     use it once `concurrency` takes its bounds.

     **Progress (2026-10-30, `2be4b6c12a`).** Done: `isMutex`/`isElection` keep `pfx.length ≤ 2 ^ 27`
     (in the pure conjunct with `pfx ≠ []`); `NewMutex`/`NewElection` take `pfx.length < 2 ^ 27`
     (the prefix before its `/`), `ResumeElection` `pfx.length ≤ 2 ^ 27`; `ownerOp_size`,
     `lastCreateOp_size`, `keyOp_size` (`InvMutexLemmas`); `Election.Leader` builds; the Lock and
     Election servers (`lockServer.Lock`, `electionServer.{Campaign,Leader,Proclaim,Resign}`) discharge
     the constructors' bounds by `grpcRecvBytesOk.lt` and build.

     **Stopped: two statements the plan assumed do not hold** (questions for the user):
     - **The held key has no length bound in the model.** `tryAcquire` and `Campaign` build the key
       with `fmt.Sprintf("%s%x", pfx, lease)`. `SprintfOut` (Perennial `Proof/fmt/Base.lean`) models
       only `%s`, `%d`, `%v`, `%0Nd`, `%%`; at `%x` the rest of the output is arbitrary
       (`SprintfOut.other`; Perennial's `TrustedCode/fmt.lean` emits `arbitraryString()`). So the key is
       `pfx ++` an unbounded string, and `acquireTxn`'s `txnSizeOk`, `Unlock`'s delete, `Lock`'s get,
       `Campaign`'s transaction, `Proclaim`/`Resign` cannot be discharged. Blocks
       `Mutex__{tryAcquire,TryLock,Lock,Unlock}`, `Election__{Campaign,Proclaim,Resign}`. A fix:
       `%x` of an integer in Perennial's `Sprintf` model and `SprintfOut` (lower-case hex, at most 16
       digits and a sign), a general change on its own Perennial branch, then a pin bump. (The
       `fmt.SprintfNamed` axiom here is stated over `SprintfOut`, so it would follow.)
     - **Keys read from etcd's state have no length bound in the model.** `waitDeletes` watches (through
       `waitDelete`) the key its get returned (`string(resp.Kvs[0].Key)`), and `Election.observe` the
       leader's key `string(kv.Key)`; `isEtcdRangeWatcher` needs `watchSizeOk`. `etcdState`/`EtcdStateWf`
       say nothing of key lengths (etcd's server bounds a stored key by its request limit, but the
       client-side model does not carry it). Blocks `waitDelete`, `waitDeletes`, `Election__observe`
       (and through `waitDeletes`, `Lock` and `Campaign`). Options: (a) a key-length fact on etcd's
       state (`EtcdStateWf` or `etcdState`: every key at most the server's limit), a trusted fact about
       the client's model of etcd, justified by the server's request limit; (b) `waitDelete`'s watch
       takes a key-length premise, and `waitDeletes`/`observe` get it from (a) anyway.

     **The user's decisions (2026-10-30):** (1) `%x`: a general Perennial change (`SprintfOut` models
     `%x` of an integer), then a pin bump, by another agent: the Sprintf-blocked proofs wait for the
     pin. (2) A key-length invariant in `EtcdStateWf` (every key at most `2 ^ 27`), proved from the
     server's receive limit where the adapters prove the contracts, drafted spec-first by another
     agent: the proofs blocked on it wait. (3) The STM as proposed: approved, done (`58ac7ee604`;
     `notes/decisions.md`, "The STM's sizes").

     **Done since (`58ac7ee604`):**
     - The STM: `STMSt.n`, `STMCallOk`, `STMSizeOk` (in `stmState`), `stmKeyMax = 2 ^ 20`,
       `stmCallMax = 2 ^ 8`, `applySpec pfx P`, `NewSTM`'s prefetch premise; `stm__commit`,
       `stm__fetch`, `stmSerializable__commit` and every STM proof build.
     - `NewLocker` takes `NewMutex`'s prefix bound (missed in `2be4b6c12a`).
     - `Election.Campaign`/`Proclaim` take `val.length ≤ 2 ^ 28` (statements; their proofs wait for
       (1) and (2)); `electionServer.Campaign`/`Proclaim` discharge it by `grpcRecvBytesOk.lt`.
     - Builds: every `concurrency` module but those below; the v3lock and v3election handler proofs.

     **Still blocked:**
     - On (1) (`%x`): `Mutex__{tryAcquire,TryLock,Lock,Unlock}`, `Election__{Campaign,Proclaim,Resign}`.
       They also need the held key's bound in `mutexState`/`electionState` (the plan's), and
       `ResumeElection` a bound on its `leaderKey` (the servers have `< 2 ^ 27` from the receive fact).
     - On (2) (keys from etcd's state): `waitDelete`, `waitDeletes`, `Election__observe` (and `Lock`,
       `Campaign` through `waitDeletes`).
     - So `concurrency`'s `Link`/`Results` and v3lock's/v3election's `Link`/`Results` do not build yet.

     **Done (2026-10-31, after the pin `d62b13ac1` and the key-length law):** `tryAcquire` and
     `Campaign` bound their key by Perennial's `SprintfOut.str_x_named_int64` (`LeaseID` is a named
     `int64` with no formatting method): at most `pfx.length + 17` bytes. `mutexState` and
     `electionState` keep the held key at most `2 ^ 28` bytes; `ResumeElection` takes that bound on
     its `leaderKey` (`electionServer.Proclaim`/`Resign` prove it by `grpcRecvBytesOk.lt`). The
     transactions' sizes are computed exactly (`acquireTxn_size`: the key three times and the owner
     get twice, about `7 · 2 ^ 27`; `campaignTxn_size`, `proclaimTxn_size`, `resignTxn_size`).
     `Election.observe` takes the owner get's `ownerOp_size` and the prefix watch's
     `watchSizeOk_opWatchModel`. Every `concurrency` module, its `Link`/`Results`, and v3lock's and
     v3election's build.
     - The examples using the STM (`lintest`, `linkvtxn`, `k8setcd3`, `kv`, `linkv3p`, `kvreconf`) need
       `applySpec`'s `P` and the per-call premises: pass 4.

2. **leasing**: each KV operation of the leasing KV gains the client's predicate. Its own
   transactions (key and lease key) must fit `txnBuilderSpecO`'s `txnSizeOk`; `isEtcdDoKV`'s get
   too.
3. **recipes** (`experimental/recipes`): the constructors gain a prefix bound kept in the object,
   and `Enqueue` a value bound.
4. **k8s**: `kubernetes.Client.{Get,OptimisticPut,OptimisticDelete}` (`client_range_any`/`txn_any`
   now take `hsz`) and the etcd3 store's specs (key and encoded-object bounds), up to the cacher
   and `k8setcd3`.
5. **The examples' closed theorems.** The size facts are discharged inside each one:
   - `GenKv` and `common.Writer.spec`;
   - linkvtxn's `GenIn`, which needs `txnSizeOk_of_bounds` (L-s4, not yet written);
   - k8setcd3's `GenIn`;
   - authkv's `ClientOn` (`client_put_on`);
   - cachekv (`New`'s `pfx` bound, `"ck/"`);
   - linkv3p's `MainWatch`.
6. **The checks.** None has been run: the full build, `etc/tcb-report.py --check` and the
   collections, `etc/api-check.py`, `etc/gen-interface.py --check --layout`, `gen-link`,
   `gen-init`.

**Possible follow-up, not done:** the adapters' "Todo" premises still have no size premise:
`kmTxnUncoveredTodo`, `kmPutRestTodo`, `kvLeasedPutTodo`, `kvLeasedCommitTodo`. They are premises
about the uncovered client calls, which reach the same `Invoke`. A size premise would make them
weaker and more honest, but they are statements the draft does not list.

## Receive-size fact

The user chose (a) (2026-10-30). The fact, in
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/RecvLimit.lean` (namespace
`Perennial.EtcdGrove.v3rpc`):

```lean
def grpcOverheadBytes : Nat := 512 * 1024
def etcdMaxRecvMsgSize (maxReq : Nat) : Nat := maxReq + grpcOverheadBytes
def etcdMaxRequestBytesOk (maxReq : Nat) : Prop := etcdMaxRecvMsgSize maxReq < 2 ^ 27
theorem etcdMaxRequestBytesOk_default : etcdMaxRequestBytesOk (3 * 2 ^ 19)
/-- The receive-size fact: a `bytes` field `b` of a request grpc's server decoded under the
receive limit `lim` is at most `lim` bytes long. -/
def grpcRecvBytesOk (lim : Nat) (b : GoString) : Prop := b.length ≤ lim
```

It is a premise of the handlers' specs, where grpc's runtime is the caller. Each spec quantifies
`maxReq` (the configuration's `MaxRequestBytes`) and takes `⌜v3rpc.etcdMaxRequestBytesOk
maxReq⌝`, plus `⌜v3rpc.grpcRecvBytesOk (v3rpc.etcdMaxRecvMsgSize maxReq) b⌝` for each field `b`:

- `lockServer.Lock`: `Name`;
- `electionServer.Campaign`: `Name`, `Value`;
- `electionServer.Leader`: `Name`;
- `electionServer.Proclaim`: the leader's `Name` and `Key` (in the leader branch), `Value`;
- `electionServer.Resign`: the leader's `Name` and `Key` (in the leader branch).

**Soundness.**

- grpc v1.84 checks the frame's length against `maxReceiveMessageSize` before reading it
  (`parser.recvMsg`, `rpc_util.go:797`), and the decompressed size too (`decompress`).
- etcd sets the limit to `MaxRequestBytes + 512 KiB` (`v3rpc/grpc.go:74`).
- `proto.Unmarshal` (`v3rpc.codec`) copies each `bytes` field out of the message, so a field is no
  longer than the message.
- The fact is not stated over `wireLen`. `wireLen` is an upper bound (it adds `wireSlack` per
  node), so `wireLen ≤ limit` would be false.
- Not covered: a `MaxRecvMsgSize` in `GRPCAdditionalServerOptions`, which would replace etcd's.

`notes/decisions.md`, "The receive-size fact"; `notes/audit.md`, its row.

## Departures from the approved draft

- `wireSlack` and the payload predicates are in the client's `InvOp`, not in `InvKVConn`.
  `txnWireLen`/`txnSizeOk` are in `cache/v3/InvEtcdTxn`, so that cache/v3's contracts can state
  them (`InvKVConn` imports the contracts).
- `readTxnBuilderSpec`'s `Commit` bounds `readTxn os` (a new definition: the read transaction's
  gets).
- `pbTxnRequest.send` also pins the top-level `TxnRequest`'s `unknownFields` (an extension of W3).
- The lease stubs and retry clients (`LeaseGrant`, `LeaseRevoke`) gain the `unknownFields` premise.
  The draft had "unchanged".
- `Op.toRangeRequest.spec`'s post (internal) also gives `req.unknownFields' = slice.nil`.
- The watch has no filters bound: `createOf` has `filters := []`.
- `watcher.Watch`'s premise is `watchSizeOk` (key and range end), not `opSizeOk`, because a watch
  sends no value. With `opSizeOk`, the adapter could not bound a value the options might set.
- L-s5 takes the `OpShape`/`optsKeep` form: options that keep `key ≤ K`, `rangeEnd ≤ E` and
  `val ≤ V`, with `K + E + V ≤ 2 ^ 30`.
- The client results take the size as a Lean hypothesis (`hsz`), as `client_txn_any` already took
  `hp`/`hin`, rather than as a pure conjunct in the pre.

## What `txn-nested` must fold (from `lean` at this branch)

- **D1** `reqOpAt` (`Proof/go_etcd_io/etcd/client/v3/InvKVConn.lean:537`): the put case is
  `⌜op = txn.putTxnOp o ∧ (o.ignoreValue = true → o.val = [])⌝`. `reqOpAt_put` (`:601`) takes
  `(hv : o.ignoreValue = true → o.val = [])`. The nested case is unchanged: its bound is
  `TxnOp.wireLen`'s `.txn` case (`Proof/go_etcd_io/etcd/cache/v3/InvEtcdTxn.lean:167`).
- **S2** `Op.toRequestOp.spec` (`Spec/go_etcd_io/etcd/client/v3/Op__toRequestOp.lean:31`): on
  `lean`, the leaf premise is `(o.t = W64 1 ∨ o.t = W64 2 ∨ o.t = W64 3) ∧ (o.t = W64 2 →
  o.ignoreValue = true → o.val = [])`.
  - On `txn-nested`, **S2/S4** (`Op.toTxnRequest.spec`) take it for every leaf: `∀ o ∈
    t.leaves, …`.
  - `txn.Then`/`Else` pass `⟨Ht123, txnOpOf_put_val Hto⟩` (`txnOpOf_put_val`,
    `InvKVConn.lean:227`).
- **L5** `OpT.txnOp_leaves` (and L4 `opsAt_leaves`/`txnOps_leaves`): the conclusion gains the
  conjunct, from `txnOpOf_put_val`.
- **R1** `client_txn_on` (`Proof/go_etcd_io/etcd/client/v3/ResultsOn.lean:322`): `(hsz : txnSizeOk
  (txnWireOf b.model))`. The same hypothesis is on `client_txn_any` (`Results.lean:2002`) and
  `client_txn_end_to_end` (`:2315`).
- **The auth-off `txn.Commit`** (`Spec/go_etcd_io/etcd/client/v3/txn__Commit.lean:50`, `specM`/`specG`
  at `Proof/go_etcd_io/etcd/client/v3/KVMembers.lean:152,270`): the pre's last conjunct is
  `⌜txnSizeOk (txnWireOf b.model)⌝`.
- **`txnBuilderSpecO`'s `Commit`** (`Proof/go_etcd_io/etcd/cache/v3/InvEtcdTxnOwn.lean:449`):
  `⌜b.model.Under pfx ∧ txnSizeOk b.model⌝`. txn-nested's own nested-op builder is the same
  definition, so the fold is its `Commit`'s pure gaining `∧ txnSizeOk b.model`.
- **Unchanged:** D3 `etcdTxnSpecOn`, D4 `txnUpdAtOn`, S1, S3, S5, D2 and N1–N4. The size is the
  sender's obligation to grpc, not part of the registered spec.

## Pass 4: the examples (2026-10-31)

The size facts are discharged inside each closed theorem; no closed theorem's statement changes.

- `common.wkvSizeOk` (`common/WatchBase.lean`): a pair whose key and value are at most `2 ^ 28`
  bytes, `wkvSizeOk.put` its put's `opSizeOk`, `GenKv.sizeOk` from `GenKv` with short keys. The
  writers (`common.Writer.spec`, `linkv3p.writer.spec`) take it of every pair tried; watchkv's,
  cachekv's and linkv3p's Mains prove it from `GenAll`'s `GenKv`.
- `linkv3p.client_Put_km` and `authkv.client_Put_on` take their put's `opSizeOk`; authkv's `SetUp`
  proves it of its keys (`setupKeys`, by `decide`) and the admin calls' `strsSizeOk`.
- authkv after `lean`'s Main (2026-10-31, the merge `7e4b39d3a1`): `ClientOn`'s other wrappers
  (`client_Put_onG`, `client_Get_on`, `client_Delete_on`) and `WorkCalls`' `work_put`,
  `work_delete`, `work_get`, `work_commit` take their request's `opSizeOk`/`txnSizeOk`, which
  `Work` proves (`keyOfK_principal_le`: a principal's key `x/who/n` within `2 ^ 20`;
  `akPut_sizeOk`, `akDelete_sizeOk`, `akRange_sizeOk`, `akPrefix_sizeOk`; `t1M_size`..`t3M_size`
  by `txnSizeOk_of_bounds`); `newUserClient.spec` takes `strsSizeOk [name, pw]` (`New`'s
  credentialed case), which `Main` proves of its literals; `Main`'s last put its literal's.
  `MainServe` takes `watchLaws_srv` from the member's `srvKVFacts` (keylen). `Main.spec` unchanged.
- putget, putget3, putgetc: their literals; cachekv: its prefix's length (`New`).
- linkvtxn: `GenIn` gains `minBytesLe inMax` of the decoded input (`inMax = 2 ^ 20`: every key and
  value, a comparison's key and value too), which `genFrom` proves; `callGet`, `callPut`,
  `callDel` take their strings' bounds and `callTxn` `minBytesLe` of its transaction, from `GenIn`
  in `call`; `txnSizeOk_txnOf` bounds the transaction (`txnSizeOk_of_bounds`, at most five
  nodes, `decIn_txn_length`). linkvtxn builds.
- k8setcd3: `GenIn` gains `x.Val'.length ≤ 2 ^ 20` (`genFrom`: the workload's values); `call`
  takes it (from `Apply`) and proves the store's key bound (from `InOk`) and `Create`'s
  `storedSizeOk`; `seedOne` its put.
- **Left, k8setcd3's `call`, the Update branch** (`call.lean`, BLOCKED): `GuaranteedUpdate.spec`
  takes `storedSizeOk` of every result of the update function from any object. `call`'s
  function on a no-op input returns the object it read, whose value nothing bounds. Closing it
  needs a change to `GuaranteedUpdate`'s exported premise (e.g. only for an object whose stored
  value fits, or only for a result that is written), beyond what pass 4 may change.

  **The user's choice (2026-10-31), "only for a result that is written", does not close it.**
  Checked against the code: (1) Go's `GuaranteedUpdate` skips the write only when
  `!origState.stale && bytes.Equal(data, origState.data)`, so a stale reading is written even
  when its encoding equals the stored bytes; a premise "when the encoding differs from the stored
  bytes" is unprovable in `GuaranteedUpdate` for a general codec (the stale, equal case writes with
  no bound), and the faithful one is "when stale or different" (`fromS v = some (d, stl)`,
  `decode d = some o`, `f o n = .ok o'`, `stl = true ∨ encode o' ≠ d`). (2) Even that does not
  close k8setcd3's branch: `driverCodec` decodes both tags, and the driver seeds keys with the old
  `v0:` encoding (`encodeV0`, `k8setcd3.go:763`), so a no-op update of a seeded key re-encodes it
  with `v1:` (different bytes: written), and the write is as long as the stored value, which no
  fact of the model bounds. Closing it needs a bound on a stored value: a value-length law on
  etcd's state like `etcdState_keys` (a new trusted fact, justified by the same request limit),
  or a premise of `GuaranteedUpdate` that the stored value fits, which its caller cannot prove
  either without such a law. Not changed; a question for the user.

  **Closed (2026-10-31, the user's choice of the value-length law; `notes/vallen.md`):**
  `etcdState_vals` bounds every stored value, `GuaranteedUpdate`'s premise is the faithful
  "stale or different" with the value read within `2 ^ 27`, and the re-encoding of a decoded
  object is as long as its data (`decodeObjD_encode_length`).

