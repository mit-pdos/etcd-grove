# Requirements on `go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc` (the gRPC handlers, batch 2a)

## from W0

The client's KV contract (`client/v3/Api.lean`'s `KV.*Triple`, over `api/v3/Model.lean`'s `Step`)
is what a program sees of the cluster. The handlers are where the request meets the cluster:
what W0's sketches (`retryKVClient.*.spec` through `remoteKVAt`) need of the KV service a member
registers, in plain terms. This is also the core of the **cluster contract** (`top.md`), whose
start-up parts go to 2e (`req/go_etcd_io_etcd_server_v3_etcdserver.md`).

1. **Serving**: once a member serves (2e's `Serve` over 2a's `grpc.start`), `servesAt γ ep`
   (`api/v3/State.lean`) holds for its client endpoint `ep`: each of `KV`'s unary methods
   (`/etcdserverpb.KV/Range`, `Put`, `DeleteRange`, `Txn`, `Compact`) and `RangeStream` is
   registered with a spec that, together with grpc (`req/google_golang_org_grpc.md`) and the stub
   (3h), gives `RemoteKV.*Triple` at `pb.NewKVClient(conn)` for every connection `connOk conn γ who`
   (1c).

2. **Each answer is a `Step`**: a handler's success reply, or an error the client classifies as
   `.etcd e` with `e` definite (`EtcdErr.indefinite e = false`), is the answer `res` of `Step who rq
   σ σ' res` for the request `rq` the client sent (the message's model), at a state `σ` at which the
   caller's update was **fired** (`Q σ σ' res` delivered with the reply), the principal `who` being
   the one the request's token or certificate names (none with auth off: the model's permission
   check is then vacuous). In particular:
   * the gRPC layer's own validations (`checkPutRequest`, `checkRangeRequest`,
     `checkTxnRequest`: empty key, value or lease provided with an ignore flag, too many operations,
     duplicate keys, invalid sort) are refusals or the model's validation answers;
     **the duplicate-key check must reject every transaction whose run the model's sequential
     semantics would not describe** (with the fork's #22395 fix, a from-key delete followed by an
     ignore-put of a key in its range is rejected; `issues/etcd-txn-delete-then-ignore-put.md`);
   * an answer from the quota, an alarm, an auth token check, `ErrTooManyRequests`,
     `ErrRequestTooLarge`: refusals (`EtcdErr.refusal`), the state unchanged, the update fired
     with that answer (or the error is indefinite);
   * `togRPCError` maps every server error to rpctypes' status of the same kind (so that the
     client's `rpctypes.Error` gives `errVal e`); an error it does not map is `.other` (indefinite).

3. **Firing discipline** (what makes the client's update shapes sound):
   * a **write** (`Put`, `DeleteRange`, a `Txn` that is not read-only, `Compact`) is fired **at
     most once per call**, when its entry commits, with the answer its apply computes; a write
     rejected for a stale auth revision (`ErrAuthOldRevision`, retried by the client's
     interceptor) or an invalid token **is not fired** (the update stays for the retry) unless
     the client gives up, in which case the client fires the refusal itself (1c);
   * a **read** (`Range`, a read-only `Txn`, `RangeStream`) takes a persistent update, registered
     before its read index is taken, and may fire it at every state from then on; the reply goes
     with the `Q` of the firing at the state the member read (a linearizable read: its applied
     state after the read index, possibly behind the latest committed state; a serializable one:
     the member's view, `KVHist.IsView`, the update fired at the current state);
   * an **unpinned `RangeStream`** whose pinned revision is compacted between two chunks ends with
     `ErrCompacted` and no `Q` (`wireStreamAt_recv`'s compaction disjunct);
   * the **permission** of a linearizable read is checked at an auth state the cluster had from
     the call's start (`Step`'s `lo`) to the answer: `State.permittedSince` (the check saw an older auth state: auth
     off: `doSerialize`'s race with `AuthEnable`), `State.deniedSince` (a denial at the state
     checked); a `Compact` and a keep-alive may be refused by a member's local auth state;
   * an error after which the request may still take effect is indefinite: `ErrTimeout*`,
     `ErrStopped`, `ErrNoLeader`, `ErrLeaderChanged`, ... (`EtcdErr.indefinite`).
   Used by: every `KV.*Triple` (exclusive or persistent updates), `txn.Commit.spec`.

4. **Configuration bounds** the handlers need for the model to hold (scope restrictions of the
   cluster contract, taken where the server is configured, 2e): `--max-txn-ops` at most 4999
   (`issues/etcd-txn-nested-depth-apply-panic.md`), `--max-request-bytes` below about 10 MiB
   (`issues/etcd-txn-keysonly-reply-alloc-panic.md`). No premise on the client's requests.

5. **Streamed ranges** (`RangeStream`): the chunks are pages read at the revision pinned by the
   first (`EtcdServer.rangeStream`): the client's `streamMatches` (only the last chunk has a
   header, `More` and `Count`; earlier chunks are non-empty; at the default ordering the pages'
   key-values are the range's answer and the last `Count` its count).

6. **The principal** a request is authenticated as is the client's `who` whenever the request's
   context satisfies `ctxPrin ctx who` (no token metadata of its own); a context with a token issued
   to no one is refused (`ErrInvalidAuthToken`, a refusal).
   Used by: `kv.GetStream.spec` (`wireStreamAt_recv`).

## from 1b

Batch 1b (the client's watch) needs the member's **Watch stream handler** (2b, `v3rpc/watch.go`,
over mvcc's watchable store, 3f) to give each response the facts of `wireStep`
(`SpecPlan/Spec/go_etcd_io/etcd/client/v3/ApiWatch.lean`), through grpc's stream (`req/google_golang_org_grpc.md`,
`wireWatchRecv_recv.spec`): with `etcdLb γ σ` for a state `σ` of the cluster the response's events
and revisions are read against (the committed log's state the member's store had reached), and
`etcdLb γ σa` for the auth state that admitted the watch. In plain terms, for a stream of a client
of `γ` as `who` (`servesAt γ ep`):

1. **Creates are answered in order**: the `k`-th response with `Created` answers the `k`-th create
   request the member read. A refused create (`isWatchPermitted` failing, a negative start revision,
   mvcc's errors: an empty range, a duplicate id) is answered `Created`, `Canceled`, a non-empty
   `CancelReason`, `WatchId = -1`; a registered one with a fresh id, never reused on that stream, and
   **only if `who` may read the range** at the member's applied auth state (`σa.permits who
   [(.read, range)] []`, the key normalized: an empty key is `"\x00"`).
2. **A registration's responses are `watchStep`s** of it (`watchStep who w σ σa p m p'`, the position
   `p` starting at `WatchPos.init start`): its events are exactly the range's events (`watchEvents`:
   filters applied) of the revisions after its position up to the last event's, **every event of
   a revision in one response** (mvcc's batches are cut at revision boundaries), the header's
   revision at least the last event's and reached; `PrevKv` as `WatchReq.prevOk` (the range at
   `ModRevision - 1`, none for a creation or below the compaction); no response of the id before
   its `Created` (the pending buffer), none after its compaction or cancel response.
3. **Progress**: a response of an id (or `-1`) with no events, not created, not canceled, is a
   progress notification at its header's revision `P`: no event of the watch between its position
   and `P`, and **`P` not below its position** (for a watch from a revision above the store's, no
   progress until the store reaches it: the fork's #20229 check; a progress requested before a
   watch's creation is not sent after its `Created`: the fork's fix of
   `issues/etcd-watch-progress-before-created.md`); id `-1` (a `RequestProgress` answer): such a
   notification for every registration of the stream.
4. **Compaction**: `Canceled` with `CompactRevision = cr`, no events: `cr` at most the cluster's
   compaction revision at `σ`, and above the registration's position + 1 (mvcc: `minRev <
   compactRev`).
5. **Cancel**: `Canceled` without compaction ends the id's registration.
6. **Fragments**: the fragments of one response are sent contiguously, all with the same id, the
   last without `Fragment` (`sendFragments` on the one send goroutine).
7. **Every response has a header** (`newResponseHeader`); mvcc responses whose events were all
   filtered are not sent.

Used by: `watchGRPCStream.run.spec` (through `deliverOk`), hence every fact of `watchChAt_recv`
(`watcher.Watch.spec`, `Client.Watch.spec`) and the snippets `examples/specreq/clientv3watch/`.
`WithRequireLeader` (`ctxRequireLeader`, W0's slot) needs nothing of safety: closing a stream whose
member lost its leader is liveness; the client ends its watches with that error (`closeErr`).

## from 1c

The lease, auth, cluster and maintenance services, as 1c's wire contract (`RemoteCallTriple`,
`ApiClient.lean`) and the interceptor (`AttemptTriple`) need them:

1. **Every answer is a `Step`** of the request's model (`Model.lean`'s `leaseStep`, `authStep`,
   `clusterStep`), as W0's item 2 for KV; a **repeatable** RPC (`reqRetryRep`: lease grant, revoke,
   time-to-live, leases, user/role get and list, member list, alarm) takes a persistent update and
   may fire it on every attempt the client resends (a resent grant grants again).
2. **Unfired refusals**: a request refused for its token (`ErrInvalidAuthToken`,
   `ErrAuthOldRevision`, `ErrUserEmpty`) or by a learner (`ErrGRPCNotSupportedForLearner`, the
   interceptor before the handler) returns the caller's update unfired (the client resends or fires
   the refusal itself). Used by: `AttemptTriple`, `uiOk_call`.
3. **`LeaseTimeToLive` of an unknown lease** is the reply `TTL = -1`, `GrantedTTL = 0`, the
   request's `ID` (the handler's mapping of `ErrLeaseNotFound`), fired as the model's
   `.err .leaseNotFound` answer (`leaseTTLReply`). `LeaseLeases`' `ErrLeaseNotFound`: an empty list.
4. **`LeaseKeepAlive`'s responses** carry the request's `ID` (`resp.ID = req.ID`) and the renewed
   TTL, `0` for an unknown lease. Used by: `lessor.keepAliveOnce.spec`, `kaChan`'s values.
5. **`Authenticate`'s reply** gives `tokenOf γ tok name` (the token issued names the user that
   authenticated; 3d's token providers). Used by: `authReply`, `Client.getToken.spec`.

### from 1b, round 1 (changes to the above)

* Item 6 (fragments) is now formal: `WireSt.frag` records the pending fragment's **id**; while a
  fragment is pending, the next response is of that id and neither a creation nor a cancel.
* Item 1: a registration from start `0` is at `WatchPos.init 0 H` with `H` the `Created` header's
  revision: **every event of the range above `H` is sent** (the member registers at `R ≤ H`, so
  its events start at `R + 1 ≤ H + 1`).
* Progress and compaction revisions are the header's / `CompactRevision`'s `sint.Z` value (no
  wrap-around).

## from 2c

The server's request path (`EtcdServer.*`, `ApiReq.lean`) gives the handlers three outcomes per call
(`SrvCallTriple`): the update fired with the answer (`srvReply`: the reply, or a server error with
`srvErrOf err e`), the update given back with a `srvUnfired` error (never applied: the client may
resend; K4's stale auth revision), or a `srvIndef` error. What 2c needs of 2a:

1. **`togRPCError` realizes `srvErrOf`**: `srvErrOf err e → togRPCError(err) = errVal e` as the
   client sees it (or grpc's `Canceled`/`DeadlineExceeded` codes for the context's errors, which
   the client classifies `.canceled`/`.deadlineExceeded`); an unmapped error becomes `Unknown`
   (indefinite at the client). Used by: every handler over a server spec.
2. **`reqPrin ctx who`** (`ApiReq.lean`) for the handler's incoming context: the same fact as 2b's
   `srvCtxPrin ctx who` (`api/v3rpc/ApiWatch.lean`): one should be the other (a law
   `srvCtxPrin ctx who ⊢ reqPrin ctx who`, or one predicate at integration).
3. **The validations the server's specs take**: `Range`/`RangeStream`: `rm.key ≠ [] ∧ rm.validSort`
   (`checkRangeRequest`); `Txn`: `txnChecked t` (`ApiReq.lean`, provisional: `checkTxnRequest`'s
   `nil` at the server's `--max-txn-ops` gives it) and, for a write, `txnMsgDepth t + 1 ≤ 10000`
   (from `--max-txn-ops ≤ 4999`, `irr-depth.md`'s `txnCheck_msgDepth`).
   ```go
   if err := checkTxnRequest(r, int(s.maxTxnOps)); err != nil { return nil, err }
   resp, err := s.kv.Txn(ctx, r)
   ```
4. **The update's persistence at the server**: one-shot for every write and for `LeaseRenew`,
   `LeaseTimeToLive`, `LeaseLeases`, the auth reads (all fired once); **persistent for `Range`, a
   read-only `Txn`, `RangeStream` and `Authenticate`** (fired by the read registry at every state
   after the call began). `Authenticate`'s client update is one-shot today (W0's `CallTriple`,
   `reqRetryRep`): see `req/go_etcd_io_etcd_api_v3.md`, "from 2c".
5. **`rsSink rs γ who r Q ms fin`** (provisional slot in `ApiReq.lean`): the server end of a range
   stream (the `headerFillingRangeStream` over grpc's `ServerStream`), with send laws: a non-final
   chunk (key-values, no header) appended to `ms`; the final chunk (header, `More`, `Count`) sent
   with `Q σ σ res` of an answer `res = .ok (.range rev a)` such that `streamMatches r (ms ++ [m]) rev
   a` (W0's), setting `fin`; `rs.Context()` a context with `reqPrin` of `who`. 2a's
   `wireStreamAt_recv` (client side) is its mirror. Used by: `EtcdServer.RangeStream.spec`.
6. **The outcome-2 path to the client**: a `srvUnfired` error the client's interceptor resends
   (`errRetryAuth`) or treats as `.notSent`/refusal must reach W0's `AttemptTriple`'s "update given
   back" case with the handler's update (the server gives it back).

## from 2e

1. `v3rpc.Server(s, …)` takes `EtcdServer.isServer s γ` (`Start`'s post; `ApiBoot.lean`) and, served,
   gives `servesAt γ ep` (K3).
2. `EtcdServer.v3rpcBootCfg cfg` (provisional slot of `NewServer`): K8's `MaxTxnOps ≤ 4999` and the
   `MaxRequestBytes` bound; replace by your slot.
3. The Election and Lock services (`v3election`, `v3lock`, registered by `v3rpc.Server` over
   `v3client.New(s)`): their specs take `isClient c γ who`, `ctxPrin ctx who`, 1d's `etcdPerm γ T`
   and a `threadTok` per call (the session's keep-alive goroutine); the registration must supply them
   from the request's metadata.

## from 3b

**The checks give txn's premise**: `txnCheck n t = none → intervalsOk t.success → intervalsOk
t.failure → Txn.txnSafe t` (txn's `Api.lean`: no empty operation, a known sort target, and no put with
an ignore flag after a delete that may cover its key, at any depth, both branches; `checkRequestOp`
refuses the first two, `checkIntervals` with the fork's fix of
`issues/etcd-txn-delete-then-ignore-put.md` the third). 2c's provisional `txnChecked t` should give it
too. Used by: `Txn.spec` (its callers: 2c's `EtcdServer.Txn`, 3a's apply).

## from 2c (round 1)

2c's API changed (round 1; your files using it no longer build until updated):
`reqPrin ctx p tls` (`p` the principal with auth enabled, the token's user else the certificate's
name; `tls` the certificate's name, used with auth disabled), `SrvCallTriple e P B γ p tls rq rep
reply` (the caller's `authLb γ lo`, the update over `srvStep p tls rq σ σ' res lo`), `rsSink rs γ p tls
r ms` (no `Q`, no `fin`), every error with `srvErrShape err` (`errors/Api.lean`: your `togRPCError`'s
precondition, as you asked: "from 2a" item 3).

1. **`reqPrin_of_md`** in your module (it imports `ApiReq.lean`): from `Grpc.rpcCtx ctx md` and
   `mdPrin γ md who` (and the connection's certificate), `EtcdServer.reqPrin ctx who tls` with
   `tls` the certificate's name under `--client-cert-auth` (none otherwise); 2b's `srvCtxPrin` the
   same fact (one predicate at integration). `reqPrin_child`/`reqPrin_value` keep it for the
   in-process client's derived contexts.
2. **`srvStep p tls` vs W0's `Step p`**: equal for reads; a write may be stepped as `tls`
   (`nonissues/etcd-write-tls-principal-auth-enable.md`). Equal to `Step p` when `tls = p`, or
   `tls = none` (a principal-less write is refused with auth on): W0's `ctxPrin` premise
   (`req/go_etcd_io_etcd_api_v3.md`, "from 2c" round 1).
3. **`rsSink`'s laws** (yours, as you planned `rsSink_intro`/`rsSink_out`): a send appends a chunk
   (any page; no `Q`); the stream's `Q` comes with `RangeStream`'s `nil` return (`streamMatches` of all
   chunks): the code sends the last chunk before it knows the permission held
   (`issues/etcd-rangestream-auth-revoked-midstream.md`), so `Q` must reach the client with the
   end of the stream (status OK), not with the last chunk; `RangeStream` may also end with
   `ErrAuthOldRevision` after every chunk, or `ErrCompacted` with **no** chunk
   (`nonissues/etcd-rangestream-count-compacted.md`): `rsSink_out` must admit both.
4. **Premises you establish**: `Put`'s `pr.invalid = none` (`checkPutRequest`), `DeleteRange`'s
   `d.key ≠ []` (`checkDeleteRequest`), `Range`'s `validSort ∧ (key = [] → rangeEnd = [])`,
   `RangeStream`'s `key ≠ [] ∧ validSort ∧ rangeStreamOk` (`checkRangeStreamRequest`), `Compact`'s
   `rev ≠ 0` (**your contract of `/etcdserverpb.KV/Compact` must carry it** for raw gRPC clients, as
   W0's client contract does: completeness F6).
5. **Errors**: `srvErrOf` never names a context's own error (`srvErrOf_notCtx`); a mapped error is a
   leaf sentinel (`srvErrVal_leaf`, `srvErrOf_inj`), so `errors.Is(err, lease.ErrLeaseNotFound)` is
   decided by `srvErrOf err .leaseNotFound` once `lease`'s initialization law gives the global's
   value (3c); an unmapped one has a message and wraps no sentinel (`srvErrNotMapped`).

## from 2e, round 1

1. 2e now specifies 2a's item 7: `EtcdServer.{AddMember, UpdateMember, RemoveMember,
   PromoteMember}` (each with `urlsRight` for the URLs it gives a member, where applicable), the getters
   `Cluster`, `KV`, `IsLearner`, `IsMemberExist`, `Alarms`, `MemberID`, `Leader`, `Term`, `Logger`
   (with a `threadTok`), and the membership constructors `NewMember`, `NewMemberAsLearner`.
2. Every request-path call holds a share of `srvGate s q` (from `Start`); a member is stopped only
   with the whole gate back, so the gRPC server is drained first (`HardStop.spec`).
3. `v3rpcBootCfg_intro` (`ApiBoot.lean`): `MaxTxnOps ≤ 4999` and `MaxRequestBytes ≤ 10 MiB`, a
   provisional bound for your `issues/etcd-txn-keysonly-reply-alloc-panic.md` value: refine it in
   your slot.
4. The client address on a restart (second tier F14): the restarted member re-serves the same client
   address; your `addrAt` is persistent, which suffices.


## from 3f

**Reader tokens through the watch handler's loops** (the coordinator's decision on 3f's review F3,
keeping the user's 2026-11-07 decision for mvcc: a call that reads mvcc's store takes one of its
reader tokens, 3e's `mvccReaders γ 1`, and gives it back; no thread token is converted inside mvcc).
mvcc's watch stream (`SpecPlan/Spec/go_etcd_io/etcd/server/v3/storage/mvcc/ApiWatch.lean`) takes one in
`watchStream.Watch`, `Rev`, `RequestProgress`, `RequestProgressAll` (and `watchableStore.Range`,
3e's contract, for `prevKV`). So `serverWatchStream.recvLoop` (`Watch`, `Rev`, `RequestProgressAll`)
and `sendLoop` (`RequestProgress`, `Range`) each need a reader token of the member's store for their
lifetime: the run (`swsAt`'s shares, `swsRecver`, `swsSender`) carries one per loop, from what
`watchServer.Watch` gets of the member (2d's `srvWatchable`, below), given back when the loops end.
```go
id, err := sws.watchStream.Watch(ctx, mvcc.WatchID(creq.WatchId), creq.Key, creq.RangeEnd, creq.StartRevision, filters...)
sws.watchStream.RequestProgress(id)   // send loop
```
Also from round 1: `Watch` and `Rev` fire a read atomic update of the store's state (3e's `KV.Rev`
form), so the floor (`Created`'s header from `Rev()` after `Watch`) is at least the watcher's
position; `Watch` gives `id = n` (the control side's next id, `wsReg_ctl`) and the package's
`ErrEmptyWatcherRange` on refusal; a compaction response is checked against the watcher's events
position (`posEvOf`), not its position after progress (1b's `watchStep` changes alike). Used by: 3f's
`watchStream.*.spec`; 2b's `recvLoop.spec`, `sendLoop.spec`, `watchServer.Watch.spec`.

## from 3e (round 1 repairs)

`header.fill`/`fillWithoutRevision`'s `s.KV().Rev()` (`header.go:35`) is `KV.Rev.contract`: it takes a
reader token (`mvccReaders γ 1`, given back) or a `Rev` token (`revRd γ rt`). Under the coordinator's
decision (a), the handler lends one from its allotment (the server's stock, `req/..._etcdserver.md`,
"from 3e (round 1 repairs)", item 1): `header.fill.spec` needs it in its precondition (with the
store's `isMvcc` and an update over `mvccState`, or a stale-read form the server's invariant gives).
The maintenance `Hash`/`HashKV` additionally take a share of `mvccRestoreGate` (no restore during a
hash). Used by: `header.fill.spec`, `maintenanceServer.{Hash,HashKV}.spec`.
