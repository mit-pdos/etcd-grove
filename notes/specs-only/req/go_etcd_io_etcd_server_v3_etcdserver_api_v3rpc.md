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
   * the **permission** of a read is checked at the state it answers from; `doSerialize`'s race
     with `AuthEnable` breaks it (`nonissues/etcd-doserialize-auth-enable-race.md`): a fix or a
     scope premise, the user's decision;
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
(`Spec/go_etcd_io/etcd/client/v3/ApiWatch.lean`), through grpc's stream (`req/google_golang_org_grpc.md`,
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
