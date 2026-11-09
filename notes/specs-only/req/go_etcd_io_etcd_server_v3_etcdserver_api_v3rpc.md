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
   * a **read** (`Range`, a read-only `Txn`, `RangeStream`) takes a persistent update and may fire
     it at every state; the answer is the one at the state it was last fired at (a linearizable
     read: the state at the member's applied index after the read index; a serializable one: the
     member's view, `KVHist.IsView`);
   * an error after which the request may still take effect is indefinite: `ErrTimeout*`,
     `ErrStopped`, `ErrNoLeader`, `ErrLeaderChanged`, ... (`EtcdErr.indefinite`).
   Used by: every `KV.*Triple` (exclusive or persistent updates), `txn.Commit.spec`.

4. **Configuration bounds** the handlers need for the model to hold (scope restrictions of the
   cluster contract, taken where the server is configured, 2e): `--max-txn-ops` at most 4999
   (`issues/etcd-txn-nested-depth-apply-panic.md`), `--max-request-bytes` below about 10 MiB
   (`issues/etcd-txn-keysonly-reply-alloc-panic.md`). No premise on the client's requests.

5. **Streamed ranges** (`RangeStream`): the chunks are pages read at the revision pinned by the
   first (`EtcdServer.rangeStream`): the client's `streamMatches` (default ordering: the pages'
   key-values are the range's answer, the last chunk carries the header's revision and `More`).
   Used by: `kv.GetStream.spec` (`wireStreamAt_recv`).
