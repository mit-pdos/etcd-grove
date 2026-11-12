# Batch 2b (gRPC watch server): completeness review, round 1

Reviewer: completeness. Read: `SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/*.lean` (16
files), `examples/specreq/v3rpcwatch/{protocol,serve}.go`, 1b's `SpecPlan/Spec/go_etcd_io/etcd/client/v3/ApiWatch.lean`
(`wireStep`, the wire slots), the Go code (`S = .../server/v3@...a4d2bb1720b9`, client `.../client/v3@...a4d2bb1720b9`,
tests `.../tests/v3@v3.0.0-20261103162249-673da07c8fab`, the latest tests module in the cache), and
`batch-2b.md` only after forming the findings below.

Paths: `W = S/etcdserver/api/v3rpc/watch.go`, `C = client/v3/watch.go`, `T = tests/.../integration/clientv3/watch/v3_watch_test.go`.

## The users, classified

| # | user | what it relies on | snippet | status |
|---|---|---|---|---|
| U1 | `v3rpc.Server` (`S/etcdserver/api/v3rpc/grpc.go:81`), called per client listener from `embed/serve.go` after `ReadyNotify` (`S/embed/serve.go:136`), so concurrently on one member | a started member's service, built more than once | `ReqServeWatch` | covered (`watchMemberAt` persistent) |
| U2 | the in-process client `v3client.New` (`S/etcdserver/api/v3client/v3client.go:39`), used by `embed/serve.go:148-150` for v3lock and v3election (2e): their `concurrency.Mutex.Lock` (`waitDeletes`) and `Election.Observe` watch through `adapter.WatchServerToWatchClient` | the handler run on a pipe stream (`S/proxy/grpcproxy/adapter/watch_client_adapter.go:30-70`, `chan_stream.go:142-173`), messages passed by pointer | none | **not served** (F4) |
| U3 | `SetProgressReportInterval`/`GetProgressReportInterval` in tests (`watch_test.go:512-516`, `T:1122-1126`) | set a small interval; save and restore the old one | `ReqInterval` (set, get) | the restore is not provable (S3) |
| U4 | the Go client (1b: `C:run`, `serveWatchClient`, `dispatchEvent`) | creates answered FIFO (`C:605-612`); refused = id `-1`/reason; ids route responses to substreams (`C:767-777`); a cancel response ends an id (`C:625-638`); fragments merged (`C:596-603`, `:640`); `-1` progress broadcast (`C:748`); per-id progress (`WithProgressNotify`); `prevKV`, filters, start rev `0` vs explicit (`nextRev = H` on `Created`, 1b), compaction | most of `protocol.go` | see F1, S2 |
| U5 | grpc-proxy (`S/proxy/grpcproxy/watch_broadcast.go:57-68`) | a client of the member **through clientv3** (wire requests): `WithProgressNotify` (per-id progress), `WithCreatedNotify`, `WithPrevKV`, `WithRev(nextrev)`; also calls `v3rpc.FiltersFromRequest` on its own downstream requests (`watch.go:272`) | prevKV yes; per-id progress no; `FiltersFromRequest` no | S2 |
| U6 | the grpc-gateway (`/v3/watch`, registered by `embed` when `EnableGRPCGateway`, the default; `tests/e2e/v3_curl_watch_test.go:34-51`) | forwards whatever JSON an HTTP client posts: any `watch_id` (documented, `api/v3/etcdserverpb/rpc.proto:813-818`), an empty `{}` request | none | excluded by the scope premise (S6) |
| U7 | raw-stream tests (`T`, `v3_watch_restore_test.go`, `v3_lease_test.go`) | creates with `WatchId` 0 and non-nil oneofs (none sends an explicit id or an empty request: grep of `WatchId:` in the tests module finds only a cancel, `T:465`); a wrong range refused and a from-key range accepted (`TestV3WatchWrongRange`, `T:378-420`); filters (`T:1216-1230`); per-id progress (`TestWatchWithProgressNotify`, `T:1120-1141`); several live watches routed by id (`T:619-690`); first id on a stream is `0` (`T:1079`); first event of a from-now watch exactly `H + 1` (`TestV3WatchCurrentPutOverlap`, `T:540-557`) | partly | F2, S2, S4, S5 |

## First tier

### F1. `ReqCancel` is not provable: the wire contract lets a canceled id be reused and lets the member send responses of it after its cancel response

`protocol.go:226-268` panics if (a) a later `Created` reuses the canceled id, or (b) any response of
the id arrives after its cancel response. Neither follows from `srvWireStep`/`wireStep`
(`client/v3/ApiWatch.lean:348-385`): the registered-`Created` case asks only `st.reg m.watchId =
none` (fresh among the **live** registrations; the cancel case removed the id), and a response of an
id with no registration is `| none => st' = { st with frag := none }`, i.e. allowed.

The code gives both: mvcc's auto ids are never reused on a stream (`req/..._storage_mvcc.md` item 2
asks it), and after a cancel response the send loop deletes the id from `ids` (`W:564-566`), so its
later mvcc responses go to `pending` and are never sent (`W:468-474`). The protocol documents (b):
"No further events will be sent to the canceled watcher" (`rpc.proto`, `WatchResponse.canceled`).
The Go client does not need (a) or (b) (an unknown id is answered with a cancel, `C:650-668`; a
reused id's responses would have to be steps of the new registration, which `wireStep` already
demands), so this is the snippet asking for more than the contract gives, but the documented
guarantee is the generally useful one.

Fix (preferred, "prefer the stronger spec"): ask 1b (`req/go_etcd_io_etcd_client_v3.md`) to add to
`WireSt` the ids retired on the stream (canceled; compacted ones too), with a `Created`'s id fresh
over live and retired ones, and a response of a retired id allowed only as a compacted id's resend
(`issues/etcd-watch-compacted-resent.md`). 2b's `sendLoop` sketch then carries "an id leaves `ids`
only when it is retired, and mvcc never reissues it". Otherwise, rewrite `ReqCancel` to rely only on
what `wireStep` gives.

### F2. `ReqCreatesInOrder` is not provable: nothing ties a refusal to its reason

`protocol.go:59-82` panics unless the first create (start `0`) is registered and the second (start
`-1`) refused. `wireStep`'s `Created` case lets **any** create be refused (`m.canceled = true →
m.watchId = -1 ∧ m.cancelReason ≠ []`, nothing more) and lets a create with a negative start be
registered (`WatchPos.init s H` for `s < 0`). The header of `ApiWatch.lean` says a refusal is for a
negative start, the permission check or mvcc's refusal, but the definition does not.

Users relying on the reasons: the raw tests (`TestV3WatchWrongRange`, `T:378-420`: `[a,a)` and
`[b,a)` refused, `foo` from-key accepted; every raw test that `t.Fatal`s on a canceled create).
The Go client does not (a refused watch just ends its channel). What the code guarantees:

* `s < 0` is always refused (`W:272-287`): add `s < 0 → m.canceled = true` to the `Created` case
  (true on every path, no caveat);
* a refusal is for `s < 0`, the permission check failing (`W:289-320`: not permitted at the
  member's auth state, or the token invalid/old), or mvcc's `Watch` error (`W:342, 355-357`: an
  empty range `key ≥ end` with `end` non-empty, or the mvcc stream already closed, which happens only
  after the handler's context branch closed it, `W:228-235`). The last disjunct is not something a
  client can exclude, so "valid create ⇒ registered" holds only up to "the stream is ending".

Fix: add the first bullet to 1b's `wireStep` (via `req/`), and either add the reason disjunction
(with the closing case) or change the snippet's first check to "if refused, then …".

### F3. `ReqProgress` and `ReqFragments` are not provable as written (snippet-level)

* `ReqProgress` (`protocol.go:197`) takes `P` from any response with id `-1`, no events, not
  created, not canceled: that admits a `Fragment` response, whose header `wireStep`'s fragment case
  does not constrain. Fix: test `!r.Fragment` too (or strengthen the fragment case: a fragment has
  events and a registered id, true of `sendFragments`, `W:618`, and of `fragment[id]` being keyed by
  mvcc ids, never `-1`).
* `ReqFragments` (`protocol.go:365-405`) watches from the current revision and requires the first
  reassembled response to be exactly the transaction's two events. `WatchPos.init 0 H` only bounds
  the first event by `H + 1` from above, so earlier writes to `pfx` (an "owned" prefix may have been
  written before by its owner) may come first. Fix: `Assumes:` "`pfx` was never written", or start
  from a revision.

### F4. The in-process client is a user of `NewWatchServer` and `Watch`, in 2e's scope, and is not served

`NewWatchServer.lean` lists `v3client.go:39` as "not in scope, nothing of ours calls it", but
`embed/serve.go:148-150` builds v3lock and v3election (batch 2e) on `v3client.New(s)`, and every
contended `Lock` and every `Observe` watches through `ws2wc`: the handler runs on a
`chanServerStream` pipe. 2b's statements quantify over any `st`, but:

* nothing produces `srvWatchStreamAt`/`srvWatchRecv`/`srvWatchSend` for a pipe stream (they are 2a's
  slots, realized by grpc's server);
* the slot laws cannot hold of a pipe, which passes the message pointer itself:
  `srvWatchRecv_recv` gives the server `watchReqOwn p (own 1) r` of the very message 1b's
  `wireWatchSend_send` gives back to the client, and `recvLoop` writes `creq.Key` and
  `creq.RangeEnd` into it (`W:268-330`); `srvWatchSend_send` gives the response back to the server,
  which reads `c.WatchId`/`c.Canceled`/`c.Created` after `Send` (`W:560-568`), while 1b's
  `wireWatchRecv_recv` gives the client `own 1` and the client writes `cur.Events`/`cur.Fragment`
  of a received fragment (`C:596-603`).

Fix: list the user. Either put it to the user as a known unserved user (with 1b's C-S4: the
adapter belongs to no batch), or, if v3lock/v3election are to be served, state the boundary laws
so a pipe can realize them: `Send` transfers the message (the sender keeps only a persistent
read-only part, which needs the sender not to write it afterwards: true of both ends here), with 1b
adjusting `wireWatchSend_send`/`wireWatchRecv_recv` alike.

## Second tier

### S1. `srvWireStep` is now the same as 1b's `wireStep` (stale)

1b adopted the exemption (`batch-1b.md`, "Round 1b: 2b's correction of `wireStep`"; the `-1` case
at `client/v3/ApiWatch.lean:370-378`). Under `srvWireStep`'s guard (not a fragment, not created, not
a plain cancel, id `-1`), `wireStep` reduces to the same body, so the two are equal. The header
(`ApiWatch.lean`, "The correction"), the docstring, `batch-2b.md` finding 1 and decision 1's "until
then 2a's boundary cannot turn a `srvWireStep` into a `wireStep`" are stale. Fix: delete
`srvWireStep`, state `srvWatchSend_send` with `wireStep`, and update the header (a second copy of the
contract is one more definition to keep in sync).

### S2. Patterns the specs give but no snippet covers

* **Per-id progress** (`ProgressNotify`): grpc-proxy (`watch_broadcast.go:60`), Kubernetes' bookmarks
  (through 1b), `TestWatchWithProgressNotify` (`T:1120-1141`), `TestV3WatchProgressOnMemberRestart`.
  `create()` in `protocol.go` cannot even set it. Given by `watchStep`'s progress case.
* **Filters**: `TestV3WatchWithFilter` (`T:1216-1230`), grpc-proxy's own use of
  `FiltersFromRequest` (`watch.go:272`). Given by `WatchReq.keeps`.
* **Several live watches on one stream, routed by id**: the client's substream map (`C:767-777`),
  `T:619-690`. `ReqCreatesInOrder`'s second create is refused, so no snippet holds two live
  registrations. Given by `st.reg m.watchId = none`. Could be the repaired `ReqCreatesInOrder` (F2):
  two creates on different keys, events of `k1` only on the first `Created`'s id.
* (Minor) a from-now watch delivering every write after its `Created` (the floor, the client's
  `nextRev = H`): only implicit in `ReqFragments`.

### S3. The tests' save-and-restore of the interval is not provable

`oldpi := GetProgressReportInterval(); SetProgressReportInterval(3s); defer SetProgressReportInterval(oldpi)`
(`watch_test.go:512-516`, `T:1122-1126`). `GetProgressReportInterval`'s post is `0 < d`;
`SetProgressReportInterval` needs `progressIntervalOk d`. It is not true in general (the value
includes up to 10% jitter, so near the top of the invariant's range `d + d / 10` exceeds `2 ^ 63`),
only for the 10-minute default. Test-only; record it as an unserved test pattern in the spec's
Margin, or strengthen the post to `∃ I, progressIntervalOk I ∧ I ≤ d < I + I / 10` (true, and
enough for a caller that knows `I`).

### S4. A test relies on what the code does not guarantee (no spec change)

`TestV3WatchCurrentPutOverlap` (`T:540-557`) requires a from-now watch's first event to be exactly
the `Created` header `+ 1`. The member registers at `R` and reads the header `H ≥ R` afterwards
(`W:342, 360`); with puts in between, events in `(R, H]` arrive and the test fails (racy). The spec
is right not to give it. Worth a line in `issues/etcd-watch-current-resume-past-event.md` (same
cause: the header is not the registration revision): etcd's own test depends on it.

### S5. Tests relying on the first id being `0` (`T:1079`)

An mvcc implementation detail. Margin, no change.

### S6. The scope premise (no explicit `WatchId`, no empty/`nil` oneof)

Who sends such requests: the Go client never (`C:1081-1100`, `:664-668`, `:707-711`); grpc-proxy
never (it talks to the member through clientv3, `watch_broadcast.go:57-68`); the in-process client
never; no test in the tests module; **the gateway** forwards whatever an HTTP client posts, and
`watch_id` is documented (`rpc.proto:813-818`); non-Go clients may. So the premise excludes the
gateway and foreign clients only. Two corrections to `batch-2b.md` decision 1: grpc-proxy is not
excluded (it is a clientv3 user); the gateway is.

Judgment: acceptable as a scope restriction for now, but cheaper than the decision text suggests.
A misbehaving request affects only its own stream, so a per-stream weakening serves everyone with
one spec: an empty oneof is a no-op in Go (`W:403-408`; stuck only because of the Goose bug, which
is recorded in `notes/perennial-changes.md`), and an explicit id could be a `create` with an id
whose guarantee holds when the id was never used on the stream (the fresh/retired bookkeeping of F1
is exactly what that needs). Put that option beside "keep the restriction" in the decision. Note
also that the premise is not checkable by 2a for an arbitrary network peer: `srvWatchRecvdLb_sent`
assumes every stream is opened by a modelled client (holding `wireWatchSend`); say so where the
decision is recorded.

### S7. Small

* `FiltersFromRequest.lean`'s Users calls grpc-proxy "not in scope"; true (no batch), but it is the
  one external user, and the spec fits it (persistent filter slice).
* `watchMemberAt_cfg` exposes `EtcdServer.Cfg`'s fields by address in 2b's vocabulary: what
  `NewWatchServer` reads, fine as a slot law, but its realizer is 2e; check 2e states it.

## A suspected Go bug (not in `issues/` or `nonissues/`)

**In-process watches of different principals share one stream and are checked as the first
one's principal.** v3lock/v3election calls run their client operations on the RPC's context (1d's C5).
The in-process client's `Watch` keys streams by **outgoing** metadata (`C:330`,
`streamKeyFromCtx`), which those contexts lack, so every lock and election watch shares the stream
keyed `""`, opened with the first caller's context (`C:281-288`: `valCtx` keeps its values). The
pipe passes that context to the handler (`chan_stream.go:152`), and `isWatchPermitted` checks
`AuthInfoFromCtx` against its **incoming** metadata (`S/auth/store.go:1077-1092`): the first
caller's token. With auth on, user B's `Lock` on its prefix, while user A's waiter is still
watching, is checked as A: refused if A cannot read B's prefix (and `waitDelete` returns the error),
or admitted although B could not read it. The stream also keeps A's token after A's RPC ends, so it
goes on failing once that token expires. Found by code reading, not run. It belongs with
`nonissues/etcd-watch-stream-key-collision.md` (the same sharing, here reached by etcd's own server).
Recommend the coordinator write a test (auth on, two users with disjoint prefixes, a contended
`Lock` by each over v3lock) and file it in `issues/` if it fails. It does not change 2b's specs:
the stream's `who` is the first opener, as stated. It matters to 1d/2e's per-call principal.

## Good

* One contract for both ends: the handler's facts are 1b's wire protocol (1b adopted the
  exemption), so the Go client's, grpc-proxy's (through clientv3) and the raw tests' reliances on
  ordering, fragments, prevKV, compaction and `-1` progress are all stated in one place.
* The scope widened as the principles ask: prevKV, fragments, filters, compaction, auth on and off in
  one statement, any number of watches, cancels and progress requests.
* `watchServiceAt` and `WatchTriple` give 2a exactly what a registration needs. The service is
  persistent, so several listeners each calling `NewWatchServer` (U1) are covered.
* The interval premise was relaxed to what the code needs. The configuration premise sits where the
  server is configured.
* The snippets `ReqFromStart`, `ReqWholeRevision`, `ReqCompaction`, `ReqPrevKV` and `ReqPermission`
  rely on what the users rely on, and they are provable under their stated assumptions. (Sketch:
  each `Created` is matched to its create through `creates ss`; each event step is `watchStep`'s
  `Forall₂` against `watchEvents` of the owned key; the compaction bounds come from `cr ≤
  σ.kv.compacted` and `done + 1 < cr`; for permission, no `σa` permits, so the create is refused.)

## Ranking (need of revision)

1. `examples/specreq/v3rpcwatch/protocol.go`: F1, F2 and F3 (four snippets), plus the missing
   patterns of S2.
2. `ApiWatch.lean`: S1 (drop `srvWireStep`, stale header), F4 (the pipe user, the ownership in the
   slot laws), the `req/` asks to 1b from F1 and F2, and S6's wording.
3. `NewWatchServer.lean`: its Users list (F4).
4. `GetProgressReportInterval.lean` / `SetProgressReportInterval.lean`: S3.
5. `watchServer__Watch.lean`, `FiltersFromRequest.lean`, the filters, `IsCreateEvent`: fine (S7).
   The internal specs were not judged beyond their Users lists (no outside user).

## Verdict

Not done. Five first-tier findings: three snippets unprovable through gaps in the contract (F1,
F2), two through the snippets' own wording (F3), and a real user (the in-process client behind
v3lock/v3election) not served and wrongly called out of scope (F4). Apart from F4, the spec covers
what the Go client and the gateway-free world rely on. The repairs are mostly to strengthen
1b's `wireStep` in ways the code already supports (retired ids; `s < 0` refused), fix the snippets,
and make a decision about the pipe user.
