# Integration I3: the gRPC boundary (2a, 2b, 3h's etcdserverpb part, 2f's net/http part)

Directories: `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/`, `Spec/google_golang_org/`,
`Spec/go_etcd_io/etcd/api/v3/{v3rpc/rpctypes,etcdserverpb,version}/`, `Spec/net/http/`, the
v3lockpb/v3electionpb `Api.lean`s; snippets `examples/specreq/{v3rpc,grpc,v3rpcwatch,etcdserverpb}/`.

## What changed, by file

- `etcdserverpb/Api.lean`
  - Build fix: `reqType` now covers W0's `Req.alarmActivate` (I1's item 1).
  - `mergeDstOk` (3h's provisional name) removed. `rangeRespDst_msgAt` is now stated over 2a's
    `Proto.mergeDst`, which already holds the message's `msgAt`.
  - `IrrBody.authToken (name)` stays 3h's. Go proposes no password (`v3_server.go:872`). I4's
    `ApiReq.lean` now re-exports 3h's `IrrBody`.
- `etcdserverpb/Realize.lean`: the header records two things:
  - 1b's watch messages now live in W0's `Wire.lean`.
  - W0/I1's new persistence laws are this batch's obligations: `eventOwn_persist`,
    `eventOwn_discard_persistent` and `msgOwn_discard_persistent`. Each follows from the `*_msgAt`
    relation laws and from `Proto.msgAt`'s `persist` and its persistence at a discarded fraction.
- `v3rpc/Api.lean` (2a's vocabulary):
  - `reqModels`, `replyModels` and `chunkModels` are now definitions equal to 3h's
    `EtcdServerPb.*` (they were opaque slots).
  - **`etcdAU γ p rq rep lo Q`** is new: the update over `Step p rq σ σ' res lo`. 1c's `callAU`
    is `etcdAU … 0`.
  - **`etcdUnary`** now carries `lo` with `authLb γ lo` (I1's item 2, W0's rounds 4–6). It also
    carries **`reqRight γ rq`**: I1's peer-URL right, which travels to 2e's
    `AddMember`/`UpdateMember` and is spent on every outcome.
  - `etcdUnary` also requires `Compact`'s `rev ≠ 0` (2c's round-1 item 4).
  - `rangeStreamSpec.up` likewise carries `lo` and `authLb`.
  - `mdPrin`'s meaning is spelled out, including the TLS scope: one identity per client, from
    W0's round 5.
  - New `credMD` (a slot for 1c: what the credentials add to the metadata) and two laws:
    - **`mdPrin_of`**: `ctxPrin dflt ctx p ∗ outMD ctx md0 ∗ credMD γ dflt mdc ∗ mdSeen` gives
      `mdPrin γ md p`.
    - **`reqPrin_of_md`**: `rpcCtx ctx md ∗ mdPrin γ md who` gives
      `∃ tls, reqPrin ctx who tls ∗ ⌜tls = none ∨ tls = who⌝`.
  - Further new laws: `rpcCtx_reqCtxOk` (4b's request) and `ctxNoIncoming_inMD` (2c's contexts).
  - **`kaSpec`**: each request is recorded (`kaReq g i id`). Each response is about a lease some
    request asked for (`replyModels … (.leaseKeepAlive id ttl)`). Laws `kaLog_alloc`, `kaLog_add`,
    `kaReq_lookup` and `kaReq_persistent` realize 1c's `kaSent`/`kaSent_sent`.
  - **`watchSpec` is now a definition** (I1's item 2):
    - `up` is a wire request recorded in `wsReq`.
    - `dn` is 1b's `wireStep who σ σa rs sst m sst'`, read against `etcdLb` of both states. `rs`
      is the recorded requests; `sst`/`sst'` are the stream states in `wsSt g j`/`wsSt g (j+1)`;
      `who` is the stream's principal in `wsWho`.
    - `fin` is trivial.
    - New laws: `watchSpec_records` (persistence, agreement, `wsSt g 0 init`) and
      **`watchRun_open`**, which turns grpc's halves of a run on 3h's generic wrapper into 2b's
      server slots.
  - `srvErrOk` is now an `abbrev` for 2c's `srvErrShape` (the two are identified).
  - The header has a new section, "Integration I3": how a handler composes with 2c's
    `SrvCallTriple`.
- `v3rpc/ApiWatch.lean` (2b's vocabulary):
  - `srvCtxPrin ctx who` is now `∃ tls, EtcdServer.reqPrin ctx who tls`, a definition. It was a
    slot of its own.
  - `WatchServer.WatchTriple`'s post now says the error is `nil` or has a `Grpc.sentStatus`. This
    is what grpc's `streamOut` needs.
  - `srvWatchRecv_recv`'s error is now `io.EOF` or `Grpc.ownErr`.
  - The header records the reader-token gap (see "Open" below).
- `serverWatchStream__recvLoop.lean`: the post gives `nil ∨ ownErr err`.
- `watchServer__Watch.lean`: the post gives the error shape, and the sketch says how it is obtained.
- `google_golang_org/grpc/Api.lean`, for 3d's request:
  - New predicates **`ctxInMD ctx o`**, **`ctxPeerCN ctx c`** (both opaque, persistent) and
    **`ctxCertUser`** (transparent). They describe any context's incoming metadata and TLS peer.
  - New laws: `ctxInMD_persistent`, `ctxInMD_agree`, `rpcCtx_inMD`, `ctxInMD_background`,
    `ctxInMD_child` and `ctxInMD_value`.
  - `grpcOver_inj`'s docstring now withdraws the `protoAt_agree` request (see below).
- `grpc/metadata/FromIncomingContext.lean`: now stated for any context over `ctxInMD`.
- `grpc/metadata/New.lean` and `grpc/metadata/NewIncomingContext.lean`: new, for 3d's `WithRoot`.
- `net/http/Api.lean`, for 4b's request: new `readsThrough` and `closesThrough`, with the laws
  **`readerAt_wrap`**, **`readerCloser_wrap`** and `wrap_persistent`.
- About 58 handler sketches in `v3rpc/` were updated:
  - the principal is now `reqPrin ctx who tls`, from `reqPrin_of_md`;
  - the update is converted to one over `srvStep … lo`;
  - the stale phrase "once W0's round 4 …" is replaced.
- `togRPCError.lean`'s Changes note now says `srvErrOk` is `srvErrShape` (an identification).

## Provisional names

**Resolved:**
- 2a's `reqModels`, `replyModels` and `chunkModels` are now 3h's.
- 2b's `srvCtxPrin` is now 2c's `reqPrin`.
- 2a's `srvErrOk` is now 2c's `srvErrShape`.
- 3h's `mergeDstOk` is now `Proto.mergeDst`.
- 2a's `watchSpec` slot is now a real contract.
- 2c's `IrrBody` copy: 3h's survives, as the coordinator decided, and I4 has already switched to it.
- 3d's `Auth.ctxInMD`, `Auth.ctxPeerCN` and `Auth.ctxCertUser` now have real definitions in
  `Grpc.*`. The owner of `auth/Api.lean` still has to define them as those.

**Kept, with the gap recorded:**
- `mdPrin` (2a's own, realized over 3d).
- `credMD`: 1c must pass it as grpc's `R`.
- `quotaOk` (2e).
- `sicEtcdOk`: still opaque, and there is still no stream form of `icChain_call`.
- `watchMemberAt` (the server batches').
- 2c's `txnChecked`: it is 2c's opaque predicate, introduced by 2a's `txnCheck_checked`. It cannot
  live in v3rpc because `ApiReq` would then import v3rpc.

## Sketches that did not fit, and how each was handled

1. **The read window.** The handlers held a `Step who … 0` update, but 2c takes `authLb γ lo` and
   `srvStep … lo`, and W0's KV triples carry `lo`. Fixed by adding `lo` and `authLb` to the
   contract.
2. **`srvStep` against `Step`.** 2c fires the update over `srvStep p tls`, which has a TLS-write
   disjunct and an empty-key disjunct.
   - The handler's `rangeCheck` excludes the empty key.
   - For `tls`, `reqPrin_of_md` gives `none` or `who`.
   - That `Step none` of a write is only refused with auth on is a model fact. It needs a law of
     2c's (see I4 below).
3. **Fired token refusals.** 2c's outcome 1 does not exclude a fired `ErrUserEmpty`,
   `ErrAuthOldRevision` or `ErrInvalidAuthToken`. `etcdUnary`'s first way and 1c's `AttemptTriple`
   both need `firedAns`. Requested of I4.
4. **`togRPCError`.** It needs comparable errors (the map lookup) and an unmapped message that
   settles nothing (`indefMsg`). `srvErrShape` gives neither. Requested of I4.
5. **The watch registration.** `streamOk` needs the stream's halves turned into 2b's slots, and an
   error that has a status. Fixed with `watchRun_open` and the error shapes above.
6. **`protoAt_agree`.** The request `⌜P = P'⌝` is unrealizable: a protocol holds `IProp`s, so ghost
   agreement gives at most `▷ ≡`. Nothing composes two bindings of one address, so 2a's request
   is withdrawn rather than weakened.

## Needed from directories I3 does not own

**I4** (`server/v3/etcdserver/{ApiReq,errors/Api}.lean`):
- (a) In `SrvCallTriple`, outcome 1 should add `⌜V3rpc-style firedAns res⌝`, that is,
  `∀ e, res = .err e → errRetryAuth e = false`: token refusals at apply time are given back
  (outcome 2).
- (b) A pure law, `srvStep_step.spec`:
  `(tls = none ∨ tls = p) → (∀ r, rq = .range r → r.key ≠ []) → srvStep p tls rq σ σ' res lo →
  Step p rq σ σ' res lo` (the header already claims it).
- (c) `srvErrShape`: a law `srvErrLeaf err → Grpc.cmpErr err`. In the unmapped case, add
  `⌜Grpc.cmpErr err⌝` and require that the message is no description of a definite, mapped etcd
  error (2a's `indefMsg`).
- (d) The server's stock of mvcc readers for request handlers (3e's `header.fill`, 3f's two watch
  loops). There is no law that turns a handler's or a goroutine's thread token into
  `mvccReaders γm 1` for its lifetime. The bounds plan's thread pool of reader slots, as a law of
  `isServer`/`watchMemberAt`, is the expected shape. Until then neither 2b's loops nor
  `header.fill` hold the reader 3e/3f require: **open**. I did not state an unsound law that
  re-borrows against a token that is kept.
- (e) `txnChecked t → Txn.txnSafe t`, which is 3b's request to 2c/2a.
- (f) `ctxNoIncoming` could be defined as `Grpc.ctxInMD ctx none ∗ Grpc.ctxPeerCN ctx none`. Its
  intro laws then follow from `ctxInMD_background/_child/_value`.

**Auth owner** (`server/v3/auth/Api.lean`): define `Auth.ctxInMD`, `ctxPeerCN` and `ctxCertUser`
as `Grpc.ctxInMD`, `Grpc.ctxPeerCN` and `Grpc.ctxCertUser`. `WithRoot`'s sketch can cite
`Grpc.New.spec` and `Grpc.NewIncomingContext.spec`.

**I1 / 1c** (`client/v3/ApiClient.lean`, `ApiLease.lean`, `ApiWatch.lean`):
- `callAU`, `AttemptTriple` and `uiOk_call` should take `lo` with `authLb γ lo`, over
  `Step p rq σ σ' res lo`, as the RemoteKV read triples do. Today a client `RemoteKV.RangeTriple`
  at `lo > 0` cannot reach the interceptor's `callAU` (`lo = 0`). The server side accepts any
  `lo`.
- The dial's `R` should be `credMD γ who`.
- `kaSent sc id` should be realized as `∃ g i, … ∗ V3rpc.kaReq g i id`.
- 1b's `WatchStreamNames` should be realized over grpc's `StreamName` plus the `wsReq`/`wsSt`/`wsWho`
  records.
- 1b's `wireWatchSend_send` counting a failed send as sent matches grpc's `cliSend_send`, which
  gives back `cliSend … (i+1)` on an error.

**raftpb owner** (`raftpb/Api.lean:58`): the text still names 3h's `mergeDstOk`; it should say
`Proto.mergeDst`. raftpb's `bootEntryData` is still opaque, even though 2a's
`noMaps`/`marshalOut` now give deterministic `Marshal`.

**2f/rafthttp owner**: 4b's other net/http items are not done:
- a shared reader of trivial knowledge, for `GracefulClose` racing `ReadAll`;
- `GET /raft/probing` with trivial knowledge, in `raftProto`.

Both are protocol and rafthttp facts, not boundary ones.

## Requests to my batches: status

- **W0** (all six req files): metadata, `servesAt_addr`, the error classes: met in round 1. The
  read window: now met.
- **1c**: `grpcConnAt` and the `.notSent` exclusion were met in round 1; `kaSent` is now met. The
  gRPC proxy's interceptors and the peer holder were met in round 1.
- **2b**: met. The `watchSpec` integration is done.
- **2c**:
  - items 1–5 and the round-1 items: met, except that `rsSink`'s laws need nothing new;
  - `reqPrin_of_md`: now met;
  - `srvErrShape`: identified, with the strengthenings asked back of I4.
- **2e**: `v3rpcBootCfg` was 2e's; nothing new here.
- **3b**: `txnChecked → txnSafe` is passed to I4 as item (e).
- **3d**: items 1 and 2 are met (`ctxInMD`, `ctxPeerCN`, `ctxCertUser`, `New`, `NewIncomingContext`,
  any-context `FromIncomingContext`). Item 3 is `mdPrin`'s doc.
- **3e/3f**: reader tokens are **open** (I4 item (d)).
- **4b**:
  - the grpc trace context: `rpcCtx_reqCtxOk`;
  - `readerAt_wrap` and `readerCloser_wrap`: done;
  - the GracefulClose and probing items: open (see above).
- **3h → 2a**: `StaticMethod`, deterministic `Marshal`, `zero` and `mergeDst` were met in round 1.

## Build

`etc/specs-build.sh --dir` on every directory I own (15 directories), last run: **OK (285 modules)**. It
passed after the owners of `ApiReq.lean` and `mvcc/Api.lean` finished their concurrent edits.
`go vet ./specreq/{v3rpc,grpc,v3rpcwatch,etcdserverpb}/...`: clean.
