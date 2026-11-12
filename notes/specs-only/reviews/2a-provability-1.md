# Batch 2a, provability review, round 1

Reviewer: provability (soundness, snippets), round 1, at `b5cecfd608` plus the working tree. Targets:
`SpecPlan/Spec/google_golang_org/protobuf/proto/`, `SpecPlan/Spec/google_golang_org/grpc/**`,
`SpecPlan/Spec/go_etcd_io/etcd/api/v3/v3rpc/rpctypes/`, `SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/`
(not `ApiWatch`/`WatchInternal`), `examples/specreq/{v3rpc,grpc}/`. Go: grpc-go v1.84.0,
protobuf-go v1.36.12 (`examples/go.mod`), etcd fork `a4d2bb17` (module cache). I wrote my findings
before reading `batch-2a.md`. Afterwards I marked which ones the author already lists ("known").
Both snippet packages pass `go vet`. I did not build any Lean.

## First tier

### F1. Two independent "one per address" tokens: a program can fake a gRPC reply (unsound)

`Grpc.addrFree ep` (`grpc/Api.lean:269`, bound by `addrFree_bind`) and `Http.addrFree a`
(`SpecPlan/Spec/net/http/Api.lean:193`, bound by `reserve` to `protoAt a P`) are separate exclusive
resources, and the adequacy theorem hands out both for every string. Nothing stops a program from
binding the same socket twice:

- `Grpc.addrAt a C`, with some `C.unary m = S`;
- `Http.protoAt a P`, then serving at `a` with `net/http` (`SpecPlan/Spec/net/http/Serve.lean`).

The net/http handler can answer a gRPC client's HTTP/2 request with gRPC framing
(`content-type: application/grpc`, a length-prefixed message, trailer `grpc-status: 0`). This is
exactly what `grpc.Server.ServeHTTP` does, and what etcd's TLS path does through
`grpcHandlerFunc`, `server/embed/serve.go:260,314-324`. grpc-go's client accepts the reply.
`attemptOk_call` (`grpc/Api.lean:471`) then gives the client `Φ (.ok r)` that no run under `S`
produced. With `S md c Φ := Φ (.status 5 "x")` and the client's `Φ o := ⌜o = .status 5 "x"⌝`, the
client proves `False` while Go reaches its panic.

There are two related gaps:

- `Grpc.listenerAt` (`:285`) is a third opaque predicate with **no producer**. `net.Listen`
  gives `Http.listenerAt`. So `start.spec` cannot be applied at all, and neither can the snippet
  `v3rpc/serve.go`.
- grpc's header does not state the physical premise that net/http's header does (at most one
  reserved string per socket). Without it, `localhost:p` and `127.0.0.1:p` bound to different
  contracts are the same socket.

Fix: one network model. Make `Grpc.addrAt ep C` an instance of `Http.protoAt` (a gRPC protocol
`P_grpc C`), or have one package own `addrFree` and the physical premise. Use `Http.listenerAt`.
State what the cmux and `ServeHTTP` paths guarantee: a gRPC request at `ep` reaches only a
`start`ed `grpc.Server` that meets `C`.

### F2. The handler runs' thread tokens have no source in any stated spec (hard rule: "A trusted statement never gives out a counted resource it did not take"; known, decision 3)

`unaryOk`/`streamOk` (`grpc/Api.lean:373,400`) give each run a `threadTok`. Nothing takes one:

- `Server.Serve.spec` takes only `serveTok`;
- `start.spec` takes none;
- `attemptOk_call` takes none.

The header and `Server__Serve.lean` justify the tokens by "a trusted Goose model of `Serve`'s
dispatch forking each run". No such model exists: `Code/google_golang_org/grpc.toml` is names and
types only, and there is no `TrustedCode/google_golang_org/grpc`. This is precisely the argument
the principle rules out: "analogy with a modelled operation ... is no argument when the thing is
outside the semantics". It is also the refutation of R11
(`specs-ref/notes/axiom-review/r11-grpc-threadtok.md`).

A dispatch model alone is not enough either. Its loop must receive the requests that
`attemptOk_call` sends, so the client's invoke, the streams and the network would also have to
become trusted Goose code. That turns every spec in `grpc/` from an axiom into a theorem about the
model, which contradicts the header ("every spec ... is assumed").

The repository's decision for net/http (`SpecPlan/Spec/net/http/Api.lean`, "Handler runs borrow their
caller's thread tokens", citing the grpc pool decision) is a pool of `n` tokens from `Serve`'s
caller, with the physical premise of at most `n` concurrent runs.

Fix: either adopt the same shape (`start`/`Serve` take `threadToks n`, a premise on concurrent
streams, which `MaxConcurrentStreams` bounds only per connection), or commit to the trusted model
and write down its scope (which functions become `TrustedCode`). Until then `regsOk`/`unaryOk`
hand out tokens nobody gave.

### F3. Every read handler is unprovable against 2c (known, decision 4; still open at HEAD)

Two definitions do not match:

- `etcdUnary` passes 1c's `callAU`, an atomic update committed under `Step`
  (`client/v3/ApiClient.lean:318`).
- 2c's `SrvCallTriple` (`ApiReq.lean:348`) takes an update committed under `srvStep`, which is
  `Step` plus the `doSerialize`/`AuthEnable` race for reads (`ApiReq.lean:132`).

An update's commit condition is supplied by the committer, so turning an update over `Step` into
one over `srvStep` needs `srvStep → Step`. That is false exactly at the race disjunct.

Affected (every `rq.isRead`):

- `kvServer.Range` and `kvServer.Txn` read-only, and their `quotaKVServer` wrappers;
- `LeaseTimeToLive`, `LeaseLeases`;
- `AuthStatus`, `UserGet`/`UserList`/`RoleGet`/`RoleList`;
- `RangeStream` (its `up` update is over `Step`);
- the 2a snippets `v3rpc/put-then-range` and `grpc/at-most-once`.

None of these files' sketches mentions the mismatch; each says "the update passed on". Fix: as the
author proposes, `srvStep = Step` after a fork fix, or a scope premise. Until then each read
handler's sketch should say it is blocked.

### F4. `etcdUnary`'s answered branch does not compose with 1c's `AttemptTriple` at token and learner refusals (contract too weak for its client)

Branch 1 of `etcdUnary` (`v3rpc/Api.lean:183`) lets the member fire the update with any `Step`
answer and send `desc e`. `Step.refuse` admits `.invalidAuthToken`, `.authOldRevision`,
`.userEmpty`, `.notSupportedForLearner` (`Model.lean:324`).

On the client side, `AttemptTriple` (`ApiClient.lean:379`) allows a fired answer only with
`errRetryAuth e = false ∧ e ≠ .notSupportedForLearner`. For those four errors it promises the
update back (`callAU`), so that the retry interceptor can resend an exclusive write. A client
receiving `desc .invalidAuthToken` cannot get `callAU` from `Φ` when the member took branch 1.
Hence `AttemptTriple` cannot be proved from `attemptOk_call` plus `etcdUnary`.

The case is real in the code. With auth enabled after a write was proposed without a user, the
apply's `isOpPermitted` returns `ErrUserEmpty` for a committed entry (`auth/store.go:869`,
`apply/auth.go:59`).

Fix: restrict branch 1 to answers that are not `errRetryAuth` and not the learner refusal. 2c must
then never fire on them. It must classify the apply-time `ErrUserEmpty` and `ErrAuthOldRevision`
as outcome 2 (the entry is a no-op, so not firing is sound). Put that request in `req/` for 2c.

### F5. `icEtcdOk`, `unaryOk` and `HandlerTriple` do not give what the implementations read (hard rule "Complete": a callback contract checked against the body)

- **The `info` argument.** `newLogUnaryInterceptor` defers
  `logUnaryRequestStats(..., info, ...)`, which reads `info.FullMethod` (`interceptor.go:85,108`).
  Its spec requires `info.FullMethod ↦□ fm` (`logUnaryRequestStats.lean:37`). `icEtcdOk`
  (`Api.lean:313`) quantifies over `info : Loc` with no points-to, and so do `icChain_call` and
  `icHandler_call`. So `newLogUnaryInterceptor.spec` is unprovable. The generated handler allocates
  `info` with `FullMethod` set: `icChain_call` should give `info.FullMethod ↦□ m`.
- **The request's depth.**
  - `logUnaryRequestStats.spec` and `quotaAlarmer.check.spec` (`:37`) need `depth c < depthMax` of
    the request.
  - Neither `decOk_call`, nor `unaryOk`, nor `icEtcdOk`, nor `HandlerTriple` (`:429`) gives it.
  - So `quotaKVServer.Put/Txn`, `quotaLeaseServer.LeaseGrant` and the log interceptor are
    unprovable as stated.
  - The fact is true: grpc decoded the request, and protobuf-go refuses more than 10000 levels,
    `internal/impl/decode.go:105`.
  - Fix: `decOk_call`'s post gives `⌜depth c < depthMax⌝`, and `unaryOk`/`icEtcdOk`/`HandlerTriple`
    carry it.
- **The error path of the log interceptor.** `logUnaryRequestStats.spec` requires a reply
  `msgAt repT r dr c'`. On an error the handler's reply is a typed nil or `nil`, which the code
  handles (`if _resp != nil`, `interceptor.go:120`). The spec needs an error-path case, or the log
  interceptor cannot call it after a failed handler.

### F6. The error path of every handler does not compose with 2c (sketch implausible; requested of 2c, still open at HEAD)

`togRPCError.spec`'s pre (`togRPCError.lean:36`) needs one of:

- `context.isCtxErr err`;
- its negation, together with `srvErrOf err e`;
- its negation, together with `errMsg err m ∗ ⌜∀ e, ¬ srvErrOf err e⌝`.

`SrvCallTriple`'s outcomes 2 and 3 give only the pure `srvUnfired err`/`srvIndef err`
(`ApiReq.lean:248-254`): no `errMsg`, no context-error or not-context-error fact.

The handler's branch 3 also needs `indefMsg m` for the unmapped message (`Api.lean:94`), which
nothing gives. `togRPCError` also does `toGRPCErrorMap[err]` with an interface key. Go panics on an
unhashable dynamic type, and Perennial models it (`CheckComparable`, `Golang/Defn/PostLang.lean:328`).
The third disjunct of the pre admits any `errMsg` error, so the spec as stated is false at a
non-comparable error. No caller passes one, but the pre admits it.

Fix: 2c's error classes carry an `errOk err` resource: a context error, or a comparable non-status
error with `errMsg err m`, `indefMsg m`/`srvErrOf`. Then `togRPCError` takes it.

### F7. `Server.spec`'s post is unprovable: grpc's health service is registered through `RegisterService`

`v3rpc.Server` calls `healthpb.RegisterHealthServer(grpcServer, hsrv)` (`grpc.go:88`), which is
`s.RegisterService(&Health_ServiceDesc, srv)` (grpc `health/grpc_health_v1/health_grpc.pb.go:216`).
By `Server.RegisterService.spec` that adds `/grpc.health.v1.Health/{Check,List}` to `B.regs` and
`Watch` to `B.sregs`. `etcdContract` has no entry for them, so `regsOk B (etcdContract γ)`, the
post of `Server.spec`, fails. The sketch's "the health server (grpc's, not in `B.regs`)"
contradicts the registration spec.

Health runs also go through etcd's interceptors, and no spec covers them. Fix: give the health
methods contracts in `etcdContract` (`etcdLocal`, a trivial stream contract), plus an assumed
`unaryOk`/`streamOk` for grpc's health handlers.

There are smaller gaps in the same file:

- `serverMetrics.InitializeMetrics(grpcServer)` (`grpc.go:92`, which calls `GetServiceInfo`) has
  no spec.
- `ReqServe`'s `gs == nil` check needs a law that `srvBuild gs B` implies `gs ≠ null`.
- etcd's TLS path serves gRPC through `ServeHTTP` (embed `serve.go:260,317`), which has no spec.

### F8. Snippets that are not provable (and two that panic in Go)

- **`v3rpc/validation-answer` panics in Go and is unprovable.** `quotaKVServer.Put/Txn` run
  `qa.check` before `checkPutRequest`/`checkTxnRequest` (`quota.go:58-70`). On a member over its
  quota, an empty-key put returns `ErrGRPCNoSpace`. `indefinite()` returns false for it, so the
  snippet panics. Other cases do the same:
  - a learner's `ErrGRPCNotSupportedForLearner`;
  - `ErrTooManyRequests`, `ErrRequestTooLarge`.

  The model (`Step.refuse`, any refusal at any state) cannot force `.emptyKey`. Fix: accept any
  refusal (`EtcdErr.refusal`) as well, or add `Assumes:` (under quota, not a learner, no
  backpressure).
- **`v3rpc/compact-admin` is unprovable even after the W0 request.** The request
  (`req/go_etcd_io_etcd_api_v3.md`, "from 2a", item 1) only *adds* a refusal disjunct. The success
  disjunct of `.compact` (`Model.lean:932-936`) still needs no permission, so a non-root
  compaction may succeed in the model. The snippet needs success to require admin, at least at
  some past state.

  Note the Go: the only admin check is `aa.isPermitted` on the member's local auth store
  (`key.go:140`). The apply does not re-check compaction (`apply/auth.go:244`, `needAdminPermission`
  has no `Compaction`). A user whose root role was just revoked can compact through a lagging
  member. This is a race of the same kind as `nonissues/etcd-doserialize-auth-enable-race.md`, and
  is not filed. The snippet's "a user without the root role" holds if the user never had it; the
  model needs a condition of that shape.
- **`v3rpc/range-stream` is unprovable: two laws are missing.**
  - *Agreement.* `rsChunk` has a weakening law (`rsChunk_ids`, `:297`) but no agreement law, so
    the client's received chunk (`dn`) and the `fin`'s list `ms` (whose `streamMatches` says the
    last has a header) need not be the same chunk.
  - *Header-last.* Nothing says a chunk with a header is the last one sent. That fact is what the
    second panic (a chunk received after the header chunk) needs at the moment it happens, before
    any `fin`.

  Fix: `rsChunk_agree` up to ids, and `rsChunk_hdr_last : rsChunk g j m ∗ ⌜m.hdr ≠ none⌝ ∗
  rsChunk g j' m' ⊢ ⌜j' ≤ j⌝` (true: `RangeStream` sends the header chunk last).
- `v3rpc/put-then-range` and `grpc/at-most-once` are blocked by F3. With auth off and F3 fixed
  they are provable: Put's update fires once; the client's invariant on the owned key; the Range
  reply's revision and version through `replyModels`.
- `v3rpc/serve` is blocked by F1 (no `Grpc.listenerAt` producer) and F7.
- `v3rpc/lease-ttl-unknown`, `grpc/status-classify` and `grpc/metadata-out` are provable:
  - lease-ttl-unknown: `ansOutcome`'s TimeToLive case; `leaseAnsAt` forces `.leaseNotFound` for a
    never-granted id (`Model.lean:853-854`);
  - status-classify: `Error.spec` and `init.spec`;
  - metadata-out: `outMD_noMeta` and the metadata specs.

### F9. A handler's status message with invalid UTF-8 is altered in transit (an assumed spec false at an input)

grpc-go's server percent-encodes `grpc-message`, replacing each invalid byte by U+FFFD
(`internal/transport/http_util.go:241-265`, `encodeGrpcMessageUnchecked`). The client decodes the
replaced bytes. `statusErr_sent`/`errMsg_sent` (`grpc/Api.lean:416,443`) then send `msg` itself,
and `attemptOk_call` gives `Φ (.status code msg')` for the received `msg' ≠ msg`. Under
`grpcMsg`'s stated meaning ("the messages grpc-go's code makes"), `msg'` is not one of those, so the
axiom has to give a `Φ` nobody provided.

A program can build such a status: `status.Error(code, "\xff")`; the client checks
`Message() == "\xff"` and panics. etcd's own descriptions are ASCII, so no closed result is
affected.

Fix: `sentStatus err code (fixUtf8 msg)` (a pure function of the encoding), or widen `grpcMsg` to
every string containing U+FFFD and say so in the header.

## Second tier

- **(a) Proto: what `encodes` means.**
  - `Marshal.spec`, `Unmarshal.spec` and `encodes_fun` are jointly satisfiable only if
    `encodes t c bs` means "decoding `bs` at `t` gives `c`". Then `Marshal.spec` asserts the round
    trip `Unmarshal(Marshal c) = c`.
  - That is true for contents reachable by field writes and decoding. It is false for unknown
    fields that carry a known field number, or malformed ones, which `ProtoReflect().SetUnknown`
    can create: they decode to a different content.
  - Unreachable for Goose programs today, since protoreflect is untranslated. State the
    interpretation, and the reachable-content restriction, in the header.
  - Depth: `depth c < depthMax` (at most 9999) is safely inside protobuf-go's limit, which accepts
    10000 levels (`decode.go:105`). It is correct.
  - No law equates two heaps' contents beyond `msgAt_agree` at one address. Good.
  - `msgAt` has no split/combine law for fractions. The header promises concurrent readers "holding
    fractions", but only `msgAt_persist` exists.
- **(d) `msgsFit` is not minimal.**
  - The 2^48 half is needed. `make` panics above `maxAlloc` (`2^48`), and an encoding that large
    is possible with shared submessages.
  - The depth half is avoidable on the receiving side. A request over 10000 levels makes
    `dec(in)` fail and the generated handler return grpc's own `Internal` status; that is no
    panic. Give `decOk_call` an `ownErr` error branch and `unaryOut` an `ownErr` disjunct (no
    `Φ`). Only the sender's stack bound remains, and it is far above 10000.
  - Formally `msgsFit` is one global opaque `Prop` for every program. It is honest only as a
    hypothesis that the adequacy theorem interprets per run. The approved `grpcRepliesFit`
    precedent covers this; make sure the closed theorems say so.
- **(c) The at-most-one-run-per-attempt claim holds** for grpc-go v1.84: transparent retry happens
  only for an unprocessed or never-created stream; there is no retry policy without a service
  config; etcd's resolver sets only `round_robin` (`internal/resolver/resolver.go:44`).
  `resolverAt`'s meaning should exclude a service config with `retryPolicy` or hedging: the
  resolver, not a dial option, can supply one.
- **`errMsg` vs status errors.** `errView`'s second disjunct (`grpc/Api.lean:226`) needs only
  `errMsg err msg`. If `errMsg` can hold of a status error, or of an error wrapping one (`FromError`
  uses `errors.As`), then `FromError.spec` and `rpctypes.Error/ErrorDesc.spec` are false. Fix: put
  "no `GRPCStatus` by `errors.As`" into `errMsg`'s meaning, or into `errView`.
- **`perRPCAt` has no introduction.** 1c's `rpcCredsAt v γ who`
  (`credentials/perRPCCredentialBundle__PerRPCCredentials.lean:38`) is never related to
  `perRPCAt pc R`. The bridge must be a callback contract on `GetRequestMetadata`: it never returns
  a status error, since grpc passes a creds' status error through verbatim with a non-`grpcMsg`
  message.
- **Stream chain.** `icChain`/`icChain_call` have no stream variant (the author's open question),
  and `sicEtcdOk` has no laws. So `Server.spec`'s `streamOk` for `RangeStream`, `LeaseKeepAlive`
  and `Snapshot` cannot be derived yet.
- **`LeaseTimeToLive`'s not-found reply vs `AttemptTriple`.** It arrives with `err = nil`, but
  `AttemptTriple`'s `nil` branch demands `Q σ σ' (.ok b)`, while the update fired with
  `.err .leaseNotFound`. 1c's `retryLeaseClient.LeaseTimeToLive` (whose reply `leaseTTLReply`
  handles this case) cannot be built on `AttemptTriple`. This is 1c's composition, through 2a's
  `ansOutcome`: raise it with 1c.
- **W0's `ansReply` at the two unmapped definite errors** is not false. `CallTriple` is a
  disjunction, and the client can take `indefCall` (`.other`). The finding is a weakening, not an
  unsoundness, as `rpctypes/Api.lean`'s header and `batch-2a.md` say.
- **`rpctypes`.** The six unmapped errors are correct (`error.go:100-163`). So are `mapped`,
  `desc`, `desc_not_grpcMsg` (every description starts with `etcdserver: `), and `Error.spec`'s
  exact result. `callErr_view` excludes `.etcd e` for an unmapped `e` except at `errVal e`.
  Consistent.

## What is good

- **proto**: the content-keyed `msgAt`/`encodes` vocabulary closes the old `pbEnc`-by-address
  inconsistency, and no caller-built model is left. The depth bound matches the decoder exactly.
  `Size`'s modular result and the `sizeCache` atomicity argument are right.
- **grpc**:
  - The `UnarySpec` urpc shape and per-address contracts replace the caller-chosen pool. `regsOk`
    is tied to `srvBuild`, which `start` consumes, so nothing can register after `Serve`.
  - `ownErr`/`grpcMsg` with `desc_not_grpcMsg` is a clean classification.
  - The stream halves with `fin` at the received count are right for HTTP/2's in-order delivery.
  - `srvSend_send` not incrementing on error matches grpc-go: `ResourceExhausted` leaves the stream
    usable.
- **v3rpc**:
  - One contract per method, with modes inside the model.
  - Validation errors fired as model answers.
  - `backendUnderQuota` is gone.
  - `ansOutcome`'s TimeToLive case matches `lease.go:67-73`.
  - `txnCheck_checked` moves the depth fact to a law over the configuration bound.
  - The learner fix on the fork is real (`membership/cluster.go:786-795`).
- **rpctypes**: an exact transcription of the table.

## Targets ranked by need of revision

1. `grpc/Api.lean` and its server specs (`start`, `Server.Serve`, `RegisterService`): F1, F2, F9,
   the `errMsg` and stream-chain gaps.
2. `v3rpc/Api.lean` (`etcdUnary`, `icEtcdOk`, `HandlerTriple`) and the handlers: F3, F4, F5, F6,
   F7.
3. The snippets `v3rpc/kv.go` and `serve.go`: F8.
4. `proto/`: interpretation and fraction laws (second tier).
5. `rpctypes/`: nothing first tier.

## Verdict

**Not done.** The proto and rpctypes layers are close. The grpc boundary has a real unsoundness
(F1: two address tokens for one socket), an unbacked counted resource (F2), and a false transport
claim (F9). The v3rpc contracts do not yet compose:

- with 2c on reads (F3) and on errors (F6);
- with 1c on token refusals (F4);
- with their own implementations on `info`, depth and health (F5, F7).

Three of the seven snippets are unprovable, and two of those panic in real runs (F8).

Bug in the Go code (not filed, code reading): compaction's admin check runs only at the gRPC layer
against the member's local auth store, so a user whose root role was just revoked can compact
through a lagging member (F8). Candidate for `nonissues/`, beside
`etcd-doserialize-auth-enable-race.md`.
