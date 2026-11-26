# `statusErrOk` after the combined change, `stTypedErr` + `grpcStatusIs` (#45, #24 Q4): review of its producers (2026-11-25)

An independent review by the `axiom` skill, by reading and one Go test (no Lean run: Lean builds are
forbidden on this machine). Branch `prove-isstatuserr/2026-11-25`, head `6aea5074b6` (the merge of
`status-bodies` that lands both conjuncts together); Perennial pin unchanged; grpc-go v1.84.0 (and its
model `models/grpc`, whose `internal/status` and `status` are byte-identical to v1.84.0's but for the
tests); etcd fork `upamanyus/etcd` `df6af0c36a6b`; go1.27.3. **It supersedes the scope of
[sterr-typing](sterr-typing.md)** (which reviewed `stTypedErr` alone, at `47946949c0`): that report's
findings on (a) stand and are not repeated in full here; this one covers (a) and (b) together.

**Verdict: survives.** No producer, real (grpc v1.84.0, the fork's etcd) or modelled, hands out an
error whose value is not of its dynamic type, or an error with `GRPCStatus() *Status` that is not a
`*internal/status.Error`, or a `*status.Error` whose `s`, whose status's `s`, or whose proto's `Code`
or `Message` is written after the error is handed out. No trusted entailment or premise class carries
`statusErrOk`, `grpcStatusIs` or `stTypedErr`, so the cross-world check has nothing to bite on.

## The change

`statusErrOk err` (`Proof/go_etcd_io/etcd/cache/v3/Base.lean`) now gives, for every non-nil
`e : GoInterfaceOk`:

- (a) `⌜stTypedErr e⌝`: an error of dynamic type `rpctypes.EtcdError` holds an `EtcdError`, one of
  type `context.deadlineExceededError` holds `deadlineExceededError{}`, one of a pointer type holds a
  `Loc`;
- (b) in `grpcErrMethodsOk e`'s `GRPCStatus` clause, instead of a WP of `GRPCStatus()` returning `s`:
  `∃ s c m, status.grpcStatusIs e s c m` (`Proof/google_golang_org/grpc/status/StatusRO.lean`):
  `e.ty = *internal/status.Error`, `e.v = #l`, `l.s ↦□ s`, and `status.statusAt s c m` (`s ≠ nil`,
  `s.s ↦□ p`, `p ≠ nil`, `p.Code ↦□ c`, `p.Message ↦□ m`). `descIs` and `statusCodeIs` read the
  description and the code off the same `grpcStatusIs`, and `grpcStatusIs_agree` (proved: the
  persistent points-to agree) makes two of them on one error agree.

So the trusted producers of `statusErrOk` now claim, besides (a), a type (`*internal/status.Error`) for
every error whose method set has `GRPCStatus`, and **read-only ownership** of three heap cells (four
fields) for each such error.

## The trusted statements that give `statusErrOk`

Found by grepping every occurrence of `statusErrOk`, `grpcErrMethodsOk`, `grpcStatusIs`, `stTypedErr`
in `Proof/`, `Spec/`, `TrustedCode/`, `Net/`, `GooseLang/`, `models/`, the parts and Perennial (only
`Proof/`/`Spec/` have any), listing the definitions that carry them, and checking every axiom of
`etc/tcb-baseline.txt` whose statement or `.spec` names one of those definitions
(`/shared/tmp/zeldovich-proving-3/review2/ax2.py`, by name; a namespaced axiom name the script could
not resolve was checked by hand where it could carry an error: the context and `v3rpc` axioms). As in
sterr-typing, the list:

| statement | what it asserts of the error | producer in Go |
|---|---|---|
| `status.Error.wp_proof` (axiom; `Spec/google_golang_org/grpc/status/Error.lean`) | `statusErrOk`, `descIs err msg`, `statusCodeIs err c`, `ty = *internal/status.Error`, `v = #l`, `hasGRPCStatus` | `internal/status/status.go:58,77-79,125-130`: `New(c, msg).Err()` = `&Error{s: &Status{s: &spb.Status{Code: c, Message: msg}}}`, three fresh allocations |
| `grpc.ClientConn.Invoke.wp_proof` through `grpcInvokerOk`/`grpcInvokerDone` (`Proof/google_golang_org/grpc/InvGrpc.lean:628,742`) | an attempt's error | `toRPCErr` (`rpc_util.go:1133-1157`): `nil`/`io.EOF` through; the grpc globals `errContextCanceled`, `errContextDeadline`; `status.Error(...)` (fresh); an error `FromError` accepts, returned as is: a status error grpc made (`ErrClientConnClosing`, a global; the client transport's `NewWithProto` of the received headers, `http2_client.go`, model `model_transport.go:581`, fresh) |
| `grpc.ClientConn.NewStream.wp_proof` through `cliStreamErr`/`cliStreamIs` (`InvGrpcStream.lean:367`) | stream errors | as above; with etcd's stream interceptor, `retry_interceptor.go:135,368-372` `status.Error`/`Errorf` (fresh), its token refresh's `EtcdError`s and the attempt errors passed through |
| `grpc.Server.Serve.wp_proof` through `grpcDecOk` (`InvGrpcBase.lean:709`) and the server stream contracts (`InvGrpcStream.lean:516-632`) | the decoder's and `serverStream.RecvMsg`/`SendMsg`'s errors | `io.EOF`, `io.ErrUnexpectedEOF`, `toRPCErr`'s, `status.Errorf` (fresh) |
| `Client.streamClientInterceptor.wp_proof` (`etcdStreamInterceptor`) | the stream contracts above | etcd's interceptor, as in the `NewStream` row |
| `ctxErrsErr` (in `ctxOk`) from the context axioms, `withVersion.wp_proof`, `tracing.Start.wp_proof` | `Err()`'s error | `Canceled` (`*errors.errorString`), `DeadlineExceeded` (`deadlineExceededError{}`), or the parent's (value contexts delegate `Err`): no `GRPCStatus`. `ctxErrMsg` excludes a `*status.Error` (its `Error()` is `rpc error: ...`) |
| `toGRPCErrorMap_init` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/Init.lean:103`, pre `True`) | every map value | `rpctypes.ErrGRPC*` (package-level `status.Error`s, `api/v3/v3rpc/rpctypes/error.go`), `ErrTooManyRequests`, `ErrMemberNotEnoughStarted` (`EtcdError`s) |

Not producers (checked): `rpctypesInit` and `sortNamesOk` (proved by the translated `rpctypes`
initializer over `status.Error`'s axiom, or a premise of the results; `∃`-bound, per run), `eofOk`
(theorem `eofOk_of_init`), `metrics.RecordEtcdRequest`/`OperationLatencyTracker.Record` and the
prometheus interceptor (`statusErrOk`/`srvErrOk` in a precondition, or of the handler's own error,
which the handler's proof gives), `InvKVConn.lean`'s call outcomes (`putCallOut`, `kvErr`, ...:
definitions that proofs establish; no axiom of `InvKVConn.lean`), `status.Errorf`/`FromError`/`Code`/
`Status.Code` (now theorems over the translated bodies, although `etc/tcb-baseline.txt` still lists
them as axioms: see "Side findings").

## Attacks tried

1. **An error with `GRPCStatus` that is not a `*internal/status.Error`** (b, type). grpc v1.84.0 has
   exactly one method `GRPCStatus()` (`internal/status/status.go:216`, `func (e *Error)`); the model
   `models/grpc` the same; etcd's fork has none; of every module in the Go module cache only
   `gax-go/apierror` and grpc-middleware's test proto define one, neither on etcd's or the k8s
   store's paths. In the translated code the only non-interface types whose method set has it are
   `*internal/status.Error`; the other `"GRPCStatus"` method sets (`Code/k8s_io/apiserver/pkg/storage/
   {value,etcd3}.lean`, `grpc/status`'s local `grpcstatus`) are interface types, which are never an
   interface value's dynamic type. No trusted model (`TrustedCode/`, `Net/`, Perennial's) builds an
   error with that method. Wrappers (`fmt.Errorf("%w")`, an exhausted retry policy's, a credentials
   error wrapped by grpc) have no `GRPCStatus` of their own (`errors.As` finds the inner one) and are
   not leaves, which `statusErrOk` and `grpcInvokerOk`'s bounds (`perRPCCredsOk`, no retry policy)
   already exclude. *Failed.*
2. **A `*status.Error` whose cells are written after it is handed out** (b, read-only). Every write of
   `Error.s`: the composite literal in `(*Status).Err()` (`status.go:129`), nowhere else (the type is
   in an `internal` package, not nameable outside grpc, so no whole-struct copy `*e = *e2` is possible
   from etcd or k8s; grpc has none: grep of `*x = *y` assignments). Every write of `Status.s`: the
   constructors `New`, `NewWithProto` (a fresh or freshly unmarshalled `*spb.Status`), `FromProto` (a
   clone), `WithDetails` (a new `Status` over a clone). Every write of the proto's `Code`/`Message`:
   the same constructors before the `Status` exists, and `FromError`'s `p.Message = err.Error()` on a
   `Proto()` clone. The raw proto escapes only through `RawStatusProto`, whose two callers
   (`internal/transport/http2_server.go:985,1113`; model `model_transport.go:1087,1325`) read
   `GetDetails()` and `proto.Marshal` it (writes `sizeCache` only). `grpc/status.Status` is an alias
   of the exported `*Status`, so `*st = *other` is possible from any package; neither grpc, nor the
   model, nor etcd's fork does it (grep; etcd's two `*x = *y` are bbolt options and a call option),
   the condition recorded by `examples/premisefix/grpcstatusro`. *Failed.*
3. **Measured in Go**: `examples/axiomcx/statuserr/statuserr_test.go` (`TestStatusErrCombined`, the
   examples module, go1.27.3, grpc v1.84.0 over `bufconn`). A health server whose handler returns
   `rpctypes.ErrGRPCNoLeader` (shared), a fresh `status.Error`, a status with details (the server's
   `RawStatusProto` + `proto.Marshal` path), an `EtcdError`, a plain error and `context.Canceled`;
   three rounds of calls; then a canceled, an expired and a closed-connection call. For every error
   with `GRPCStatus` it checks the dynamic type is `*internal/status.Error`, `GRPCStatus()` is the
   `Error.s` field, the proto is non-nil, and it snapshots (`Error.s`, `Status.s`, `Code`, `Message`)
   by reflection; at the end every snapshot of the handlers' errors and of the globals
   (`grpc.ErrClientConnClosing`, `ErrGRPCNoLeader`, `ErrGRPCCompacted`) is unchanged, the client's
   errors share no object with the server's, and `FromError` of a wrapper leaves the wrapped status
   unchanged:

   ```
   client:noleader   *status.Error code=14 msg="etcdserver: no leader"
   client:fresh      *status.Error code=14 msg="fresh"
   client:details    *status.Error code=9 msg="det"
   client:etcderr    *status.Error code=2 msg="etcdserver: too many requests"
   client:plain      *status.Error code=2 msg="plain"
   client:ctxcancel  *status.Error code=1 msg="context canceled"
   closed            *status.Error code=1 msg="grpc: the client connection is closing"
   canceled          *status.Error code=1 msg="context canceled"
   deadline          *status.Error code=4 msg="context deadline exceeded"
   closed: is grpc.ErrClientConnClosing's object (shared)
   --- PASS: TestStatusErrCombined (0.01s)
   ```
   The closed-connection error is grpc's global `ErrClientConnClosing` itself: shared read-only
   statuses are real, which `grpcStatusIs` (persistent) allows. *Failed.* (a)'s measurements are
   sterr-typing's attack 3 and still hold (no producer changed).
4. **Ownership conflict: a trusted post claiming `↦□` of cells the program owns exclusively.** The new
   conjunct is the first heap claim in `statusErrOk`; a trusted post that hands back, as `statusErrOk`,
   an error the verified program built and still owns (`l.s ↦ s` at fraction 1) would give `False` by
   combining the two points-to. Looked for every path by which a program's error reaches a trusted
   post: unary interceptors (`chainWP`: the axiom passes the interceptor's own post through, no claim
   of its own), server handlers (their `srvErrOk` is the handler's obligation; grpc sends the status
   over the wire and the client builds a fresh one: attack 3's "shares no object"; the model's client
   too, `model_transport.go:581`), context errors (`ctxErrsErr`: the context producer proves
   `statusErrOk` itself, and `ctxErrMsg` excludes a status error), per-RPC credentials (excluded:
   `perRPCCredsOk`, no error). `toGRPCErrorMap_init` (pre `True`) claims `↦□` of `rpctypes`' cells, which
   `rpctypes`' proved initializer also only has read-only (from `status.Error`'s axiom), and the
   opaque `toGRPCErrorMap.init` is called only by `v3rpc`'s initializer, after `rpctypes`'. *Failed.*
5. **Interaction of (a), (b) and the other facts.** `grpcStatusIs` fixes `e.ty = *Error`, `e.v = #l`:
   (a)'s arm 3. `rpctypesEtcdErrorTy` says `EtcdError` has no `GRPCStatus`, and `deadlineExceededError`
   has none, so (b) never asks a `*Error` shape of (a)'s arms 1-2. `status.Error`'s post (`ty`, `#l`,
   `descIs err msg`, `statusCodeIs err c`) is one `grpcStatusIs` in Go (the real cells hold `c`, `msg`),
   and `grpcStatusIs_agree` only identifies what Go identifies. *Failed.*
6. **Cross-world entailments** (LESSONS 2026-11-17). Every trusted occurrence is in a WP post or under a
   per-run `∃`; no axiom is an entailment concluding any of the three, and no premise class mentions
   them (there are none in those files). The laws over them (`grpcStatusIs_agree`,
   `grpcStatusIs_statusAt`, `grpcStatusIs_wp`, `grpcStatusIs_ty`, `statusAt_agree`, `statusErrOk_descIs`)
   are theorems. `grpcStatusIs`'s pure parts are about `e`'s type and value, not an opaque function of a
   pointer. *Failed.*

## Not tried

- No Lean: neither a counterexample nor a check that the proved producers (`New`'s and the accessors'
  proofs in `Proof/google_golang_org/grpc/internal/status/Methods.lean`, `rpctypes`' initializer,
  `errorString_statusErrOk`, the gRPC driver's) discharge the new obligations without `sorry`, nor that
  `methodSet (*internal/status.Error)` in the translation has `GRPCStatus` at exactly the signature the
  clause names. That is the remote build's job (`etc/tcb-report.py --check`).
- The axiom search is by name (`ax2.py`) and by hand; an axiom reaching `statusErrOk` through a
  definition chain with none of the listed names would be missed. Any such axiom is about grpc or etcd
  code, where attacks 1-2 hold for every error, so the residual risk is a trusted Lean model building a
  `*status.Error`, and none does.
- Reflection or `unsafe` writes into a status by third-party code (none on the paths read), and
  grpc versions other than v1.84.0.

## Side findings (not soundness)

- `etc/tcb-baseline.txt` still lists `status.Code.wp_proof`, `status.Errorf.wp_proof`,
  `status.FromError.wp_proof` and `status.Status.Code.wp_proof` as axioms; on this branch they are
  theorems (`Proof/google_golang_org/grpc/status/`), so `etc/tcb-report.py --check` should report the
  difference until `--check --update`.
- `status.Error.wp_proof` stays an axiom although `status.Error` is now translated with its body
  (`Code/google_golang_org/grpc/status.toml`); its spec's and proof file's header ("grpc is not
  translated") are stale. It could now be proved over the bodies (`Methods.lean` has `New`'s
  proofs, `wp_internal_New`, `wp_New_statusAt`), which would take it out of the trust base;
  `Errorf`, `Code` and `FromError` are proved over it.
