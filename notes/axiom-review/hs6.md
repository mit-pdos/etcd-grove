# Axiom review: HS-6's restatements (`statusErrOk` on the server's error paths), k8s etcd3 7c

**Reviewed** 2026-11-06, branch `k8s-etcd3-7c` at `da6390e83b` (HS-6, WIP draft), and the two
restatements HS-6 plans but has not written yet (2 and 3 below). `statusErrOk err`
(`Proof/go_etcd_io/etcd/cache/v3/Base.lean:322`): for `err = ok e`, `errorStringSpec e` (`Error()`
returns), `isLeafError e` (no `Unwrap`/`As` method) and `grpcErrMethodsOk e` (`GRPCStatus()` and
`Is(target)`, if present, return). At this commit `handlerDescs = []` (`InvGrpc.lean:122`), so
every `errDesc err ∉ handlerDescs` conjunct is vacuous; the review also checks them at 7c-1b's
value `[futureRevDesc, compactedDesc]`.

Go: grpc-go v1.84.0, go-grpc-middleware `providers/prometheus` v1.1.0 over `v2` v2.3.4 (etcd's
`server/go.mod` at the pin `673da07c8f`; `error.go` and `util.go` there are identical to the
`.lake/go-src/etcd` checkout `249d76bea7` the line numbers below refer to), go1.27.3. Go probes in
`hs6/` (`*_test.go.txt`, `go.mod.txt`; run as a module of their own, the etcd `api` module replaced
by the checkout), output `hs6/gotest.log`. No Lean counterexample: nothing was refuted.

| statement | verdict |
|---|---|
| 1. `grpcDecOk`'s error branch `⌜err ≠ nil ∧ errDesc err ∉ handlerDescs⌝ ∗ statusErrOk err` | **survives**, for `grpc.Server.Serve` (the only transport `grpc.start` covers); false under `ServeHTTP` (out of scope; a docstring caveat proposed) |
| 2. `rpctypes.ErrGRPC*_init` posts gain `statusErrOk` (planned) | **survives** |
| 3. `toGRPCErrorMap_init`'s values gain `statusErrOk` (planned) | **survives** (two values are `EtcdError`s, not status errors; still `statusErrOk`) |
| 4. `status.Error.spec`: `err ≠ nil ∗ statusErrOk err ∗ errDesc err = msg` | **survives** |
| 5. prometheus `UnaryServerInterceptor` with the restated `srvInterceptorOk`, `grpcHandlerOk*`, `grpcMethodOk*` | **survives**: 7c1b-grpc's refutation is repaired |
| 6. `EtcdGrove.ContextReadErrs` (premise class) with `errLeaf`'s and `ctxDeadlineLeaf`'s new `GRPCStatus = none` conjunct (uncommitted draft) | **survives** |
| 7. `bcrypt.GenerateFromPassword.wp_proof`'s error branch with `GRPCStatus = none` (uncommitted draft) | **survives**; the two-error list is complete (no `KeySizeError`, no `rand` error) |

Items 6 and 7 were added at the coordinator's request; both read the uncommitted draft in
`/shared/etcd-grove-7c` on 2026-11-06.

Findings in Go: one in etcd (verified code, recorded as
`nonissues/etcd-v3rpc-togrpcerror-etcderror-unknown-code.md`), one in grpc (trust base, here only).

## 1. `grpcDecOk` — survives (scope: `Serve`)

`grpcDecOk` reaches a handler only through `grpc.serve`, whose server token comes from `grpc.start`
(`InvGrpcServer.lean:266-275`: "`Serve(lis)` serves every call accepted on `lis`"), so the
transport is `http2Server`. Every verified program calls `gs.Serve(l)`
(`examples/lib/etcdstart/common.go:200`, `examples/lib/cluster3/cluster3.go:111`).

The unary `dec` is `df := func(v any) error { return stream.RecvMsg(v) }` (`server.go:1283`), i.e.
`serverStream.RecvMsg` (`stream.go:1891-1971`). The generated handlers call `dec` once, before the
interceptor, and return its error unchanged.

**Producers of a server-side read error** (`http2Server`):

| producer | error | leaf / `statusErrOk` |
|---|---|---|
| `recvBuffer` messages: `http2_server.go:534` (headers with END_STREAM), `:834` (DATA with END_STREAM) | `io.EOF` | the only errors `http2Server` ever puts in the buffer (`write(recvMsg{err: …})`: these two sites only); `closeStream`/`finishStream`/`Close` (`:1291-1381`) only cancel the stream's context |
| context done: `recvBufferReader.readMessageHeader`/`read` (`transport.go:280-295`) | `ContextErr(ctx.Err())` (`transport.go:870-878`): `status.Error(DeadlineExceeded \| Canceled, …)`, else `status.Errorf(Internal, …)` | `*status.Error`: leaf; the stream's context is `context.WithTimeout`/`WithCancel` (`http2_server.go:536-540`) |
| partial header/body then EOF: `Stream.ReadMessageHeader` (`transport.go:479`), `Stream.read` (`:525`), `parser.recvMsg` (`rpc_util.go:804`) | `io.ErrUnexpectedEOF` (sticky in `trReader.er`) | `*errors.errorString`: leaf, `Error()` returns, no `GRPCStatus`/`Is` |
| `parser.recvMsg` size checks (`rpc_util.go:794-799`) | `status.Errorf(ResourceExhausted, …)` | leaf |
| `checkRecvPayload` (`rpc_util.go:908-925`) | `status.New(…).Err()` | leaf |
| `decompress` (`rpc_util.go:985-1047`) | `status.Errorf(Internal \| ResourceExhausted, …)` | leaf |
| `recv`'s unmarshal (`rpc_util.go:1064`) | `status.Errorf(Internal, "grpc: failed to unmarshal …")` | leaf |
| `RecvMsg` itself (`stream.go:1931,1970`) | the two cardinality violations, `status.Error(Internal, …)` | leaf |

The sticky `recvBufferReader.err` (`transport.go:239-275`) and `transportReader.er` only replay one
of these. `transport.ConnectionError` (non-leaf: `Unwrap`, `transport.go:820`) is never put in an
`http2Server` stream's buffer: its only reader-side producer is `serverHandlerTransport`'s
`mapRecvMsgError` (`handler_server.go:493-506`), i.e. `ServeHTTP`.

**First recv** (`stream.go:1921-1938`): `io.EOF` becomes the cardinality status error (a unary
call has `!ClientStreams` and `!recvFirstMsg`), `io.ErrUnexpectedEOF` becomes `status.Error(Internal,
…)`, the rest goes through `toRPCErr` (`rpc_util.go:1133-1155`). Its `status.FromError(err) ok →
return err` case returns the error unchanged: reached only by the `*status.Error` leaves above (a
non-leaf with a status in its chain has no producer; `ConnectionError` is caught by the type switch
first, `rpc_util.go:1146`, and becomes `status.Error(Unavailable, e.Desc)`). Its `switch err` compares
interfaces, which cannot panic here (a panic needs both sides of one uncomparable type). All
results are `*status.Error` leaves.

**Second recv** (`stream.go:1964-1969`) returns `err` raw unless it is `io.EOF`: a `*status.Error`
leaf or the raw `io.ErrUnexpectedEOF`. Go confirms it (`TestDecErrors`: a complete first message
followed by 2 bytes of a header, or by a header and a short body, then END_STREAM: `dec` returns
`*errors.errorString "unexpected EOF"`, `== io.ErrUnexpectedEOF`; every other case a
`*status.Error`).

**Which non-`statusErrOk` errors reach `dec`'s caller under `Serve`: none.** The only non-status
error, `io.ErrUnexpectedEOF`, meets `statusErrOk`. At `handlerDescs = [futureRevDesc, compactedDesc]`
none of these descriptions can equal either: they are fixed grpc texts, `"unexpected EOF"`,
`"context canceled"`/`"context deadline exceeded"`, or the unmarshal error's fixed prefix (the
codec is `proto`'s, `grpcProtoCodec`).

**Out of scope, and false there: `ServeHTTP`.** etcd serves gRPC through `(*grpc.Server).ServeHTTP`
when TLS and HTTP share a port (`server/embed/serve.go:260,314-324`). There the body-reading
goroutine puts `mapRecvMsgError(err)` in the buffer (`handler_server.go:449`), which for a `net/http`
body error that is neither `io.EOF`/`io.ErrUnexpectedEOF`, nor `x/net`'s `http2.StreamError`
(`net/http`'s bundled HTTP/2 server uses its own type), nor "body closed by handler", is
`connectionErrorf(true, err, …)`: a `transport.ConnectionError`, whose `Unwrap` makes it no leaf.
The second recv returns it raw. `TestServeHTTPConnErr`: a request declaring `content-length: 100`
with one 5-byte message and END_STREAM gives `dec` `transport.ConnectionError "connection error:
desc = \"request declared a Content-Length of 100 but only wrote 5 bytes\""` in 200 of 200 runs
(an RST_STREAM instead gives `Canceled`: the request's context wins). No panic follows (grpc's
`processRPC` handles it; `status.FromError` walks to the inner `*errors.errorString`). No axiom of
this repository covers `ServeHTTP`, so this refutes nothing; but `grpcDecOk`'s docstring ("grpc's
`dec` for a call") does not say so.

**True shape.** For `Serve`, the branch as written. Proposed (not applied): `grpcDecOk`'s docstring
names the scope ("of `Serve`'s HTTP/2 transport; under `ServeHTTP` a body-read error reaches `dec`
as a `transport.ConnectionError`, no leaf"). If `ServeHTTP` is ever modeled, its branch is
`⌜err ≠ nil ∧ errDesc err ∉ handlerDescs⌝ ∗ (statusErrOk err ∨ grpcConnErr err)` with
`grpcConnErr` a `ConnectionError` whose `Error()` and `Unwrap()` return and whose `Unwrap()` is a
`net/http` body error meeting `statusErrOk`, and the method handler's post could then no longer give
`statusErrOk err` (it would carry the same disjunction to `processRPC`, which accepts it).

**grpc finding (trust base, no file):** `RecvMsg`'s second recv returns `io.ErrUnexpectedEOF`
unconverted while the first converts it (`stream.go:1935-1936` vs `:1965-1968`), so a client's
truncated second message makes the call end with `codes.Unknown` (`processRPC`'s
`FromContextError`, `server.go:1461-1467`) where a truncated first message gives `Internal`. No
panic; a code inconsistency only.

## 2. `rpctypes.ErrGRPC*_init` gain `statusErrOk` — survives

`api/v3rpc/rpctypes/error.go:23-96`: all 64 `ErrGRPC*` variables but one are `status.Error(codes.X, "…")`
with a code other than `OK` (63 `status.Error(codes` calls in the file, none with `OK`), no
wrapping; the exception is `ErrGRPCClusterIdMismatch = ErrGRPCClusterIDMismatch` (`:53`), the same value. So
each is a non-nil `*status.Error` (`internal/status/status.go:125-130`), a leaf: its methods are
`Error`, `GRPCStatus`, `Is` (`:211-228`). `Error()` is `e.s.String()`, a `Sprintf` of the code
(`codes.Code.String` formats any value) and the message; `GRPCStatus()` returns `e.s`. `Is(target)`
returns for every target a program can build: it type-asserts to `*Error` and runs `proto.Equal`;
it would dereference `nil` on a typed-nil `*internal/status.Error` target, which code outside grpc
cannot name (an internal package, and grpc never returns one: "a nil `*Error` should never be
returned"), so no Go program reaches it without `reflect`/`unsafe`.

The `_init` axioms the restatement changes are those without `statusErrOk` today
(`Proof/go_etcd_io/etcd/api/v3/v3rpc/rpctypes/Init.lean`): `ErrGRPCFutureRev` (`error.go:33`),
`ErrGRPCCompacted` (`:32`), `ErrGRPCInvalidAuthToken` (`:73`), `ErrGRPCAuthOldRevision` (`:75`),
`ErrGRPCUserEmpty` (`:62`), `ErrGRPCPermissionDenied` (`:69`), `ErrGRPCWatchCanceled` (`:40`): all
`status.Error`. None is reassigned anywhere in etcd (grep). **None to list as not
`status.Error`-built.**

## 3. `toGRPCErrorMap_init`'s values gain `statusErrOk` — survives

`server/etcdserver/api/v3rpc/util.go:35-97`: 53 entries; 51 values are `rpctypes.ErrGRPC*` (status
errors, as in 2); two are client-side `EtcdError`s: `rpctypes.ErrMemberNotEnoughStarted`
(`util.go:42`, `error.go:187`) and `rpctypes.ErrTooManyRequests` (`util.go:48`, `error.go:195`),
each `Error(ErrGRPCx)` = `EtcdError{code, desc}` (`error.go:256-272`). `EtcdError` is a struct with
the value methods `Code()` and `Error()` (`:248-254`): a leaf, `Error()` returns `e.desc`, no
`GRPCStatus`, no `Is`, so `grpcErrMethodsOk` holds vacuously and `statusErrOk` holds. The map is
never written after init (its one other use is the lookup, `util.go:103`). The restated docstring
should say "status errors and two `EtcdError`s", not "status errors": `errDesc` of the two is their
`desc` (no status: `FromError` gives `Unknown` with `Error()`), which `grpcErrMapOk` already allows.

**etcd finding** (`nonissues/etcd-v3rpc-togrpcerror-etcderror-unknown-code.md`): those two values
reach the wire as `codes.Unknown`, not `FailedPrecondition`/`ResourceExhausted` (`TestWireCode`):
`processRPC`'s `status.FromError` finds no status in an `EtcdError` and falls to `Unknown`
(`server.go:1461-1467`). etcd's Go client recovers the right `EtcdError` by description
(`rpctypes.Error`), so only the wire code (other clients, the gateway's HTTP status, metrics) is
wrong.

## 4. `status.Error.spec` — survives

`status.Error(c, msg)` = `New(c, msg).Err()`; for `c ≠ OK` it returns `&Error{s}` with
`s.s = &spb.Status{Code: c, Message: msg}` (`internal/status/status.go:76-78,125-130`): non-nil,
`statusErrOk` as in 2 (the attack on `Is` with a typed-nil target fails the same way; `s` is never
nil). `errDesc err = msg`: `errDesc` is what `status.FromError(err).Message()` returns; `FromError`
takes the direct `GRPCStatus()` branch and returns `e.s`, whose `Message()` is `msg` byte for byte
(no UTF-8 check at `New`; grpc rewrites invalid UTF-8 only when it encodes `grpc-message` on the
wire, which is `grpcInvokerOk`'s business, not this spec's: a desc in `handlerDescs` is valid UTF-8
and survives the trip, and a rewritten one gains U+FFFD so cannot become one).

Not attacked (D29's design, shared with `withtimeout-md`'s caveat): `errDesc` is a function of the
interface value, fixed before the run, while the `*Error`'s location is chosen by the allocator; a
single run cannot give one location two messages, so no program can exploit it.

## 5. prometheus `UnaryServerInterceptor` and the restated contracts — survives

7c1b-grpc refuted this axiom (in Go) because `srvInterceptorOk` left the handler's error
unconstrained while `PostCall` runs `status.FromError` on it. HS-6's `srvInterceptorOk`
(`InvGrpc.lean:540-549`) gives the interceptor `statusErrOk err` with the handler's result and
requires it on the early return.

- **The interceptor** (`v2/interceptors/server.go:16-28`, `providers/prometheus/reporter.go`): it
  calls `handler(newCtx, req)` once, with `newCtx = ctx` (`reportable.reporter` returns the context it
  is given, `reporter.go:130`), and returns `resp, err` unchanged; it never returns early (the
  second conjunct is unused). `PostMsgReceive`/`PostMsgSend` ignore the error. `PostCall(err)`
  (`reporter.go:24-46`) runs `FromError` (`options.go:14-21`): `status.FromError` on a
  `statusErrOk` error asserts `GRPCStatus` (returns, maybe `nil`: then `New(Unknown, err.Error())`),
  else `errors.As` on a leaf only checks its type, then `New(Unknown, err.Error())` (`Error()`
  returns); on `!ok`, `status.FromContextError` runs `errors.Is` twice (an `==` that cannot panic
  across types, then `Is` if present: returns), then `New`. `Code()` and `Code.String()` return;
  the label counts match (`grpc_type`, `grpc_service`, `grpc_method`, `grpc_code`; no context labels
  without options). **No panic.**
- **grpc's server** (`server.go:1459-1497`): `status.FromError(appErr)` as above; on `!ok`
  `FromContextError(appErr).Err()`; `writeStatus` of a non-nil status; the trace's `Message()` and
  the stats handler's `toRPCErr(err)` (the deferred `stats.End`, `server.go:1343-1348`) likewise.
  `RecvMsg`'s own defer (`stream.go:1892-1914`) runs `status.FromError(toRPCErr(err))` on the `dec`
  error: `toRPCErr` of the raw `io.ErrUnexpectedEOF` is a status error. **No panic.**
- **What the contracts now promise.** `grpcHandlerOk*`/`grpcHandlerOwnOk*`/`grpcMethodOk*` posts
  gain `statusErrOk err`: obligations on the proved handlers, consumed by `grpc.serve` (a stronger
  premise makes that axiom weaker). `srvInterceptorOk`'s early branch now takes `statusErrOk err`:
  an obligation on the proved interceptors. `grpcSrvChain`/`srvChainWP` (grpc's chain closure) are
  unchanged: the fact rides in `Ψ` (`srvChainWP_of_ok`), so grpc is promised to do nothing new.
  `grpcDecOk` is the one new promise grpc makes (1). The client side (`grpcInvokerOk`) is unchanged
  by HS-6 (`git diff 6b49f77e01 da6390e83b`). Nothing promised is false.

## 6. `EtcdGrove.ContextReadErrs` with the `GRPCStatus` conjuncts — survives

Read in the uncommitted draft of `/shared/etcd-grove-7c` (`git diff` on 2026-11-06). The class
(`Proof/go_etcd_io/etcd/server/v3/etcdserver/read/Init.lean:68-71`) is unchanged: `isPkgInit
context ⊢ errVarLeaf context.Canceled ∗ ctxDeadlineLeaf` (`read/Init.lean` has no diff). What
changes is the two definitions it is written in:

- `errLeaf` (`apply/Base.lean:71-74`): `IsPointerError e ∧ isLeafError e ∧ no Is ∧`
  **`methodSet e.ty !! "GRPCStatus" = none`**; `errVarLeaf g` (`:316`) is `g ↦□ ok e ∗ ⌜errLeaf e⌝ ∗
  errMsgOk e`, unchanged.
- `ctxDeadlineLeaf` (`BaseApply.lean:309-318`): `isLeafError e ∧ no Is ∧ not a pointer type ∧
  SafeMapKey ∧` **`methodSet e.ty !! "GRPCStatus" = none`**, then `errMsgOk e`, otherwise unchanged.

go1.27.3 (`src/context/context.go:168`): `var Canceled = errors.New("context canceled")`, a
`*errors.errorString`, whose only method is `Error` (`src/errors/errors.go:73`): a pointer, a
leaf, no `Is`, no `GRPCStatus`, and `Error()` returns. `:172-178`: `var DeadlineExceeded error =
deadlineExceededError{}`, an empty struct with the value methods `Error`, `Timeout`, `Temporary`:
not a pointer, a leaf, no `Is`, no `GRPCStatus`, comparable (a safe map key), `Error()` returns
the constant `"context deadline exceeded"`. Every conjunct, old and new, holds of both together;
the new one is independent of the others (a method-set lookup at a name none of them mentions).
The repository side is consistent with it: `ErrorStringLeaf` gains `noGRPC`, derived from goose's
method set of `*errorString` (`Proof/errors/NewVar.lean`, `errorStringLeaf_inst`), so the other
`errVarLeaf` facts (`errVarLeaf_of_newVar`) are proved, not assumed. The class stays a premise of
the closed theorems (`txnlin`, `leasegrant`, `leaseexpiry`, `watch` `Results`/`Adequacy`): it is
now harder to discharge, never easier.

## 7. `bcrypt.GenerateFromPassword.wp_proof` with `GRPCStatus = none` — survives

Read in the uncommitted draft (`Spec/golang_org/x/crypto/bcrypt/GenerateFromPassword.lean`: the
error branch's pure facts gain `methodSet ei.ty !! "GRPCStatus" = none`, the docstring cites
`bcrypt.go:50-52, 87`). Go: x/crypto v0.57.0, go1.27.3. Probe `hs6/bcrypt_test.go.txt`, output
`hs6/gotest-bcrypt.log`.

**The two errors.** `ErrPasswordTooLong = errors.New(…)` (`bcrypt.go:87`): a `*errors.errorString`,
methods `[Error]`. `InvalidCostError int` (`:50-54`): methods `[Error]` (value receiver,
`fmt.Sprintf`). Neither has `GRPCStatus` (reflection in `TestErrorMethods`; `grep GRPCStatus` in
`bcrypt/` finds nothing).

**Every other error path** of `GenerateFromPassword` (`:95-104`) → `newFromPassword` (`:139-165`):

- `checkCost` (`:299-304`): only `InvalidCostError`, only for `cost > MaxCost = 31` (a cost below
  `MinCost` becomes `DefaultCost`, `:140-142`). In the list.
- (a) `io.ReadFull(rand.Reader, unencodedSalt)` (`:154`). go1.27.3: `crypto/rand.Reader =
  rand.Reader` (`src/crypto/rand/rand.go:34`), `crypto/internal/rand`'s `reader{}`
  (`src/crypto/internal/rand/rand.go:38`), whose `Read` (`:22-31`) returns `len(b), nil` after
  `drbg.Read(b)`, or panics if the BoringCrypto reader fails; `drbg.Read`
  (`src/crypto/internal/fips140/drbg/rand.go:33-77`) has no error result: it reads the testing
  reader (set only by `testing/cryptotest`), or `sysrand.Read`, which calls `runtime.fatal` on a
  failure (`src/crypto/internal/sysrand/rand.go:37-51`), or the DRBG over `sysrand`. So `ReadFull`
  of 16 bytes gets `n = 16, nil`: **no error**, unless the program replaces `rand.Reader` (etcd does
  not; the spec's docstring says so, as `gentokenprefix.md` found).
- (b) `bcrypt(password, cost, salt)` (`:160`, `:196-215`) fails only through
  `expensiveBlowfishSetup` (`:217-235`):
  - `base64Decode(salt)` (`base64.go:23-35`): the salt is `base64Encode` of 16 bytes (`:159`):
    24 characters with the two `=` stripped, 22 characters of `alphabet`; `22 % 4 = 2`, so two `=`
    are appended back and the 24 characters decode to the 16 bytes (the encoder zeroes the
    trailing bits; `bcEncoding` is not `Strict` anyway). **No error.**
  - `blowfish.NewSaltedCipher(ckey, csalt)` (`blowfish/cipher.go:52-63`): `csalt` has 16 bytes, so
    the `len(salt) == 0 → NewCipher` branch (the one with the 1..56 bound, `:38-46`) is not taken;
    the salted branch returns `KeySizeError` only for `len(key) < 1`, and `ckey = append(key, 0)`
    (`:226`) has at least one byte. No upper bound in that branch (73 bytes are fine). **`KeySizeError`
    is unreachable.**

`TestNoOtherError`: every password length 0..72, bytes `0x00`, `'a'`, `0xff`, cost 4 (and a sample
at costs -1, 0, 3, i.e. `DefaultCost`): no error, a 60-byte hash. **The spec's two-error list is
complete.**

## Not tried

- A Lean counterexample: no attack produced a Go panic, so there was nothing to prove.
- The stream (`grpc.serveStream`, `srvStreamInterceptorOk`) side: HS-6's plan names it ("the stream
  interceptor's check") but this commit does not restate it.
- Whether each proved handler can in fact establish its new `statusErrOk err` (e.g. `togRPCError`'s
  context-error branch returns the server's error unchanged): those are proofs, not trusted
  statements; the build checks them.
