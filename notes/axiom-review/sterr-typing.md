# `statusErrOk`'s typing conjunct `stTypedErr` (#45): review of its producers (2026-11-25)

An independent review by the `axiom` skill, by reading and one Go test (no Lean run: Lean builds are
forbidden on this machine). Branch `prove-isstatuserr/2026-11-25`, head `47946949c0` (the commit
that adds the conjunct: "errors.IsStatusErr proved over errors.wp_Is (#45)"); Perennial pin
`f3c09d538`; grpc-go v1.84.0; etcd fork `upamanyus/etcd` `df6af0c36a6b`; go1.27.3.

**Verdict: survives.** No producer, real or modelled, hands out an error of the three types whose
value is not of that type, and no trusted statement claims a wrong dynamic type for an error it says
`statusErrOk` of.

## The change

`statusErrOk err` (`Proof/go_etcd_io/etcd/cache/v3/Base.lean`) gained, for every non-nil
`e : GoInterfaceOk` it covers, `⌜stTypedErr e⌝`:

1. `e.ty = rpctypes.EtcdError.ty → ∃ x : EtcdError, e.v = #x`;
2. `e.ty = context.deadlineExceededError.ty → e.v = #(zero_val deadlineExceededError)`;
3. `∀ T, e.ty = go.PointerType T → ∃ l : Loc, e.v = #l`.

These are the three target kinds `errors.IsStatusErr` (now a theorem over Perennial's `errors.wp_Is`)
compares an error with by `==` (`ComparableErr`: an error of the target's type must hold a value of
the target's Lean type for the comparison to be a `PureWp`). Perennial's model does not type interface
values, so the claim is about the values producers hand out. In real Go each arm is a fact of typing
and of the value representation: a `*T` value is a pointer (Lean `Loc`, `nil` included as `null`),
`deadlineExceededError` is `struct{}` (one value), and `EtcdError` is the translated two-field
structure (`Code/.../rpctypes.lean:1831`, a concrete Lean `structure`, not an axiomatized type), every
Go value of which is some Lean `x`.

## The trusted statements that give `statusErrOk` (and so now `stTypedErr`)

Found by grepping every `statusErrOk` occurrence outside proofs, then following the contract
definitions it appears in to the axioms that assert them (a mechanical closure over all definitions
was tried and over-approximates; the list below was checked by hand).

| statement | file | what it asserts of the error | typing |
|---|---|---|---|
| `status.Error.wp_proof` (axiom) | `Proof/google_golang_org/grpc/status/Error.lean`, triple in `Spec/google_golang_org/grpc/status/Error.lean` | `statusErrOk err`, `ii.ty = *internal/status.Error`, `ii.v = #l` | arm 3, and the post itself says `#l`: consistent by construction. grpc v1.84.0 `internal/status/status.go:125-130` returns `&Error{s: s}` |
| `grpc.ClientConn.Invoke.wp_proof` (axiom) through `grpcInvokerOk`/`grpcInvokerDone` | `Proof/google_golang_org/grpc/InvGrpc.lean:628,742` | an attempt's error: `clientErr` (types `clientErrTys`), `statusErrOk`, `hasGRPCStatus ∨ eofIs` | `*status.Error` or `io.EOF`'s `*errors.errorString`: arm 3 in Go (`rpc_util.go:1133-1157`, `toRPCErr` passes only `nil`/`io.EOF`, else `status.Error`). The `EtcdError` member of `clientErrTys` was already typed by `clientErr`'s `AsTypeTyped` (same claim as arm 1) |
| `grpc.ClientConn.NewStream.wp_proof` (axiom) through `cliStreamErr`, `cliStreamIs` | `Proof/google_golang_org/grpc/InvGrpcStream.lean:367,683-745` | stream errors: as the attempt's, plus `streamErr` (`isTypedErr`) | as above; with etcd's stream interceptor also `getToken`'s `EtcdError`s and context errors, typed (arms 1-3) |
| `grpc.Server.Serve.wp_proof` (axiom) through the server stream contracts | `Proof/google_golang_org/grpc/InvGrpcStream.lean:516-632`, `InvGrpcBase.lean:704-729` (`grpcDecOk`) | `serverStream.RecvMsg`/`SendMsg` errors, the decoder's | `io.EOF`, `*status.Error` from `toRPCErr`, or (the internal second read) grpc's own error values: all Go-typed; arm 1/2 only reachable with a real `EtcdError`/`deadlineExceededError`, which grpc never makes |
| `Client.streamClientInterceptor.wp_proof` (axiom) through `etcdStreamInterceptor` | `Spec/go_etcd_io/etcd/client/v3/Client__streamClientInterceptor.lean` | the stream contracts above | etcd's translated interceptor: values typed by Goose's translation |
| `ctxErrsErr` (in `ctxOk`), asserted by the context axioms (`context.WithValue.wp_proof`, `context.WithCancelValCtx.wp_proof`, `context.WithCancelBackground.wp_proof_canceled`, `withVersion.wp_proof`, `v3rpc.wp_WithTimeout_weak`, `v3rpc.ctxCauseOk_cancellable`) | `Proof/google_golang_org/grpc/InvGrpc.lean:365` | `Err()`'s error: `statusErrOk`, `ctxErrMsg`, `ctxErrShape`, and (already, since errors-is-deadline) arm 2 | `Canceled` (`errors.New`: `*errorString`, a `Loc`), `DeadlineExceeded` (`deadlineExceededError{}`), a parent's error, or `cancellableContext`'s `*status.Error`. Perennial's `context.isCtxErr` (`Perennial/Proof/context/Base.lean:216`) gives exactly `mkOk (*errorString) #x` or `mkOk deadlineExceededError.ty #(zero_val …)`: arms 2 and 3 |
| `toGRPCErrorMap_init` (axiom over the opaque `toGRPCErrorMap.init`) | `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/Init.lean:103` | every map value `statusErrOk` (an `∃ M`, per execution) | the values are `rpctypes.ErrGRPC*` (`*status.Error`) and `ErrTooManyRequests`, `ErrMemberNotEnoughStarted` (`EtcdError`; fork `server/v3/etcdserver/api/v3rpc/util.go:42,49`, `api/v3/v3rpc/rpctypes/error.go:187,195`): arms 3 and 1, measured below |
| `eofOk`, `sortNamesOk`, `errVarSet`, `kvErr`, `closeErrOk`, `putCallOut`/... | `InvGrpcStream.lean:423`, `InvKVConn.lean:1176-1268`, `v3rpc/Base.lean:55` | definitions: `eofOk` is a theorem (`eofOk_of_init`, from `isPkgInit io`), the others existentials or post shapes that proofs establish | no trusted assertion of its own |

Every other occurrence of `statusErrOk` is in a precondition or on the left of a wand that a proof
discharges (a stronger requirement on the prover, checked by Lean, never a soundness risk), or in a
proof.

## Attacks tried

1. **An ill-typed value from a trusted model.** Searched `TrustedCode/` (the repository's 40 models),
   `Net/TrustedCode/`, `GooseLang/Ext/`, and Perennial's `Perennial/TrustedCode/` for code building an
   error interface value. The only error-building models are `TrustedCode/os.lean`'s `model.pathError`
   (`Convert (*PathError) go.error "pe"` of a `GoAlloc`, a `Loc`) and `errors.New` calls; the
   protobuf models' `errDecode`/`errUnknown`/`Error` "do nothing" (the cells stay `nil`). None of them
   reaches a `statusErrOk` (no `os` or protobuf error is claimed `statusErrOk` by a trusted
   statement). `Net/`, `models/` and the gRPC model (`models/grpc`) never mention `statusErrOk`,
   `grpcInvokerOk` or `cliStreamErr`: in the main tree grpc's `status`/`internal/status` are names-only
   (`Code/google_golang_org/grpc/status.toml`), so its errors come only from the axioms above.
   *Failed*: no ill-typed producer.
2. **A statement that names the wrong type.** Looked for a post that says an error is an `EtcdError`
   (or `deadlineExceededError`) when the Go code returns another type, or that says an error is
   pointer-typed while fixing its value to a non-`Loc`: grepped every `mkOk (… PointerType …) #v` in the
   grpc, context, status and protobuf trust-boundary specs (all `v : Loc`), and read the types each
   axiom claims (`status.Error`: `*internal/status.Error`, true at v1.84.0; `clientErrTys`, unchanged
   and already reviewed by k8s 7e-1). *Failed*.
3. **Measured in Go** (`/shared/tmp/zeldovich-proving-3/review/sttyping/sttyping_test.go`, a scratch
   module with the examples module's pins, go1.27.3): the dynamic type and kind of every error the
   statements above cover, checked against `stTypedErr` (an `EtcdError` assertion, the zero value of
   a zero-size `deadlineExceededError`, a pointer), and `errors.Is` of each against the targets
   `IsStatusErr` admits (no panic):

   ```
   status.Error(Unknown)        *status.Error                        kind=ptr
   status.Errorf                *status.Error                        kind=ptr
   io.EOF                       *errors.errorString                  kind=ptr
   context.Canceled             *errors.errorString                  kind=ptr
   context.DeadlineExceeded     context.deadlineExceededError        kind=struct
   FromContextError(cancel)     *status.Error                        kind=ptr
   ErrGRPCNoLeader              *status.Error                        kind=ptr
   ErrTooManyRequests           rpctypes.EtcdError                   kind=struct
   ErrMemberNotEnoughStarted    rpctypes.EtcdError                   kind=struct
   ErrInvalidSortOption         rpctypes.EtcdError                   kind=struct
   Error(ErrGRPCNoLeader)       rpctypes.EtcdError                   kind=struct
   WithTimeout(0).Err()         context.deadlineExceededError        kind=struct
   --- PASS: TestTypes (0.00s)
   ```
   *Failed*: every value is of its type.
4. **Interaction with the other conjuncts and facts.** `stTypedErr` constrains only `e.v` given `e.ty`;
   the other conjuncts of `statusErrOk` (`errorMsgIs`, `isLeafError`, `grpcErrMethodsOk`, the
   `Format`/`Error` method-set facts) and the facts beside it in the posts (`clientErr`'s
   `AsTypeTyped`, `errCellOk`, `errPtrOk`, `descIs`, `hasGRPCStatus`, `ctxErrShape`, `isTypedErr`)
   constrain types, method sets or heap cells. The only overlaps are `clientErr`'s `AsTypeTyped
   EtcdError` (arm 1, identical), `ctxErrsErr`'s deadline clause (arm 2, identical), `errPtrOk` and
   `IsPointerError` (arm 3, implied by or equal to). No combination fixes a value incompatible with
   an arm: e.g. `status.Error`'s post is `PointerType … ∧ ∃ l, ii.v = #l`. *Failed*.
5. **Cross-world entailments** (LESSONS 2026-11-17). `stTypedErr` is a pure conclusion, so a trusted
   entailment from bare persistent cells to `statusErrOk` (`cell ↦□ e -∗ statusErrOk e`, without an
   `isPkgInit` that fixes the cell) would make it a Lean fact in a fresh heap holding an ill-typed
   value, hence `False`. Every trusted occurrence is in a WP postcondition (per execution) or an
   existential (`errVarSet`, `sortNamesOk`, `toGRPCErrorMap_init`'s `∃ M`); the one universal form,
   `eofOk` (`∀ err, eofIs err -∗ statusErrOk err`), is a theorem from `isPkgInit io`
   (`ErrorsNewOk.lean:223`), not an assumption. No axiom or premise class states such an entailment.
   *Failed*.
6. **Vacuity of a premise** (the `ctx-readerrs-vacuity` shape: a strengthened premise that no value
   meets). No premise class mentions `statusErrOk` (the classes in the files that use it,
   `ErrorStringNoGRPCStatus`, `RpctypesEtcdErrorMethods`, `KUserErr`, state method sets or callbacks);
   and the values that premises and contracts ask `statusErrOk` of are the ones measured in 3, which
   meet every arm (Perennial's context init gives exactly arm 2's value). *Failed*.

## Not tried

- No Lean: neither a counterexample nor a check that the new obligations (`stTypedErr` of each proved
  producer: `errorString_statusErrOk`, `eofOk_of_init`, `ChanCtx`, `rpctypes.Error`, the gRPC driver's
  `StreamDefs`) are discharged without `sorry`. That is the remote build's job; a `sorry` there would
  show in `etc/tcb-report.py --check`.
- The over-approximating closure (`/shared/tmp/zeldovich-proving-3/review/closure.py`) was not refined
  into an exact list of every axiom whose statement reaches `statusErrOk` through definitions; the
  list above comes from the contract definitions found by hand (grpc client, server, stream, context,
  `v3rpc` initializer), so an axiom reaching `statusErrOk` through an unusual definition chain may be
  missing. Any such axiom is about untranslated Go code (where arms 1-3 hold by typing) or translated
  code (typed by Goose's translation), so the residual risk is a trusted Lean model, and attack 1
  found none that builds a `statusErrOk` error.
- Goose's translation itself (that a translated expression of static type `*T` evaluates to a `Loc`,
  of type `EtcdError` to `#x`) is assumed, as everywhere in this repository.
