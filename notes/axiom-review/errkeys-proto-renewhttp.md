# `proto.MarshalIRR` and `leasehttp.RenewHTTP`: `applyErrIs` claimed of non-leaf, non-key errors (false)

Found 2026-11-26 by the map-key audit (zeldovich proving session 2, `/shared/tmp/ps2/mapkeys/report.md`,
findings F1, F2, at `lean` `9d454f138b`). Fixed or recorded by mapkeys on the same day. Both axioms
post `applyErrIs err`, which holds `errKeyOk err` (a key of `togRPCError`'s map, `v3rpc.errKeys`:
`nil`, pointers, `deadlineExceededError{}`, `InvalidCostError`) and `srvErrOk err` (a leaf error,
`statusErrOk`, or a `%w`-wrapped context error). Neither post is unsatisfiable, since the callees'
results are opaque, but both are false of Go.

## F2: `leasehttp.RenewHTTP.spec` (fixed)

`RenewHTTP` (`server/lease/leasehttp/http.go`) passes some library errors on as they are:

- `proto.Marshal`'s error, a `*prefixError` with `Unwrap`;
- `http.NewRequest`'s and `Client.Do`'s error, a `*url.Error` with `Unwrap`;
- `io.ReadAll`'s error on the body (`readResponse`). Over TLS this is `tls.RecordHeaderError`, a struct value with fields; it can also be a `*net.OpError` or a context error;
- the decode's error, wrapped by `fmt.Errorf`'s `%w`.

None of these is `errKeyOk`, and only some are leaves. The audit flagged the body-read errors, and the `*url.Error` and `%w` arms are false for the same reason (`isLeafError`).

**Fix.** The post gains a third arm, `err ≠ nil ∗ leasehttp.notLeaseNotFound err`
(`Proof/go_etcd_io/etcd/server/v3/lease/leasehttp/RenewErr.lean`). It says that the error is in an error tree in which no error is `lease.ErrLeaseNotFound`'s value and no `Is` method answers `true` for it.

This is a weakening: the old post implied it, so the axiom's trust shrinks. It is true of Go: `ErrLeaseNotFound` is a private `errors.New` pointer, and the libraries' `Is` methods compare with their own sentinels.

The one consumer, `EtcdServer.LeaseRenew`, needs no more than this. In that arm its `errors.Is(err, ErrLeaseNotFound)` is `false` (`errors.Is.spec`'s post), and it tries the next URL. Every caller still proves, and no top-level statement changes.

## F1: `proto.MarshalIRR.spec` (fixed 2026-11-26: `nonleaf-status-errs.md`)

Invalid UTF-8 in a proto3 string field is the only error `Marshal` of an `InternalRaftRequest` can return:

- the fast path returns `impl.errInvalidUTF8{}` (protobuf-go v1.36.12 `internal/impl/codec_gen.go:5041-5049`). It is a field-less struct whose methods are `Error`, `InvalidUTF8` and `Unwrap() error`, the last returning `errors.Error`;
- the reflective path returns `errors.InvalidUTF8(name)`, a `*prefixError` that also has `Unwrap`;
- `proto/encode.go:105-116, 198-204` passes either on unwrapped.

The audit found that the struct is not `errKeyOk`. This review adds a second problem: neither error is a leaf, so `srvErrOk` is false of both. Widening `errKeyOk` alone, the fix the audit preferred, therefore leaves the post false. The widening is also not provable today: `errInvalidUTF8` is names-only (`Code/google_golang_org/protobuf/internal/impl.lean`, opaque `underlying`), so its `==` has no semantics.

A UTF-8 premise, like `MarshalUser.lean:49`'s, would make the error arm unreachable. Its callers cannot discharge it yet: `apply.internalRaftRequestIs` does not carry the strings' validity, and `processInternalRaftRequestOnce`'s request comes from every proposer, with the header's `Username` taken from the auth token.

Real etcd never reaches the arm, because gRPC's decoding validates every proto3 string and usernames come from such strings. The docstring, which said every protobuf error is a pointer, is corrected. The axiom stays as it is until one of these lands:

1. a UTF-8 premise carried by the request model from the gRPC handlers' decoded requests and the auth store's names;
2. `srvErrOk`/`statusErrOk` widened to non-leaf errors (grpc's `status.FromError` spec walking `Unwrap`, grpc's area), with `errInvalidUTF8` translated as its struct and added to `errKeyOk`.
