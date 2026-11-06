# Axiom review: rpctypes' error descriptions and `toGRPCErrorMap` (k8s etcd3 7c-1b)

Reviewed 2026-11-06 by the `axiom` skill, on branch `k8s-etcd3-7c` at `e65c13c6d7`; Go at the etcd
pin `673da07c8` (`api/v3rpc/rpctypes/error.go`, `server/etcdserver/api/v3rpc/util.go`,
`server/storage/mvcc/kvstore.go:38-39`), go1.27.3.

## The axioms

- `rpctypesInit` (`Proof/go_etcd_io/etcd/cache/v3/Base.lean`) and the generated
  `rpctypes.{ErrFutureRev,ErrCompacted,ErrGRPCFutureRev,ErrGRPCCompacted}_init` and the eleven
  `ErrGRPC{EmptyKey,KeyNotFound,ValueProvided,LeaseProvided,TooManyOps,DuplicateKey,
  InvalidClientAPIVersion,InvalidSortOption,NoSpace,NoLeader,NotCapable}_init`
  (`Proof/go_etcd_io/etcd/api/v3/v3rpc/rpctypes/Init.lean`, `etc/gen-init.py`'s `_RERRDESCS`):
  each variable holds some non-nil error with the stated `errDesc`.
- `v3rpc.toGRPCErrorMap_init` (`Proof/.../etcdserver/api/v3rpc/Init.lean`) with `grpcErrMapOk`
  (`Base.lean`): non-nil values; the cells' values `kf`, `kc` of `mvcc.ErrFutureRev`/`ErrCompacted`
  map to errors with `futureRevDesc`/`compactedDesc`; no other key maps to either description.

`errDesc` is opaque. What gives it meaning: `rpctypes.ErrorDesc.spec` (returns `errDesc err`),
`status.FromError.spec` (`Message()` returns `errDesc err`; for a non-status error so does
`Error()`), `rpctypes.Error.spec` (keeps the description), `rpctypes.errDesc_etcdError` (an
`EtcdError`'s is its `desc`), `errors.IsStatusErr.spec` (`Is` true ⇒ equal descriptions), and
`errStringToError`'s fact (each value's description is its key).

## Verdict: **survives** (every claim)

## Attacks tried

1. **Literal descriptions** (the 15 errors). Go test (in package `v3rpc` at the pin,
   `7c1b-init/axiomreview_test.go.txt`, output `7c1b-init/gotest.log`: PASS) checks
   `rpctypes.ErrorDesc(e)` and `status.FromError(e).Message()` of each against the axiom's
   literal: all equal. `ErrFutureRev`/`ErrCompacted` are `EtcdError`s (`Error(ErrGRPCx)` looks up
   `errStringToError[ErrorDesc]` and builds `EtcdError{code, Message()}`), so `errDesc_etcdError`
   agrees with the axioms.
2. **Through the other specs**: `FromError` of a `*status.Error` returns its own `*Status`
   (message unchanged); `errors.Is` on two status errors compares the protos (same message), on
   `EtcdError`s compares by value: neither can force two different descriptions on one value.
   `rpctypes.Error` keeps the description in Go. No spec equates two of the variables' values, so
   no equation `futureRevDesc = compactedDesc` (or any two literals) follows.
3. **Mutation** of the errors' descriptions: the variables are `↦□`; grpc's `*Status` has no
   mutator (`Proto()` clones); the `*status.Error` type is grpc-internal. Only `reflect` or a
   reassignment of the exported variable changes it, neither of which a proof here can do.
4. **Map: duplicate keys / aliasing.** The literal has 53 entries and the runtime map 53 (test):
   no two key variables hold the same value, so no later entry overwrites `kf` or `kc`. No server
   variable is assigned `mvcc.ErrCompacted`/`ErrFutureRev` (grep); they are two distinct
   `errors.New` pointers (`kf ≠ kc`, which `grpcErrMapOk` implies too).
5. **Map: coinciding descriptions.** The test iterates the map: no nil value; exactly one value
   with each description, at `kf`/`kc`, the `ErrGRPCFutureRev`/`ErrGRPCCompacted` values. The two
   `EtcdError` values (`ErrTooManyRequests`, `ErrMemberNotEnoughStarted`) have other descriptions.
6. **Ownership**: the axiom asserts `↦□` of mvcc's two cells from `True`; mvcc's initializer
   persists them itself (`mvcc/Init.lean:307-308`), so no full points-to exists to clash with.

Not tried: a Lean counterexample (none was needed); `reflect`-based writes (no model).

## For 7c-2 (`handlerDescs = [futureRevDesc, compactedDesc]`)

The init facts say nothing of errors outside the map, and they need not; but they do not suffice:

- `togRPCError`'s fallback `status.Error(Unknown, err.Error())` has description `err.Error()`
  (grpc), and **`status.Error.spec` states no description at all**, so a proof cannot show the
  fallback's description is outside `handlerDescs` without strengthening it (to
  `errDesc err = msg`, true of grpc).
- With that, the fallback carries a handler description exactly when `err.Error()` is one of the
  two strings. The test shows it does for `rpctypes.ErrFutureRev`/`ErrCompacted` (client-side
  `EtcdError`s) and for `errors.New(futureRevDesc)` (code `Unknown`, same description). In the
  server only `corrupt.go:607,610` (the peer HashKV HTTP client) returns those, not a gRPC handler;
  no other server code builds the strings. A wrapped mvcc error misses the map (`==` lookup) and
  gets `"…: mvcc: required revision …"`, equal only with the prefix `"etcdserver: "` (none found).
  A status error re-converted gets `"rpc error: code = OutOfRange desc = …"`: different.
- Context errors return unchanged (`"context canceled"`, `"context deadline exceeded"`).

So 7c-2 needs, per handler, that each unmapped error it can return has a message other than the two
(the `srvErrIs` premise of `togRPCError` is the place), plus the `status.Error` strengthening.

## Proposed restatement

None for these axioms. For 7c-2: `status.Error.spec`'s post gains `⌜errDesc err = msg⌝` (true of
grpc: `FromError` returns the `*Status` with that message).

No Go bug found.
