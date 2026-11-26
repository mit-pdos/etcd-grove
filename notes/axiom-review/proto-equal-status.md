# Review: `proto.EqualStatus.wp_proof` and the read-only `statusAtRaw` extension

Reviewer: an independent `axiom`-skill run, 2026-11-26, for coordinator #37. Revision: worktree
`prove-statuserror/2026-11-26` at `d31b1781b5688d65bc5c832d97556840432725d0` plus uncommitted
changes (the statements below are in the uncommitted part). Go checked against protobuf-go v1.36.12,
grpc-go v1.84.0 (both `examples/go.mod`'s pins; `models/grpc/{internal/,}status/status.go` are
byte-identical to v1.84.0's), genproto `googleapis/rpc` at `examples/go.mod`'s pin, go1.27.3. No Lean
was run: no counterexample triple was reachable (below), so there was nothing to prove.

## Statements reviewed

1. `proto.EqualStatus.spec` (`Spec/google_golang_org/protobuf/proto/EqualStatus.lean`) and its axiom
   `proto.EqualStatus.wp_proof` (`Proof/google_golang_org/protobuf/proto/EqualStatus.lean`): for any
   `p q`, from `isPkgInit proto ∗ pbStatusRO p c m ∗ pbStatusRO q c' m'`, `proto.Equal` of the two
   `*spb.Status` interface values returns some `b` with `b = true → c = c' ∧ m = m'`. Used by
   `status.wp_Error_Is` (`Proof/google_golang_org/grpc/internal/status/ErrorMethods.lean`), hence by
   the now-proved `status.Error.wp_proof`.
2. The trusted vocabulary `status.statusAtRaw` (`Proof/google_golang_org/grpc/status/StatusRO.lean`),
   now `∃ p, s.s ↦□ p ∗ pbStatusRO p c m`, with `pbStatusRO` = `p ≠ nil`, `Code ↦□ c`, `Message ↦□ m`,
   `pbStatusRestRO p` (`unknownFields ↦□ u ∗ u ↦*□ ub`, `Details ↦□ d ∗ d ↦*□ ds`, each element
   `pbAnyRO`: nil, or `TypeUrl ↦□`, `Value ↦□ v ∗ v ↦*□ vb`, `unknownFields ↦□ u ∗ u ↦*□ ub`). Every
   trusted post giving `statusAt`/`grpcStatusIs`/`statusErrOk`/`descIs`/`statusCodeIs` now also
   claims these cells (`InvGrpc*`, `InvKVConn`, v3rpc's and rpctypes' `Init`, the grpc model's
   contracts). `anypb.Any`'s struct newly translated (`Code/google_golang_org/protobuf/types/known/
   anypb.{toml,lean}`).

## Verdict

**Survives in the current trust base, with one statement-level gap recorded.** The axiom is false of
Go as stated: `proto.Equal` of two non-nil `*spb.Status` **panics** when their (or a detail `Any`'s)
unknown-field bytes are syntactically invalid, of equal length, and different (measured below). No
program verifiable in this repository can build such a message: invalid unknown bytes come only from
protobuf reflection (`protoreflect.Message.SetUnknown`, or `protoimpl`), which has no spec here, and
whose documentation makes validity a precondition ("The raw fields must be syntactically valid
according to the wire format. An implementation may panic if this is not the case.",
`reflect/protoreflect/value.go:132-134`). Every producer of a `statusAt` builds its `*spb.Status` with
`status.New` (no unknown fields, no details) or from the wire through `proto.Unmarshal` (which stores
only fields it parsed). So no Lean counterexample exists today; the counterexample is stuck at a spec
that does not exist, and it would become one if someone adds a spec of `SetUnknown` (or of a
`protoimpl` route) without the validity premise, or a trusted post giving `statusAt` for a status
built from a program-supplied message (e.g. `status.FromProto`) whose bytes the program set that way.
Proposed restatement (not applied: for the coordinator/user): carry the invariant explicitly, a pure
`⌜pbValidRaw ub⌝` on both `unknownFields` byte lists in `pbStatusRestRO`/`pbAnyRO` (an opaque,
documented predicate "`protowire.ConsumeField` consumes `ub` to the end without error", with the law
`pbValidRaw []` for `status.New`'s proof), or, at least, say in `pbStatusRO`'s and the spec's
docstrings that the bytes are syntactically valid wire format (protobuf's own invariant) and that a
spec letting a program store unknown bytes must require it.

Everything else asked survives: `true` implies equal `Code` and `Message`; the spec cannot be applied
to anything but non-nil `*spb.Status`; no writer of the newly claimed fields exists after
construction; `sizeCache` and `state` are rightly excluded.

## Evidence: Go test

`examples/axiomcx/protoequal/protoequal_test.go` (uncommitted; Go only, no Goose project, no Lean
file). `cd examples && GOTOOLCHAIN=go1.27.3 go test -race -v ./axiomcx/protoequal/`:

```
=== RUN   TestEqualStatusNoPanic
    code 0 vs code 0: true
    code 1 vs code 2: false
    msg a vs msg b: false
    nil Any vs nil Any: true
    nil Any vs empty Any: true
    Any malformed Value: false
    well-formed unknown, equal length: false
--- PASS: TestEqualStatusNoPanic
=== RUN   TestEqualVsMarshalRace
--- PASS: TestEqualVsMarshalRace          (also -count=3: no race report)
=== RUN   TestMalformedUnknownPanics
    malformed unknown, proto.Equal: PANIC runtime error: slice bounds out of range [:-1]
    malformed unknown, FromProto + errors.Is: PANIC runtime error: slice bounds out of range [:-1]
    malformed Any unknown, FromProto + errors.Is: PANIC runtime error: slice bounds out of range [:-1]
--- PASS: TestMalformedUnknownPanics
```

(The test imports genproto's `status` directly, which `examples/go.mod` lists as `// indirect`;
`go test` runs without `-mod=mod`, but `go mod tidy` would move the line. Delete the directory if the
test is not kept.)

## Attacks, question by question

### (a) `true` with differing `Code`/`Message`; arguments other than non-nil `*spb.Status`; panics or blocking

- **Identical pointers** (`proto/equal.go:46`, `x == y` → `true`): then `p = q`, and the two
  `pbStatusRO` agree (`Code ↦□ c`, `Code ↦□ c'` give `c = c'`), so the post holds. Fails.
- **Field comparison** (`internal/impl/equal.go:22-131`, the fast path: `Status`'s `messageInfo` sets
  `methods.Equal = equal`, `codec_message.go:202`; the slow path `protoreflect/value_equal.go:90-115`
  is the same logic): for each field, presence must agree (`hx != hy → false`), then values. `Code`
  (proto3 `int32`, no presence: populated iff non-zero) and `Message` (string, populated iff
  non-empty): `true` needs both unpopulated (both 0 / both `""`) or equal values. "Zero vs unset" is
  one state in proto3. No float fields, so no NaN case. Measured: `Code 1/2`, `"a"/"b"` → `false`.
  Fails.
- **Not a non-nil `*spb.Status`**: the spec fixes both arguments to
  `interface.mkOk (PointerType Status.ty) #p` and `pbStatusRO` carries `p ≠ null`. `(*Error).Is`
  passes `e.s.s`, `tse.s.s` (`internal/status/status.go:222-228`), both from `statusAt`. Nil
  interfaces, invalid (typed-nil) messages and other types are outside the spec. Fails.
- **`Details` with nil elements** (`pbAnyRO` allows `a = null`): a nil `*anypb.Any`'s
  `ProtoReflect()` is `mi.MessageOf(nil)` → the nil wrapper; `equalMessage` falls to the reflective
  path, whose `has`/`getUnknown` check `p.IsNil()`. Measured: nil/nil, nil/empty → `true`, no panic.
  Fails (and `true` there says nothing about `Code`/`Message`, which were compared first).
- **Malformed `Any.Value`**: compared as bytes (`vx.Equal(vy)`), never parsed. Measured: no panic.
- **Unknown fields**: `equalUnknown` (`internal/impl/equal.go:193-221`, same in
  `protoreflect/value_equal.go:147-166`) returns early on unequal length or equal bytes; otherwise it
  splits both with `protowire.ConsumeField` and slices `x[:n]` without checking `n < 0`. Invalid bytes
  → `n` negative → `slice bounds out of range [:-1]`. **Succeeds in Go** (the gap above), directly and
  through grpc's public API (`status.FromProto` clones the unknown bytes, `proto.Clone` → `merge.go:110`
  `append(*du, *su...)`; `errors.Is` → `(*Error).Is`), for the status's and for an `Any`'s unknown
  fields. **Not reachable from a verified program**: no spec of `SetUnknown`/`ProtoReflect`/
  `protoimpl`; `proto.Unmarshal` refuses invalid data (measured) and stores each unknown field as
  `AppendTag` + the bytes `ConsumeFieldValue` accepted (`internal/impl/decode.go:222-229`), with the
  same recursion limit `ConsumeField` uses (`protowire.DefaultRecursionLimit`), so wire-received
  statuses (`NewWithProto`, `model_transport.go:581`) always have valid unknown bytes; equal-length
  different valid bytes measured: `false`, no panic. Go programs cannot write the unexported
  `unknownFields` otherwise (no `unsafe` in Goose; reflection cannot set unexported fields).
- **Concurrency / lazy init**: `Equal` calls `ProtoReflect()` on the status and on each `Any`
  (`status.pb.go`: `LoadMessageInfo`, `StoreMessageInfo` if nil, both `atomic` on
  `MessageState.atomicMessageInfo`, `internal/impl/pointer_unsafe.go:204-208`), and `mi.init()`
  (mutex-guarded, on the global `MessageInfo`, not the message). Measured: 200 rounds of 4 concurrent
  `errors.Is` on fresh statuses, under `-race`: no panic, no race report. No blocking: the mutex is
  taken non-reentrantly and released; no callbacks into user code.
- **Extensions**: `google.rpc.Status` and `Any` have no extension ranges; `extensionMap` is nil.
- **Package init**: the spec asks only `isPkgInit proto`; the real `Equal` also needs genproto's and
  anypb's file registration, which Go runs before `main` in every program (in Lean those `init`s are
  trusted no-ops), so no Go execution differs.

### (b) Writers of the new cells after construction

- `internal/status` (v1.84.0 = the model): `New`/`Newf` allocate `&spb.Status{Code, Message}`;
  `FromProto` and `Proto()` `proto.Clone` (deep: new `Details` slice, new `Any`s, `Value` copied by
  `append(emptyBuf[:], ...)`, unknown bytes appended into a nil slice); `WithDetails` appends to a
  clone and returns a new `Status`; `Details()` returns `UnmarshalNew` results (fresh messages; default
  `Unmarshal` does not alias its input); `NewWithProto` unmarshals into a fresh `st` and stores it. No
  method writes `s.s`'s fields after construction.
- `RawStatusProto` (the only raw escape; `internal/`, importable only inside grpc): callers
  `http2_server.go:985,1113` (real) and `model_transport.go:1087,1325` (model) call `GetDetails()`
  (read: `len` only) and `proto.Marshal(p)`. Other grpc users of statuses (`handler_server.go:251`,
  `binarylog/method_logger.go:347`, `status.FromError`'s wrapped case, `testutils`) take `Proto()`
  clones; `FromError` writes `p.Message` on its clone before `FromProto` clones again.
- `proto.Marshal` writes: the status's and each `Any`'s `sizeCache` (`atomic.StoreInt32`,
  `internal/impl/encode.go:67,123,128`) and `MessageState` (`StoreMessageInfo`, atomic). It reads
  `unknownFields`, `Details`, `TypeUrl`, `Value` and never writes them. Measured: `Equal` racing
  `Marshal` of the same statuses (with details and a nil detail) under `-race`, 4×1000 iterations
  ×3: no race report, `Equal` stays `true`.
- etcd and k8s translated code: no use of `spb.Status`, `GetDetails`, `RawStatusProto`, `FromProto`,
  `ErrorProto` or `WithDetails` (grep of `.lake/go-src/etcd` at its pin and of `Code/`); etcd's
  `ErrGRPC*` are `status.Error(code, desc)` (`New`). In `Code/` only grpc's `status`/`internal/status`
  and genproto/anypb name these types; no translated function reads `Any`'s fields.
- Reflection: a program can reach `Status.s` with `reflect` but not set it or its target's
  unexported fields; `protoreflect` needs the `*spb.Status` itself, which outside grpc is only ever a
  clone. No route found. Fails.

### (c) `sizeCache` and `state` excluded

`Equal` never reads `sizeCache` (it ranges over `rangeInfos`, the declared fields, plus
`GetUnknown`; no `sizecacheOffset` in `equal.go`/`value_equal.go`). `state` is `MessageState`, whose
only non-zero-size field `atomicMessageInfo` is accessed only through `atomic.LoadPointer`/
`StorePointer` (`pointer_unsafe.go:204-208`; grep of `internal/impl`); Go code outside protobuf cannot
name `state` or `sizeCache`, so no program writes them non-atomically. Excluding them is right, and
including them would be wrong (`Marshal` writes `sizeCache`).

### (d) Other attacks

- **Too much ownership**: the spec consumes and returns only persistent facts; the claimed cells are
  all ones no one writes after construction (b). Fails.
- **Cross-world entailment**: no entailment or law here concludes a pure fact about an opaque function
  from bare cells; the only pure conclusion is about one call's return value. The axiom is satisfiable
  by an implementation that reads the cells it is given (or returns `false`), in every heap, so a
  fresh-heap argument yields nothing. `statusAt_agree` concludes equalities from two points-to of one
  location, which hold in every heap. Fails.
- **Too-strong persistent facts in producers**: every trusted post that now also claims
  `pbStatusRestRO` describes a status built by `New` (nil `unknownFields`, nil `Details`: the cells are
  the zero values, trivially read-only) or by `NewWithProto` from the wire (fresh, private to the
  `Status`, written only inside `Unmarshal` before the `Status` exists). Fails.
- **`ds`/the `Details` slice**: `d ↦*□ ds` covers the elements up to `len`, which is all `Equal`
  reads (`equalMessageList` uses `Len`/`Get`). Duplicate or shared `Any` pointers are harmless
  (persistent).

## Not tried

- A Lean proof (none was reachable; the Go panic needs a reflection call no spec covers).
- `purego`/`appengine` builds (`protoimpl.UnsafeEnabled = false`: `ProtoReflect` always wraps, no
  `MessageState`); the deployments use the default build.
- protobuf-go's lazy decoding (`protolazy`): neither message has lazy fields.
- `notes/audit.md` was not updated (outside this review's allowed edits); its row for the new axiom
  should point here.

## Follow-up (the author, 2026-11-26): the gap closed

The proposed restatement is applied, with the repository's existing description of the decoder's
unknown fields instead of a new opaque predicate: `status.pbStatusRestRO` and `status.pbAnyRO`
(`Proof/google_golang_org/grpc/status/StatusRO.lean`) carry `⌜ufWire status.spbStatusSchema ub⌝` and
`⌜ufWire status.anySchema ub⌝` (`Proof/google_golang_org/protobuf/proto/UfWire.lean`: whole well-formed
fields with minimal outer tags, groups at most 10001 deep, each routed to the unknown fields by the
message's schema), so `proto.EqualStatus.spec`'s premise `pbStatusRO` excludes the panicking input
class: on such bytes every `protowire.ConsumeField` of `equalUnknown` succeeds (the decoder that left
them parsed them with the same consumers). The producers meet it: `status.New` (proved) has nil unknown
fields (`ufWire_nil`); a status from the wire has what `proto.Unmarshal` left, which is `ufWire` of its
schema by definition. Not a new trusted claim beyond the read-only facts reviewed above: a status whose
unknown bytes were set through reflection has no `statusAt` here.
