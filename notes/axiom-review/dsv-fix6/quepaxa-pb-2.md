# Review: QuePaxa's `proto.Marshal` / `proto.Unmarshal` axioms (dsv-fix6, second, independent review)

Reviewed 2026-11-25, worktree `dsv-fix6` at `c7b8cc6ee7`, read-only (`axiom` skill). Done without
reading the earlier reviews in this directory.

## The axioms

- `Perennial.raxos.hyp.proto.Marshal.wp_proof : raxos.hyp.proto.Marshal.spec`
  (`Dsverify/Proof/google_golang_org/protobuf/proto/Marshal.lean`)
- `Perennial.raxos.hyp.proto.Unmarshal.wp_proof : raxos.hyp.proto.Unmarshal.spec`
  (`Dsverify/Proof/google_golang_org/protobuf/proto/Unmarshal.lean`)

The statements are in `Dsverify/Proof/raxos/Hyp.lean` (section `pb`), over `msg.marshalPre` /
`msg.unmarshalPre`, `rep*`, `pt*`, `stateOk`, `replicaMI`/`clientMI` and the sealed `rt*`
(`Dsverify/Proof/raxos/Msg.lean`). The Go: protobuf-go v1.36.12 (the module's `go list -m`), the
fork's `examples/dsverify/quepaxa/replica/src/consensus.pb.go` and `proto/client/client.pb.go`
(protoc-gen-go v1.27.1 output), go1.27.3.

### What they claim, in plain words

1. `Marshal(m)`, `m` a pointer to one of the seven top-level kinds (`ProposerMessage`,
   `RecorderResponse`, `DecideRequest`, `DecideResponse`, `Decisions`, `Empty`,
   `client.ClientBatch`), with `isPkgInit` of `proto` and of the declaring package, its
   representation read with any `dq`: returns err = nil and an owned fresh slice holding exactly
   `enc*` of the value when the value is well formed (`*Ok`: valid UTF-8 strings), else err != nil.
   Because the client chooses Ψ, this is also "never errors on a well formed message" and "never
   succeeds on an ill-formed one". The representation is given back.
2. The representation: owned (`dq = 1`) is the whole struct with `state` null or the type's own
   `MessageInfo` (`stateOk`, `replicaMI i`/`clientMI i`, opaque), `sizeCache` free, no unknown
   fields, sub-messages owned separately, every pointer non-nil; shared (`dq ≠ 1`) is the other
   fields with `dq` plus `inv pbRtN (rt* l)`, `rt*` sealed.
3. `Unmarshal(b, m)` into an owned zero message of a kind: `b` given back; err = nil iff `Ψ true`;
   on success, if `bs` is `enc` of a well-formed value, the decoded message is owned (`rep … 1 v`)
   and `v` equals every well-formed `v0` with `enc v0 = bs` (so `enc` must be injective on
   well-formed values).

## Verdict

**Survives with a condition.** No program outside the declaring packages panics while the axioms
prove it safe; every attack below was tried in Go at the pins. The condition: **no code of
`raxos/replica/src` or `raxos/proto/client` itself may reach `proto.Marshal`/`proto.Unmarshal` of
its own message types during that package's initialization before its generated `init()`.** The
fork's packages meet it (their only package-level initializers are the generated `.pb.go`
variables and `Consensus_ServiceDesc`, and their only `init` is the generated one), but the axiom
does not enforce it: the `isPkgInit` premise added in dsv-fix6 does not show that the generated
`init` has run (finding 1).

## Finding 1: `isPkgInit` of the declaring package does not show its generated `init` ran (the condition)

The dsv-fix6 docstrings (`Hyp.lean:92-95`, `Msg.lean` header) say that asking `isPkgInit` of the
declaring package excludes a `Marshal` before that package's generated `init`. It does so only
for code outside the package. Inside it, `isPkgInit` can be assembled before the generated
`init`:

- `isPkgInit pkg_id.raxos.proto.client` is `define_is_pkg_init iprop(True)`
  (`Dsverify/Proof/raxos/proto/client/Base.lean`): its dependencies' `isPkgInit` and `True`. Its
  `wp_initialize'_lb` (`.../proto/client/Init.lean`) has all of them once the imports are
  initialized, before the variable initializers and `init.«0»`; `is_pkg_init_finish` uses nothing
  that `init.«0»` produces (it is a trusted no-op, `Dsverify/TrustedCode/raxos/proto/client.lean`).
- `isPkgInit pkg_id.raxos.replica.src` is its dependencies plus `srcState`
  (`.../replica/src/Base.lean`): `Consensus_ServiceDesc ↦□ sd` and its methods slice. Both come from
  a variable initializer (`consensus_grpc.pb.go:158`). `wp_initialize'_lb`
  (`.../replica/src/Init.lean`) persists them (`ipersist HConsensus_ServiceDesc`, `ipersist Hml`)
  before `init.«0»`. So every `init()` of the package can assemble `isPkgInit`, and so can a
  variable initializer that runs after `Consensus_ServiceDesc` in Go's order.

So if the package contained a variable initializer or an `init()` in a file sorted before the
`.pb.go` that marshals one of its messages, the proof of its `initialize'` could meet
`marshalPre` (a fresh composite literal is owned with `state` zero: `stateOk_zero`). The axiom
would then prove a call safe that Go runs as a panic. Tested on a copy of `proto/client` (the
real `client.pb.go` plus one file; the package's import path changed, which the proto file path
does not depend on):

```go
// a.go, variant 1: a package-level variable initializer
var early = func() []byte { b, _ := proto.Marshal(&ClientBatch{Id: "x"}); return b }()
// a.go, variant 2: an init() in a file sorted before client.pb.go
func init() { proto.Marshal(&ClientBatch{Id: "x"}) }
```

```
== variant 1
panic: runtime error: index out of range [0] with length 0
  .../clientcopy.(*ClientBatch).ProtoReflect   client.pb.go:49
  google.golang.org/protobuf/proto.Marshal     proto/encode.go:111
  .../clientcopy.init.func1                    a.go:6
== variant 2
panic: runtime error: invalid memory address or nil pointer dereference
  google.golang.org/protobuf/internal/impl.opaqueInitHook   message_opaque.go:40
  internal/impl.(*MessageInfo).initOnce                      message.go:81
  internal/impl.(*messageState).ProtoMethods                 message_reflect_gen.go:31
```

This is no counterexample under the skill's rules. The program must be a new package, and Go
initializes a package before any importer can run code, so only the declaring package's own code
can run before its generated `init`, and the fork's has none. It does mean that the premise is
not what makes the axiom true here: Go's import order and the absence of such code in the two
packages are. **Proposed restatement (not applied):** tie the premise to something only the
generated `init` produces. For example, give the trusted model of `init.«0»` a postcondition
holding a persistent token (say `msgTypesReady pkg`), and make `isPkgInitDef` of the two packages
(or `marshalPre`/`unmarshalPre` directly) contain it, so that `isPkgInit` can be closed only
after `init.«0»`. Otherwise, state the condition in the axiom's docstring, and as an
`etc/`-checked fact about the two packages (no non-generated package-level initializer or
`init`).

## Attacks tried that failed

All in a scratch Go module (`replace raxos => examples/dsverify/quepaxa`), go1.27.3, protobuf-go
v1.36.12; `go test` and `go test -race` all pass.

1. **Encoding exactness** (claim 1). `enc*`, `varint`, `fVarint`, `fBytes`, `fStr`, `fBool` and
   `fStrs` were transcribed into Go and compared with `proto.Marshal` on 20,000 random values of
   each of the seven kinds: negative values, `INT64_MIN`/`INT64_MAX`, zero fields, empty and
   multi-byte strings, empty repeated elements, absent and present-but-empty sub-messages
   (`P`, `F`, `M`). All equal. Each also decodes back to a message `proto.Equal` to it, with no
   unknown fields. `Empty` marshals to zero bytes (protobuf returns the global `emptyBuf[:]`,
   length and capacity 0, so `s ↦* []` is harmless). The fields are emitted in field-number order
   (`orderedCoderFields`), which matches `enc*`'s order. There are no oneofs or maps.
2. **UTF-8 and the error case.** Lean's `validUtf8` (transcribed) agrees with `utf8.Valid` on
   2,000,000 random byte strings biased with surrogates, overlongs and out-of-range bytes
   (`ED A0 80`, `C0 80`, `E0 9F BF`, `F4 90 …`, `F0 8F`). Every proto3 string here is checked
   (`coderStringValidateUTF8`/`…SliceValidateUTF8`, `internal/impl/codec_gen.go:5053,5263`).
   `Marshal` returns an error for an invalid string at each of the twelve string positions of the
   seven kinds (top level, nested `Proposal`/`ClientBatch`/`SingleMessage`/`DecidedSlot`/`F`/`M`).
   No other `Marshal` error is reachable on a well-formed message. A size above `MaxInt32` is
   handled (`sizePointerSlow` stores 0 and recomputes, `internal/impl/encode.go:118-129`).
   `SizeMismatchError` (`codec_field.go:160-170`) needs the message to change between `Size` and
   `Marshal`, which the representation excludes (an owned message is exclusive, a shared one
   read-only).
3. **Stale `sizeCache`/`state` in an owned message.** From outside the package a program can set
   these only by whole-struct copy, and the owned representation allows it. Copying a large,
   already-marshalled message's struct (and a sub-message's) onto a smaller one, then marshalling,
   2,000 times: the output is still exactly `encPM`. The reason: `proto.Marshal` calls `Size`
   without `UseCachedSize` first, which recomputes every level's cache
   (`proto/encode.go:183-191`). The copied `state` is the same type's `MessageInfo`. `stateOk`
   allows nothing else, and the client cannot move a `MessageInfo` between types:
   `replicaMI`/`clientMI` are opaque, and the indices in `Msg.lean` are distinct per type and match
   the generated `msgTypes` indices.
4. **`state` after the calls** (does the post's `stateOk` hold?). After `Marshal`, and after
   `Unmarshal` of an encoding, every message at every level of 2,000 random `ProposerMessage`s has
   `state` nil or its type's own `MessageInfo` (read with reflection). Sub-messages that
   `Unmarshal` allocates keep `state` nil.
5. **`Unmarshal` aliasing.** The decoded strings are copies (`string(v)`, `codec_gen.go:5064,
   5275`): overwriting the input buffer after a decode leaves every decoded string (`Ids`, batch
   `Id`, `Message`, slot `Ids`) unchanged. The decoded slices and sub-messages are fresh
   allocations. The input slice is returned with its fraction, and protobuf keeps no reference to
   it.
6. **Injectivity of `enc*` on well-formed values** (the `decInto` uniqueness fact, which would
   give `False` if two well-formed values shared an encoding). Every field has a distinct tag and
   is emitted in tag order. A zero scalar and an empty string are omitted and decode back to zero
   and empty. A present empty sub-message is written (`tag, 0`), so it differs from an absent one.
   Repeated elements are always written. Varints of `uint64(x)` are injective on the `int64`
   range. So `enc*` is injective on well-formed values, and the decoded value is the unique `v0`.
7. **Shared messages and concurrency.** Eight goroutines marshal one shared message (and decode
   its encoding), while reading its exported fields, 200 times under `-race`. There is no race
   report and every output is exact. protobuf's only stores are the atomic `state`/`sizeCache`
   stores, and concurrent sizings of an immutable message store equal values. The client cannot
   take the runtime fields out of `inv pbRtN (rt* l)` (sealed), nor load a shared message's whole
   struct, so it cannot copy its runtime fields. A sub-message shared by two parents, or listed
   twice in one parent, is possible only with `dq ≠ 1`, where it is immutable and has one size.
8. **Ownership mixing.** `rep*` uses one `dq` throughout, so an owned parent cannot have a shared
   (concurrently marshalled) sub-message, nor two owned parents one sub-message or one pointer
   slice. Every pointer in `repList`/`repOpt some` is non-nil (`pt*_not_null`), so nil elements of a
   repeated message field (which protobuf would encode as empty messages, not `enc`) are
   excluded. `Unmarshal` needs an owned zero struct, so it cannot run into a shared message or one
   that is being marshalled.
9. **Cross-world** (`notes/axiom-review` lesson 2026-11-17). There is no entailment from bare
   persistent cells to a pure equation about an opaque function of a pointer. `replicaMI`/`clientMI`
   take a `Nat`, and no law relates them to the heap. The axioms never give ownership of a
   `MessageInfo` location. Code outside the package cannot read `state` in Go (unexported), so a
   program cannot compare a fresh allocation with `replicaMI i`.
10. **Package initialization from outside the package.** A package that names the types imports
    their package, and Go (and `wp_initialize'_lb`) initialize it, generated `init` included,
    before the importer's variables. So a call from outside always comes after the generated
    `init`. From inside, see finding 1.

## Not tried / out of scope

- gRPC's codec path (`proto.Size`, then `MarshalOptions{UseCachedSize: true}`) is not these
  axioms. The `Hyp.lean` docstring says `PbCodec.marshal` is this precondition. Whoever reviews
  gRPC's codec should check that its `Size` and `Marshal` are not separated by a mutation (owned
  messages handed to gRPC), since `UseCachedSize` trusts the cache.
- The trusted `init.«0»` models ("cannot panic") were not reviewed. One observation: protobuf's
  registry panics by default on a registration conflict (`conflictPolicy = "panic"`,
  `reflect/protoregistry/registry.go:42`). Both `.proto` files declare no `package`, so their
  messages are top-level names (`ClientBatch`, `Empty`, `ProposerMessage`, ...). A program that
  links another generated package with a top-level message of the same full name, or the same
  `.proto` path, panics in that `init`. QuePaxa's two files do not conflict with each other.
- Out-of-memory on huge messages (a Go `fatal error`, not a panic) was not considered.
- No Lean proof was built (read-only review). The Lean side of finding 1 is argued from the two
  `Init.lean` proofs and the two `IsPkgInit` instances, and was not checked mechanically.

No bug in the Go code (QuePaxa's or protobuf-go's) was found.
