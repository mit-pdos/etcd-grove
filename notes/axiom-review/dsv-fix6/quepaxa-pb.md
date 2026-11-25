# Axiom review: protobuf-go `proto.Marshal`/`proto.Unmarshal` on QuePaxa's messages, narrowed representation (dsv-fix6)

Reviewed 2026-11-25 by the `axiom` skill (an independent reviewer), in the worktree
`/shared/etcd-grove-dsvfix6` (branch `dsv-fix6`, `3a6222e221`); protobuf-go v1.36.12
(`~/go/pkg/mod/google.golang.org/protobuf@v1.36.12`); Go go1.27.1. Read-only review: the brief allowed
no branch, translation or Lean file in the repository, so the attacks are Go tests (a scratch module
`/shared/tmp/qpbrev6` holding a copy of `proto/client/client.pb.go`, deleted after) and arguments about
what a Lean proof can derive, not machine-checked proofs. This is the re-review that the fix-4 review
(`notes/axiom-review/dsv-fix4/quepaxa-pb.md`) asked for after its counterexamples A and B.

## The axioms

`Perennial.raxos.hyp.proto.Marshal.wp_proof : raxos.hyp.proto.Marshal.spec`
(`Dsverify/Proof/google_golang_org/protobuf/proto/Marshal.lean`) and
`Perennial.raxos.hyp.proto.Unmarshal.wp_proof : raxos.hyp.proto.Unmarshal.spec`
(`Dsverify/Proof/google_golang_org/protobuf/proto/Unmarshal.lean`); the specs are in
`Dsverify/Proof/raxos/Hyp.lean`, section `pb`:

    Marshal:   ∀ m Ψ, {{ isPkgInit proto ∗ marshalPre m Ψ }} proto.Marshal m
               {{ s err; (err = nil ∗ ∃ bs, s ↦* bs ∗ Ψ (some bs)) ∨ (err ≠ nil ∗ errAny err ∗ Ψ none) }}
    Unmarshal: ∀ b dq bs m Ψ, {{ isPkgInit proto ∗ b ↦*{dq} bs ∗ unmarshalPre bs m Ψ }} proto.Unmarshal b m
               {{ err; ∃ ok, b ↦*{dq} bs ∗ ⌜err = nil ↔ ok⌝ ∗ Ψ ok ∗ (if ok then True else errAny err) }}

What changed since fix 4 (`Dsverify/Proof/raxos/Msg.lean`): a message's `pt*` read with `dq = 1` is the
whole struct **and** `stateOk mi x.state` (its `state` unset or `replicaMI i`/`clientMI i`, the type's
own entry of `file_*_msgTypes`); read with any other `dq`, its program fields at `dq` and
`inv pbRtN (rt* l)`, where `rt*` (the two runtime fields, owned, with `stateOk`) is `@[no_expose]`.
`sizeCache` stays unconstrained.

Claims, in plain words:

1. `Marshal` of a message of one of the seven kinds (`ProposerMessage`, `RecorderResponse`,
   `DecideRequest`, `DecideResponse`, `Decisions`, `Empty`, `client.ClientBatch`), in that
   representation, does not panic; it returns exactly `enc*(v)` when the strings are valid UTF-8, and an
   error otherwise; the representation comes back (existentially: the runtime fields may have changed).
2. `Unmarshal` into a fresh zero message of one of the kinds does not panic, leaves `b` unchanged and
   unaliased, and on success with `bs = enc v0` (`v0` well formed) gives the message owned with value
   `v0`.
3. Both need only `isPkgInit` of protobuf's `proto` package.

## Verdict: **refuted** (as stated, by a missing premise); **survives with a condition**: the message's own package is initialized (`isPkgInit pkg_id.raxos.replica.src` / `pkg_id.raxos.proto.client`)

The fix-4 counterexamples A and B are closed by the narrowed representation (attacks 1-3 below). The new
counterexample needs a program in the package that declares the message types, as A and B did; QuePaxa
itself has no hand-written `init` or package-variable initializer that marshals
(`grep -rn 'func init\|^var .*= .*(' examples/dsverify/quepaxa --include=*.go | grep -v pb.go`: nothing),
so the QuePaxa result is not affected in fact.

### Counterexample C: `Marshal`/`Unmarshal` during the declaring package's initialization

The axioms ask `isPkgInit` of `proto` only, and `marshalPre`/`unmarshalPre` ask nothing of the message's
package. But the generated `ProtoReflect` (`proto/client/client.pb.go:48-58`) indexes
`file_proto_client_client_proto_msgTypes`, a package variable `make([]protoimpl.MessageInfo, 3)`
(`client.pb.go:232`) that `file_proto_client_client_proto_init()` fills from the package's `init()`
(`client.pb.go:247`). Inside the declaring package, a package-variable initializer runs before every
`init()`, and a hand-written `init()` in a file sorting before `client.pb.go` runs before the generated
one. At that point `proto`'s package is initialized (an import), so `isPkgInit proto` holds in the
model's `initialize'`, while the message tables are not:

    // proto/client/aaa_early.go, in package client
    var early = func() int {
        b, err := proto.Marshal(&ClientBatch{Sender: 1, Id: "x"})
        if err != nil { panic(err) }
        return len(b)
    }()

Output (go1.27.1, deterministic):

    panic: runtime error: index out of range [0] with length 0
    qpbrev/client.(*ClientBatch).ProtoReflect(...)   (client.pb.go:49: &file_..._msgTypes[0])

The same with `proto.Unmarshal([]byte{0x08, 0x01}, &cb)` into a zero `ClientBatch` (same panic), and with
a hand-written `func init()` in `aaa_early.go` that marshals (the slice is made by then, but the
generated init has not filled it):

    panic: runtime error: invalid memory address or nil pointer dereference
    google.golang.org/protobuf/internal/impl.opaqueInitHook(...) message_opaque.go:40
    google.golang.org/protobuf/internal/impl.(*MessageInfo).initOnce(...)

The triple: the package's `wp_initialize'` (or the triple `{{ isPkgInit proto }} early's initializer
{{ True }}`). In the model the package initializer first initializes the imports (giving
`isPkgInit proto`, as `Dsverify/Proof/raxos/proto/client/Init.lean:46-60` does for the real package),
then runs the variable's initializer: `&ClientBatch{…}` allocates `l ↦ v` with
`v.state = zero` (`stateOk_zero`), so `repCB l 1 ⟨1, "x", []⟩` holds with `batchOk`; `marshalPre`'s
seventh disjunct with `Ψ (some bs) := ⌜bs = encBatch b⌝`, `Ψ none := False` (dischargeable from
`batchOk`) and `Marshal.wp_proof` give `err = nil`, so the `panic(err)` branch is unreachable in the
logic. Every step is an allocation, a `wp_apply` of the axiom and an `if`; not written in Lean (no
repository edits). The trusted no-op models of `file_*_msgTypes`'s initializer and of the generated
`init` (`Dsverify/TrustedCode/raxos/proto/client.lean`) do not matter: the axiom never looks at them.

**Fix (proposed, not applied).** Add the declaring package's init to each kind of `marshalPre` and
`unmarshalPre` (`isPkgInit pkg_id.raxos.replica.src` for the six consensus kinds,
`isPkgInit pkg_id.raxos.proto.client` for `ClientBatch`), or to the axioms' preconditions. It is
persistent, and the callers have it: `cbMarshal.spec` (`examples/quepaxanet/KitWire.lean:42`) already
holds `isPkgInit pkg_id.raxos.proto.client`; the gRPC handlers and proposer run in package `raxos` after
its init. In the model `isPkgInit` of a package exists only after its `initialize'` finishes, which is
after Go's `init()` functions, so the premise excludes counterexample C exactly.

### Attacks that failed (the axioms survive them)

1. **Another type's `MessageInfo` in an owned message's `state`** (fix-4 counterexample A). `stateOk`
   now pins the top-level `state` to `null` or the type's own `replicaMI i`/`clientMI i` (indices checked
   against the generated `ProtoReflect`s: `ProposerMessage` 0, `RecorderResponse` 1, `DecideRequest` 2,
   `DecideResponse` 3, `Decisions` 4, `Empty` 5, `PM_ClientBatch` 6, `PM_Proposal` 7, `PM_DecidedSlot` 8,
   `PM_ClientBatch_SingleMessage` 9, `RR_Proposal` 10, `DR_ClientBatch` 11, `DR_ClientBatch_SingleMessage`
   12, `Decisions_DecidedSlot` 13; client `ClientBatch` 0, `ClientBatch_SingleMessage` 2). A program can
   only produce a `MessageState` value as a zero literal or a copy (its field is unexported in
   `internal/impl`, `StoreMessageInfo` is untranslated, so it has no WP), and every copy the logic gives
   back after a `Marshal`/`Unmarshal` is existential `stateOk` of its own type: `rr.state = pm.state`
   then needs `null ∨ replicaMI 0 ⊢ null ∨ replicaMI 1`, not provable (the size of the opaque
   `MessageInfo` is unknown, so neither `replicaMI 0 = replicaMI 1` nor its negation is). The logic
   never knows a `state` is `null` while Go has set it: Go sets it only in `ProtoReflect`, reached by
   `Marshal`/`Unmarshal` (existential posts), gRPC's codec (a premise, over the same `marshalPre`),
   and the untranslated `String`/`Reset`/`ProtoReflect`; `fmt.Println`'s hypothesis (`printOk`,
   `fmt.ArgWf`) excludes pointers. Conversions between identically-laid-out types
   (`PM_ClientBatch_SingleMessage` ↔ `DR_ClientBatch_SingleMessage`) copy `state` the same way and
   are blocked the same way; for sub-messages Go ignores `state` anyway (test: a `ClientBatch_SingleMessage`
   holding `ClientBatch`'s state marshals correctly inside a `ClientBatch`, `12030a01711a017a`; marshalled
   top-level it gives garbage `0886e08703`, but it is no top-level kind).
2. **A client writing a shared message's runtime fields** (fix-4 counterexample B). `rt*` is
   `@[no_expose]` and no exported lemma unfolds it (`grep -rn 'rtPM\|rtCB\|...\|pbRtN' Dsverify` outside
   `Msg.lean`: only the docstring in `Hyp.lean`; no `import all` of `Msg`). Opening `inv pbRtN (rt* l)`
   yields an opaque `▷ rt* l` that must be returned in the same atomic step. The only source of such an
   invariant is `pt*_persist`, which consumes the whole struct and discards the fields, so a shared
   message (and, by `rep*`'s uniform `dq`, its sub-messages and slices) is immutable, and no
   `pt* l (own q)` with `q < 1` can be built. Concurrent marshals then store equal `sizeCache` values.
   Test: 16 goroutines × 20000 marshals of two shared `ClientBatch`es sharing a `Messages` slice and one
   sub-message twice: 0 of 320000 wrong or failed.
3. **`sizeCache` arbitrary in an owned message.** `proto.Marshal` sizes first without
   `UseCachedSize` (`proto/encode.go:183-191`: `o.flags()` is 0, `sizePointerSlow` stores every
   message's `sizeCache`, `internal/impl/encode.go:47-128`), then marshals with the cached sizes it
   just stored; the owner has exclusive access in between. Test: a whole-struct copy `*b = *a` of a
   marshalled message (stale `state`/`sizeCache` copied), mutated, and a copied marshalled sub-message,
   marshal to exactly the encoding of the fresh equivalent.
4. **Whole-struct loads/stores and copies.** Owned: the whole struct is the program's; a same-type copy
   keeps a correct `state` (above). Shared: no rule gives the whole struct (the runtime fields are in the
   sealed invariant), so a copy racing protobuf's atomic stores has no WP. `MessageState` is not
   comparable (`DoNotCompare`), so `==` on messages or states does not compile, and `any(x.state) == …`
   panics in Go and has no WP.
5. **Nil and nested messages.** `pt*_not_null` excludes a nil top-level pointer and nil repeated
   elements; an absent singular sub-message is `null ↔ none` and omitted, as `enc*`. The message types
   are not recursive. Unchanged from fix 4.
6. **Encoding exactness, errors.** As fix 4 (attacks 3-5 there): field order, proto3 zero omission,
   negative `int64`, UTF-8 validation (`validUtf8` = Go's `utf8.Valid`); `Empty` returns a non-nil
   zero-length slice of cap 0 (`emptyBuf[:]`, shared between calls: `s ↦* []` gives nothing to write);
   no required fields, so no `checkInitialized` error; sizes above `MaxInt32` recomputed, not an error.
   With B closed, nothing makes a well-formed marshal fail.
7. **Unmarshal's ownership.** The target must be `l ↦ zero_val` (owned, `state` zero); protobuf
   allocates sub-messages and copies strings (no `AliasBuffer`), so `decInto`'s owned `rep … 1` and
   `b ↦*{dq} bs` back are right; no lazy fields in these `.proto`s. Failure (`Ψ false`) is always
   allowed. `decInto`'s uniqueness fact rests on `enc*`'s injectivity on well-formed values (fix 4,
   attack 9).
8. **`replicaMI` is not the address Go stores** (a remark, not a counterexample).
   `file_replica_src_consensus_proto_msgTypes` is a slice variable (`make([]protoimpl.MessageInfo, 14)`,
   `consensus.pb.go:964`), so `&file_…_msgTypes[i]` is an element of a heap array, while `replicaMI i`
   is `arrayIndexRef MessageInfo i (globalAddr file_…_msgTypes)`, an offset into the variable holding
   the slice header (likewise `clientMI`). After a real `Marshal`, `state` holds neither `null` nor
   `replicaMI i`, so `stateOk` is literally false of the heap. It is unobservable: translated code cannot
   read `atomicMessageInfo` (unexported in `internal/impl`; `LoadMessageInfo` untranslated), the
   variable's points-to is never handed out (`srcState` holds only `Consensus_ServiceDesc`; its trusted
   initializer is a no-op), and states are not comparable. `stateOk` acts as a per-type tag; the
   docstrings' "`file_*_msgTypes[i]`" is inaccurate. Either define the tag abstractly (an opaque
   per-type location) or say so in the docstring; if a later change translates `MessageState`'s methods
   or exposes the variable, re-review.
9. **Cross-world entailments.** None: the statements are triples; `stateOk` is a pure fact about a value
   the program holds in that execution.

Not tried: gRPC's codec path (`GrpcHyp`, a premise), `ClientStatus` (no kind), a machine-checked Lean
proof of counterexample C (no repository edits), `-race` runs (a race report is no panic).

## Findings in the Go code

None in QuePaxa or protobuf-go: that generated messages cannot be used before their package's
`init()` is the ordinary Go initialization order, and QuePaxa does not do it.
