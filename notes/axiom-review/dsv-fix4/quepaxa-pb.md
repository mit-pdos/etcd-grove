# Axiom review: protobuf-go `proto.Marshal`/`proto.Unmarshal` on QuePaxa's messages (`raxos.hyp.proto.{Marshal,Unmarshal}.wp_proof`)

Reviewed 2026-11-25 by the `axiom` skill (an independent reviewer), in the worktree
`/shared/etcd-grove-mathrand` (branch `dsv-fix4`, at `5c6274f9e0` plus the uncommitted files, among
them the two axiom files); protobuf-go v1.36.12 (`~/go/pkg/mod/google.golang.org/protobuf@v1.36.12`);
Go at the pinned toolchain go1.27.3 (also run at go1.27.1: same results). No repository file but this
report was changed; the Go tests below were throwaway (`/shared/tmp/qpb-axiom`, deleted), and no Lean
counterexample was written (the brief forbids repository edits).

## The axioms

`Perennial.raxos.hyp.proto.Marshal.wp_proof : raxos.hyp.proto.Marshal.spec`
(`Dsverify/Proof/google_golang_org/protobuf/proto/Marshal.lean`) and
`Perennial.raxos.hyp.proto.Unmarshal.wp_proof : raxos.hyp.proto.Unmarshal.spec`
(`Dsverify/Proof/google_golang_org/protobuf/proto/Unmarshal.lean`), the fields of the former premise
`raxos.hyp.PbHyp` verbatim; specs in `Dsverify/Proof/raxos/Hyp.lean:73-104`, over `msg.marshalPre`,
`msg.unmarshalPre`, `msg.decInto` and the representations `rep*`/`pt*`/`fields*`/`rt*` of
`Dsverify/Proof/raxos/Msg.lean`.

    Marshal:   ∀ m Ψ, {{ isPkgInit proto ∗ marshalPre m Ψ }} proto.Marshal m
               {{ s err; (err = nil ∗ ∃ bs, s ↦* bs ∗ Ψ (some bs)) ∨ (err ≠ nil ∗ errAny err ∗ Ψ none) }}
    Unmarshal: ∀ b dq bs m Ψ, {{ isPkgInit proto ∗ b ↦*{dq} bs ∗ unmarshalPre bs m Ψ }} proto.Unmarshal b m
               {{ err; ∃ ok, b ↦*{dq} bs ∗ ⌜err = nil ↔ ok⌝ ∗ Ψ ok ∗ (if ok then True else errAny err) }}

Claims, in plain words:

1. `Marshal` of a message of one of the seven kinds (`ProposerMessage`, `RecorderResponse`,
   `DecideRequest`, `DecideResponse`, `Decisions`, `Empty`, `client.ClientBatch`), read with any
   fraction `dq`, does not panic; it succeeds with exactly `enc*(v)` when every string is valid UTF-8
   (`*Ok v`), and fails otherwise; the representation is given back.
2. In the representation, a message read with `dq = 1` is the whole struct `l ↦ x`, its runtime
   fields `state` and `sizeCache` **arbitrary**; read with `dq ≠ 1`, its other fields with `dq` and
   `state`/`sizeCache` owned (fraction 1) in the persistent invariant `inv pbRtN (rt* l)`, which any
   thread may open (Msg.lean:226-233, e.g. `ptPMSingle`, `rtPMSingle`).
3. `Unmarshal` into a fresh zero message of one of the kinds does not panic, leaves `b` unchanged and
   unaliased, and on success, when `bs = enc v0` for a well-formed `v0`, gives the message owned with
   value `v0` (no unknown fields); on failure nothing.

Used by: the `quepaxanet` result (`Dsverify/{Spec,Proof}/raxos/examples/quepaxanet/TopLevelRobustness.lean`),
through `Dsverify/Proof/raxos/{Proposer,Replica,Proxy}/*` and `examples/quepaxanet/Kit*.lean`
(`grep -rl 'Marshal.spec\|PbHyp\|qpCodec' Dsverify/Proof/raxos`). Go callers:
`examples/dsverify/quepaxa/proto/client/clientwrapper.go:16,51` (`ClientBatch`); lines 65 and 102
(`ClientStatus`) are not covered by `marshalPre`/`unmarshalPre` (no `ClientStatus` kind), so a proof
cannot use the axioms there; the rest of QuePaxa's protobuf traffic goes through gRPC's codec (a
separate hypothesis).

## Verdict: **refuted** (as stated), **survives with a condition**: no hand-written code writes a message's runtime fields `state`/`sizeCache`

Both refutations need a program in the package that declares the message types (Go package `raxos`,
`examples/dsverify/quepaxa/replica/src`, or `proto/client`), since the fields are unexported. The axiom
quantifies over every GooseLang program, and claim 2 hands such a program full write permission to
those fields; the QuePaxa program itself never names them (`grep -rn '\.state\b\|sizeCache\|MessageState'
examples/dsverify/quepaxa --include=*.go | grep -v pb.go`: nothing), so the QuePaxa result is not
affected in fact, but nothing in the statement or a gate guarantees it.

### Counterexample A (owned message, sequential): `state` holding another type's `MessageInfo`

With `dq = 1` the program owns `l ↦ x` with `x.state` arbitrary (`repPM`'s `∃ x, ptPM l 1 x ∗ …`
constrains only `unknownFields`, `Sender`, `Index`, `S`, `P`, `DecidedSlots`). The generated
`ProtoReflect` (`replica/src/consensus.pb.go:50-60`) uses whatever `MessageInfo` is already in `state`
(`if ms.LoadMessageInfo() == nil { ms.StoreMessageInfo(mi) }`), so a `ProposerMessage` whose `state`
was copied from a `RecorderResponse` is marshalled with `RecorderResponse`'s field table over
`ProposerMessage`'s memory: `RecorderResponse.F` (a pointer) is read at `ProposerMessage.Index`'s offset.

    // in package raxos (replica/src)
    rr := &RecorderResponse{S: 1}
    proto.Marshal(rr)                     // stores RecorderResponse's MessageInfo in rr.state
    pm := &ProposerMessage{Sender: 1, Index: 0x1000, S: 5}
    pm.state = rr.state                   // legal Go: both fields are protoimpl.MessageState
    proto.Marshal(pm)

Output (go1.27.3, deterministic):

    unexpected fault address 0x1028
    fatal error: fault
    [signal SIGSEGV: segmentation violation code=0x1 addr=0x1028 pc=0x5bc540]
    google.golang.org/protobuf/internal/impl.sizeInt64NoZero(...) codec_gen.go:1889
    ... (*MessageInfo).sizePointerSlow encode.go:111 ... sizeMessageInfo codec_field.go:160 ...

With `Index: 0` and `P: nil` it does not crash but returns `08072001` where `encPM` is `08072005`
(`Sender: 7, S: 5`): `err = nil` and bytes the spec excludes, so `if !bytes.Equal(b, want) { panic }`
panics in Go (tested). The triple: the program owns `pm ↦ v` (fresh), stores `rr.state` (it owns `rr`
after the first `Marshal` gives `repRR rr 1 _` back), so `repPM pm 1 ⟨…⟩` holds with
`pmOk` (no strings); the axiom yields `Ψ (some (encPM v))`, with `Ψ (some bs) := ⌜bs = encPM v⌝`, so
the check's `panic` branch is unreachable in the logic. Not written in Lean (no repository edits);
every step is a plain load/store of an owned field plus one `wp_apply` of each axiom.

### Counterexample B (shared message, concurrent): `sizeCache` written between `Size` and the marshal

`proto.Marshal` sizes the message (storing each message's `sizeCache`, `internal/impl/encode.go:118-128`),
then marshals with `UseCachedSize` (`proto/encode.go:183-191`), reading the sub-messages' cached sizes
(`encode.go:52-58`) and failing with `MismatchedSizeCalculation` when the cached size differs from what it
writes (`codec_field.go:163-171`, `:419-433`). With `dq ≠ 1`, `sizeCache` of each message sits in the
persistent `inv pbRtN (rt* l)`, so another goroutine may open it and store any value (an atomic store
needs no more). The spec then forces success on a well-formed message: choose `Ψ none := False`
(`marshalPre`'s `⌜¬ pmOk v⌝ -∗ Ψ none` is provable from `pmOk v`).

    // in package raxos; pm shared (ptPM_persist), a goroutine storing into the invariant's cell:
    go func() { for { atomic.StoreInt32(&pm.P.sizeCache, 1000) } }()
    if _, err := proto.Marshal(pm); err != nil { panic("Marshal of a well-formed message failed") }

Output: `194263/200000 marshals failed; first: marshaling ProposerMessage: size mismatch (see
https://github.com/golang/protobuf/issues/1609): calculated=999, measured=9`, then the panic. The
docstring's argument ("protobuf writes only `state` and `sizeCache`, atomically") covers concurrent
*marshals* (they store equal values for an unchanged message) but the invariant also admits arbitrary
writers.

### Attacks that failed (the axioms survive them)

1. **Concurrent `Marshal` while another goroutine writes a field.** `dq = 1` is exclusive; with
   `dq ≠ 1` the program fields are fractional, so no writer exists. Two concurrent marshals of one
   shared message (or of two messages sharing a sub-message, possible only with `dq ≠ 1`) store the same
   `sizeCache` values: no mismatch.
2. **`nil` message / `nil` sub-message.** `pt*_not_null` excludes a nil top-level pointer and nil
   elements of repeated fields (`repList` of `rep*` at every pointer); an absent singular sub-message is
   `⌜x.P' = null⌝` ↔ `none`, which Go omits, as `encPM` does. (Go would encode a nil repeated element as
   an empty message `2a00`, harmless; the rep excludes it anyway.) No cycles: the message types are not
   recursive.
3. **Encoding exactness.** Fields of the seven kinds match the `.proto`s (`consensus.proto`,
   `client.proto`; proto3, all `int64`/`string`/`bool`/messages, no `sint`, maps, oneofs or packed
   fields); protobuf-go writes fields in number order (`orderedCoderFields`), omits proto3 zeros,
   writes negative `int64` as a 10-byte varint, present empty sub-messages and empty repeated strings
   as `tag 00`. Checked against a hand evaluation of `encPM`: `08ffffffffffffffffff01 1a06 2200 2a02 1200
   2002 2a00` for `Sender -1`, a proposal with `Ids [""]` and one batch of one empty message, `S 2`, one
   empty decided slot. `Empty` marshals to a non-nil empty slice; `s ↦* []` holds either way.
4. **Invalid UTF-8.** proto3 strings, singular and repeated, nested at any depth, are validated by
   `Marshal` (`string field contains invalid UTF-8`, tested on a nested repeated `Ids` and on an
   overlong `c0 80`); `validUtf8` (Msg.lean:167) is Go's `utf8.Valid` (lead bytes `c2..f4`, the
   `e0`/`ed`/`f0`/`f4` second-byte ranges). Errors only on `¬ ok`, which is when `Ψ none` is offered.
5. **Other `Marshal` errors on a well-formed message** (where `Ψ none` may be `False`): no required
   fields (proto3: the final `checkInitialized`, `proto/encode.go:206-209`, finds none); sizes above `MaxInt32` store `0` in `sizeCache` and are
   recomputed (`encode.go:119-124`), no error. Only counterexample B makes a well-formed marshal fail.
6. **Unmarshal into a reused message.** `unmarshalPre` requires `l ↦ zero_val`; even a reused one is
   `Reset` first (`proto/decode.go:94-95`, `Merge = false`). Excluded by the premise in any case.
7. **Aliasing of the input bytes.** Strings are copied (`string(v)`); without the internal
   `AliasBuffer` flag nothing retains `b`. Test: clobbering the input after `Unmarshal` left
   `d.Ids = ["abc"]`. `b ↦*{dq} bs` back is right.
8. **Unmarshal success with unknown fields or non-canonical bytes.** `Unmarshal([08 01], &Empty{})`
   succeeds keeping unknown bytes `0801`: `decInto` gives the representation only when `bs = enc v0`
   for a well-formed `v0`, so nothing false is claimed. Invalid UTF-8 fails (`Ψ false`).
9. **`decInto`'s uniqueness claim** (`∀ v0, ok v0 → enc v0 = bs → v = v0`: if two well-formed values
   had one encoding, `False` would follow). Every `enc*` is injective on well-formed values: fixed field
   order with distinct tags, `fVarint` of a value in `int64` range injective through `u64`, presence
   of optional sub-messages and every repeated element encoded, `Batch` has exactly the three encoded
   fields (`Pure/Smr.lean:32`).
10. **Fractions.** `Unmarshal` asks only `b ↦*{dq} bs` and returns it; `Marshal` returns the whole
   representation at the same `dq`. Both are what protobuf touches (it reads, plus the runtime fields).
11. **Cross-world entailments.** None: the statements are triples, the pure conclusions are about
   values the program owns in the execution.

Not tried: gRPC's codec path (`encoding/proto`, `MarshalAppend` after `Size`; a separate hypothesis
which the docstring says writes the same fields: counterexample B applies there too), `ClientStatus`
(not in the specs).

## Proposed restatement (not applied)

Either of:

- **State it in the representation.** Constrain the runtime fields: owned (`dq = 1`), expose the
  program fields as the whole struct minus `state`/`sizeCache` and keep those two behind a protobuf
  token `rt* l` with `state` either zero or the type's own `MessageInfo` (a pure fact over the
  generated `file_…_msgTypes[i]` location), which the program cannot store into; shared, make the
  invariant's content that predicate, sealed (`@[no_expose]` or a ghost token only the axioms hold),
  so a client cannot open it, and with `sizeCache ∈ {0, size v + 1}` for the immutable value `v`.
  A whole-struct copy of a message (`*a = *b`, same type) keeps a valid `state`, so it can stay
  allowed through a law.
- **Make the condition a gate.** Keep the statement and add a check (next to `etc/exit-check.py`-style
  gates) that no non-generated Go file in a package declaring these message types names `state`,
  `sizeCache` or `protoimpl.MessageState`/`SizeCache`; record in the axiom's docstring that the
  axiom is sound only for such programs. Weaker: the Lean statement stays false.

No bug in the verified Go code (protobuf-go documents `UseCachedSize`'s preconditions,
`proto/encode.go:60-73`; QuePaxa never writes the runtime fields).
