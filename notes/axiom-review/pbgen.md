# Review: pbgen's trusted core (2026-11-19, branch `pbgen-trust`)

**Target.** `models/protobuf/pbgen_core.py` (the protobuf codec generator's trusted core: the subset
check, the refusals, the emitter), with `models/pbdesc/pbdesc.go` (the schema dump it reads) and
`models/pbcodec/pbcodec.go` (the wire helpers the emitted code calls). The claim under review:
for every schema the core accepts, the emitted `pbMarshal`/`pbUnmarshal` behave as protobuf-go
v1.36.12's `proto.Marshal`/`proto.Unmarshal` with default options (`notes/decisions.md`, "Trusted
generated code: the generator is the trusted artifact").

**Method.** A fresh reviewer agent, given only those files (a snapshot), protobuf-go's source in the
module cache and the encoding spec's facts, not the author's conclusions, asked to find an accepted
schema and a value or input on which the emitted code and protobuf-go differ. It ran its
experiments in `/tmp/pbgen-attack/` (schemas built as text `FileDescriptorSet`s, compiled by the
real protoc-gen-go, pbgen run on them, Go tests against protobuf-go).

## Findings

No accepted schema on which the emitted code's successful results (decoded values, encoded bytes)
or its error-or-not differ from protobuf-go. Three behaviours a Go program can observe differ, all
confirmed by running them, none listed among the core's documented deviations at the time:

1. **The message after a failed Unmarshal.** Input `0a 04 01 02 03 80` (a packed `repeated int32`
   field 1 whose last varint is cut short): protobuf-go errs and leaves the field's length as it was
   (`consumeInt32Slice`, `internal/impl/codec_gen.go:741-777`, decodes into a local slice, assigned
   only once the record parsed; `growInt32Slice` has already made it non-nil with capacity 3); the
   emitted code errs with `R = [1 2 3]`. The same for a packed `fixed32` record of 6 bytes.
   **Disposition: documented** (the core's doc, "what comes with an error"): protobuf-go promises
   nothing of a message after an error (a partial merge is visible in its other error paths too,
   and its nil-or-empty state after this one depends on its pre-growing), and a program must not use
   it. Decoding into a local slice would remove the visible values but not the nil-versus-empty
   difference.
2. **The bytes Marshal returns with its error.** `&M{R: []int32{1}, S: "\xff"}`: protobuf-go
   returns the partial buffer `0a01011201ff` with the error (`proto/encode.go:111-115`;
   `appendStringNoZeroValidateUTF8`, `codec_gen.go:5107-5117`, appends before checking); the
   emitted code returns nil. **Disposition: documented**, with (1).
3. **Slice capacities and aliasing on success.** A packed field of 3 values: capacity 3 (pre-grown)
   against 4 (append growth); a 12-byte Marshal result: 12 (`growcap` after a size pass,
   `proto/encode.go:190`) against 16; a 3-byte singular bytes field: 8 (`append([]byte(nil), v...)`)
   against 3 (`CopyBytesOrNil`). A program appending twice to a decoded slice sees the two appends
   share an array or not accordingly. **Disposition: documented** (the core's doc, "slice
   capacities and aliasing"): lengths and contents agree; matching capacities would mean
   reproducing protobuf-go's sizing passes, which no program we verify depends on.

Suspected, not confirmed:

- Pre-`XXX_` golang/protobuf (APIv1) messages registered through the legacy path: any exported
  `XXX_` field lands in the dump's `go_extra` and is refused; not testable here (golang/protobuf is
  not in the module cache).
- A dump built against other `.pb.go` versions than the program links would give wrong facts and
  wrong code accepted, though the dump runner is untrusted. **Disposition:** pbgen runs the dump in
  the very Go module the codec is generated into, so it links the same `.pb.go` files; the core's
  doc now says so, and that `pbdesc` is trusted with the core.

Checked and consistent (the reviewer's list, abridged): tag parsing (64-bit comparison before
conversion, overlong tags, field number 0 and above 2^29-1, end-group at message level, wire types
6 and 7); the recursion limit (10000 messages) and unknown groups' nesting (10001); packed and
unpacked acceptance, an empty packed record, fixed-width remainders; int32/enum truncation, sint32
as `DecodeZigZag(v & MaxUint32)`, bool as `v != 0`, sign-extended enum encoding; zero-value
omission; empty bytes decoding (nil singular, non-nil repeated element); UTF-8 on both sides,
singular and repeated, as `strs.EnforceUTF8` without the legacy flag (pbdesc's `enforceUTF8`
mirrors it); merge of singular messages, append of repeated ones only on success, nil repeated
elements written empty; Marshal of nil and of empty messages; field order; cached sizes with a
shared sub-message; protoc-gen-go's `API_HYBRID` (accepted: the same struct layout and coders; the
generated tests pass); naming and alias collisions (compile errors at worst); well-known types
without maps or oneofs.

## Result

No change to the emitted code. The core's documented deviations gained "what comes with an error"
and "slice capacities and aliasing", and its doc says `pbdesc` is trusted with it and that the dump
is made in the codec's own module.

## The proto2 and oneof extension (2026-11-23, branch `ps2-pbgen-proto2/2026-11-23`, proving session 2, #18, offered by #24)

**Target.** The extended core (`models/protobuf/pbgen_core.py`: proto2 and proto3 explicit presence,
required fields, defaults, closed enums, packed and unpacked repeated scalars, oneofs) and
`models/pbdesc/pbdesc.go`'s new facts (oneof holders via `protobuf_oneof` tags, wrappers via the
registered `protoimpl.MessageInfo.OneofWrappers`, the opaque/hybrid presence and lazy fields). Same
claim and method as above: a fresh reviewer agent with a snapshot of `models/` and protobuf-go's
source, not the author's notes, asked for an accepted schema on which the emitted code and
protobuf-go differ (experiments in `/shared/tmp/ps2/pbgen2/review/attack/`).

**Found by the author's tests, before the review** (now refusals, both shown on protobuf-go by
`models/internal/pbgenrand`'s `TestProtobufQuirks`, which fails if protobuf-go changes):

1. **A oneof's non-first member with required fields.** Proto2 `M0 { required int32 x = 1; }`,
   `M1 { oneof u { int32 f0 = 1; M0 f1 = 2; } }`, input `12 00` (f1, an empty M0): protobuf-go's
   Unmarshal succeeds, and Marshal of the result fails. Its fast path (`internal/impl/decode.go:189`)
   consults the isInit of the field's own coder, which only the oneof's first member's coder has
   (`codec_field.go:83-118`); the full check (Marshal's, and Unmarshal's when the fast path says
   so) goes through the first member to the set one. Found by `pbgenrand` (seed 1).
   **Disposition: refused** (a oneof member other than the first declared, of a type reaching
   required fields).
2. **Required fields reached only through a cycle.** `R { A a = 1; }`, `A { B b = 1; C c = 2; }`,
   `B { A a = 1; }`, `C { required int32 x = 1; }`: once `R`'s coder is built first, `B`'s
   Marshal and Unmarshal never check required fields (`Marshal(&B{A: &A{C: &C{}}})` succeeds;
   built in another order, it fails). `needsInitCheckLocked` (`checkinit.go:137-170`) returns
   false on meeting a type in progress and caches the result of every type it finishes, so `B`
   (finished while `A` was in progress) keeps a false. Found by reading the source.
   **Disposition: refused** (a type with no required field of its own that reaches one, in a
   cycle of two or more message types): its behavior depends on the program's history.

**The review's findings.** No divergence on any accepted schema: its own reflection-based fuzzer
(Marshal of random values, typed-nil wrappers, wrappers holding nil messages, nil repeated
elements, nil `*T`; Unmarshal of real, mutated, doubled and descriptor-guided random inputs; and
re-Marshal of decoded values), about 20k iterations per type over schemas with oneofs of every
member kind (the first-declared member numbered above later ones, three oneofs in a message, real
oneofs beside proto3 `optional`, wrapper names protoc-gen-go renames), required fields (direct,
message, bytes, enum, nested, in repeated elements, in a oneof's first member, 70 in one message),
defaults of every kind, closed enums at `INT32_MIN`, packing mixes, unchecked proto2 strings; the
recursion limits through singular, repeated, oneof and `optional` fields; and `pbgenrand` rerun on
three new seeds. It checked the two refusals sufficient (the fast path skips the check only where it
would pass, past 64 required fields included; a wrongly cached false needs a type in a cycle of two
or more that reaches required fields without its own). Reported and fixed:

- `RESERVED` lacked `new`, which the emitted code now calls: a Go package named `new` would have
  got that alias and the codec would not compile (never wrong code). **Fixed.**
- The doc said internal/impl reads a field's default only for map keys; it also does in its
  reflection and getter paths (`convert.go:95, 380`, `message_reflect_field.go:41, 53`,
  `legacy_message.go:535`): no coder reads it, the point stands. **Fixed** (the wording), with two
  off-by-a-few line citations (`decode.go:226-229`, `checkinit.go:126-170`).

## Result (the extension)

The claim stands for the extended subset, with the two refusals above. Evidence: `pbgenrand` with
proto2 and proto3 files (seeds 1-4: 24 + 3 x 48 schemas, about 620 message types and 3700 fields;
seed 4's schemas alone: 38 proto2 and 36 proto3 files, 315 explicit-presence fields, 34 required,
119 proto3 `optional`, 75 defaults, 132 oneofs with 332 members, 141 unpacked and 107 packed repeated
scalars, 57 closed enums), its refusals (`TestRefusals`, `TestProtobufQuirks`), the regression
tests beside `examples/models/pbetcd` (now raftpb, walpb, `TxnRequest`/`Compare`/`RequestOp`/
`ResponseOp`/`InternalRaftRequest`/`WatchRequest`: 66 message types, 232 fields, 13 enums) and
`models/internal/pbdifftest`, and this review.

## Pre-review of the extension (2026-11-23, upamanyus session, #24, at `884fa47be4`)

Verdict "sound as claimed": no accepted schema on which the emitted code and protobuf-go differ
beyond the documented deviations (now including that a known oneof member with another wire type is
an unknown field, dropped). Its reruns: `TestRandomSchemas` at seeds 1, 7 (96 schemas) and 1234 (96
schemas), `TestRefusals`, `TestProtobufQuirks`. Findings, none unsound, and what was done:

1. The cycle refusal refuses a type with no required field of its own that reaches one and lies on
   a cycle of two or more message types, also when it reaches one outside the cycle (`A{B b; C c}`,
   `B{A a}`, `C{required x}`: `A` is refused); the doc and the message said "only through a cycle".
   Conservative, so not unsound. **Fixed**: the wording (core doc, refusal message, `decisions.md`);
   the behavior kept.
2. Every test ran one order of protobuf-go's lazy type setup per process (its `needsInitCheck` is
   cached per type at first use). **Added** `models/internal/pbgenrand`'s `TestOrders`: a proto2
   and proto3 schema (a self-loop and a two-type cycle whose types have required fields of their
   own, a self-loop reaching required fields only outside it, a cycle with no required field, a type
   outside a cycle reaching one, a oneof whose first member needs the check, unchecked proto2 and
   checked proto3 strings), the generated tests run in 13 orders, each in a fresh process (an empty
   message of every type marshaled first, in that order). All agree.
3. The random schemas never have more than about 10 required fields in a message, and
   `avoidQuirks` strips the cycles it targets. **Added** to `TestOrders`'s schema a message of 70
   required fields and the near-miss cycles above, and `TestFullRequired` (each type with every
   required scalar set, then each missing in turn: Marshal, and Unmarshal of the partial encoding),
   which reaches the full check past protobuf-go's 64-bit mask.
4. Defense in depth: `pbdesc` now records a Go type that is not an APIv2 message or has its own
   codec methods (`Marshal`, `Unmarshal`, `XXX_Marshal`, `XXX_Unmarshal`, `XXX_Size`: APIv1 and
   gogo), and the core refuses it (protobuf-go's legacy path); `TestRefusals` has one (`p3.Leg`, a
   generated message given its own `Marshal`/`Unmarshal`).

## The pbmodel mode: same-package methods, unknown fields, the size cache, Clone (2026-11-23, branch `proto-s3-go`, #37 stage S3, Go side)

Not a review: the author's account of what changed in the trusted core, for the review requested on
#37. Decisions it implements: D1 (dispatch by methods in each message's own package), D2 (unknown
fields kept), D-A (a default `Marshal` reads the caches as protobuf-go does), D-C (a size mismatch is
an error the specs rule out, not one they describe).

**What changed in the trusted core.**

- `pbgen_core.py`: a second mode, `--pbmodel` (`pbmodel_go`, the `pm_*` functions; the doc's new
  section "THE SAME-PACKAGE METHODS", every choice cited to protobuf-go v1.36.12). The codec mode is
  unchanged (its emitted code is byte for byte the same; only its generated test changed) and keeps
  its deviations, unknown fields dropped among them: it stays for the dsverify kits that register a
  codec (`quepaxa`) until they move. The doc's deviations are now the codec mode's; the pbmodel
  mode has none but the error values (beyond their class) and slice capacities.
- `Schema(pbmodel=True)` refuses a message whose Go struct lacks protoc-gen-go's `sizeCache int32`
  or `unknownFields []byte` (the fields internal/impl's struct reader finds by those names), and a
  type with a method or field of the generated prefix `PbModel` (which a hand-written method could
  otherwise shadow, or collide with).
- `pbdesc` dumps those facts (`go_size_cache`, `go_unknown_fields`, `go_pbmodel_methods`); the
  codec mode ignores them.
- New untrusted pieces: the generated test (`pbgen_testgen.py`: an exact mode, and the Size/Clone,
  interleaving and concurrency tests), `pbgen.py --pbmodel` (writes into every package of the closure,
  refusing a package in the module cache), the proto model's composition (`models/protobuf-go/proto/model.go`)
  is trusted with the methods: it is the one place the methods are composed into `proto`'s API.

**Why each choice** (the protobuf-go lines are in the core's doc; the points a reviewer may doubt):

1. *Methods only, all exported, prefix `PbModel`* (no package-level function or variable, no init):
   a package-level name could collide with the message package's own code, which the dump cannot
   see; an exported method is in reflect's method set, so `pbdesc` sees a collision and the core
   refuses it. The imports are renamed (`pbmodelcodec`, `pbmodelatomic`) for the same reason; the
   gates (and `pbmodel_forks.py` on the forks) check that no other Go code names the methods.
2. *Unknown fields as protobuf-go keeps them*: the tag re-encoded minimally from the number and wire
   type read, then the value's bytes as `ConsumeFieldValue` delimits them (so a non-minimal tag is
   normalised, the value never is), appended in arrival order, a nested message's into it; written
   after the known fields (and after the oneofs); merged by `Clone` only when non-empty.
3. *The size cache*: `PbModelSize(cached)` is `sizePointer` exactly, including that a cached size is
   used only when above 0, that a recomputed level stores size+1 (0 past MaxInt32-1) atomically,
   and that a level recomputed over a stale child stores the stale-derived value.
   `PbModelAppend(b, cached)` checks only nested lengths (the top level's cache is never compared),
   returns nil on a mismatch and what was appended on a nested error (the check is skipped then).
   The proto model's `Marshal` is a size pass with the options' `UseCachedSize`, then an append pass
   with the caches read, as `proto.MarshalOptions.marshal`. So a default `Marshal` can fail when a
   concurrent cached `Size` writes a stale-derived size in between (W14's measurement, D-A): the
   methods reproduce it (`cache_test.go`, 1 in 5000 races).
4. *What comes with an error is protobuf-go's*, which the codec mode did not claim: Marshal's
   partial bytes on invalid UTF-8 (appended, then checked) and full bytes with a required-field
   error; Unmarshal's partial message, where every store happens where protobuf-go's consumer's
   does. The one subtle case: a packed record first grows the slice to a new array (stored at once,
   so a nil slice becomes non-nil even if the record then fails), as `growInt32Slice`; the first
   pbdifftest run found it (an empty non-nil slice left by a failed decode).
5. *Marshal's buffer is pre-sized as protobuf-go's* (`growcap` when the size does not fit): not for
   the capacity (unclaimed) but for nil-ness: a cached `MarshalAppend(nil, m)` over a garbage
   top-level cache of an empty message returns a non-nil empty slice in protobuf-go (its pre-sized
   buffer), which the first interleaving run found against a model without it.
6. *Clone* is `mergePointer` into a new message, with each field's merger chosen as protobuf-go's
   `fieldCoder` chooses it. The surprises, each reproduced: an implicit-presence bytes field that is
   empty but non-nil clones to nil, an explicit-presence one to a non-nil empty slice; an empty
   non-nil repeated field clones to nil; a nil element of a repeated bytes field clones to a non-nil
   empty slice, of a repeated message field to an empty message; a oneof wrapper holding nil bytes
   clones to one holding an empty non-nil slice, holding a nil message to one holding an empty
   message (the member's coder has presence, so it copies unconditionally); a typed-nil oneof
   wrapper clones to a nil oneof; unknown fields are copied, the size cache is not.
7. *Error classes*: Marshal's (invalid UTF-8, size mismatch, required field) are claimed; Unmarshal's
   only required-or-not (the decoder returns a bool, as the codec mode's).
8. *The proto model* (`models/protobuf-go/proto/model.go`) composes the methods as `proto` composes
   protobuf-go's coders, and panics `NotModelled` for a type without methods, other unmarshal
   options, `MarshalState`, `UnmarshalState`; `Deterministic` is accepted (no maps, extensions or
   lazy fields in the subset: the only places internal/impl reads it). `MessageV2Of` returns a v2
   message as it is (protobuf-go's `protoMessageV2Of`). Its own test (`models/internal/pbmodeltest`)
   compares transcripts of the real build and the model build.

**Evidence (2026-11-23).** `pbgenrand` seed 1, 24 schemas (81 message types, 507 fields; 14 proto2
and 20 proto3 files, 65 oneofs, 14 required fields): the methods' Marshal 45840 encodings equal and
3067 errors agreed (bytes and class); 112433 mutated decodes equal and 135567 errors agreed with the
message left (unknown fields included); 18600 Size and Clone comparisons; about 119,000 interleaved
operations on shared messages (1085 size mismatches, 2173 required-field errors agreed); the
concurrent test under `-race`. pbdifftest's packages (pb, xpb: about 16,600 encodings, 37,700
mutated decodes, 6000 Size/Clone comparisons, 39,000 interleaved operations with 478 mismatches).
etcd's and raft's packages (`pbmodel_forks.py`: authpb, etcdserverpb, membershippb, mvccpb, leasepb,
walpb, raftpb, 16,329 generated lines): all their generated tests pass, and their `-race` run.
`cache_test.go`'s named cases and `pbmodeltest` (9748 transcript lines equal across the builds).
