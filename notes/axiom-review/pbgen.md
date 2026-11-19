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
