# Review: jsongen's trusted core, the 2026-11-23 extension (branch `ps2-jsongen/2026-11-23`)

**Target.** `models/json/jsongen_core.py` with `models/jsondesc/jsondesc.go` (trusted with it) and
`models/jsoncodec/jsoncodec.go`, after the extension to embedded structs, pointers and a type's own
`MarshalJSON`/`UnmarshalJSON` (`notes/jsongen-extension.md`, `notes/decisions.md` "jsongen's subset
extended to embedded structs, pointers and a type's own JSON methods"). The claim under review: for every
set of types the core accepts, the emitted `jsonMarshal`/`jsonUnmarshal` behave as Go 1.27.3's
encoding/json (default build: v1 over v2 with `DefaultOptionsV1`): bytes and error-or-not, decoded
values, and the user methods called, in order, on the same receivers with the same bytes; but for
`NotModelled` panics and the documented deviations.

**Method.** A fresh reviewer agent, given only a snapshot of `models/` (commit `f8b72d52e4`), Go's
source and the claim, not the author's conclusions or tests' results, asked to find an accepted input on
which the emitted code and encoding/json differ. Its experiments: `/shared/tmp/ps2/jsongen/review-work/`
(`e1`..`e4`).

## Findings (all confirmed by running; all fixed or made a stated precondition)

1. **UnmarshalJSON on a slice element ran on a temporary.** The slice decoder decoded each element into
   a local and appended it; the real one grows the slice (`reflect.Value.Grow(1)`) and decodes into
   `va.Index(i)` in place (`v2/arshal_default.go`:1565-1588). A method keeping its receiver (`p.self =
   p`, or a registry of receivers) saw a different address: input `{"S":[1],"F":2,"P":3}` into
   `Holder{S []SP; F SP; P *SP}`, real `S[0].self == &S[0]`, codec not. **Fixed:** the element is appended
   as a zero value and decoded in place (`s = append(s, z); jdec(…, &s[n], …)`); Go's append and
   `reflect.Value.Grow(1)` grow by the same rule from the same capacity, so the backing arrays, the
   capacities and the receivers' addresses are the real ones (`TestReceiversAndCycles`, also with nine
   elements across several growths; the pre-fix core fails it).
2. **A fatal error from UnmarshalJSON.** Under v1's options `isFatalError` (`v2/errors.go`:53-65) still
   stops decoding on a `*jsontext.SyntacticError` or jsontext's I/O-error wrapper; the codec recorded it
   and went on, calling the later methods (real `[SE.U 1]`, codec `[SE.U 1, SE.U 2, SE.U 3]`).
   **Disposition: a stated precondition** (the core's doc, OWN METHODS): those error values are made only
   by `encoding/json/jsontext` and `encoding/json/v2`, which the model does not cover (the v1 API turns
   syntactic errors into `*SyntaxError` and unwraps I/O errors: `v2_scanner.go`:56-70,
   `internal.TransformUnmarshalError`); a program whose methods return one is outside the claim.
   Recognizing them in the codec would need jsontext's types, which the model does not have.
3. **Pointer cycles.** The real encoder tracks pointers and slices from depth 1000 and fails on a cycle
   (`visitPointer`, `startDetectingCyclesAfter`, `arshal_default.go`:50, 62-83, 1479-1485, 1729-1735);
   the codec ran to the 10000 nesting limit. Error-or-not agreed, but the methods called did not (1001
   against 10000 `MarshalJSON` calls on `Cyc{M ML; Next *Cyc}`, `c.Next = c`). **Fixed:** the pointer and
   slice encoders panic `NotModelled` from depth 1000 (at or before where the real one starts tracking,
   whichever way its depth is counted), so no value nested that deep through a pointer or slice is
   claimed (`TestReceiversAndCycles`'s `TestCycle`; the generated test admits a `NotModelled` panic where
   the real encoding nests 1000 deep).

Three docstring claims were wrong or incomplete in the same places (the slice rule, the pointers'
encoding without the cycle check, the method errors as never fatal); rewritten with the fixes.

Suspected, not confirmed: other fatal errors a method can produce by driving its own `jsontext.Decoder`
(covered by the precondition of finding 2).

## Checked and consistent (the reviewer's list, abridged)

Breadth-first flattening; the `seen`/visitChildren rule with a type embedded twice; self- and mutual
embedding through pointers; ambiguous names dropped at equal depth; tagged beating untagged; exact match
before case folding, folded matches in breadth-first order, `a_b` against `AB`; nil embedded pointers
skipped on encode and allocated on decode, also an exported embedded pointer reached through an unexported
embedded struct (real can set it: no `errNilField`); the selector refusals; pointer-receiver
`MarshalJSON` on a value root, a pointer root, a field, a slice element, a pointer field, behind an
embedded pointer, in a nested struct; `null` to the method but a `*T`'s `null` to the pointer;
the method's bytes without whitespace; merging into existing pointees; `MarshalJSON` output compacted,
numbers verbatim (`1.50E+2`, `-0`), duplicate keys allowed, 0x7f raw; `omitempty` on method types; the
nesting limit around 10000; the integer and quoted-integer parsers.

## The author's own evidence

`models/internal/jsongenrand`: random types (embedded, unexported embedded, embedded pointers, repeated
and self-embedded types, colliding Go and JSON names at equal and different depths, pointers, types with
JSON methods on value and pointer receivers in every context) against the real encoding/json, comparing
bytes, values, errors-or-not and the logged method calls in order; 40 modules (seed 1000): 2362 types,
about 2.0M encodings and 120k decodings, 299k method calls agreed; after the review's fixes, 30 more (seed 5000): 2079 types, 271k method calls agreed. Nine mutants of the core caught.
`TestRefusals` (one input per refusal), `TestAccepted`, `TestReceiversAndCycles`. Regression codecs
`examples/models/jsonetcd` and `models/internal/jsonvsr`.
