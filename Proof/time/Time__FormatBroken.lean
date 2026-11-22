/-
**TRUST-BOUNDARY AXIOM** (2026-11-22, the user's approval): `time.Time.Format` at the WAL's layout
`"20060102.150405.999999"` (`cleanupWAL`, the broken directory's name) returns a string with no `/` and
no NUL byte, does not panic, and changes nothing else (`Spec/time/Time__FormatBroken.lean`,
`time.Time.Format.specBroken`). Review: `notes/axiom-review/time-format-broken.md`.

Why an axiom: Perennial's `time` has `Time.Format` names-only (no body: the call cannot be stepped), and
a model would need `appendFormat` with `Time`'s calendar arithmetic and `Location` lookup translated.
The claim is the WAL's whole use of the result (`brokenName_nameOk`) and is far weaker than what Go's
`appendFormat` does at this layout: every byte it appends is a digit, `.` (the layout's two literal dots,
the fraction's), or a `-` (a negative year) -- see the spec's header. It never panics on a `Time` whose
`Location` no one writes: `appendFormat` handles every layout and every `Time` (no index or division by
a value it does not bound), and the `Location` lookup of `Local` (`initLocal` under a `sync.Once`,
falling back to UTC on a missing or malformed zone file) or of `UTC` has no failure path. A write to the
`Location` racing with `Format` does make it panic (`Location.lookup`, index out of range), hence the
precondition: the `Location` is `UTC`'s or `Local`'s, which no program can write (the spec's header;
independent review 2026-11-22).
-/
module

public import Spec.time.Time__FormatBroken

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- **Trust-boundary axiom**: see the file header. -/
axiom time.Time.Format.wp_proofBroken : time.Time.Format.specBroken (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
