/-
`Spec/fmt/ErrorfSlice.lean`: a trust-boundary axiom (Perennial's model of `fmt` is stuck on a slice
argument). Lean-first.
-/
module

public import Spec.fmt.ErrorfSlice

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
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- **Trust boundary** (fmtmodel, 2026-11-20; before, `fmt.ErrorfLeaf`'s proof over the previous model
of `Errorf`, which ignored the arguments). Go (go1.27.3, `src/fmt/print.go`): `printArg` (line 674) of a slice finds no method on it
(`handleMethods`, line 614: a slice type has none) and `printValue` (line 756, its `reflect.Slice`
case at line 856) writes `[`, each element by `printValue(f.Index(i), verb, depth+1)` (line 889) and
`]`; an element, of a non-interface type, is formatted at depth 1 by `handleMethods` with the same
verb, exactly as a top-level argument `fmt.argOkAtBase` that verb (its `Error()`/`String()` returning
some string needing nothing, or no method: `fmt.sliceArgOk`'s header). The slice is only read (the
caller holds it persistently, `↦*□`). The other arguments are as Perennial's model covers them. `Errorf` (`src/fmt/errors.go:23-95`) returns
an `*errors.errorString`, a `*wrapError` or a `*wrapErrors` (by its `%w` directives), each with
`Error() string` returning the message, no `Format` and no `Errors` method (`errors.go:75-95`,
`errors/errors.go`). -/
axiom fmt.ErrorfSlice.wp_proof : fmt.ErrorfSlice.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
