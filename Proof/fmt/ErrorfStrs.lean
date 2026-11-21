/-
`Spec/fmt/ErrorfStrs.lean`: a trust-boundary axiom (Perennial's model of `fmt` is stuck on a
`[]string` argument).
-/
module

public import Spec.fmt.ErrorfStrs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [_root_.Perennial.fmt.Assumptions]

/-- **Trust boundary** (fmtmodel, 2026-11-20; proved over Perennial's previous model of `Errorf`,
`errors.New(format)`, from 2026-11-18, which ignored the arguments; an axiom before). Perennial's
model of `fmt` (`Perennial/TrustedCode/fmt.lean`) is stuck on reflection into a slice, so it does not
cover a `[]string` argument. Go (go1.27.3, `src/fmt/print.go`): `printArg` (line 674) of a `[]string`
finds no method (`handleMethods`, line 614: a slice type has none) and `printValue` (line 756)
prints it element by element (`reflect.Slice`, line 856; `fmtBytes` only for a `uint8` element
kind), each a `string` (no method) by its kind, under any verb (a bad verb prints `%!q(...)`); `%p`
prints its address (`fmtPointer`, line 542); it reads the slice, of which the caller holds a
fraction (given back). An `io/fs.FileMode` (`uint32` kind) under a method verb gets its `String()`
called (`io/fs/fs.go:215-239`: at most 23 bytes into its own `[32]byte`, no panic, no effect),
otherwise is printed as an integer. Basic values call nothing. `Errorf` (`src/fmt/errors.go:23-95`)
then returns `errors.New(s)` (no `%w` with an argument), a `*wrapError` (one) or a `*wrapErrors`
(several): each has `Error() string` returning `s` and no `Format` (`errOk`). The argument slice is
only read. -/
axiom fmt.ErrorfStrs.wp_proof :
    fmt.ErrorfStrs.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
