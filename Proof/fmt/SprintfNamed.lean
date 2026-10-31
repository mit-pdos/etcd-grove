/-
The trust boundary: `fmt.Sprintf` with arguments of methodless named types
(`Spec/fmt/SprintfNamed.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.fmt.SprintfNamed

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

/-- **The trust boundary**: `fmt.Sprintf` with arguments each `nil`, of a predeclared basic type,
or of one of `fmt.methodlessNamedTypes` returns a string `s` with `fmt.SprintfOut format xs s`,
and only reads the arguments' slice.

True of Go: a value of a named type with a basic underlying type and no methods is formatted by
reflection on its kind (`fmt.(*pp).printValue`), calling no method of it, so `Sprintf` neither
panics nor touches memory; and `SprintfOut` constrains the output only at the directives it
formats (`%%`, `%s` of a `string`, `%d`/`%v`/`%0Nd`/`%x` of a predeclared integer type), leaving
it arbitrary from any other directive on. Since Perennial `d62b13ac1` it also formats these integer
directives of a named integer type without formatting methods (`fmt.IntArgValue.named`,
under `fmt.NoFmtMethods`) as Go does (`LeaseID` is one), and leaves a directive consuming any other
named-type argument arbitrary. True of Perennial's model of `Sprintf`
(`Perennial/TrustedCode/fmt.lean`) as well, whose `wp_Sprintf` now admits named integer types
without formatting methods itself (`fmt.IsIntArgType`): this axiom could be derived from it for
`LeaseID` (`notes/STATUS.md`, "Perennial pin d62b13ac1"). -/
axiom fmt.SprintfNamed.wp_proof : fmt.SprintfNamed.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
