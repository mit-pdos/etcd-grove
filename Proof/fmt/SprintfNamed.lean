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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
formats (`%%`, `%s` of a `string`, `%d`/`%v`/`%0Nd` of a predeclared integer type), leaving it
arbitrary from any other directive on, in particular from the first that consumes a named-type
argument (its dynamic type is neither `string` nor a predeclared integer type). True of
Perennial's model of `Sprintf` (`Perennial/TrustedCode/fmt.lean`) as well, which formats such an
argument as an unknown directive: its `wp_Sprintf` asks `fmt.IsBasicType` only for the model's
faithfulness to Go. -/
axiom fmt.SprintfNamed.wp_proof : fmt.SprintfNamed.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
