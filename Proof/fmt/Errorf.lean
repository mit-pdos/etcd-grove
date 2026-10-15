/-
The trust boundary: `fmt.Errorf` for arguments that are not all of predeclared basic types
(Perennial's model of `Errorf` calls no method of its arguments, so it is faithful only for
those, and its `fmt.wp_Errorf` is stated for them only).
-/
module

public import Spec.fmt.Errorf

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

/-- **The trust boundary**: Go's `fmt.Errorf` formats its arguments and returns a non-nil
error (`*fmt.wrapError`, `*fmt.wrapErrors` or `*errors.errorString`) whose `Error()` returns
the formatted string, which it computed. For the arguments `fmt.argsOk` allows it calls only
their `Error()`/`String()` methods, which return a string without effects by that premise;
it only reads the arguments' slice. -/
axiom fmt.Errorf.wp_proof : fmt.Errorf.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
