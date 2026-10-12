/-
The trust boundary: `fmt.Printf` for arguments that are not all of predeclared basic types
(as `fmt.Errorf`, `Proof/fmt/Errorf.lean`).
-/
module

public import Spec.fmt.Printf

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

/-- **The trust boundary**: Go's `fmt.Printf` formats its arguments, writes the result to
`os.Stdout` (outside the model) and returns the count written and the write's error. For the
arguments `fmt.argsOk` allows it calls only their `Error()`/`String()` methods, which return a
string without effects by that premise; it only reads the arguments' slice. -/
axiom fmt.Printf.wp_proof : fmt.Printf.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
