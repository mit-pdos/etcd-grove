/-
The trust boundary: `fmt.Sprintf` for arguments that are not all of predeclared basic types
(as `fmt.Printf`, `Proof/fmt/Printf.lean`; rafthttp stage 7e, the user's choice).
-/
module

public import Spec.fmt.SprintfArgs

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

/-- **The trust boundary**: Go's `fmt.Sprintf` formats its arguments and returns the result.
For the arguments `fmt.argsOk` allows it calls only their `Error()`/`String()` methods, which
return a string without effects by that premise; it only reads the arguments' slice. -/
axiom fmt.SprintfArgs.wp_proof : fmt.SprintfArgs.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
