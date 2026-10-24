/-
The trust boundary: `fmt.Errorf` with arguments of methodless named types
(`Spec/fmt/ErrorfNamed.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.fmt.ErrorfNamed

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

axiom fmt.ErrorfNamed.wp_proof : fmt.ErrorfNamed.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
