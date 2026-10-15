/-
The trust boundary: `sort.Stable` (`Spec/sort/Stable.lean`). Perennial translates it but has no
proof of it (it proves `sort.Sort`'s pdqsort); a model of a stable sort is a standard result.
-/
module

public import Spec.sort.Stable

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
variable [package_sem : _root_.Perennial.sort.Assumptions]

axiom sort.Stable.wp_proof : sort.Stable.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
