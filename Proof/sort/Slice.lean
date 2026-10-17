/-
`sort.Slice` (`Spec/sort/Slice.lean`): the trust boundary. Perennial does not translate it (its
swaps go through `reflectlite.Swapper`), so its spec is assumed: the standard library's
`sort.Slice` permutes the slice, calling `less` only on indices in range.
-/
module

public import Spec.sort.Slice

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

axiom sort.Slice.wp_proof : sort.Slice.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
