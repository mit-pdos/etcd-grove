/-
The trust boundary: `sort.Slice` (`Spec/sort/Slice.lean`). Perennial names it but does not
translate it (`reflectlite.Swapper`, `pdqsort_func`); that a pdqsort by a strict weak order
permutes the slice into sorted order is a standard result (Perennial proves it of `sort.Sort`'s
and `slices.SortFunc`'s pdqsorts).
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
