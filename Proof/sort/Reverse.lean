/-
The trust boundary: `sort.Reverse` (Perennial translates `sort` without it), over a
`sort.Interface` (`Spec/sort/Sort.lean`).
-/
module

public import Spec.sort.Reverse

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

axiom sort.Reverse.wp_proof : sort.Reverse.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
