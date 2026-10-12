/-
The trust boundary: `sort.Sort` (Perennial translates `sort` without it), over a
`sort.Interface` (`Spec/sort/Sort.lean`).
-/
module

public import Spec.sort.Sort

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

axiom sort.«Sort».wp_proof : sort.«Sort».spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
