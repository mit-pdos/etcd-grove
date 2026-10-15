/-
`sort.Reverse` over a `sort.Interface` (`Spec/sort/Sort.lean`): Perennial's `sort.wp_Reverse`.
-/
module

public import Spec.sort.Reverse
public import Perennial.Proof.sort

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

open Iris.ProofMode in
theorem sort.Reverse.wp_proof : sort.Reverse.spec (GF := GF) (hG := hG) := by
  intro E x R lt
  iintro %Φ ⟨#Hinit, #Hs⟩ HΦ
  ihave #Hs' := sorterSpec_isSorter x R lt $$ Hs
  iapply _root_.Perennial.sort.wp_Reverse x R (fun a b => lt a b = true) $$ [] 
  · iframe #
  inext
  iintro %y #Hy
  iapply HΦ
  iapply (isSorter_sorterSpec y R (fun a b => lt b a)) $$ Hy

end proof

end EtcdGrove
end Perennial
