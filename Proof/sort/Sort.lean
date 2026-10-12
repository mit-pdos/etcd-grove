/-
`sort.Sort` over a `sort.Interface` (`Spec/sort/Sort.lean`): Perennial's `sort.wp_Sort`.
-/
module

public import Spec.sort.Sort
public import Perennial.Proof.sort_proof.sortInterface

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
theorem sort.«Sort».wp_proof : sort.«Sort».spec (GF := GF) (hG := hG) := by
  intro E x R lt l hswo
  iintro %Φ ⟨#Hinit, #Hs, Hl, %Hlen⟩ HΦ
  ihave #Hs' := sorterSpec_isSorter x R lt $$ Hs
  iapply _root_.Perennial.sort.wp_Sort x R (fun a b => lt a b = true) hswo l $$ [Hl]
  · iframe Hl; iframe #; ipureintro; exact Hlen
  inext
  iintro %l' ⟨Hl', %Hperm, %Hsorted⟩
  iapply HΦ
  iframe Hl'
  ipureintro
  refine ⟨Hperm, fun i j a b ha hb hij => ?_⟩
  have := Hsorted i j a b ha hb hij
  simpa using this

end proof

end EtcdGrove
end Perennial
