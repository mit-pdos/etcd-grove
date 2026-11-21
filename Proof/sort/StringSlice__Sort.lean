/-
`sort.StringSlice.Sort`, proved over Perennial's translation of Go's (`sort.Sort` over the slice's `Len`, `Less`, `Swap`).
-/
module

public import Spec.sort.StringSlice__Sort
public import Perennial.Proof.sort.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.sort.Assumptions]

theorem sort.StringSlice.Sort.wp_proof : sort.StringSlice.Sort.spec (GF := GF) (hG := hG) := by
  intro x xs
  iintro %Φ ⟨#Hpkg, Hx, %Hlen⟩ HΦ
  wp_apply _root_.Perennial.sort.StringSlice.wp_Sort $$ [$Hx] as %xs' ⟨Hx, %Hperm, %Hsorted⟩
  · ipureintro; exact Hlen
  iapply HΦ
  iframe Hx
  ipureintro
  exact ⟨Hperm, Hsorted⟩

end proof

end EtcdGrove
end Perennial
