/-
`maps.Keys` on a `map[string]runtime.Object` (see its spec, `Spec.maps.Keys`): Perennial's
`maps.wp_Sorted_Keys_string` at `V := GoInterface`, without its slice's capacity.
-/
module

public import Spec.maps.Keys
public import Perennial.Proof.maps.Results

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.maps.Assumptions]
variable [package_sem' : _root_.Perennial.slices.Assumptions]
variable [package_sem'' : _root_.Perennial.cmp.Assumptions]

theorem maps.Keys.wp_proof_objMap : maps.Keys.spec_objMap (GF := GF) (hG := hG) := by
  intro m
  wp_start_folded as -
  wp_apply (_root_.Perennial.maps.wp_Sorted_Keys_string (V := GoInterface) m) as %f #Hf
  iapply HΦ
  imodintro
  iintro %M %dq %Ψ #Hinit HM %Hsize HΨ
  iapply Hf $$ %dq %M %Ψ Hinit HM %Hsize
  inext
  iintro %s %ks HM' Hs - %Hks
  iapply HΨ $$ HM' Hs %Hks

end proof

end EtcdGrove
end Perennial
