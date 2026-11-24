/-
`typedNilString` (see its spec): proved over Perennial's model of `reflect` (reflect S0).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.specreq.reflect.typedNilString
public import Perennial.Spec.reflect.ValueOf
public import Perennial.Spec.reflect.Value__IsNil
public import Perennial.Spec.reflect.Value__Kind

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace specreq_reflect

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.specreq.reflect

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.specreq.reflect.Assumptions]

theorem typedNilString.wp_proof
    (hV : _root_.Perennial.reflect.ValueOf.spec (GF := GF) (hG := hG))
    (hK : _root_.Perennial.reflect.Value.Kind.spec (GF := GF) (hG := hG))
    (hN : _root_.Perennial.reflect.Value.IsNil.spec (GF := GF) (hG := hG)) :
    typedNilString.spec (GF := GF) (hG := hG) := by
  intro T p
  wp_start
  wp_auto
  wp_apply (hV.1 (t := go.PointerType T) 22 #p rfl
    (by simp [_root_.Perennial.reflect.rtype.ty]) (by omega))
  wp_method_call
  wp_pures
  wp_load
  wp_pures
  wp_apply hK
  wp_method_call
  wp_pures
  wp_load
  wp_pures
  wp_apply (hN.1 _ (t := go.PointerType T) (e := T) p (by simp only; rfl) (by simp only; rfl) rfl)
  by_cases hp : p = null
  · simp only [hp, decide_true, if_true]
    wp_auto
    iapply HΦ
    itrivial
  · simp only [hp, decide_false, if_false]
    wp_auto
    iapply HΦ
    itrivial

theorem typedNilString.wp_proof_int
    (hV : _root_.Perennial.reflect.ValueOf.spec (GF := GF) (hG := hG))
    (hK : _root_.Perennial.reflect.Value.Kind.spec (GF := GF) (hG := hG)) :
    typedNilString.spec_int (GF := GF) (hG := hG) := by
  intro n
  wp_start
  wp_auto
  have h1 : go.kindOf go.int = some 2 := by
    simp [go.kindOf, List.find?, go.bool, go.int]
  have h2 : go.int ≠ _root_.Perennial.reflect.rtype.ty := by
    simp [_root_.Perennial.reflect.rtype.ty, go.int]
  have h3 : go.isInterfaceType go.int = false := by rfl
  wp_apply (hV.2.1 (V := w64) (t := go.int) 2 n h1 h2 (by omega) (by omega) (by omega) h3) as %q Hq
  wp_method_call
  wp_pures
  wp_load
  wp_pures
  wp_apply hK
  iapply HΦ
  itrivial

end proof

end specreq_reflect
end EtcdGrove
end Perennial
