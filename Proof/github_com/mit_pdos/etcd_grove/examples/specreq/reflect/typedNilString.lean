/-
`typedNilString` (see its spec): proved over Perennial's model of `reflect` (reflect S0).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.specreq.reflect.typedNilString
public import Perennial.Proof.reflect.Link
public import Perennial.Proof.reflect.Results

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

theorem typedNilString.wp_proof :
    typedNilString.spec (GF := GF) (hG := hG) := by
  intro T p
  wp_start
  wp_auto
  wp_apply (_root_.Perennial.reflect.wp_ValueOf_reflPtr T p) as %w %Hw
  subst Hw
  wp_method_call
  wp_pures
  wp_load
  wp_pures
  wp_apply _root_.Perennial.reflect.Value.wp_Kind
  wp_method_call
  wp_pures
  wp_load
  wp_pures
  wp_apply (_root_.Perennial.reflect.Value.wp_IsNil.1 _ (t := go.PointerType T) (e := T) p (by simp only; rfl) (by simp only; rfl) rfl)
  by_cases hp : p = null
  · simp only [hp, decide_true, if_true]
    wp_auto
    iapply HΦ
    itrivial
  · simp only [hp, decide_false, if_false]
    wp_auto
    iapply HΦ
    itrivial

theorem typedNilString.wp_proof_int :
    typedNilString.spec_int (GF := GF) (hG := hG) := by
  intro n
  wp_start
  wp_auto
  have h1 : go.kindOf go.int = some 2 := by
    simp [go.kindOf, List.find?, go.bool, go.int]
  haveI : go.NotLayoutModelled go.int := ⟨by decide⟩
  have h3 : go.isInterfaceType go.int = false := by rfl
  wp_apply (_root_.Perennial.reflect.wp_ValueOf.2.1 (V := w64) (t := go.int) (u := go.int) 2 1 n h1
    (_root_.Perennial.reflect.directIfaceN_of_kind (u := go.int) (k := 2) 0 h1 (by omega) (by omega)) h3) as %q Hq
  wp_method_call
  wp_pures
  wp_load
  wp_pures
  wp_apply _root_.Perennial.reflect.Value.wp_Kind
  iapply HΦ
  itrivial

end proof

end specreq_reflect
end EtcdGrove
end Perennial
