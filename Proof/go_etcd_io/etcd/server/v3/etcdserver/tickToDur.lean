/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/tickToDur.lean`: `fmt.Sprintf("%v", d)` of a
`time.Duration` (Perennial's `fmt` model: `%v` calls the argument's `String()`, Perennial's
`time.Duration.String`, some string). Lean-first; prove-ps2-srv (2026-11-22).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.tickToDur
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.time.Link

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
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem tickToDur.wp_proof : tickToDur.spec (GF := GF) (hG := hG) := by
  intro ticks tickMs
  wp_start as -
  ihave #Pfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_slice_literal (V := GoInterface)
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  have hE := go.method_set_is (t := _root_.Perennial.time.Duration.ty) go!"Error"
  have hF := go.method_set_is (t := _root_.Perennial.time.Duration.ty) go!"Format"
  have hS := go.method_set_is (t := _root_.Perennial.time.Duration.ty) go!"String"
  have hC := go.method_set_is (t := _root_.Perennial.time.Duration.ty) go!"CanInterface"
  simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at hE hF hS hC
  wp_apply (_root_.Perennial.fmt.wp_Sprintf _ _ _ (DFrac.own 1)) $$ [$Pfmt $Hsl] as %s -
  · iapply (_root_.Perennial.fmt.argsOk_intro (ds := [⟨W8 118, false⟩]) (by rfl))
    unfold _root_.Perennial.fmt.argsOkAt _root_.Perennial.fmt.argsOkAt
    isplitl
    · unfold _root_.Perennial.fmt.argOkAt
      iright; iright; ileft
      isplitr
      · ipureintro; refine ⟨by decide, rfl, fun h => by cases h⟩
      unfold _root_.Perennial.fmt.argOk
      iright; iright
      isplitr
      · unfold _root_.Perennial.fmt.stringMethodSpec
        imodintro
        iintro %Φ' HΦ'
        wp_apply time.Duration.wp_String as %s' -
        iapply HΦ'
      · ipureintro; exact ⟨hF, hE, hS, hC⟩
    · itrivial
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
