module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalNode__color

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3.adt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

theorem adt.intervalNode.color.wp_proof : adt.intervalNode.color.spec (GF := GF) (hG := hG) := by
  intro x s c dq
  wp_start as Hc
  wp_auto
  unfold adt.colorAt
  icases Hc with (⟨%Hx, %Hcb⟩ | ⟨%Hx, Hc⟩)
  · subst Hx Hcb
    rw [_root_.decide_eq_true rfl]
    wp_auto
    rw [show black = #(adt.colorW .black) from rfl]
    iapply HΦ
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  · rw [_root_.decide_eq_false Hx]
    wp_auto
    iapply HΦ
    iright; iframe; ipureintro; exact Hx

end proof

end EtcdGrove
end Perennial
