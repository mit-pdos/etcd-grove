/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/register/Register__Get.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.register.Register__Get
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.Register__do

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

theorem Register.Get.wp_proof (wp_do : register.Register.do.spec (GF := GF) (hG := hG)) :
    Register.Get.spec (GF := GF) (hG := hG) := by
  intro γr γp r Ψ
  wp_start as ⟨#Hreg, Hcr, Hau⟩
  wp_auto
  have h : ∀ x, opNext (W8 2) ([] : List w8) x = x := fun x => ite_eq_right (by decide)
  wp_apply wp_do γr γp r (W8 2) [] Ψ (by simp) $$ [$Hreg $Hcr Hau] as %res HΨ
  · simp only [h]
    iexact Hau
  iapply HΦ $$ HΨ

end proof

end register
end EtcdGrove
end Perennial
