/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/register/Register__Put.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.register.Register__Put
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

theorem Register.Put.wp_proof (wp_do : register.Register.do.spec (GF := GF) (hG := hG)) :
    Register.Put.spec (GF := GF) (hG := hG) := by
  intro γr γp r val Ψ Hval
  wp_start as ⟨#Hreg, Hcr, Hau⟩
  wp_auto
  have h : ∀ x, opNext (W8 1) val x = val := fun x => if_pos rfl
  wp_apply wp_do γr γp r (W8 1) val (fun _ => Ψ) Hval $$ [$Hreg $Hcr Hau] as %res HΨ
  · simp only [h]
    iexact Hau
  iapply HΦ $$ HΨ

end proof

end register
end EtcdGrove
end Perennial
