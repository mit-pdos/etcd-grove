/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvwitness/KV__Get.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.KV__Get
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.KV__do

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]
variable [KVStor GF]

theorem KV.Get.wp_proof (wp_do : kvwitness.KV.do.spec (GF := GF) (hG := hG)) :
    KV.Get.spec (GF := GF) (hG := hG) := by
  intro γr γp r key Ψ Hkey
  wp_start as ⟨#Hreg, Hau⟩
  wp_auto
  have h : ∀ x, kvNext (W8 2) key ([] : List w8) x = x := fun x => by
    unfold kvNext; rw [ite_eq_right (by decide), ite_eq_right (by decide)]
  wp_apply wp_do γr γp r (W8 2) key [] Ψ Hkey (by simp) $$ [$Hreg Hau] as %res HΨ
  · simp only [h]
    iexact Hau
  iapply HΦ $$ HΨ

end proof

end kvwitness
end EtcdGrove
end Perennial
