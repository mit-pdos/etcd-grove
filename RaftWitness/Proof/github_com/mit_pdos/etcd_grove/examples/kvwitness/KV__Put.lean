/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvwitness/KV__Put.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.KV__Put
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

theorem KV.Put.wp_proof (wp_do : kvwitness.KV.do.spec (GF := GF) (hG := hG)) :
    KV.Put.spec (GF := GF) (hG := hG) := by
  intro γr γp r key val Ψ Hkey Hval
  wp_start as ⟨#Hreg, Hau⟩
  wp_auto
  have h : ∀ x, kvNext (W8 1) key val x = kvUpd x key val := fun x => ite_eq_left rfl
  wp_apply wp_do γr γp r (W8 1) key val (fun _ => Ψ) Hkey Hval $$ [$Hreg Hau] as %res HΨ
  · simp only [h]
    iexact Hau
  iapply HΦ $$ HΨ

end proof

end kvwitness
end EtcdGrove
end Perennial
