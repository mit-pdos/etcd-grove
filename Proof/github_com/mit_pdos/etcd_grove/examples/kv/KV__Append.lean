/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/KV__Append.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.KV__Append
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.KV__do

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

theorem KV.Append.wp_proof (wp_do : kv.KV.do.spec (GF := GF) (hG := hG)) :
    KV.Append.spec (GF := GF) (hG := hG) := by
  intro γr γp r key val Ψ Hkey Hval
  wp_start as ⟨#Hreg, Hau⟩
  wp_auto
  have h : ∀ x, kvNext (W8 4) key val x = kvUpd x key (x key ++ val) := fun x => by
    unfold kvNext; rw [ite_eq_right (by decide), ite_eq_left (by rfl)]
  wp_apply wp_do γr γp r (W8 4) key val (fun _ => Ψ) Hkey Hval $$ [$Hreg Hau] as %res HΨ
  · simp only [h]
    iexact Hau
  iapply HΦ $$ HΨ

end proof

end kv
end EtcdGrove
end Perennial
