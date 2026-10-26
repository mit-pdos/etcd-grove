/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/NewStorage.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.NewStorage
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Lemmas

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

theorem NewStorage.wp_proof
    (wp_NewMemoryStorage : NewMemoryStorage.spec (GF := GF) (hG := hG)) :
    NewStorage.spec (GF := GF) (hG := hG) := by
  intro vsl voters
  wp_start as ⟨#Hreg, #Hv⟩
  wp_auto
  wp_apply wp_NewMemoryStorage (2 ^ 64) (by simp only [memStorEmpty]; word) as %ms %γs ⟨%Hcap, Hown, -, Htok, Hca⟩
  wp_alloc s as Hs
  iStructNamed Hs
  imod kvStor_register s ms γs ⊤ CoPset.subseteq_top $$ Hreg MemoryStorage with #Hrec
  ipersist voters
  wp_auto
  iapply HΦ
  iexists ms, γs
  iframe Hrec voters Hown Hca Htok
  ipureintro; exact Hcap

end proof

end kv
end EtcdGrove
end Perennial
