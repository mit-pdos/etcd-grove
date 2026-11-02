/-
kvreconf's proof (the same Go text), ported. Proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Cluster__Get.lean`. Lean-first (no
Rocq counterpart): `do` of a `Get` (`kvNext opGetB` leaves the store).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__Get
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.DefsLaws
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__do

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open kvreconf (kvNext opPutB)
open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

theorem Cluster.Get.wp_proof (wp_do : Cluster.do.spec (GF := GF) (hG := hG)) :
    Cluster.Get.spec (GF := GF) (hG := hG) := by
  intro γ vs dir c key Ψ Hkey
  wp_start as ⟨#Hcc, Hau⟩
  try wp_auto
  have h : ∀ x, kvNext (W8 2) key ([] : List w8) x = x := fun x => by
    unfold kvNext opPutB; rw [ite_eq_right (by decide)]
  wp_apply wp_do γ vs dir c (W8 2) key [] Ψ Hkey (by simp) $$ [$Hcc Hau] as %res HΨ
  · simp only [h]
    iexact Hau
  try wp_auto
  iapply HΦ $$ HΨ

end proof

end kvdurable
end EtcdGrove
end Perennial
