/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/Cluster__transferer.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__transferer
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.below
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__running
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__pick
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__deliver
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessPersist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem Cluster.transferer.wp_proof (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_running : Cluster.running.spec (GF := GF) (hG := hG))
    (wp_pick : Cluster.pick.spec (GF := GF) (hG := hG))
    (wp_deliver : Cluster.deliver.spec (GF := GF) (hG := hG)) :
    Cluster.transferer.spec (GF := GF) (hG := hG) := by
  intro c γ
  wp_start as ⟨#Hc, Htok, %Htr⟩
  ihave #Hc' := Hc
  iunfold antCluster at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, #Hcfg, %Hcok, %Hmode, #Hr, #Hrec, #Hro, #Hnodes, #Hstop, #Hbc,
    #Hnj, #Hmu, #Hinv, %Hfits, #Hpm⟩
  ihave Hcf := Hcfg
  iStructNamed Hcf
  iunfold clusterRO at Hro
  icases Hro with ⟨%nsl, %ivl, #Hn, #Hns, %HN, #Hm, #Hiv, #Hivs⟩
  ihave Hm' := Hm
  iStructNamed Hm'
  have hpos : 0 < uint.Z γ.mode.Nodes' := by
    rcases Hmode.1.1 with h | h <;> rw [h] <;> decide
  have hle : uint.Z γ.mode.Nodes' ≤ 5 := by
    rcases Hmode.1.1 with h | h <;> rw [h] <;> decide
  wp_auto
  ihave IH : iprop("c" ∷ c_ptr ↦ c) $$ [c]
  · iframe
  wp_for IH
  wp_apply wp_running c γ $$ [$Hpkg $Hc] as %b -
  wp_if_destruct
  · try wp_auto
    wp_apply wp_pick c γ $$ [$Hpkg $Hc] as %n ⟨%j, #Hn⟩
    try wp_auto
    wp_apply wp_below γ.mode.Nodes' hpos as %t %ht
    try wp_auto
    wp_apply wp_deliver c γ n j _ $$ [$Hpkg $Hc $Hn]
    · iunfold inputOk
      iright; iright; iright; ileft
      ipureintro
      have htN : uint.nat t < γ.R.N := by rw [Hmode.2.1]; word
      refine ⟨rfl, Htr, ⟨uint.nat t, htN⟩, ?_⟩
      simp only [AntSim.nodeId]
      word
    try wp_auto
    wp_for_post
    iframe
  · wp_if_destruct
    · try wp_auto
      iapply HΦ
      iframe
    · exfalso; cases b <;> simp_all

end proof

end AntHarness
end EtcdGrove
end Perennial
