/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/Cluster__pick.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__pick
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.below
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
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem Cluster.pick.wp_proof (wp_below : below.spec (GF := GF) (hG := hG)) :
    Cluster.pick.spec (GF := GF) (hG := hG) := by
  intro c γ
  wp_start as #Hc
  ihave #Hc' := Hc
  iunfold antCluster at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, #Hcfg, %Hcok, %Hmode, #Hr, #Hrec, #Hro, #Hnodes, #Hstop, #Hbc,
    #Hnj, #Hmu, #Hinv, %Hfits, #Hpm⟩
  iunfold clusterRO at Hro
  icases Hro with ⟨%nsl, %ivl, #Hn, #Hns, %HN, #Hm, #Hiv, #Hivs⟩
  ihave %Hl := ownSlice_len $$ Hns
  ihave Hm' := Hm
  iStructNamed Hm'
  have hpos : 0 < uint.Z γ.mode.Nodes' := by
    rcases Hmode.1.1 with h | h <;> rw [h] <;> decide
  wp_auto
  wp_apply wp_below γ.mode.Nodes' hpos as %k %hk
  try wp_auto
  have hlen : uint.nat γ.mode.Nodes' = sint.nat nsl.len := by rw [← HN, Hl.1]
  have hk' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z nsl.len := by
    have : uint.Z γ.mode.Nodes' ≤ 5 := by rcases Hmode.1.1 with h | h <;> rw [h] <;> decide
    constructor <;> word
  simp only [hk', and_self, ↓reduceIte]
  have hkN : uint.nat k < γ.R.N := by rw [Hmode.2.1]; word
  obtain ⟨z, hz⟩ : ∃ z, ns[uint.nat k]? = some z := ⟨_, List.getElem?_eq_getElem (by rw [HN]; word)⟩
  wp_apply wp_load_slice_index nsl (sint.Z k) ns DFrac.discard z hk'.1 $$ [Hns] as -
  · iframe Hns; ipureintro; rw [show (sint.Z k).toNat = uint.nat k by word]; exact hz
  try wp_auto
  iapply HΦ
  iexists ⟨uint.nat k, hkN⟩
  ihave H := nodeRO_lookup c γ ns ⟨uint.nat k, hkN⟩ $$ Hnodes
  rw [show ns[uint.nat k]! = z by simp [List.getElem!_eq_getElem?_getD, hz]] at *
  iexact H

end proof

end AntHarness
end EtcdGrove
end Perennial
