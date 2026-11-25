/-
Lean-first (no Rocq counterpart). #33 S4: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/Cluster__node.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__node

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

theorem Cluster.node.wp_proof : Cluster.node.spec (GF := GF) (hG := hG) := by
  intro c ns N id
  wp_start as #Hc
  iunfold clusterRO at Hc
  icases Hc with ⟨%nsl, #Hn, #Hns, #HN⟩
  ihave %Hl := ownSlice_len $$ Hns
  wp_auto
  wp_if_destruct
  · rw [show nodeOf ns (W64 0) = null by simp [nodeOf]]
    iapply HΦ
    ipureintro; trivial
  have hlen : uint.Z nsl.len = sint.Z nsl.len := by word
  wp_if_destruct
  · rw [show nodeOf ns id = null by
      simp only [nodeOf]; rw [if_pos (Or.inr (by rw [Hl.1]; word))]]
    iapply HΦ
    ipureintro; trivial
  have hid : 1 ≤ uint.Z id := by
    have : uint.Z id ≠ 0 := fun h => Hif (by word)
    word
  have hi : sint.Z (id - W64 1) = uint.Z id - 1 := by word
  have hz' : (uint.Z id - 1).toNat = id.toNat - 1 := by word
  obtain ⟨z, Hz⟩ : ∃ z, ns[id.toNat - 1]? = some z :=
    ⟨_, List.getElem?_eq_getElem (by rw [Hl.1]; word)⟩
  try wp_auto
  rw [if_pos (show 0 ≤ sint.Z (id - W64 1) ∧ sint.Z (id - W64 1) < sint.Z nsl.len by omega)]
  wp_apply wp_load_slice_index nsl (sint.Z (id - W64 1)) ns DFrac.discard z (by omega) $$ [Hns] as -
  · iframe Hns; ipureintro; rw [hi, hz']; exact Hz
  try wp_auto
  have hid0 : ¬ id = W64 0 := by assumption
  rw [show nodeOf ns id = z by
    simp only [nodeOf]
    rw [if_neg (by rw [not_or]; exact ⟨hid0, by rw [Hl.1]; word⟩)]
    simp [List.getElem!_eq_getElem?_getD, Hz]]
  iapply HΦ
  ipureintro; trivial

end proof

end AntHarness
end EtcdGrove
end Perennial
