/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/tracecheck/Cluster__replica.lean`. Lean-first
(no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Cluster__replica

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

theorem Cluster.replica.wp_proof : Cluster.replica.spec (GF := GF) (hG := hG) := by
  intro c rs id
  wp_start as #Hr
  iunfold replicasRO at Hr
  icases Hr with ⟨%sl, #Hf, #Hsl⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  have Hlz : uint.Z sl.len = sint.Z sl.len := by word
  wp_if_destruct
  · try wp_auto
    iapply HΦ
    ipureintro
    unfold replicaOf
    rw [if_pos (.inl (by decide))]
  · wp_if_destruct
    · try wp_auto
      iapply HΦ
      ipureintro
      unfold replicaOf
      rw [if_pos (.inr (by have := Hlen.1; word))]
    · have Hid0 : uint.Z id ≠ 0 := by intro h; apply Hif; word
      have Hk : sint.Z (id - W64 1) = uint.Z id - 1 := by word
      have Hbnd : 0 ≤ sint.Z (id - W64 1) ∧ sint.Z (id - W64 1) < sint.Z sl.len := by
        constructor <;> word
      have Hkn : uint.nat id - 1 < rs.length := by have := Hlen.1; word
      obtain ⟨r0, Hr0⟩ : ∃ r0, rs[uint.nat id - 1]? = some r0 := ⟨_, List.getElem?_eq_getElem Hkn⟩
      have Hr0' : rs[sint.nat (id - W64 1)]? = some r0 := by
        rw [show sint.nat (id - W64 1) = uint.nat id - 1 by word]; exact Hr0
      simp only [Hbnd, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index _ (sint.Z (id - W64 1)) _ _ r0 Hbnd.1 $$ [Hsl] as Hsl'
      · iframe Hsl; ipureintro; exact Hr0'
      try wp_auto
      iapply HΦ
      ipureintro
      unfold replicaOf
      have Hn : ¬ (uint.Z id = 0 ∨ (rs.length : Int) < uint.Z id) := by
        rintro (h | h)
        · exact Hid0 h
        · have := Hlen.1; word
      rw [if_neg Hn, Hr0]
      rfl

end proof

end TraceCheck
end EtcdGrove
end Perennial
