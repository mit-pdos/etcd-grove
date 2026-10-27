/-
Port of election_proof/proof_raftLog__appliedTo.v.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raftLog__appliedTo

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
theorem raftLog.appliedTo.wp_proof : raftLog.appliedTo.spec (GF := GF) (hG := hG) := by
  intro l ls i size Hi Hipo
  wp_start as Hlog
  iNamed Hlog
  wp_auto
  rw [decide_eq_false (by rw [Hcm]; omega)]
  wp_auto
  rw [decide_eq_false (by rw [Hap]; omega)]
  wp_auto
  -- `max(l.applying, i)`
  wp_func_call
  wp_call
  wp_if_destruct <;> wp_if_destruct
  all_goals
    iapply HΦ
    reseal_raftLog
  all_goals
    simp only [Hcm, Hap, Hapg, Hasz, Hamx] at *
    first
      | rfl
      | omega
      | (intro Hn; have := Hpapplied Hn; omega)
      | (unfold w64Max; split <;> first | rfl | omega)
      | (split <;> first | rfl | omega)
      | (intro Hpz; simp only [decide_eq_false_iff_not] at Hpz; split <;> word)
      | (refine ⟨Hfl.1, ?_, Hfl.2.2.1, Hfl.2.2.2⟩; have := Hfl.2.1; simp only; omega)
      | (refine ⟨Hfl.1, ?_, Hfl.2.2.1, Hfl.2.2.2⟩; have := Hfl.2.1; simp only
         unfold w64Max; split <;> omega)
      | (refine ⟨Hfl.1, ?_, ?_, Hfl.2.2.2⟩
         · have := Hfl.2.1; simp only; unfold w64Max; split <;> omega
         · intro Hs; have := Hfl.2.2.1 Hs; simp only; unfold w64Max
           split <;> first | omega | (rename_i hnl; rcases Int.lt_or_eq_of_le (Int.not_lt.1 hnl) with h | h <;> first | exact Hipo h Hs | (rw [← h]; exact this)))

end proof

end EtcdGrove
end Perennial
