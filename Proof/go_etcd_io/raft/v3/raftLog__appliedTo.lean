/-
Port of election_proof/proof_raftLog__appliedTo.v.
-/
module

public import Spec.go_etcd_io.raft.v3.raftLog__appliedTo

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
theorem raftLog.appliedTo.wp_proof : raftLog.appliedTo.spec (GF := GF) (hG := hG) := by
  intro l ls i size Hi Hipo
  wp_start as Hlog
  iNamed Hlog
  wp_auto
  rw [decide_eq_false (show ¬ (uint.Z lv.committed' < uint.Z i) by rw [Hcm]; omega)]
  wp_auto
  rw [decide_eq_false (show ¬ (uint.Z i < uint.Z lv.applied') by rw [Hap]; omega)]
  wp_auto
  -- `max(l.applying, i)`
  wp_func_call
  wp_call
  wp_if_destruct <;> wp_if_destruct
  all_goals
    iapply HΦ
    reseal_raftLogW
  all_goals
    simp only [Hcm, Hap, Hapg, Hasz, Hamx] at *
    first
      | rfl
      | omega
      | (intro Hn; have := Hpapplied Hn; omega)
      -- (D22 S-d1b) `appliedSnap`'s window ends at the boundary
      | (intro Hn Ha
         rcases Bool.eq_false_or_eq_true ls.aps with Ha0 | Ha0
         · rw [Ha0] at Ha; simp only [Bool.true_and, decide_eq_false_iff_not] at Ha; omega
         · have := Hpapplied Hn Ha0; omega)
      | (unfold w64Max; split <;> first | rfl | omega)
      | (split <;> first | rfl | omega)
      | (intro Hpz; simp only [decide_eq_false_iff_not] at Hpz; split <;> word)
      | (refine ⟨Hfl.1, ?_, Hfl.2.2.1, Hfl.2.2.2⟩; have := Hfl.2.1; simp only; omega)
      | (refine ⟨Hfl.1, ?_, Hfl.2.2.1, Hfl.2.2.2⟩; have := Hfl.2.1; simp only
         unfold w64Max; split <;> omega)
      | (refine ⟨Hfl.1, ?_, ?_, Hfl.2.2.2⟩
         · have := Hfl.2.1; simp only; unfold w64Max; split <;> omega
         · have := Hfl.2.2.1; simp only; unfold w64Max
           split <;> first | omega | (rename_i hnl; rcases Int.lt_or_eq_of_le (Int.not_lt.1 hnl) with h | h <;> first | exact Hipo h | (rw [← h]; exact this)))

end proof

end EtcdGrove
end Perennial
