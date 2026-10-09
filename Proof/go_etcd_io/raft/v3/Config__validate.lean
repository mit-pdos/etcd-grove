/-
Port of election_proof/proof_Config__validate.v.
-/
module

public import Spec.go_etcd_io.raft.v3.Config__validate
public import Spec.go_etcd_io.raft.v3.IsLocalMsgTarget

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

theorem Config.validate.wp_proof
    (wp_IsLocalMsgTarget : IsLocalMsgTarget.spec (GF := GF) (hG := hG)) :
    Config.validate.spec (GF := GF) (hG := hG) := by
  intro c cv Hvalid
  wp_start as Hc
  obtain ⟨Hid, Hid1, Hid2, Hticks, Hst, Hinfl, Hib, Hlog, Hro⟩ := Hvalid
  wp_auto
  rw [decide_eq_false Hid]
  wp_auto
  wp_apply wp_IsLocalMsgTarget
  rw [decide_eq_false (by rintro (h | h) <;> contradiction)]
  wp_auto
  rw [decide_eq_false (by word)]
  wp_auto
  rw [decide_eq_false (by word)]
  wp_auto
  obtain ⟨sv, Hsv⟩ : ∃ sv, cv.Storage' = GoInterface.ok sv := by
    cases h : cv.Storage' <;> simp_all
  rw [Hsv]
  have Hcq : cv.ReadOnlyOption' = W64 1 → cv.CheckQuorum' = true := by
    intro h; rcases Hro with h' | h'
    · exfalso; rw [h] at h'; word
    · exact h'
  obtain ⟨lv, Hlv⟩ : ∃ lv, cv.Logger' = GoInterface.ok lv := by
    cases h : cv.Logger' <;> simp_all
  wp_auto
  -- the three defaults and the two remaining checks
  wp_if_destruct
  all_goals wp_if_destruct
  all_goals rw [decide_eq_false (by word)]
  all_goals wp_auto
  all_goals wp_if_destruct
  all_goals try (rw [decide_eq_false (by rcases Hib with h | h <;> first | contradiction | word)]; wp_auto)
  all_goals rw [Hlv]
  all_goals wp_auto
  all_goals wp_if_destruct
  all_goals try (rw [Hcq Hif]; wp_auto)
  all_goals iapply HΦ
  all_goals iframe Hc
  all_goals ipureintro
  all_goals
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, ?_, ?_, rfl⟩ <;>
      first | rfl | exact Hlv.symm | exact (Hcq Hif).symm | (split <;> simp_all)

end proof

end EtcdGrove
end Perennial
