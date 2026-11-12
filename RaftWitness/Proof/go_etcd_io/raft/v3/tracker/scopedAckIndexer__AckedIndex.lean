/-
Proof of `Spec/go_etcd_io/raft/v3/tracker/scopedAckIndexer__AckedIndex.lean`.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.tracker.scopedAckIndexer__AckedIndex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The scope's lookup (a nil scope holds nothing), then the inner indexer for an id in it. -/
theorem tracker.scopedAckIndexer.AckedIndex.wp_proof :
    tracker.scopedAckIndexer.AckedIndex.spec (GF := GF) (hG := hG) := by
  intro s P acked S id
  wp_start as ⟨#Hi, #Hs, HP⟩
  wp_auto
  iunfold ownScope at Hs
  icases Hs with (%Hnil | ⟨%ids, %Hids, #Hmap⟩)
  · obtain ⟨Hn, HS⟩ := Hnil
    rw [Hn]
    wp_auto
    have : scopedAcked S acked id = none := by
      unfold scopedAcked; rw [HS, if_neg (GMap.not_elem_of_empty _)]
    rw [this]
    simp only [Option.getD_none, Option.isSome_none]
    iapply HΦ
    iexact HP
  · wp_apply wp_map_lookup2 _ _ _ ids id $$ [$Hmap] as -
    by_cases hin : id ∈ S
    · have hk : (ids !! id).isSome = true := by
        have h : id ∈ domSet ids := by rw [Hids]; exact hin
        exact (GMap.elem_of_dom' ids id).1 h
      rw [hk]
      wp_auto
      iNamed Hi
      rw [Hlok]
      ihave Hack := HAckedIndex $$ %id
      wp_bind (App (Val #(methods _ _ _)) (Val #id))
      iapply Hack $$ HP
      imodintro
      iintro HP
      wp_auto
      have : scopedAcked S acked id = acked id := by unfold scopedAcked; simp [hin]
      rw [this]
      iapply HΦ
      iexact HP
    · have hk : (ids !! id).isSome = false := by
        cases h : (ids !! id).isSome with
        | false => rfl
        | true => exact absurd (by rw [← Hids]; exact (GMap.elem_of_dom' ids id).2 h) hin
      rw [hk]
      wp_auto
      have : scopedAcked S acked id = none := by unfold scopedAcked; simp [hin]
      rw [this]
      simp only [Option.getD_none, Option.isSome_none]
      iapply HΦ
      iexact HP

end proof

end EtcdGrove
end Perennial
