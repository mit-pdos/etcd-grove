/- (D22 S-d1b, 2026-10-21) Lean-first. -/
module

public import Spec.go_etcd_io.raft.v3.raftLog__stableSnapTo
public import Spec.go_etcd_io.raft.v3.unstable__stableSnapTo

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

/-- The `unstable` field is lent to `unstable.stableSnapTo`. On a hit the `sapp` window's
storage relation (`snapV`: the storage at the snapshot, the stable part after it) is the one
with no snapshot pending, and `SappOk` gives what the quiet facts need: nothing unpersisted. -/
theorem raftLog.stableSnapTo.wp_proof
    (wp_unstable_stableSnapTo : unstable.stableSnapTo.spec (GF := GF) (hG := hG)) :
    raftLog.stableSnapTo.spec (GF := GF) (hG := hG) := by
  intro l ls i Hiff
  wp_start as H
  iNamed H
  iNamed Hlog
  wp_auto
  lend_unstable
  wp_apply wp_unstable_stableSnapTo _ (unstableOf lv ls) i $$ [$Hun] as Hun
  iclear Husnap Hpksn Hu_logger
  icases ownUnstable_reopen _ _ _ $$ Hlback Hun
    with ⟨%uv', Hl, Huents_cap, Huents, #Husnap, #Hpksn, #Hu_logger, %Huoff, %Hip', %Hsip'⟩
  clear Hip Hsip
  iapply HΦ
  unfold logStableSnap
  by_cases Hh : snapHit ls.snap i = true
  · -- the hit: the storage, at the snapshot, is the boundary
    have Hsa := Hiff.1 Hh
    obtain ⟨-, -, Hlnt, Hunp, -⟩ := Hsappi Hsa
    have Hus : unstableSnapTo (unstableOf lv ls) i = { unstableOf lv ls with snap := none, sip := false } := by
      simp only [unstableSnapTo, unstableOf]; rw [ite_eq_left_iff.2 (fun h => absurd Hh h)]
    rw [ite_eq_left_iff.2 (fun h => absurd Hh h)]
    rw [Hus] at Huoff Hip' Hsip'
    simp only [Hus]
    reseal_raftLogW
    all_goals first
      | exact (snapV_sapp Hsa) ▸ Hstore
      | (intro _ h; cases h; done)
      | exact fun _ => Hssnap (snapV_sapp Hsa)
      | exact fun _ => Hpersist (snapV_sapp Hsa)
      | (intro _; rw [Huoff]; exact Hpersist (snapV_sapp Hsa))
      | (intro _; rfl)
      | exact ⟨Hpend.1, fun _ e0 He0 => by simp [Hunp] at He0⟩
      | exact Hfl
      | exact ⟨Hfl.1, Hfl.2.1, Hfl.2.2.1, Hfl.2.2.2.1, fun h => absurd rfl h, fun h => absurd rfl h⟩
      | exact Hsksn
      | (intro h; simp only at h; rw [Hlnt] at h; cases h; done)
      | (intro h; simp at h; done)
      | exact ⟨(fun h => by simp at h), (fun h => by simp at h)⟩
      | (simp only at Hip' ⊢; exact Hip')
      | (simp only at Hsip' ⊢; exact Hsip')
      | (rw [Huoff]; simp only [unstableOf] at Hoff; exact Hoffset)
      | (rw [Huoff]; exact Hipb)
      | skip
  · -- a miss: nothing changes
    have Hus : unstableSnapTo (unstableOf lv ls) i = unstableOf lv ls := by
      simp only [unstableSnapTo]; rw [ite_eq_right_iff.2 (fun h => absurd h Hh)]
    rw [ite_eq_right_iff.2 (fun h => absurd h Hh)]
    rw [Hus] at Huoff Hip' Hsip'
    simp only [Hus]
    reseal_raftLogW

end proof

end EtcdGrove
end Perennial
