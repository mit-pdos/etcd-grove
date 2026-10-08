/-
Port of election_proof/proof_Progress__SentEntries.v.
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.Progress__SentEntries
public import Spec.go_etcd_io.raft.v3.tracker.Inflights__Add
public import Spec.go_etcd_io.raft.v3.tracker.Inflights__Full

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

theorem tracker.Progress.SentEntries.wp_proof
    (wp_Inflights_Add : tracker.Inflights.Add.spec (GF := GF) (hG := hG))
    (wp_Inflights_Full : tracker.Inflights.Full.spec (GF := GF) (hG := hG)) :
    tracker.Progress.SentEntries.spec (GF := GF) (hG := hG) := by
  intro pr p entries bytes Hnotsnap Hnotfull
  wp_start as H
  iNamed H
  unfold ownProgress
  iNamed Hpr
  have Habs0 := (progressAbs_Some _ _ _).1 Habs
  obtain ⟨Hl, Hst, -⟩ := Habs0
  wp_auto
  -- the record's state is Probe or Replicate -- the premise excludes
  -- Snapshot -- so the `panic` arm is unreachable.
  rw [Hst]
  cases Hps : p.state with
  | snapshot => exact absurd Hps Hnotsnap
  | probe =>
    -- StateProbe: the switch falls through to the second arm
    rw [decide_eq_false (by simp [prstateW64])]
    rw [show tracker.StateProbe = #(prstateW64 .probe) from rfl]
    wp_auto
    wp_if_destruct
    · have Hgt : 0 < sint.Z entries := by word
      iapply HΦ
      iexists _
      iframe Hpv
      simp only [progressSentEntries, Hps, Hgt, ↓reduceIte]
      iframe Hinfl
      ipureintro
      rw [progressAbs_Some] at Habs ⊢
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := Habs
      exact ⟨h1, by rw [h2, Hps], h3, h4, h5, h6, h7, rfl, h9⟩
    · have Hgt : ¬ 0 < sint.Z entries := by word
      iapply HΦ
      iexists _
      iframe Hpv
      simp only [progressSentEntries, Hps, Hgt, ↓reduceIte]
      iframe Hinfl
      ipureintro
      exact Habs
  | replicate =>
    rw [decide_eq_true (by simp [prstateW64])]
    wp_auto
    wp_if_destruct
    · -- entries > 0: `Next` moves and the window records the batch. The
      -- `Add` is legal because the caller promised the window is not
      -- full -- see the spec.
      have Hgt : 0 < sint.Z entries := by word
      wp_apply wp_Inflights_Add _ _ _ _ (Hnotfull Hps Hgt) $$ [$Hinfl] as Hinfl
      wp_apply wp_Inflights_Full $$ [$Hinfl] as Hinfl
      iapply HΦ
      iexists _
      iframe Hpv
      simp only [progressSentEntries, Hps, Hgt, ↓reduceIte]
      iframe Hinfl
      ipureintro
      rw [progressAbs_Some] at Habs ⊢
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := Habs
      exact ⟨h1, by rw [h2, Hps], h3, by simp only [h4], h5, h6, h7, rfl, rfl⟩
    · have Hgt : ¬ 0 < sint.Z entries := by word
      wp_apply wp_Inflights_Full $$ [$Hinfl] as Hinfl
      iapply HΦ
      iexists _
      iframe Hpv
      simp only [progressSentEntries, Hps, Hgt, ↓reduceIte]
      iframe Hinfl
      ipureintro
      rw [progressAbs_Some] at Habs ⊢
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := Habs
      exact ⟨h1, by rw [h2, Hps], h3, h4, h5, h6, h7, rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
