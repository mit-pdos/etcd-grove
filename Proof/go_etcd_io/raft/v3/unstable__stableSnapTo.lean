/- (D22 S-d1, 2026-10-20) Lean-first. -/
module

public import Spec.go_etcd_io.raft.v3.unstable__stableSnapTo
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex

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

/-- The test reads the pending snapshot's index through the getters (`ownSnap`'s snapshot,
whose index is the state's); a hit stores `nil` and `false`. -/
theorem unstable.stableSnapTo.wp_proof
    (wp_Snapshot_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_SnapshotMetadata_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG)) :
    unstable.stableSnapTo.spec (GF := GF) (hG := hG) := by
  intro u us i
  wp_start as H
  iNamed H
  open_unstable
  wp_auto
  rcases snap_some_or_none us.snap with ⟨sid, Hs⟩ | Hs
  · ihave Hsn := Hsnap
    icases ownSnap_of_eq_some Hs $$ Hsn with ⟨%sv, #Hsv, %Hid⟩
    ihave %Hnn : ⌜uv.snapshot' ≠ null⌝ $$ [Hsv]
    · iunfold ownSnapM at Hsv; iNamed Hsv; ipureintro; exact Hnn
    simp only [Hnn, _root_.decide_false]
    wp_auto
    wp_apply wp_Snapshot_GetMetadata.1 _ DFrac.discard sv $$ [$Hsv] as %pm ⟨Hm, -⟩
    wp_apply wp_SnapshotMetadata_GetIndex pm DFrac.discard _ $$ [$Hm] as -
    by_cases Hi : sv.Metadata'.Index' = i
    · rw [decide_eq_true Hi]
      wp_auto
      iapply HΦ
      have Hh : snapHit us.snap i = true := by
        rw [Hs]; simp only [snapHit, decide_eq_true_eq]; rw [← Hid.1]; exact Hi
      unfold unstableSnapTo
      rw [if_pos Hh]
      iapply ownUnstable_intro $$ Hu Hents_cap Hents
      · iapply (ownSnap_None _).2; ipureintro; rfl
      · iapply pendKsn_none
      · iexact Hlogger
      · ipureintro; exact ⟨rfl, rfl, rfl⟩
    · rw [decide_eq_false Hi]
      wp_auto
      iapply HΦ
      have Hh : snapHit us.snap i = false := by
        rw [Hs]; simp only [snapHit, decide_eq_false_iff_not]; rw [← Hid.1]; exact Hi
      unfold unstableSnapTo
      rw [if_neg (by rw [Hh]; simp)]
      close_unstable
  · ihave %Hn := ownSnap_of_eq_none Hs $$ Hsnap
    simp only [decide_eq_true Hn]
    wp_auto
    iapply HΦ
    have Hh : snapHit us.snap i = false := by rw [Hs]; rfl
    unfold unstableSnapTo
    rw [if_neg (by rw [Hh]; simp)]
    close_unstable

end proof

end EtcdGrove
end Perennial
