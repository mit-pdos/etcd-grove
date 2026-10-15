/-
Proof of `Raft37/Spec/go_etcd_io/raft/v3/raftpb/EnsureSnapshotMetadata.lean`.
-/
module

public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.EnsureSnapshotMetadata
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.EnsureConfState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A metadata at `m` whose fields hold a conf state set by `EnsureConfState` and two cells
holding `md`'s is an owned metadata holding `md`. -/
private theorem smPts_intro (m pc pi pt : Loc) (md : SnapshotMetadataM) (uf : List w8)
    (Hnn : m ≠ null) :
    (m.[raftpb.SnapshotMetadata, go!"ConfState"] ↦ pc ∗ csPts pc (DFrac.own 1) md.ConfState' true ∗
      m.[raftpb.SnapshotMetadata, go!"Index"] ↦ pi ∗ cellRO pi md.Index' ∗
      m.[raftpb.SnapshotMetadata, go!"Term"] ↦ pt ∗ cellRO pt md.Term' ∗
      pbMsg raftpb.SnapshotMetadata m uf : IProp GF) ⊢ smPts m (DFrac.own 1) md := by
  iintro ⟨HC, Hcs, HI, #cI, HT, #cT, #Hpb⟩
  ihave Hc := csPts_weaken _ _ _ _ $$ Hcs
  iunfold smPts
  iexists pc, pi, pt, uf
  isplitr
  · ipureintro; exact Hnn
  iframe HC HI HT
  isplitl
  · iunfold csOpt; iright; iexact Hc
  iframe cI cT Hpb

theorem raftpb.EnsureSnapshotMetadata.wp_proof
    (wp_EnsureConfState : raftpb.EnsureConfState.spec (GF := GF) (hG := hG)) :
    raftpb.EnsureSnapshotMetadata.spec (GF := GF) (hG := hG) := by
  intro m md
  wp_start as Hm
  iapply wp_fupd
  iunfold smOpt at Hm
  icases Hm with (⟨%Hp, %Hmd⟩ | Hm)
  · subst Hp Hmd
    wp_auto
    wp_apply wp_EnsureConfState null (ConfStateM.mk [] [] [] [] false) $$ [] as %rc ⟨Hcs, -⟩
    · iunfold csOpt; ileft; ipureintro; exact ⟨rfl, rfl⟩
    rename_i pm pi
    rw [show (zero_val w64) = W64 0 from rfl]
    irename : (pi ↦ W64 0 : IProp GF) => Hi
    irename : («$r0_ptr» ↦ W64 0 : IProp GF) => Ht
    imod cellRO_alloc pi (W64 0) $$ Hi with #ci
    imod cellRO_alloc «$r0_ptr» (W64 0) $$ Ht with #ct
    ihave Hc := csPts_weaken _ _ _ _ $$ Hcs
    imod smPts_of_struct pm { (zero_val raftpb.SnapshotMetadata) with ConfState' := rc, Index' := pi, Term' := «$r0_ptr» }
      (SnapshotMetadataM.mk (ConfStateM.mk [] [] [] [] false) (W64 0) (W64 0)) ⊤ (by rfl)
      $$ [«$r0» Hc] with Hsm
    · dsimp only
      iframe «$r0»
      isplitl
      · iunfold csOpt; iright; iexact Hc
      iframe ci ct
    imodintro
    iapply HΦ
    iframe
    ipureintro; intro h; exact absurd rfl h
  · iNamed Hm
    wp_auto
    wp_if_destruct
    · exact absurd rfl Hnn
    wp_apply wp_EnsureConfState pc md.ConfState' $$ [Hc] as %rc ⟨Hcs, %Hrc⟩
    · iexact Hc
    wp_if_destruct
    all_goals try (have e := Hrc Hif; subst e)
    all_goals
      wp_if_destruct
      any_goals
        ihave (⟨-, %Hv⟩ | ⟨-, %Hpn⟩) := cellRO_cases $$ cI
        rotate_left
        · exact absurd rfl Hpn
        iclear cI
        imod cellRO_alloc «$r0_ptr» md.Index' $$ [«$r0»] with #cI
        · rw [Hv]; iexact «$r0»
      all_goals
        wp_if_destruct
        any_goals
          ihave (⟨-, %Hv⟩ | ⟨-, %Hpn⟩) := cellRO_cases $$ cT
          rotate_left
          · exact absurd rfl Hpn
          iclear cT
          imod cellRO_alloc «$r0_ptr» md.Term' $$ [«$r0»] with #cT
          · rw [Hv]; iexact «$r0»
        all_goals
          imodintro
          iapply HΦ
          isplitl
          · iapply smPts_intro _ _ _ _ _ _ Hnn
            iframe
            iframe cI cT Hpb
          · ipureintro; intro _; rfl

end proof

end EtcdGrove
end Perennial
