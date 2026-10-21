/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/EnsureSnapshotMetadata.lean`.
-/
module

public import Spec.go_etcd_io.raft.v3.raftpb.EnsureSnapshotMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.EnsureConfState

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

/-- A metadata at `m` whose fields hold a nested conf state and two cells holding `md`'s is an owned
metadata holding `md`. -/
private theorem smPts_intro (m pc pi pt : Loc) (md : SnapshotMetadataM) (uf : List w8)
    (Hnn : m ≠ null) (Hpc : pc ≠ null) :
    (m.[raftpb.SnapshotMetadata, go!"ConfState"] ↦ pc ∗ csOptA pc (DFrac.own 1) md.ConfState' ∗
      m.[raftpb.SnapshotMetadata, go!"Index"] ↦ pi ∗ cellRO pi md.Index' ∗
      m.[raftpb.SnapshotMetadata, go!"Term"] ↦ pt ∗ cellRO pt md.Term' ∗
      pbMsg raftpb.SnapshotMetadata m uf : IProp GF) ⊢ smPtsW m (DFrac.own 1) md := by
  iintro ⟨HC, Hc, HI, #cI, HT, #cT, #Hpb⟩
  iunfold smPtsW
  iexists pc, pi, pt, uf
  isplitr
  · ipureintro; exact ⟨Hnn, Hpc⟩
  iframe HC HI HT Hc
  iframe cI cT Hpb

/-- `smPts_of_struct` (`InvPb.lean`) for a set conf state: whole (D17d). -/
private theorem smPtsW_of_struct (p : Loc) (v : raftpb.SnapshotMetadata) (md : SnapshotMetadataM)
    (E : CoPset) (Hu : v.unknownFields' = slice.nil) (Hc : v.ConfState' ≠ null) :
    (p ↦ v ∗ csOptA v.ConfState' (DFrac.own 1) md.ConfState' ∗ cellRO v.Index' md.Index' ∗
      cellRO v.Term' md.Term' : IProp GF) ⊢ |={E}=> smPtsW p (DFrac.own 1) md := by
  iintro ⟨Hp, Hc, #cI, #cT⟩
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨state, ConfState, Index, Term, unknownFields, sizeCache, -⟩
  rw [Hu]
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod pbMsg_alloc raftpb.SnapshotMetadata p v.state' v.sizeCache' slice.nil [] E $$ [state sizeCache unknownFields Hnil] with #Hpb
  · iframe
  imodintro
  iunfold smPtsW
  iexists v.ConfState', v.Index', v.Term', []
  isplitr
  · ipureintro; exact ⟨Hnn, Hc⟩
  iframe
  iframe cI cT Hpb

/-- `EnsureConfState` on a snapshot's nested conf state (`csOptA`, D7) held at `1`: in each case a
non-`nil` nested conf state holding the same record (owned if it was nil or owned, still frozen if
it was frozen), `pc` itself unless `pc` was `nil`. -/
private theorem wp_EnsureConfState_A
    (wp_EnsureConfState : raftpb.EnsureConfState.spec (GF := GF) (hG := hG))
    (pc : Loc) (c : ConfStateM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ csOptA pc (DFrac.own 1) c }}
      (App (Val #(functions raftpb.EnsureConfState [])) (Val #pc))
    {{ (r : Loc), RET #r; csOptA r (DFrac.own 1) c ∗ ⌜r ≠ null⌝ ∗ ⌜pc ≠ null → r = pc⌝ }} := by
  iintro %Φ ⟨#Hinit, Hc⟩ HΦ
  iunfold csOptA at Hc
  icases Hc with (⟨%Hp, %Hc⟩ | Hc | #Hc)
  · subst Hp Hc
    wp_apply wp_EnsureConfState.2 as %r Hcs
    icases csPts_nn _ _ _ _ $$ Hcs with ⟨Hcs, %Hr⟩
    iapply HΦ
    isplitl
    · iunfold csOptA; iright; ileft; iapply csPts_weaken $$ Hcs
    isplitr
    · ipureintro; exact Hr
    · ipureintro; intro h; exact absurd rfl h
  · wp_apply wp_EnsureConfState.1 pc (DFrac.own 1) c false $$ [Hc] as Hcs
    · iframe; ipureintro; intro h; exact absurd rfl h
    icases csPts_nn _ _ _ _ $$ Hcs with ⟨Hcs, %Hr⟩
    iapply HΦ
    isplitl
    · iunfold csOptA; iright; ileft; iapply csPts_weaken $$ Hcs
    isplitr
    · ipureintro; exact Hr
    · ipureintro; intro _; rfl
  · wp_apply wp_EnsureConfState.1 pc DFrac.discard c true $$ [] as #Hcs
    · iframe Hc; ipureintro; intro _; rfl
    icases csPts_nn _ _ _ _ $$ Hcs with ⟨-, %Hr⟩
    iapply HΦ
    isplitl
    · iunfold csOptA; iright; iright; iexact Hcs
    isplitr
    · ipureintro; exact Hr
    · ipureintro; intro _; rfl

/-- The owned triple (`raftpb.EnsureSnapshotMetadata.spec`'s first). -/
private theorem wp_EnsureSnapshotMetadata_own
    (wp_EnsureConfState : raftpb.EnsureConfState.spec (GF := GF) (hG := hG))
    (m : Loc) (md : SnapshotMetadataM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ smOpt m (DFrac.own 1) md }}
      (App (Val #(functions raftpb.EnsureSnapshotMetadata [])) (Val #m))
    {{ (r : Loc), RET #r; smPtsW r (DFrac.own 1) md ∗ ⌜m ≠ null → r = m⌝ }} := by
  wp_start as Hm
  iapply wp_fupd
  iunfold smOpt at Hm
  icases Hm with (⟨%Hp, %Hmd⟩ | Hm)
  · subst Hp Hmd
    wp_auto
    wp_apply wp_EnsureConfState.2 as %rc Hcs
    rename_i pm pi
    rw [show (zero_val w64) = W64 0 from rfl]
    irename : (pi ↦ W64 0 : IProp GF) => Hi
    irename : («$r0_ptr» ↦ W64 0 : IProp GF) => Ht
    imod cellRO_alloc pi (W64 0) $$ Hi with #ci
    imod cellRO_alloc «$r0_ptr» (W64 0) $$ Ht with #ct
    icases csPts_nn _ _ _ _ $$ Hcs with ⟨Hcs, %Hrc⟩
    ihave Hc := csPts_weaken _ _ _ _ $$ Hcs
    imod smPtsW_of_struct pm { (zero_val raftpb.SnapshotMetadata) with ConfState' := rc, Index' := pi, Term' := «$r0_ptr» }
      (SnapshotMetadataM.mk (ConfStateM.mk [] [] [] [] false) (W64 0) (W64 0)) ⊤ (by rfl) Hrc
      $$ [«$r0» Hc] with Hsm
    · dsimp only
      iframe «$r0»
      isplitl
      · iunfold csOptA; iright; ileft; iexact Hc
      iframe ci ct
    imodintro
    iapply HΦ
    iframe
    ipureintro; intro h; exact absurd rfl h
  · iNamed Hm
    wp_auto
    wp_if_destruct
    · exact absurd rfl Hnn
    wp_apply wp_EnsureConfState_A wp_EnsureConfState pc md.ConfState' $$ [Hc] as %rc ⟨Hcs, %Hrn, %Hrc⟩
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
          · iapply smPts_intro _ _ _ _ _ _ Hnn Hrn
            iframe
            iframe cI cT Hpb
          · ipureintro; intro _; rfl

/-- (D22 S-d4, 2026-10-21) `EnsureSnapshotMetadata` of a metadata with every pointer field set, at
any fraction: it writes nothing and returns the metadata (`smPtsS`). -/
private theorem wp_EnsureSnapshotMetadata_set
    (wp_EnsureConfState : raftpb.EnsureConfState.spec (GF := GF) (hG := hG))
    (m : Loc) (dq : DFrac) (md : SnapshotMetadataM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ smPtsS m dq md }}
      (App (Val #(functions raftpb.EnsureSnapshotMetadata [])) (Val #m))
    {{ RET #m; smPtsS m dq md }} := by
  wp_start as Hm
  iNamed Hm
  obtain ⟨Hmn, Hpc, Hpi, Hpt⟩ := Hnn
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hmn
  wp_apply wp_EnsureConfState.1 pc dq md.ConfState' true $$ [Hc] as Hc
  · iframe Hc; ipureintro; intro _; rfl
  wp_if_destruct
  · exact absurd rfl Hpc
  wp_if_destruct
  · exact absurd rfl Hpi
  wp_if_destruct
  · exact absurd rfl Hpt
  iapply HΦ
  iunfold smPtsS
  iexists pc, pi, pt, uf
  isplitr
  · ipureintro; exact ⟨Hmn, Hpc, Hpi, Hpt⟩
  iframe HC Hc HI HT cI cT Hpb

theorem raftpb.EnsureSnapshotMetadata.wp_proof
    (wp_EnsureConfState : raftpb.EnsureConfState.spec (GF := GF) (hG := hG)) :
    raftpb.EnsureSnapshotMetadata.spec (GF := GF) (hG := hG) :=
  ⟨wp_EnsureSnapshotMetadata_own wp_EnsureConfState,
   wp_EnsureSnapshotMetadata_set wp_EnsureConfState⟩


end proof

end EtcdGrove
end Perennial
