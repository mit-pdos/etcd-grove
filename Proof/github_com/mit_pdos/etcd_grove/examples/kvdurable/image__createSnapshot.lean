/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/image__createSnapshot.lean`.
Lean-first (no Rocq counterpart): the image's snapshot index read (refused at or below it); the
term at `i` (`prevTerm` at the log's start, the entry's after it); the configuration (`cs`, or the
old snapshot's); then a new snapshot built from fresh structs, the data copied, frozen read-only
(`smPts_of_struct_ro`, `ownSnapM_of_struct_ro`: a snapshot whose configuration is read-only for good
is built read-only).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.image__createSnapshot
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetConfState
public import Proof.go_etcd_io.raft.v3.LemmasEnts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- A freshly allocated `*pb.SnapshotMetadata` (hidden fields zero) whose conf state is read-only
and whose cells hold `md`'s is a read-only metadata holding `md`. -/
private theorem smPts_of_struct_ro (p pc pi pt : Loc) (md : SnapshotMetadataM) (E : CoPset) :
    (p ↦ raftpb.SnapshotMetadata.mk zeroValDef pc pi pt slice.nil 0 ∗
      csOptA pc DFrac.discard md.ConfState' ∗ cellRO pi md.Index' ∗
      cellRO pt md.Term' : IProp GF) ⊢ |={E}=> smPts p DFrac.discard md := by
  generalize Hv : raftpb.SnapshotMetadata.mk zeroValDef pc pi pt slice.nil 0 = v
  have Hu : v.unknownFields' = slice.nil := by rw [← Hv]
  have Hc' : v.ConfState' = pc := by rw [← Hv]
  have Hi' : v.Index' = pi := by rw [← Hv]
  have Ht' : v.Term' = pt := by rw [← Hv]
  rw [← Hc', ← Hi', ← Ht']
  iintro ⟨Hp, #Hc, #cI, #cT⟩
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨state, ConfState, Index, Term, unknownFields, sizeCache, -⟩
  rw [Hu]
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod pbMsg_alloc raftpb.SnapshotMetadata p v.state' v.sizeCache' slice.nil [] E $$ [state sizeCache unknownFields Hnil] with #Hpb
  · iframe
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ ConfState with #ConfState
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Index with #Index
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Term with #Term
  imodintro
  iunfold smPts
  iexists v.ConfState', v.Index', v.Term', []
  isplitr
  · ipureintro; exact Hnn
  iframe ConfState Hc Index cI Term cT Hpb

/-- A freshly allocated `*pb.Snapshot` (hidden fields zero) whose data bytes and metadata are
read-only and hold `s`'s is a read-only snapshot holding `s`. -/
private theorem ownSnapM_of_struct_ro (p : Loc) (ds : GoSlice) (pm : Loc) (s : SnapshotM)
    (E : CoPset) :
    (p ↦ raftpb.Snapshot.mk zeroValDef ds pm slice.nil 0 ∗ ds ↦*□ s.Data' ∗
      smOpt pm DFrac.discard s.Metadata' : IProp GF) ⊢
      |={E}=> ownSnapM p DFrac.discard s := by
  generalize Hv : raftpb.Snapshot.mk zeroValDef ds pm slice.nil 0 = v
  have Hu : v.unknownFields' = slice.nil := by rw [← Hv]
  have Hd' : v.Data' = ds := by rw [← Hv]
  have Hm' : v.Metadata' = pm := by rw [← Hv]
  rw [← Hd', ← Hm']
  iintro ⟨Hp, #Hd, #Hm⟩
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨state, Data, Metadata, unknownFields, sizeCache, -⟩
  rw [Hu]
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod pbMsg_alloc raftpb.Snapshot p v.state' v.sizeCache' slice.nil [] E $$ [state sizeCache unknownFields Hnil] with #Hpb
  · iframe
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Data with #Data
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Metadata with #Metadata
  imodintro
  iunfold ownSnapM
  iexists v.Data', v.Metadata', []
  isplitr
  · ipureintro; exact Hnn
  iframe Data Hd Metadata Hm Hpb

theorem image.createSnapshot.wp_proof
    (wp_GetTerm : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG))
    (wp_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (wp_GetConfState : raftpb.SnapshotMetadata.GetConfState.spec (GF := GF) (hG := hG)) :
    image.createSnapshot.spec (GF := GF) (hG := hG) := by
  intro p I i cs co data dq bs eood Hok
  wp_start as ⟨Himg, Hcs, Hdata, #Herr⟩
  -- the configuration: `cs`, read-only for good, or `nil` (the old snapshot's)
  ihave #Hco : (⌜co = none ∧ cs = null⌝ ∨
      (⌜cs ≠ null ∧ co ≠ none⌝ ∗ csOptA cs DFrac.discard (co.getD I.snap.Metadata'.ConfState')))
      $$ [Hcs]
  · cases co with
    | none => icases Hcs with %H; ileft; ipureintro; exact ⟨rfl, H⟩
    | some c =>
      iright
      icases csPts_nn _ _ _ _ $$ Hcs with ⟨#Hcs, %Hnn⟩
      isplitr
      · ipureintro; exact ⟨Hnn, by simp⟩
      simp only [Option.getD_some]
      iunfold csOptA; iright; ileft; iexact Hcs
  iunfold ownImage at Himg
  icases Himg with ⟨%hsp, %sp, %es, Himg⟩
  iNamed Himg
  ihave %Hlen := entsPts_len $$ HentsO
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_GetMetadata.1 sp DFrac.discard I.snap $$ [$Hpb $HsnapO] as %pm ⟨#Hsm, -⟩
  wp_apply wp_GetIndex pm DFrac.discard I.snap.Metadata' $$ [$Hpb $Hsm] as -
  wp_if_destruct
  · -- at or below the snapshot's index: `ErrSnapOutOfDate`
    have Hst : imgCreateStale I i := by unfold imgCreateStale; word
    iapply HΦ
    iframe Hdata
    rw [ite_eq_left Hst]
    isplitr
    · ipureintro; rfl
    iunfold ownImage
    iexists hsp, sp, es
    iframe # ∗
    ipureintro; exact Hwf
  have Hst : ¬ imgCreateStale I i := by unfold imgCreateStale; word
  obtain ⟨Hlo, Hhi⟩ := Hok.resolve_left Hst
  have Hsum : uint.Z (I.prev + es.len) = uint.Z I.prev + I.ents.length := by word
  wp_if_destruct
  · exfalso; word
  wp_if_destruct
  · exfalso; word
  -- the term at `i`
  -- (the two branches meet with `term` at `imgTermAt I i`: the rest is proved for both)
  wp_if_destruct
  rotate_left
  -- at the log's start: `prevTerm`
  ihave Hterm : term_ptr ↦ imgTermAt I i $$ [term]
  · have Ht : imgTermAt I i = I.prevTerm := by
      unfold imgTermAt; rw [ite_eq_left (by word)]
    rw [Ht]; iexact term
  rotate_left
  -- after it: the entry's
  have Hgt : uint.nat I.prev < uint.nat i := by word
  obtain ⟨e, He⟩ : ∃ e, I.ents[uint.nat i - uint.nat I.prev - 1]? = some e :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  icases entsRO_lookup es I.ents _ e He $$ HentsO with ⟨%ls, %l, #Hls, #Hel, %Hl⟩
  rw [ite_eq_left ⟨by word, by word⟩]
  wp_apply wp_load_slice_index es (sint.Z (i - I.prev - W64 1)) ls DFrac.discard l (by word)
    $$ [Hls] with -
  · iframe Hls; ipureintro
    rw [show (sint.Z (i - I.prev - W64 1)).toNat = uint.nat i - uint.nat I.prev - 1 by word]
    exact Hl.1
  wp_apply wp_GetTerm.1 l DFrac.discard e $$ [Hel] with -
  · iframe Hel
  try wp_auto
  ihave Hterm : term_ptr ↦ imgTermAt I i $$ [term]
  · have Ht : imgTermAt I i = e.Term' := by
      unfold imgTermAt; rw [ite_eq_right (by omega), He]; rfl
    rw [Ht]; iexact term
  all_goals
    -- the configuration
    -- (the branches meet with `cs` at a read-only configuration, `Hcsf`)
    wp_if_destruct
    icases Hco with (⟨%Hco1, %Hco2⟩ | ⟨⟨%Hco1, %Hco2⟩, #Hcsf⟩)
    rotate_left
    · exfalso; exact Hco1 rfl
    icases Hco with (⟨%Hco1, %Hco2⟩ | ⟨⟨%Hco1, %Hco2⟩, #Hcsf⟩)
    · exfalso; exact Hif Hco2
    rotate_left
    wp_apply wp_GetMetadata.1 sp DFrac.discard I.snap $$ [$Hpb $HsnapO] as %pm' ⟨#Hsm', -⟩
    wp_apply wp_GetConfState pm' DFrac.discard I.snap.Metadata' $$ [$Hpb $Hsm'] as %pc ⟨#Hpc, -⟩
    try wp_auto
    ihave #Hcsf : csOptA pc DFrac.discard (co.getD I.snap.Metadata'.ConfState') $$ []
    · rw [Hco1, Option.getD_none]; iexact Hpc
    all_goals
      -- the new snapshot, frozen read-only
      imod cellRO_alloc $$ «$v1» with #cI
      imod cellRO_alloc $$ «$v2» with #cT
      imod smPts_of_struct_ro «$v0_ptr» _ «$v1_ptr» «$v2_ptr»
        (SnapshotMetadataM.mk (co.getD I.snap.Metadata'.ConfState') i (imgTermAt I i)) ⊤
        $$ [«$v0» Hcsf cI cT] with #Hsmn
      · iframe «$v0»; iframe Hcsf cI cT
      ihave Hnil : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
      · iapply ownSlice_nil
      ihave Hnilc := ownSliceCap_nil (GF := GF) (V := w8)
      wp_apply +noauto wp_slice_append_persistent (V := w8) slice.nil [] data bs dq
        $$ [$Hnil $Hnilc $Hdata] as %ds ⟨#Hds, -, Hdata⟩
      iapply wp_fupd
      wp_auto
      imod ownSnapM_of_struct_ro «$r0_ptr» ds «$v0_ptr»
        (memSnapMade i (imgTermAt I i) (co.getD I.snap.Metadata'.ConfState') bs) ⊤
        $$ [«$r0» Hds Hsmn] with #Hsn
      · iframe «$r0»
        simp only [memSnapMade, List.nil_append] at *
        isplitl []
        · iexact Hds
        iunfold smOpt; iright; iexact Hsmn
      imodintro
      iapply HΦ
      iframe Hdata
      rw [ite_eq_right Hst]
      isplitr
      · ipureintro; rfl
      iunfold ownImage
      iexists hsp, «$r0_ptr», es
      simp only [imgCreateSnapshot]
      iframe # ∗
      ipureintro; exact Hwf

end proof

end kvdurable
end EtcdGrove
end Perennial
