/-
Proof of `(*bootstrappedWAL).fillBackendAheadGap()`
(`Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrappedWAL__fillBackendAheadGap.lean`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedWAL__fillBackendAheadGap
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedWAL__AppendAndCommitEntries

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3 go_uber_org

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxHeartbeats 0 in
theorem bootstrappedWAL.fillBackendAheadGap.wp_proof
    (wp_Entry_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF))
    (wp_Snapshot_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF))
    (wp_SnapshotMetadata_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF))
    (wp_Uint64 : zap.Uint64.spec (GF := GF))
    (wp_Info : zap.Logger.Info.spec (GF := GF))
    (wp_Enum : raftpb.EntryType.Enum.spec (GF := GF))
    (wp_AppendAndCommitEntries : bootstrappedWAL.AppendAndCommitEntries.spec (GF := GF)) :
    bootstrappedWAL.fillBackendAheadGap.spec (GF := GF) := by
  intro w bw sv hs es Hlg Hlast_le Hcommit_lt Hlen_bound
  wp_start as Hpre
  iNamed Hpre
  iunfold entsPts at Hents
  icases Hents with ⟨%ls, Hs, #Hb⟩
  ihave %Heq := entsBig_length _ _ $$ Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave #Hpkgr : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Hpkgz : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  (try wp_auto)
  wp_join iprop(
      "lastIndex" ∷ lastIndex_ptr ↦ walLastIndex sv es ∗
      "wal" ∷ wal_ptr ↦ w ∗
      "Hwal" ∷ w ↦ bw ∗
      "Hs" ∷ bw.ents' ↦* ls)
    at next with [lastIndex wal Hwal Hs] as Hjoined
  · wp_if_destruct
    · -- `len(wal.ents) > 0`
      have Hpos_ls : 0 < ls.length := by rw [Hlen.1]; word
      have Hpos_es : 0 < es.length := by rw [← Heq]; exact Hpos_ls
      obtain ⟨l_last, Hllast⟩ : ∃ l_last, ls[es.length - 1]? = some l_last :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨e_last, Helast⟩ : ∃ e_last, es[es.length - 1]? = some e_last :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have Hidx_z : sint.Z (bw.ents'.len - W64 1) = (es.length - 1 : Nat) := by
        rw [← Heq, Hlen.1]; unfold sint.nat; word
      have Hidx_lt : sint.Z (bw.ents'.len - W64 1) < sint.Z bw.ents'.len := by word
      have Hidx_ge : 0 ≤ sint.Z (bw.ents'.len - W64 1) := by omega
      have Hllast' : ls[(sint.Z (bw.ents'.len - W64 1)).toNat]? = some l_last := by
        rw [Hidx_z]; simpa using Hllast
      simp only [Hidx_ge, Hidx_lt, _root_.and_self, ↓reduceIte]
      icases ownSlice_elem_acc (sint.Z (bw.ents'.len - W64 1)) l_last _ _ _ Hidx_ge Hllast' $$ Hs
        with ⟨Hll, Hs_close⟩
      ihave #Hent : entRO l_last e_last $$ []
      · iapply (BigSepL2.bigSepL2_lookup Hllast Helast) $$ Hb
      ihave #HentPts : entPts l_last DFrac.discard e_last $$ []
      · iexact Hent
      (try wp_auto)
      ihave Hs := Hs_close $$ Hll
      rw [list_insert_id Hllast']
      wp_apply wp_Entry_GetIndex.1 l_last DFrac.discard e_last $$ [$Hpkgr $HentPts] as _
      (try wp_auto)
      have Hwlast : walLastIndex sv es = e_last.Index' := by
        unfold walLastIndex
        rw [List.getLast?_eq_getElem?, Helast]
      rw [← Hwlast]
      isplitr; · itrivial
      simp only [named]; iframe
    · -- `len(wal.ents) <= 0` (`es = []`)
      have Hempty : es = [] := by
        apply List.eq_nil_of_length_eq_zero
        have : ls.length = 0 := by rw [Hlen.1]; word
        omega
      have Hwlast : walLastIndex sv es = sv.Metadata'.Index' := by
        unfold walLastIndex; rw [Hempty]; rfl
      iunfold snapOptRO at Hsnap
      icases Hsnap with (⟨%Hsn_null, %Hsv_zero⟩ | #Hsn_set)
      · subst Hsv_zero
        (try wp_auto)
        rw [Hsn_null]
        wp_apply wp_Snapshot_GetMetadata.2 $$ [$Hpkgr]
        (try wp_auto)
        ihave Hsm0 : smOpt (null : Loc) DFrac.discard snapZero.Metadata' $$ []
        · iunfold smOpt; ileft; ipureintro; exact ⟨rfl, rfl⟩
        wp_apply wp_SnapshotMetadata_GetIndex null DFrac.discard snapZero.Metadata'
          $$ [$Hpkgr $Hsm0] as _
        (try wp_auto)
        rw [Hwlast, show snapZero.Metadata'.Index' = W64 0 from rfl]
        isplitr; · itrivial
        simp only [named]; iframe
      · ihave HsnM := ownSnapS_M bw.snapshot' DFrac.discard sv $$ Hsn_set
        (try wp_auto)
        wp_apply wp_Snapshot_GetMetadata.1 bw.snapshot' DFrac.discard sv
          $$ [$Hpkgr $HsnM] as %pm ⟨Hsm, _⟩
        (try wp_auto)
        wp_apply wp_SnapshotMetadata_GetIndex pm DFrac.discard sv.Metadata'
          $$ [$Hpkgr $Hsm] as _
        (try wp_auto)
        rw [← Hwlast]
        isplitr; · itrivial
        simp only [named]; iframe
  iNamed Hjoined
  (try wp_auto)
  wp_apply wp_hsPts_GetCommit bw.st' (DFrac.own 1) hs $$ [$Hpkgr $Hst] as Hst
  (try wp_auto)
  wp_if_destruct
  · -- `commit <= lastIndex`: early return
    have Hle_z : uint.Z hs.Commit' ≤ uint.Z (walLastIndex sv es) := by word
    have Hgap_nil : gapEntries hs.Term' (walLastIndex sv es) hs.Commit' = [] :=
      gapEntries_of_le _ _ _ Hle_z
    iapply HΦ
    rw [Hgap_nil, List.append_nil]
    iexists bw.ents'
    iframe Hwal Hst Hcap
    iunfold entsPts
    iexists ls
    iframe Hs Hb
  · -- `lastIndex < commit`: log, build `gapEnts`, and call `AppendAndCommitEntries`
    have Hlt_z : uint.Z (walLastIndex sv es) < uint.Z hs.Commit' := by word
    (try wp_auto)
    wp_apply wp_Uint64 $$ [$Hpkgz] as %f0 -
    (try wp_auto)
    wp_apply wp_Uint64 $$ [$Hpkgz] as %f1 -
    (try wp_auto)
    wp_apply wp_Uint64 $$ [$Hpkgz] as %f2 -
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr; · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply (wp_Info bw.lg') $$ [$Hpkgz]
    · ipureintro; exact Hlg
    (try wp_auto)
    ihave Hgsl0 : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
    · iapply ownSlice_nil
    ihave Hgcap0 : ownSliceCap Loc slice.nil (DFrac.own 1) $$ []
    · iapply ownSliceCap_nil
    ihave #Hgb0 : ([∗list] l;e ∈ ([] : List Loc);gapEntriesAux hs.Term' (walLastIndex sv es) 0,
        entRO (GF := GF) l e) $$ []
    · rw [gapEntriesAux_zero]; iapply BigSepL2.bigSepL2_nil; itrivial
    ihave IH : iprop(∃ (k : Nat) (gsl : GoSlice) (gls : List Loc),
        "wal" ∷ wal_ptr ↦ w ∗
        "Hwal" ∷ w ↦ bw ∗
        "Hst" ∷ hsPts bw.st' (DFrac.own 1) hs ∗
        "commit" ∷ commit_ptr ↦ hs.Commit' ∗
        "gapEnts" ∷ gapEnts_ptr ↦ gsl ∗
        "idx" ∷ idx_ptr ↦ W64 (uint.Z (walLastIndex sv es) + 1 + (k : Int)) ∗
        "Hgsl" ∷ gsl ↦* gls ∗
        "Hgcap" ∷ ownSliceCap Loc gsl (DFrac.own 1) ∗
        "#Hgb" ∷ ([∗list] l;e ∈ gls;gapEntriesAux hs.Term' (walLastIndex sv es) k, entRO l e) ∗
        "%Hk" ∷ ⌜k ≤ (uint.Z hs.Commit' - uint.Z (walLastIndex sv es)).toNat⌝)
      $$ [wal Hwal Hst commit gapEnts idx Hgsl0 Hgcap0]
    · iexists 0, (zero_val GoSlice), []
      simp only [named]
      rw [show W64 (uint.Z (walLastIndex sv es) + 1 + ((0 : Nat) : Int)) = walLastIndex sv es + W64 1 by word,
        show (zero_val GoSlice) = slice.nil from rfl]
      iframe
      iframe Hgb0
      ipureintro; exact Nat.zero_le _
    wp_for IH
    wp_if_destruct
    · -- Inside loop: `idx <= commit`
      have Hidx_le : uint.Z (W64 (uint.Z (walLastIndex sv es) + 1 + (k : Int))) ≤ uint.Z hs.Commit' := by
        word
      have Hk_lt : k < (uint.Z hs.Commit' - uint.Z (walLastIndex sv es)).toNat := by
        have : uint.Z (W64 (uint.Z (walLastIndex sv es) + 1 + (k : Int))) =
            uint.Z (walLastIndex sv es) + 1 + (k : Int) := by word
        omega
      (try wp_auto)
      rw [show raftpb.EntryNormal = #((W32 0 : raftpb.EntryType)) from rfl]
      haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
      wp_apply wp_Enum (W32 0) $$ [$Hpkgr] as %pty Hpty
      (try wp_auto)
      wp_apply wp_hsPts_GetTerm bw.st' (DFrac.own 1) hs $$ [$Hpkgr $Hst] as Hst
      (try wp_auto)
      -- Freeze the newly allocated entry at `«$sl0_ptr»` while goal is `WP`
      imod cellRO_alloc pty (W32 0) $$ Hpty with #HcY
      imod cellRO_alloc «$v1_ptr» hs.Term' $$ «$v1» with #HcT
      imod cellRO_alloc «$v2_ptr» (W64 (uint.Z (walLastIndex sv es) + 1 + (k : Int))) $$ «$v2» with #HcI
      ihave Hnil_w8 : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
      · iapply ownSlice_nil
      imod (ownSlice_dfractional (GF := GF) slice.nil ([] : List w8)).dfractional_persist _ $$ Hnil_w8
        with #Hd
      imod entOwn_of_struct «$sl0_ptr»
        (⟨zero_val _, «$v1_ptr», «$v2_ptr», pty, slice.nil, slice.nil, 0⟩ : raftpb.Entry)
        (gapEntry hs.Term' (W64 (uint.Z (walLastIndex sv es) + 1 + (k : Int)))) ⊤ rfl
        $$ [«$sl0»] with HentOwn
      · simp only [gapEntry]; iframe «$sl0» HcT HcI HcY Hd
      imod entOwn_freeze «$sl0_ptr» _ $$ HentOwn with #HentRO
      ihave #Hgb1 : ([∗list] l;e ∈ [«$sl0_ptr»];[gapEntry hs.Term' (W64 (uint.Z (walLastIndex sv es) + 1 + (k : Int)))],
          entRO (GF := GF) l e) $$ []
      · iapply BigSepL2.bigSepL2_singleton.2; iexact HentRO
      ihave #Hgb' := entsBig_app gls [«$sl0_ptr»]
        (gapEntriesAux hs.Term' (walLastIndex sv es) k)
        [gapEntry hs.Term' (W64 (uint.Z (walLastIndex sv es) + 1 + (k : Int)))]
        $$ [$Hgb $Hgb1]
      isimp only [← gapEntriesAux_succ] at Hgb'
      wp_apply wp_slice_literal
      isplitr; · ipureintro; rfl
      iintro %esl ⟨Hesl, -⟩
      (try wp_auto)
      wp_apply wp_slice_append (V := Loc) $$ [$Hgsl $Hgcap $Hesl] as %gsl' ⟨Hgsl', Hgcap', -⟩
      (try wp_auto)
      wp_for_post
      iframe
      iexists (k + 1), gsl', (gls ++ [«$sl0_ptr»])
      simp only [named]
      rw [show W64 (uint.Z (walLastIndex sv es) + 1 + (k : Int)) + W64 1 =
        W64 (uint.Z (walLastIndex sv es) + 1 + ((k + 1 : Nat) : Int)) by word]
      iframe Hgsl' Hgcap' Hgb'
      iframe
      ipureintro; omega
    · -- Loop exit: `commit < idx`
      have Hidx_gt : uint.Z hs.Commit' <
          uint.Z (W64 (uint.Z (walLastIndex sv es) + 1 + (k : Int))) := by word
      have Hk_eq : k = (uint.Z hs.Commit' - uint.Z (walLastIndex sv es)).toNat := by
        have : uint.Z (W64 (uint.Z (walLastIndex sv es) + 1 + (k : Int))) =
            uint.Z (walLastIndex sv es) + 1 + (k : Int) := by word
        omega
      (try wp_auto)
      have Hgap_eq : gapEntriesAux hs.Term' (walLastIndex sv es) k =
          gapEntries hs.Term' (walLastIndex sv es) hs.Commit' := by
        rw [Hk_eq]; rfl
      isimp only [Hgap_eq] at Hgb
      ihave Hents : entsPts bw.ents' (DFrac.own 1) es $$ [Hs]
      · iunfold entsPts; iexists ls; iframe Hs Hb
      ihave Hgents : entsPts gsl (DFrac.own 1)
          (gapEntries hs.Term' (walLastIndex sv es) hs.Commit') $$ [Hgsl]
      · iunfold entsPts; iexists gls; iframe Hgsl Hgb
      have Hlen_app : (es.length : Int) +
          ((gapEntries hs.Term' (walLastIndex sv es) hs.Commit').length : Int) < 2 ^ 63 := by
        rw [gapEntries_length]
        omega
      wp_apply wp_AppendAndCommitEntries w bw gsl (DFrac.own 1) hs es
        (gapEntries hs.Term' (walLastIndex sv es) hs.Commit') Hlen_app
        $$ [$Hwal $Hst $Hents $Hcap $Hgents $Hsave]
        as ⟨%ents', Hwal, Hst, Hents', Hcap', -⟩
      (try wp_auto)
      isimp only [hsAfterAppend_gapEntries hs es (walLastIndex sv es) Hlt_z] at Hst
      iapply HΦ
      iexists ents'
      iframe Hwal Hst Hents' Hcap'

end proof

end EtcdGrove
end Perennial
