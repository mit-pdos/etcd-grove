-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/raftpb/CloneSM.lean` (etc/copy-part.py; rerun it, do not edit).
/-
`cloneSnapshotMetadata` (`raftpb/noax.go`), for `CloneSnapshot`'s proof: the core (the fields of a
non-`nil` metadata, its conf state's clone abstracted as a triple `R`/`Q`), the conf state's two
forms (`csOptA`, `csSet`), and the four metadata forms the snapshot predicates use (`smOpt`,
`smPtsW`, `smPtsS`, `smPtsV`). The part's own (raft without hand-written axioms,
`notes/raft-noax-part.md`, "Stage 3a").
-/
module

public import KvNet.Proof.go_etcd_io.raft.v3.raftpb.CloneCS
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.CloneSnapshot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A cell's clone keeps its record and its nullness. -/
theorem wp_cloneUint64_RO (p : Loc) (v : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ cellRO p v }}
      (App (Val #(functions raftpb.cloneUint64 [])) (Val #p))
    {{ (p' : Loc), RET #p'; cellRO p' v ∗ ⌜p ≠ null → p' ≠ null⌝ }} := by
  iintro %Φ ⟨#Hi, #Hc⟩ HΦ
  icases nx_cellRO_optCell _ _ $$ Hc with ⟨%o, #Ho, %Hv⟩
  ihave %Hn := optCell_null _ _ $$ Ho
  iapply wp_cloneUint64 p o $$ [$Hi $Ho]
  iintro %p'
  inext
  iintro #Ho'
  ihave %Hn' := optCell_null _ _ $$ Ho'
  iapply HΦ
  isplitl
  · rw [Hv]; iapply nx_optCell_cellRO; iexact Ho'
  · ipureintro; intro h h'; exact h (Hn.2 (Hn'.1 h'))

/-- **`cloneSnapshotMetadata` of a non-`nil` metadata**, by its fields; the conf state's clone a
triple (`R` in, `R ∗ Q pc'` out). -/
theorem wp_cloneSM (m pc pi pt : Loc) (dq : DFrac) (md : SnapshotMetadataM) (uf : List w8)
    (R : IProp GF) (Q : Loc → IProp GF)
    (hcs : {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ R }}
      (App (Val #(functions raftpb.CloneConfState [])) (Val #pc))
      {{ (pc' : Loc), RET #pc'; R ∗ Q pc' }})
    (hm : m ≠ null) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗
        m.[raftpb.SnapshotMetadata, go!"ConfState"] ↦{dq} pc ∗ R ∗
        m.[raftpb.SnapshotMetadata, go!"Index"] ↦{dq} pi ∗ cellRO pi md.Index' ∗
        m.[raftpb.SnapshotMetadata, go!"Term"] ↦{dq} pt ∗ cellRO pt md.Term' ∗
        pbMsg raftpb.SnapshotMetadata m uf }}
      (App (Val #(functions raftpb.cloneSnapshotMetadata [])) (Val #m))
    {{ (m' : Loc), RET #m';
        m.[raftpb.SnapshotMetadata, go!"ConfState"] ↦{dq} pc ∗ R ∗
        m.[raftpb.SnapshotMetadata, go!"Index"] ↦{dq} pi ∗
        m.[raftpb.SnapshotMetadata, go!"Term"] ↦{dq} pt ∗
        ∃ (pc' pi' pt' : Loc),
          ⌜m' ≠ null ∧ (pi ≠ null → pi' ≠ null) ∧ (pt ≠ null → pt' ≠ null)⌝ ∗
          m'.[raftpb.SnapshotMetadata, go!"ConfState"] ↦ pc' ∗ Q pc' ∗
          m'.[raftpb.SnapshotMetadata, go!"Index"] ↦ pi' ∗ cellRO pi' md.Index' ∗
          m'.[raftpb.SnapshotMetadata, go!"Term"] ↦ pt' ∗ cellRO pt' md.Term' ∗
          pbMsg raftpb.SnapshotMetadata m' uf }} := by
  wp_start as ⟨HC, HR, HI, #cI, HT, #cT, #Hpb⟩
  iapply wp_fupd
  ihave %Huf := pbMsg_ufWire _ _ _ $$ Hpb
  icases pbMsg_uf _ _ _ $$ Hpb with ⟨%us, #Hus, #Hub⟩
  wp_auto
  wp_if_destruct
  · exact absurd rfl hm
  wp_apply hcs $$ [$HR] as %pc' ⟨HR, HQ⟩
  wp_apply wp_cloneUint64_RO pi md.Index' $$ [$cI] as %pi' ⟨#cI', %Hpi'⟩
  wp_apply wp_cloneUint64_RO pt md.Term' $$ [$cT] as %pt' ⟨#cT', %Hpt'⟩
  wp_apply wp_cloneUnknown us uf $$ [$Hub] as %us' Hus'
  ihave %Hnn := typedPointsto_not_null $$ «$r0»
  icases typedPointsto_split _ _ _ $$ «$r0» with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨state, ConfState, Index, Term, unknownFields, sizeCache, -⟩
  imod pbMsg_alloc raftpb.SnapshotMetadata _ _ _ _ uf ⊤ Huf $$ [state sizeCache unknownFields Hus'] with #Hpb'
  · iframe
  imodintro
  iapply HΦ
  iframe HC HR HI HT
  iexists pc', pi', pt'
  iframe
  iframe cI' cT' Hpb'
  ipureintro; exact ⟨Hnn, Hpi', Hpt'⟩

/-- `cloneSnapshotMetadata(nil)` is `nil`. -/
theorem wp_cloneSM_nil :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb }}
      (App (Val #(functions raftpb.cloneSnapshotMetadata [])) (Val #(null : Loc)))
    {{ RET #(null : Loc); True }} := by
  wp_start
  wp_auto
  iapply HΦ; ipureintro; trivial

/-! ## The conf state's forms -/

/-- `CloneConfState` of a snapshot's nested conf state (`csOptA`): an owned (or `nil`) one. -/
theorem wp_clone_csOptA (pc : Loc) (dq : DFrac) (c : ConfStateM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ csOptA pc dq c }}
      (App (Val #(functions raftpb.CloneConfState [])) (Val #pc))
    {{ (pc' : Loc), RET #pc'; csOptA pc dq c ∗
        (csOptA pc' (DFrac.own 1) c ∗ ⌜pc ≠ null → pc' ≠ null⌝) }} := by
  iintro %Φ ⟨#Hi, Hc⟩ HΦ
  iunfold csOptA at Hc
  icases Hc with (⟨%Hp, %Hc⟩ | Hc | #Hc)
  · subst Hp
    iapply wp_CloneConfState_nil $$ [$Hi]
    inext
    iintro -
    iapply HΦ
    iunfold csOptA
    isplitl
    · ileft; ipureintro; exact ⟨rfl, Hc⟩
    isplitl
    · ileft; ipureintro; exact ⟨rfl, Hc⟩
    · ipureintro; intro h; exact absurd rfl h
  · iapply wp_CloneConfState_al pc dq c false $$ [$Hi $Hc]
    iintro %pc'
    inext
    iintro ⟨Hc, Hc'⟩
    icases csPts_nn _ _ _ _ $$ Hc' with ⟨Hc', %Hn⟩
    iapply HΦ
    iunfold csOptA
    isplitl [Hc]
    · iright; ileft; iexact Hc
    isplitl
    · iright; ileft; iexact Hc'
    · ipureintro; intro _; exact Hn
  · iapply wp_CloneConfState_al pc DFrac.discard c true $$ [$Hi $Hc]
    iintro %pc'
    inext
    iintro ⟨-, Hc'⟩
    icases csPts_nn _ _ _ _ $$ Hc' with ⟨Hc', %Hn⟩
    ihave Hc' := csPts_weaken _ _ _ _ $$ Hc'
    iapply HΦ
    iunfold csOptA
    isplitr
    · iright; iright; iexact Hc
    isplitl
    · iright; ileft; iexact Hc'
    · ipureintro; intro _; exact Hn

/-- `CloneConfState` of a set conf state (`csSet`): a set, owned one. -/
theorem wp_clone_csSet (pc : Loc) (dq : DFrac) (c : ConfStateM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ csSet pc dq c }}
      (App (Val #(functions raftpb.CloneConfState [])) (Val #pc))
    {{ (pc' : Loc), RET #pc'; csSet pc dq c ∗ (csSet pc' (DFrac.own 1) c ∗ ⌜pc' ≠ null⌝) }} := by
  iintro %Φ ⟨#Hi, Hc⟩ HΦ
  iunfold csSet at Hc
  icases Hc with (Hc | #Hc)
  · iapply wp_CloneConfState_al pc dq c true $$ [$Hi $Hc]
    iintro %pc'
    inext
    iintro ⟨Hc, Hc'⟩
    icases csPts_nn _ _ _ _ $$ Hc' with ⟨Hc', %Hn⟩
    iapply HΦ
    iunfold csSet
    isplitl [Hc]
    · ileft; iexact Hc
    isplitl
    · ileft; iexact Hc'
    · ipureintro; exact Hn
  · iapply wp_CloneConfState_al pc DFrac.discard c true $$ [$Hi $Hc]
    iintro %pc'
    inext
    iintro ⟨-, Hc'⟩
    icases csPts_nn _ _ _ _ $$ Hc' with ⟨Hc', %Hn⟩
    iapply HΦ
    iunfold csSet
    isplitr
    · iright; iexact Hc
    isplitl
    · ileft; iexact Hc'
    · ipureintro; exact Hn

/-! ## The metadata's forms -/

/-- `cloneSnapshotMetadata` of a nested metadata (`smOpt`). -/
theorem wp_cloneSM_opt (m : Loc) (dq : DFrac) (md : SnapshotMetadataM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ smOpt m dq md }}
      (App (Val #(functions raftpb.cloneSnapshotMetadata [])) (Val #m))
    {{ (m' : Loc), RET #m'; smOpt m dq md ∗ smOpt m' (DFrac.own 1) md }} := by
  iintro %Φ ⟨#Hi, Hm⟩ HΦ
  iunfold smOpt at Hm
  icases Hm with (⟨%Hp, %Hmd⟩ | Hm)
  · subst Hp
    iapply wp_cloneSM_nil $$ [$Hi]
    inext
    iintro -
    iapply HΦ
    iunfold smOpt
    isplitl
    · ileft; ipureintro; exact ⟨rfl, Hmd⟩
    · ileft; ipureintro; exact ⟨rfl, Hmd⟩
  · iNamed Hm
    iapply wp_cloneSM m pc pi pt dq md uf _ _ (wp_clone_csOptA pc dq md.ConfState') Hnn
      $$ [$Hi $HC $Hc $HI $cI $HT $cT $Hpb]
    iintro %m'
    inext
    iintro ⟨HC, Hc, HI, HT, %pc', %pi', %pt', %Hn', HC', ⟨Hc', -⟩, HI', #cI', HT', #cT', #Hpb'⟩
    iapply HΦ
    iunfold smOpt
    isplitl [HC Hc HI HT]
    · iright
      iunfold smPts
      iexists pc, pi, pt, uf
      isplitr
      · ipureintro; exact Hnn
      iframe HC Hc HI HT cI cT Hpb
    · iright
      iunfold smPts
      iexists pc', pi', pt', uf
      isplitr
      · ipureintro; exact Hn'.1
      iframe HC' Hc' HI' HT' cI' cT' Hpb'

/-- `cloneSnapshotMetadata` of a metadata whose conf state is set (`smPtsW`). -/
theorem wp_cloneSM_W (m : Loc) (dq : DFrac) (md : SnapshotMetadataM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ smPtsW m dq md }}
      (App (Val #(functions raftpb.cloneSnapshotMetadata [])) (Val #m))
    {{ (m' : Loc), RET #m'; smPtsW m dq md ∗ smPtsW m' (DFrac.own 1) md }} := by
  iintro %Φ ⟨#Hi, Hm⟩ HΦ
  iNamed Hm
  iapply wp_cloneSM m pc pi pt dq md uf _ _ (wp_clone_csOptA pc dq md.ConfState') Hnn.1
    $$ [$Hi $HC $Hc $HI $cI $HT $cT $Hpb]
  iintro %m'
  inext
  iintro ⟨HC, Hc, HI, HT, %pc', %pi', %pt', %Hn', HC', ⟨Hc', %Hpc'⟩, HI', #cI', HT', #cT', #Hpb'⟩
  iapply HΦ
  isplitl [HC Hc HI HT]
  · iunfold smPtsW
    iexists pc, pi, pt, uf
    isplitr
    · ipureintro; exact Hnn
    iframe HC Hc HI HT cI cT Hpb
  · iunfold smPtsW
    iexists pc', pi', pt', uf
    isplitr
    · ipureintro; exact ⟨Hn'.1, Hpc' Hnn.2⟩
    iframe HC' Hc' HI' HT' cI' cT' Hpb'

/-- `cloneSnapshotMetadata` of a metadata with every pointer field set (`smPtsS`). -/
theorem wp_cloneSM_S (m : Loc) (dq : DFrac) (md : SnapshotMetadataM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ smPtsS m dq md }}
      (App (Val #(functions raftpb.cloneSnapshotMetadata [])) (Val #m))
    {{ (m' : Loc), RET #m'; smPtsS m dq md ∗ smPtsS m' (DFrac.own 1) md }} := by
  iintro %Φ ⟨#Hi, Hm⟩ HΦ
  iNamed Hm
  iapply wp_cloneSM m pc pi pt dq md uf _ _ (wp_clone_csSet pc dq md.ConfState') Hnn.1
    $$ [$Hi $HC $Hc $HI $cI $HT $cT $Hpb]
  iintro %m'
  inext
  iintro ⟨HC, Hc, HI, HT, %pc', %pi', %pt', %Hn', HC', ⟨Hc', %Hpc'⟩, HI', #cI', HT', #cT', #Hpb'⟩
  iapply HΦ
  isplitl [HC Hc HI HT]
  · iunfold smPtsS
    iexists pc, pi, pt, uf
    isplitr
    · ipureintro; exact Hnn
    iframe HC Hc HI HT cI cT Hpb
  · iunfold smPtsS
    iexists pc', pi', pt', uf
    isplitr
    · ipureintro; exact ⟨Hn'.1, Hpc', Hn'.2.1 Hnn.2.2.1, Hn'.2.2 Hnn.2.2.2⟩
    iframe HC' Hc' HI' HT' cI' cT' Hpb'

/-- `cloneSnapshotMetadata` of a metadata with its pointer fields set (`smPtsV`). -/
theorem wp_cloneSM_V (m : Loc) (dq : DFrac) (md : SnapshotMetadataM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ smPtsV m dq md }}
      (App (Val #(functions raftpb.cloneSnapshotMetadata [])) (Val #m))
    {{ (m' : Loc), RET #m'; smPtsV m dq md ∗ smPtsV m' (DFrac.own 1) md }} := by
  iintro %Φ ⟨#Hi, Hm⟩ HΦ
  iNamed Hm
  iapply wp_cloneSM m pc pi pt dq md uf _ _ (wp_clone_csOptA pc dq md.ConfState') Hnn.1
    $$ [$Hi $HC $Hc $HI $cI $HT $cT $Hpb]
  iintro %m'
  inext
  iintro ⟨HC, Hc, HI, HT, %pc', %pi', %pt', %Hn', HC', ⟨Hc', %Hpc'⟩, HI', #cI', HT', #cT', #Hpb'⟩
  iapply HΦ
  isplitl [HC Hc HI HT]
  · iunfold smPtsV
    iexists pc, pi, pt, uf
    isplitr
    · ipureintro; exact Hnn
    iframe HC Hc HI HT cI cT Hpb
  · iunfold smPtsV
    iexists pc', pi', pt', uf
    isplitr
    · ipureintro; exact ⟨Hn'.1, Hpc' Hnn.2.1, Hn'.2.1 Hnn.2.2.1, Hn'.2.2 Hnn.2.2.2⟩
    iframe HC' Hc' HI' HT' cI' cT' Hpb'

end lemmas

end EtcdGrove
end Perennial
