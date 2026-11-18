/-
`cloneSnapshotMetadata` (`raftpb/noax.go`), for `CloneSnapshot`'s proof: the core (the fields of a
non-`nil` metadata, its conf state's clone abstracted as a triple `R`/`Q`), the conf state's two
forms (`csOptA`, `csSet`), and the four metadata forms the snapshot predicates use (`smOpt`,
`smPtsW`, `smPtsS`, `smPtsV`). The part's own (raft without hand-written axioms,
`notes/raft-noax-part.md`, "Stage 3a").
-/
module

public import RaftNoAx.Proof.go_etcd_io.raft.v3.raftpb.CloneCS
public import RaftNoAx.Spec.go_etcd_io.raft.v3.raftpb.CloneSnapshot

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
  icases cellRO_optCell _ _ $$ Hc with ⟨%o, #Ho, %Hv⟩
  ihave %Hn := optCell_null _ _ $$ Ho
  iapply wp_cloneUint64 p o $$ [$Hi $Ho]
  iintro %p'
  inext
  iintro #Ho'
  ihave %Hn' := optCell_null _ _ $$ Ho'
  iapply HΦ
  isplitl
  · rw [Hv]; iapply optCell_cellRO; iexact Ho'
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

end lemmas

end EtcdGrove
end Perennial
