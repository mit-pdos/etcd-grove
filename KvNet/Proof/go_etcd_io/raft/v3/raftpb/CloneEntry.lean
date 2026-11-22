-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/raftpb/CloneEntry.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Proof of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/CloneEntry.lean`: the part's own (raft without
hand-written axioms, `notes/raft-noax-part.md`, "Stage 3a"). Each cell cloned into a fresh frozen
cell (`nil` stays `nil`), the data by `cloneBytes` (`nil` stays `nil`, any other slice a fresh
non-`nil` one: `bytesC`), the unknown fields by `cloneUnknown`, frozen with the new struct's other
hidden fields (`pbMsg_alloc`).
-/
module

public import KvNet.Proof.go_etcd_io.raft.v3.raftpb.CloneLeaf

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

/-- A fresh `*Entry` whose fields hold `c`'s cells, data and unknown fields is an owned entry
holding `c`. -/
private theorem entPtsCC_of_struct (l : Loc) (v : raftpb.Entry) (c : EntryC) (E : CoPset)
    (huf : ufWire (pbSchemaOf (PbGoType.goTy raftpb.Entry)) c.uf) :
    (l ↦ v ∗ optCell v.Term' c.term ∗ optCell v.Index' c.index ∗ optCell v.Type' c.type ∗
      bytesC v.Data' c.data ∗ v.unknownFields' ↦* c.uf : IProp GF) ⊢
      |={E}=> entPtsCC l (DFrac.own 1) c := by
  iintro ⟨Hl, #cT, #cI, #cY, #Hd, Hu⟩
  ihave %Hnn := typedPointsto_not_null $$ Hl
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨state, Term, Index, Ty, Data, unknownFields, sizeCache, -⟩
  imod pbMsg_alloc raftpb.Entry l v.state' v.sizeCache' v.unknownFields' c.uf E huf $$ [state sizeCache unknownFields Hu] with #Hpb
  · iframe
  imodintro
  iunfold entPtsCC
  iexists v.Term', v.Index', v.Type', v.Data'
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cT cI cY Hd Hpb

theorem raftpb.CloneEntry.wp_proof : raftpb.CloneEntry.spec (GF := GF) (hG := hG) := by
  intro l c
  wp_start as #He
  iunfold entRoC at He
  icases He with ⟨%pt, %pi, %pty, %ds, %Hnn, #HT, #cT, #HI, #cI, #HY, #cY, #HD, #Hd, #Hpb⟩
  ihave %Huf := pbMsg_ufWire _ _ _ $$ Hpb
  icases pbMsg_uf _ _ _ $$ Hpb with ⟨%us, #Hus, #Hub⟩
  ihave %Hpty := optCell_null _ _ $$ cY
  iapply wp_fupd
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  wp_apply wp_cloneUint64 pt c.term $$ [$cT] as %pt' #cT'
  wp_apply wp_cloneUint64 pi c.index $$ [$cI] as %pi' #cI'
  wp_if_destruct
  · have hty : c.type = none := Hpty.1 rfl
    ihave #cY' : optCell (GF := GF) (zero_val raftpb.Entry).Type' c.type $$ []
    · rw [hty]; simp only [optCell]; ipureintro; rfl
    wp_apply wp_cloneBytes_C ds c.data $$ [$Hd] as %ds' #Hd'
    wp_apply wp_cloneUnknown us c.uf $$ [$Hub] as %us' Hus'
    imod entPtsCC_of_struct «$r0_ptr» _ c ⊤ Huf $$ [«$r0» Hus'] with Hc'
    · iframe «$r0» Hus' cT' cI' cY' Hd'
    imodintro
    iapply HΦ
    iexact Hc'
  · obtain ⟨t, ht⟩ : ∃ t, c.type = some t := by
      cases h : c.type with
      | none => exact absurd (Hpty.2 h) Hif
      | some t => exact ⟨t, rfl⟩
    have e : optCell (GF := GF) pty c.type = iprop(pty ↦□ t) := by rw [ht]; rfl
    ihave #Ht : (pty ↦□ t : IProp GF) $$ []
    · rw [← e]; iexact cY
    wp_auto
    irename : («$r0_ptr» ↦ t : IProp GF) => Hty
    ipersist Hty
    ihave #cY' : optCell (GF := GF) «$r0_ptr» c.type $$ []
    · rw [ht]; simp only [optCell]; iexact Hty
    wp_apply wp_cloneBytes_C ds c.data $$ [$Hd] as %ds' #Hd'
    wp_apply wp_cloneUnknown us c.uf $$ [$Hub] as %us' Hus'
    imod entPtsCC_of_struct _ _ c ⊤ Huf $$ [«$r0» Hus'] with Hc'
    · iframe «$r0» Hus' cT' cI' cY' Hd'
    imodintro
    iapply HΦ
    iexact Hc'

end proof

end EtcdGrove
end Perennial
