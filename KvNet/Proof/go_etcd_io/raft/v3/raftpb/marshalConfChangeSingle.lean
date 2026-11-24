-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/raftpb/marshalConfChangeSingle.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Proof of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/marshalConfChangeSingle.lean`: the part's own (raft without
hand-written axioms, `notes/raft-noax-codec.md`).
-/
module

public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.marshalConfChangeSingle
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.appendEnum
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.appendVarint

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

theorem raftpb.marshalConfChangeSingle.wp_proof
    (wp_appendEnum : raftpb.appendEnum.spec (GF := GF) (hG := hG))
    (wp_appendVarint : raftpb.appendVarint.spec (GF := GF) (hG := hG)) :
    raftpb.marshalConfChangeSingle.spec (GF := GF) (hG := hG) := by
  intro p c uf
  wp_start as Hc
  iunfold ccsRoC at Hc
  icases Hc with ⟨%pt, %pn, %Hnn, #HT, #cT, #HN, #cN, #Hpb⟩
  iunfold pbMsg at Hpb
  icases Hpb with ⟨⟨%st, %sc, %us, -, -, #Hus, #Huf⟩, %Hwire⟩
  have Hschema : ufWire ccsSchema uf := by
    change ufWire (pbSchemaOf raftpb.ConfChangeSingle.ty) uf at Hwire
    simpa [pbSchemaOf, raftpb.Entry.ty, raftpb.Message.ty, raftpb.Snapshot.ty,
      raftpb.SnapshotMetadata.ty, raftpb.ConfState.ty, raftpb.HardState.ty,
      raftpb.ConfChange.ty, raftpb.ConfChangeSingle.ty] using Hwire
  wp_auto
  wp_apply wp_slice_literal (V := w8) []
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, Hcap⟩
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_join iprop(∃ (cur : GoSlice) (o1 : Option w32), "s" ∷ s_ptr ↦ p ∗ "b" ∷ b_ptr ↦ cur ∗
      "Hb" ∷ cur ↦* ccEncOpt (W8 8) ccEnumEnc o1 ∗ "Hcap" ∷ ownSliceCap w8 cur (DFrac.own 1) ∗
      "%Ho1" ∷ ⌜o1.getD (W32 0) = c.Type'⌝) with [s b Hsl Hcap] as ⟨%cur, %o1, s, b, Hb, Hcap, %Ho1⟩
  · icases cellRO_cases null c.Type' $$ cT with (%Hz | ⟨-, %Hn⟩)
    · iexists _, none
      simp only [ccEncOpt]
      iframe
      ipureintro; exact Hz.2.symm
    · exact absurd rfl Hn
  · icases cellRO_cases pt c.Type' $$ cT with (%Hz | ⟨#Hpt, %Hn⟩)
    · exact absurd Hz.1 Hif
    wp_apply wp_slice_literal (V := w8) [_]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl2] as %b2 ⟨Hb2, Hcap, -⟩
    wp_apply wp_appendEnum $$ [$Hb2 $Hcap] as %b3 ⟨Hb3, Hcap⟩
    wp_join_done
    iexists b3, some c.Type'
    iframe
    ipureintro; rfl
  wp_join iprop(∃ (cur2 : GoSlice) (o2 : Option w64), "b" ∷ b_ptr ↦ cur2 ∗
      "s" ∷ s_ptr ↦ p ∗ "Hcap" ∷ ownSliceCap w8 cur2 (DFrac.own 1) ∗ "Hb" ∷ cur2 ↦* (ccEncOpt (W8 8) ccEnumEnc o1 ++ ccEncOpt (W8 16) ccVarint o2) ∗
      "%Ho2" ∷ ⌜o2.getD (W64 0) = c.NodeId'⌝) with [s b Hb Hcap] as ⟨%cur2, %o2, b, s, Hcap, Hb, %Ho2⟩
  · icases cellRO_cases null c.NodeId' $$ cN with (%Hz | ⟨-, %Hn⟩)
    · iexists _, none
      simp only [ccEncOpt, List.append_nil]
      iframe
      ipureintro; exact Hz.2.symm
    · exact absurd rfl Hn
  · icases cellRO_cases pn c.NodeId' $$ cN with (%Hz | ⟨#Hpn, %Hn⟩)
    · exact absurd Hz.1 Hif
    wp_apply wp_slice_literal (V := w8) [_]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl2] as %b2 ⟨Hb2, Hcap, -⟩
    wp_apply wp_appendVarint $$ [$Hb2 $Hcap] as %b3 ⟨Hb3, Hcap⟩
    wp_join_done
    iexists b3, some c.NodeId'
    simp only [ccEncOpt, List.append_assoc, List.singleton_append]
    iframe
    ipureintro; rfl
  wp_apply wp_slice_append $$ [$Hb $Hcap $Huf] as %out ⟨Hout, -, -⟩
  iapply HΦ
  iframe
  ipureintro
  exact ⟨_, ⟨o1, o2, rfl, Ho1, Ho2⟩, rfl, Hschema⟩

end proof

end EtcdGrove
end Perennial
