-- The copy for the part `KvRaft/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/raftpb/MarshalConfChangeV1.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Proof of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/MarshalConfChangeV1.lean`: the part's own (raft without
hand-written axioms, `notes/raft-noax-part.md`).
-/
module

public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.MarshalConfChangeV1
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.appendVarint
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.appendEnum
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.appendBytes
public import KvRaft.Proof.go_etcd_io.raft.v3.CCCodecLen
public import KvRaft.Proof.go_etcd_io.raft.v3.CCWireRoundtrip

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

theorem raftpb.MarshalConfChangeV1.wp_proof
    (wp_appendVarint : raftpb.appendVarint.spec (GF := GF) (hG := hG))
    (wp_appendEnum : raftpb.appendEnum.spec (GF := GF) (hG := hG))
    (wp_appendBytes : raftpb.appendBytes.spec (GF := GF) (hG := hG)) :
    raftpb.MarshalConfChangeV1.spec (GF := GF) (hG := hG) := by
  intro p dq m uf
  wp_start as Hc
  simp only [ccPtsCC]
  icases Hc with ⟨%p', %pt, %pn, %pi, %cs, %Hc, HT, #cT, HN, #cN, HI, #cI, HC, #Hcs, #Hpb⟩
  obtain ⟨Hc, Hnn⟩ := Hc
  have hp : p' = p := by simp at Hc; exact (GoGlobalContext.intoVal_inj_loc Hc).symm
  subst hp
  ihave %Hcl := ownSlice_len $$ Hcs
  ihave #Hsaved : pbMsg raftpb.ConfChange p' uf $$ []
  · iexact Hpb
  iunfold pbMsg at Hpb
  icases Hpb with ⟨⟨%st, %sc, %us, #Hst, #Hsc, #Hus, #Huf⟩, %Hwire⟩
  have Hschema : ufWire ccSchema uf := by
    change ufWire (pbSchemaOf raftpb.ConfChange.ty) uf at Hwire
    simpa [pbSchemaOf, raftpb.Entry.ty, raftpb.Message.ty, raftpb.Snapshot.ty,
      raftpb.SnapshotMetadata.ty, raftpb.ConfState.ty, raftpb.HardState.ty,
      raftpb.ConfChange.ty] using Hwire
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_slice_literal (V := w8) []
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, Hcap⟩
  wp_auto
  wp_join iprop(∃ (cur : GoSlice) (o1 : Option w64), "c" ∷ c_ptr ↦ p' ∗ "b" ∷ b_ptr ↦ cur ∗
      "Hb" ∷ cur ↦* (ccEncOpt (W8 8) ccVarint o1) ∗ "Hcap" ∷ ownSliceCap w8 cur (DFrac.own 1) ∗
      "HI" ∷ p'.[raftpb.ConfChange, go!"Id"] ↦{dq} pi ∗
      "%Ho1" ∷ ⌜o1.getD (W64 0) = m.id⌝) with [c b Hsl Hcap HI] as ⟨%cur1, %o1, c, b, Hb, Hcap, HI, %Ho1⟩
  · icases cellRO_cases null m.id $$ cI with (%Hz | ⟨-, %Hn⟩)
    · iexists _, none
      simp only [ccEncOpt]
      iframe
      ipureintro; exact Hz.2.symm
    · exact absurd rfl Hn
  · icases cellRO_cases pi m.id $$ cI with (%Hz | ⟨#Hp, %Hn⟩)
    · exact absurd Hz.1 Hif
    wp_apply wp_slice_literal (V := w8) [_]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl2] as %b2 ⟨Hb2, Hcap, -⟩
    wp_apply wp_appendVarint $$ [$Hb2 $Hcap] as %b3 ⟨Hb3, Hcap⟩
    wp_join_done
    iexists b3, some m.id
    simp only [ccEncOpt, List.append_assoc, List.singleton_append]
    iframe
    ipureintro; rfl
  wp_join iprop(∃ (cur : GoSlice) (o2 : Option w32), "c" ∷ c_ptr ↦ p' ∗ "b" ∷ b_ptr ↦ cur ∗
      "Hb" ∷ cur ↦* (ccEncOpt (W8 8) ccVarint o1 ++ ccEncOpt (W8 16) ccEnumEnc o2) ∗ "Hcap" ∷ ownSliceCap w8 cur (DFrac.own 1) ∗
      "HT" ∷ p'.[raftpb.ConfChange, go!"Type"] ↦{dq} pt ∗
      "%Ho2" ∷ ⌜o2.getD (W32 0) = m.type⌝) with [c b Hb Hcap HT] as ⟨%cur2, %o2, c, b, Hb, Hcap, HT, %Ho2⟩
  · icases cellRO_cases null m.type $$ cT with (%Hz | ⟨-, %Hn⟩)
    · iexists _, none
      simp only [ccEncOpt, List.append_nil]
      iframe
      ipureintro; exact Hz.2.symm
    · exact absurd rfl Hn
  · icases cellRO_cases pt m.type $$ cT with (%Hz | ⟨#Hp, %Hn⟩)
    · exact absurd Hz.1 Hif
    wp_apply wp_slice_literal (V := w8) [_]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl2] as %b2 ⟨Hb2, Hcap, -⟩
    wp_apply wp_appendEnum $$ [$Hb2 $Hcap] as %b3 ⟨Hb3, Hcap⟩
    wp_join_done
    iexists b3, some m.type
    simp only [ccEncOpt, List.append_assoc, List.singleton_append]
    iframe
    ipureintro; rfl
  wp_join iprop(∃ (cur : GoSlice) (o3 : Option w64), "c" ∷ c_ptr ↦ p' ∗ "b" ∷ b_ptr ↦ cur ∗
      "Hb" ∷ cur ↦* (ccEncOpt (W8 8) ccVarint o1 ++ ccEncOpt (W8 16) ccEnumEnc o2 ++ ccEncOpt (W8 24) ccVarint o3) ∗ "Hcap" ∷ ownSliceCap w8 cur (DFrac.own 1) ∗
      "HN" ∷ p'.[raftpb.ConfChange, go!"NodeId"] ↦{dq} pn ∗
      "%Ho3" ∷ ⌜o3.getD (W64 0) = m.nodeId⌝) with [c b Hb Hcap HN] as ⟨%cur3, %o3, c, b, Hb, Hcap, HN, %Ho3⟩
  · icases cellRO_cases null m.nodeId $$ cN with (%Hz | ⟨-, %Hn⟩)
    · iexists _, none
      simp only [ccEncOpt, List.append_nil]
      iframe
      ipureintro; exact Hz.2.symm
    · exact absurd rfl Hn
  · icases cellRO_cases pn m.nodeId $$ cN with (%Hz | ⟨#Hp, %Hn⟩)
    · exact absurd Hz.1 Hif
    wp_apply wp_slice_literal (V := w8) [_]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl2] as %b2 ⟨Hb2, Hcap, -⟩
    wp_apply wp_appendVarint $$ [$Hb2 $Hcap] as %b3 ⟨Hb3, Hcap⟩
    wp_join_done
    iexists b3, some m.nodeId
    simp only [ccEncOpt, List.append_assoc, List.singleton_append]
    iframe
    ipureintro; rfl
  wp_join iprop(∃ (cur : GoSlice) (o4 : Option (List w8)), "c" ∷ c_ptr ↦ p' ∗ "b" ∷ b_ptr ↦ cur ∗
      "Hb" ∷ cur ↦* (ccEncOpt (W8 8) ccVarint o1 ++ ccEncOpt (W8 16) ccEnumEnc o2 ++ ccEncOpt (W8 24) ccVarint o3 ++ ccEncOpt (W8 34) ccBytesEnc o4) ∗
      "Hcap" ∷ ownSliceCap w8 cur (DFrac.own 1) ∗ "HC" ∷ p'.[raftpb.ConfChange, go!"Context"] ↦{dq} cs ∗
      "%Ho4" ∷ ⌜o4.getD [] = m.context ∧ ∀ x, o4 = some x → x.length < 2 ^ 64⌝) with [c b Hb Hcap HC]
      as ⟨%cur4, %o4, c, b, Hb, Hcap, HC, %Ho4⟩
  · iexists _, none
    simp only [ccEncOpt, List.append_nil]
    iframe
    ipureintro
    refine ⟨?_, fun _ h => by cases h⟩
    have : sint.nat (slice.nil : GoSlice).len = 0 := rfl
    simp only [Option.getD_none]
    exact (List.eq_nil_of_length_eq_zero (by omega)).symm
  · wp_apply wp_slice_literal (V := w8) [_]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl2] as %b2 ⟨Hb2, Hcap, -⟩
    wp_apply wp_appendBytes $$ [$Hb2 $Hcap $Hcs] as %b3 ⟨Hb3, Hcap, -⟩
    wp_join_done
    iexists b3, some m.context
    simp only [ccEncOpt, List.append_assoc, List.singleton_append]
    iframe
    ipureintro
    refine ⟨rfl, fun x h => ?_⟩
    cases h
    have : sint.nat cs.len < 2 ^ 64 := by word
    omega
  wp_apply wp_slice_append $$ [$Hb $Hcap $Huf] as %out ⟨Hout, -, -⟩
  iapply HΦ
  iframe
  have hm : m = ⟨o2.getD (W32 0), o3.getD (W64 0), o4.getD [], o1.getD (W64 0)⟩ := by
    cases m; simp only at Ho1 Ho2 Ho3 Ho4; rw [Ho1, Ho2, Ho3, Ho4.1]
  isplitl
  · iframe cT cN cI Hcs Hsaved
    ipureintro; exact ⟨rfl, Hnn⟩
  ipureintro
  refine ⟨?_, ?_⟩
  · rw [hm]; exact ccWireV1_enc o1 o2 o3 o4 Ho4.2 uf Hschema
  · intro _
    rw [hm]
    exact ccEncodeV1_length_le o1 o2 o3 o4 Ho4.2 uf


end proof

end EtcdGrove
end Perennial
