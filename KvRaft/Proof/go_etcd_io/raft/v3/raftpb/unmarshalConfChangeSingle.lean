-- The copy for the part `KvRaft/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/raftpb/unmarshalConfChangeSingle.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Proof of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/unmarshalConfChangeSingle.lean`: the part's own (raft without
hand-written axioms, `notes/raft-noax-codec.md`).
-/
module

public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.unmarshalConfChangeSingle
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.consumeEnum
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.consumeVarint
public import KvRaft.Proof.go_etcd_io.raft.v3.raftpb.CloneLeaf
public import KvRaft.Proof.go_etcd_io.raft.v3.CCWireSound
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.consumeTag
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.consumeUnknown

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

/-- An optional field's cell as a decoder leaves it: `nil`, or a fresh pointer to the value. -/
def ccOptCellW {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc) : Option V → IProp GF
  | none => iprop(⌜p = null⌝)
  | some v => iprop(p ↦ v)

theorem ccOptCellW_persist {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc) (o : Option V)
    (E : CoPset) : ccOptCellW (GF := GF) p o ⊢ |={E}=> optCell p o := by
  cases o with
  | none => simp only [ccOptCellW, optCell]; iintro %H; imodintro; ipureintro; exact H
  | some v =>
    simp only [ccOptCellW, optCell]
    iintro H
    ipersist H
    imodintro; iexact H

theorem raftpb.unmarshalConfChangeSingle.wp_proof
    (wp_tag : raftpb.consumeTag.spec (GF := GF) (hG := hG))
    (wp_enum : raftpb.consumeEnum.spec (GF := GF) (hG := hG))
    (wp_varint : raftpb.consumeVarint.spec (GF := GF) (hG := hG))
    (wp_unknown : raftpb.consumeUnknown.spec (GF := GF) (hG := hG)) :
    raftpb.unmarshalConfChangeSingle.spec (GF := GF) (hG := hG) := by
  intro d dq bs
  wp_start as Hd
  ihave %Hlen := ownSlice_len $$ Hd
  wp_auto
  ihave %Hsn := typedPointsto_not_null $$ «$r0»
  icases typedPointsto_split _ _ _ $$ «$r0» with fields
  simp only [TypedPointsto.typedPointstoDef]
  icases fields with ⟨state, Type', NodeId, unknownFields, sizeCache, -⟩
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  ihave Hcap : ownSliceCap (GF := GF) w8 slice.nil (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  ihave IH : iprop(∃ (i : w64) (pt pn : Loc) (ot : Option w32) (onode : Option w64)
      (us : GoSlice) (uf : List w8),
      "i" ∷ i_ptr ↦ i ∗ "HT" ∷ «$r0_ptr».[raftpb.ConfChangeSingle, go!"Type"] ↦ pt ∗
      "HN" ∷ «$r0_ptr».[raftpb.ConfChangeSingle, go!"NodeId"] ↦ pn ∗
      "HU" ∷ «$r0_ptr».[raftpb.ConfChangeSingle, go!"unknownFields"] ↦ us ∗
      "cT" ∷ ccOptCellW pt ot ∗ "cN" ∷ ccOptCellW pn onode ∗
      "buf" ∷ us ↦* uf ∗ "cap" ∷ ownSliceCap w8 us (DFrac.own 1) ∗
      "%Hidx" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ bs.length⌝ ∗ "%Hwire" ∷ ⌜ufWire ccsSchema uf⌝ ∗
      "%Hres" ∷ ⌜ccWireSingle bs = ccWireAt bs (ccSingleField bs) (sint.nat i)
        ⟨ot.getD (W32 0), onode.getD (W64 0)⟩⌝) $$ [i Type' NodeId unknownFields Hnil Hcap]
  · iexists W64 0, null, null, none, none, slice.nil, []
    simp only [ccOptCellW]
    iframe
    ipureintro
    exact ⟨⟨by decide, by change (0:Int) ≤ _; omega⟩, .nil, rfl⟩
  irename «$res0» => resultPtr
  irename «$res1» => resultOK
  wp_for_core
  icases IH with ⟨%i, %pt, %pn, %ot, %onode, %us, %uf, i, HT, HN, HU, cT, cN, buf, cap, %Hidx, %Hwire, %Hres⟩
  try wp_auto
  cleanup_bool_decide
  try wp_auto
  by_cases Hif : sint.Z i < sint.Z d.len
  · simp only [decide_eq_true Hif, ↓reduceIte]
    wp_auto
    have hi : sint.nat i < bs.length := by word
    wp_apply wp_tag d dq bs i Hidx.1 Hidx.2 $$ [$Hd] as %tag %start %ok ⟨Hd, %Hr⟩
    cases ht : ccTagL bs (sint.nat i) (2^29-1) with
    | none =>
      rw [ht] at Hr
      subst Hr
      wp_auto
      wp_for_post
      iapply HΦ
      rw [Hres, ccWireAt_no_tag _ _ hi ht]
      iframe
      ipureintro; rfl
    | some ts =>
      obtain ⟨t,k⟩ := ts
      rw [ht] at Hr
      obtain ⟨rfl, rfl, hk⟩ := Hr
      have hbound := ccTagL_bound ht
      have hkn : sint.nat start = k := by word
      have hrange : 0 ≤ sint.Z start ∧ sint.Z start ≤ bs.length := by omega
      wp_auto
      wp_if_destruct
      · have htag8 : uint.nat (W64 8) = 8 := by word
        wp_apply wp_enum d dq bs start hrange.1 hrange.2 $$ [$Hd] as %v %j %ok ⟨Hd, %Hv⟩
        rw [hkn] at Hv
        cases hval : ccEnumL bs k with
        | none =>
          rw [hval] at Hv
          subst Hv
          wp_auto
          wp_for_post
          iapply HΦ
          have hv : ccSingleField bs (uint.nat (W64 8)) k ⟨ot.getD (W32 0), onode.getD (W64 0)⟩ = none := by
            rw [htag8]; simp [ccSingleField, hval]
          rw [Hres, ccWireAt_bad_field _ ht hv]
          iframe
          ipureintro; rfl
        | some pair =>
          obtain ⟨v',endIdx⟩ := pair
          rw [hval] at Hv
          obtain ⟨rfl, rfl, hj⟩ := Hv
          have he := ccEnumL_bound hval
          have hjn : sint.nat j = endIdx := by word
          wp_auto
          wp_for_post
          iframe
          iexists j, _, pn, some v, onode, us, uf
          simp only [ccOptCellW]
          iframe
          ipureintro
          refine ⟨⟨by omega, by omega⟩, Hwire, ?_⟩
          rw [Hres, hjn]
          apply ccWireAt_step (ccSingleField_advance _) ht
          rw [htag8]; simp only [ccSingleField, hval]; rfl
      · have hnot8 : uint.nat tag ≠ 8 := by word
        wp_if_destruct
        · have htag16 : uint.nat (W64 16) = 16 := by word
          wp_apply wp_varint d dq bs start hrange.1 hrange.2 $$ [$Hd] as %v %j %ok ⟨Hd, %Hv⟩
          rw [hkn] at Hv
          cases hval : ccVarintL bs k with
          | none =>
            rw [hval] at Hv
            subst Hv
            wp_auto
            wp_for_post
            iapply HΦ
            have hv : ccSingleField bs (uint.nat (W64 16)) k ⟨ot.getD (W32 0), onode.getD (W64 0)⟩ = none := by
              rw [htag16]; simp [ccSingleField, hval]
            rw [Hres, ccWireAt_bad_field _ ht hv]
            iframe
            ipureintro; rfl
          | some pair =>
            obtain ⟨v',endIdx⟩ := pair
            rw [hval] at Hv
            obtain ⟨rfl, rfl, hj⟩ := Hv
            have he := ccVarintL_bound hval
            have hjn : sint.nat j = endIdx := by word
            wp_auto
            wp_for_post
            iframe
            iexists j, pt, _, ot, some v, us, uf
            simp only [ccOptCellW]
            iframe
            ipureintro
            refine ⟨⟨by omega, by omega⟩, Hwire, ?_⟩
            rw [Hres, hjn]
            apply ccWireAt_step (ccSingleField_advance _) ht
            rw [htag16]; simp only [ccSingleField, hval]; rfl
        · have hnot16 : uint.nat tag ≠ 16 := by word
          wp_apply wp_unknown d dq bs start tag us uf hrange.1 hrange.2 $$ [$Hd $buf $cap]
            as %out %j %ok ⟨Hd, cap, Hfield⟩
          rw [hkn]
          cases hs : ccSkipField bs k (uint.nat tag) with
          | none =>
            dsimp only
            icases Hfield with ⟨%Hfail, buf⟩
            obtain ⟨rfl, rfl, rfl⟩ := Hfail
            wp_auto
            wp_for_post
            iapply HΦ
            have hv : ccSingleField bs (uint.nat tag) k ⟨ot.getD (W32 0), onode.getD (W64 0)⟩ = none := by
              unfold ccSingleField; split <;> first | contradiction | simp [hs]
            rw [Hres, ccWireAt_bad_field _ ht hv]
            iframe
            ipureintro; rfl
          | some endIdx =>
            dsimp only
            icases Hfield with ⟨%Hok, buf⟩
            obtain ⟨rfl, hj⟩ := Hok
            have he := ccSkipField_bound hbound.2 hs
            have hjn : sint.nat j = endIdx := by word
            wp_auto
            wp_for_post
            iframe
            iexists j, pt, pn, ot, onode, out, _
            iframe
            ipureintro
            refine ⟨⟨by omega, by omega⟩, ccUnknown_valid Hwire ht hs ?_, ?_⟩
            · simp [Routed, ccsSchema]; omega
            · rw [Hres, hjn]
              apply ccWireAt_step (ccSingleField_advance _) ht
              unfold ccSingleField; split <;> first | contradiction | simp [hs]
  · have hend : sint.nat i = bs.length := by word
    rw [hend, ccWireAt_end] at Hres
    simp only [decide_eq_false Hif, Bool.false_eq_true, ↓reduceIte]
    iapply wp_fupd
    imod ccOptCellW_persist pt ot ⊤ $$ cT with #cT
    imod ccOptCellW_persist pn onode ⊤ $$ cN with #cN
    ipersist HT
    ipersist HN
    have hs : ufWire (pbSchemaOf raftpb.ConfChangeSingle.ty) uf := by
      simpa [pbSchemaOf, raftpb.Entry.ty, raftpb.Message.ty, raftpb.Snapshot.ty,
        raftpb.SnapshotMetadata.ty, raftpb.ConfState.ty, raftpb.HardState.ty,
        raftpb.ConfChange.ty, raftpb.ConfChangeSingle.ty] using Hwire
    imod pbMsg_alloc raftpb.ConfChangeSingle «$r0_ptr» _ _ us uf ⊤ hs $$ [state sizeCache HU buf] with #Hpb
    · iframe
    wp_auto
    iapply HΦ
    rw [Hres]
    iframe
    isplitr
    · ipureintro; rfl
    unfold ccsRO ccsPts
    iexists pt, pn, uf
    isplitr
    · ipureintro; exact Hsn
    ihave #HcT : (cellRO pt (ot.getD (W32 0)) : IProp GF) $$ [cT]
    · rw [show W32 0 = zero_val w32 from rfl]; iapply (nx_optCell_cellRO pt ot); iexact cT
    ihave #HcN : (cellRO pn (onode.getD (W64 0)) : IProp GF) $$ [cN]
    · rw [show W64 0 = zero_val w64 from rfl]; iapply (nx_optCell_cellRO pn onode); iexact cN
    simp only
    iframe HT HN Hpb HcT HcN
end proof
end EtcdGrove
end Perennial
