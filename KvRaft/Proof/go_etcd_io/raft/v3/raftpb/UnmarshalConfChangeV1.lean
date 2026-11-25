-- The copy for the part `KvRaft/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/raftpb/UnmarshalConfChangeV1.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Proof of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/UnmarshalConfChangeV1.lean`: the part's own (raft without
hand-written axioms, `notes/raft-noax-part.md`).
-/
module

public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.UnmarshalConfChangeV1
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.consumeVarint
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.consumeTag
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.consumeUnknown
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.consumeEnum
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.consumeBytes
public import KvRaft.Proof.go_etcd_io.raft.v3.raftpb.unmarshalConfChangeSingle

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

/-- A bytes field as a decoder leaves it: `nil`, or a fresh slice holding the bytes. -/
def ccOptBytesW (q : GoSlice) : Option (List w8) → IProp GF
  | none => iprop(⌜q = slice.nil⌝)
  | some v => iprop(q ↦* v)

theorem ccOptBytesW_persist (q : GoSlice) (o : Option (List w8)) (E : CoPset) :
    ccOptBytesW (GF := GF) q o ⊢ |={E}=> q ↦*□ o.getD [] := by
  cases o with
  | none =>
    simp only [ccOptBytesW, Option.getD_none]
    iintro %H
    subst H
    ihave Hn : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
    · iapply ownSlice_nil
    imod (ownSlice_persist _ _) $$ Hn with Hn
    imodintro; iexact Hn
  | some v =>
    simp only [ccOptBytesW, Option.getD_some]
    iintro H
    imod (ownSlice_persist _ _) $$ H with H
    imodintro; iexact H

theorem ccV1_combine (p : Loc) (hp : p ≠ null) (st : google_golang_org.protobuf.internal.impl.MessageState)
    (pt pn : Loc) (cs : GoSlice) (pi : Loc) (us : GoSlice) (sc : w32) :
    (p.[raftpb.ConfChange, go!"state"] ↦ st ∗ p.[raftpb.ConfChange, go!"Type"] ↦ pt ∗
      p.[raftpb.ConfChange, go!"NodeId"] ↦ pn ∗ p.[raftpb.ConfChange, go!"Context"] ↦ cs ∗
      p.[raftpb.ConfChange, go!"Id"] ↦ pi ∗ p.[raftpb.ConfChange, go!"unknownFields"] ↦ us ∗
      p.[raftpb.ConfChange, go!"sizeCache"] ↦ sc : IProp GF) ⊢
    ∃ x' : raftpb.ConfChange, p ↦ x' := by
  iintro ⟨H1, H2, H3, H4, H5, H6, H7⟩
  iexists raftpb.ConfChange.mk st pt pn cs pi us sc
  iapply typedPointsto_combine _ _ _ hp
  simp only [TypedPointsto.typedPointstoDef]
  iframe

theorem raftpb.UnmarshalConfChangeV1.wp_proof
    (wp_tag : raftpb.consumeTag.spec (GF := GF) (hG := hG))
    (wp_varint : raftpb.consumeVarint.spec (GF := GF) (hG := hG))
    (wp_enum : raftpb.consumeEnum.spec (GF := GF) (hG := hG))
    (wp_bytes : raftpb.consumeBytes.spec (GF := GF) (hG := hG))
    (wp_unknown : raftpb.consumeUnknown.spec (GF := GF) (hG := hG)) :
    raftpb.UnmarshalConfChangeV1.spec (GF := GF) (hG := hG) := by
  intro d bs dq p x
  wp_start as ⟨Hd, Hp⟩
  ihave #Hfact : iprop(∃ e : GoInterface,
      (globalAddr go_etcd_io.raft.v3.raftpb.errDecodeConfChange ↦□ e : IProp GF) ∗
      ⌜e ≠ interface.nil⌝) $$ []
  · iapply (isPkgInit_access (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb).trans sep_elim_right $$ Hpkg
  icases Hfact with ⟨%err, #Herr, %Herrn⟩
  ihave %Hlen := ownSlice_len $$ Hd
  ihave %Hpn := typedPointsto_not_null $$ Hp
  wp_auto
  icases typedPointsto_split _ _ _ $$ Hp with fields
  simp only [TypedPointsto.typedPointstoDef]
  icases fields with ⟨state, Type', NodeId, Context, Id, unknownFields, sizeCache, -⟩
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  ihave Hcap : ownSliceCap (GF := GF) w8 slice.nil (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  ihave IH : iprop(∃ (i : w64) (pt pn pi : Loc) (cs : GoSlice) (ot : Option w32) (onode oid : Option w64)
      (oc : Option (List w8)) (us : GoSlice) (uf : List w8),
      "i" ∷ i_ptr ↦ i ∗ "HT" ∷ p.[raftpb.ConfChange, go!"Type"] ↦ pt ∗
      "HN" ∷ p.[raftpb.ConfChange, go!"NodeId"] ↦ pn ∗ "HI" ∷ p.[raftpb.ConfChange, go!"Id"] ↦ pi ∗
      "HC" ∷ p.[raftpb.ConfChange, go!"Context"] ↦ cs ∗ "HU" ∷ p.[raftpb.ConfChange, go!"unknownFields"] ↦ us ∗
      "cT" ∷ ccOptCellW pt ot ∗ "cN" ∷ ccOptCellW pn onode ∗ "cI" ∷ ccOptCellW pi oid ∗
      "cC" ∷ ccOptBytesW cs oc ∗ "buf" ∷ us ↦* uf ∗ "cap" ∷ ownSliceCap w8 us (DFrac.own 1) ∗
      "%Hidx" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ bs.length⌝ ∗ "%Hwire" ∷ ⌜ufWire ccSchema uf⌝ ∗
      "%Hres" ∷ ⌜ccDecodeV1 bs = ccWireAt bs (ccV1Field bs) (sint.nat i)
        ⟨ot.getD (W32 0), onode.getD (W64 0), oc.getD [], oid.getD (W64 0)⟩⌝)
      $$ [i Type' NodeId Id Context unknownFields Hnil Hcap]
  · iexists W64 0, null, null, null, slice.nil, none, none, none, none, slice.nil, []
    simp only [ccOptCellW, ccOptBytesW]
    iframe
    ipureintro
    exact ⟨⟨by decide, by change (0:Int) ≤ _; omega⟩, .nil, rfl⟩
  irename «$res0» => resultErr
  wp_for_core
  icases IH with ⟨%i, %pt, %pn, %pi, %cs, %ot, %onode, %oid, %oc, %us, %uf,
    i, HT, HN, HI, HC, HU, cT, cN, cI, cC, buf, cap, %Hidx, %Hwire, %Hres⟩
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
      isplitr
      · ipureintro; exact Herrn
      iapply ccV1_combine p Hpn
      iframe
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
        wp_apply wp_varint d dq bs start hrange.1 hrange.2 $$ [$Hd] as %v %j %ok ⟨Hd, %Hv⟩
        rw [hkn] at Hv
        cases hval : ccVarintL bs k with
        | none =>
          rw [hval] at Hv
          subst Hv
          wp_auto
          wp_for_post
          iapply HΦ
          have hv : ccV1Field bs (uint.nat (W64 8)) k ⟨ot.getD (W32 0), onode.getD (W64 0), oc.getD [], oid.getD (W64 0)⟩ = none := by
            rw [htag8]; simp [ccV1Field, hval]
          rw [Hres, ccWireAt_bad_field _ ht hv]
          iframe
          isplitr
          · ipureintro; exact Herrn
          iapply ccV1_combine p Hpn
          iframe
        | some pair =>
          obtain ⟨v',endIdx⟩ := pair
          rw [hval] at Hv
          obtain ⟨rfl, rfl, hj⟩ := Hv
          have he := ccVarintL_bound hval
          have hjn : sint.nat j = endIdx := by word
          wp_auto
          wp_for_post
          iframe
          iexists j, pt, pn, _, cs, ot, onode, some v, oc, us, uf
          simp only [ccOptCellW]
          iframe
          ipureintro
          refine ⟨⟨by omega, by omega⟩, Hwire, ?_⟩
          rw [Hres, hjn]
          apply ccWireAt_step (ccV1Field_advance _) ht
          rw [htag8]; simp only [ccV1Field, hval]; rfl
      · have hnot8 : uint.nat tag ≠ 8 := by word
        wp_if_destruct
        · have htag16 : uint.nat (W64 16) = 16 := by word
          wp_apply wp_enum d dq bs start hrange.1 hrange.2 $$ [$Hd] as %v %j %ok ⟨Hd, %Hv⟩
          rw [hkn] at Hv
          cases hval : ccEnumL bs k with
          | none =>
            rw [hval] at Hv
            subst Hv
            wp_auto
            wp_for_post
            iapply HΦ
            have hv : ccV1Field bs (uint.nat (W64 16)) k ⟨ot.getD (W32 0), onode.getD (W64 0), oc.getD [], oid.getD (W64 0)⟩ = none := by
              rw [htag16]; simp [ccV1Field, hval]
            rw [Hres, ccWireAt_bad_field _ ht hv]
            iframe
            isplitr
            · ipureintro; exact Herrn
            iapply ccV1_combine p Hpn
            iframe
          | some pair =>
            obtain ⟨v',endIdx⟩ := pair
            rw [hval] at Hv
            obtain ⟨rfl, rfl, hj⟩ := Hv
            have he := ccEnumL_bound hval
            have hjn : sint.nat j = endIdx := by word
            wp_auto
            wp_for_post
            iframe
            iexists j, _, pn, pi, cs, some v, onode, oid, oc, us, uf
            simp only [ccOptCellW]
            iframe
            ipureintro
            refine ⟨⟨by omega, by omega⟩, Hwire, ?_⟩
            rw [Hres, hjn]
            apply ccWireAt_step (ccV1Field_advance _) ht
            rw [htag16]; simp only [ccV1Field, hval]; rfl
        · have hnot16 : uint.nat tag ≠ 16 := by word
          wp_if_destruct
          · have htag24 : uint.nat (W64 24) = 24 := by word
            wp_apply wp_varint d dq bs start hrange.1 hrange.2 $$ [$Hd] as %v %j %ok ⟨Hd, %Hv⟩
            rw [hkn] at Hv
            cases hval : ccVarintL bs k with
            | none =>
              rw [hval] at Hv
              subst Hv
              wp_auto
              wp_for_post
              iapply HΦ
              have hv : ccV1Field bs (uint.nat (W64 24)) k ⟨ot.getD (W32 0), onode.getD (W64 0), oc.getD [], oid.getD (W64 0)⟩ = none := by
                rw [htag24]; simp [ccV1Field, hval]
              rw [Hres, ccWireAt_bad_field _ ht hv]
              iframe
              isplitr
              · ipureintro; exact Herrn
              iapply ccV1_combine p Hpn
              iframe
            | some pair =>
              obtain ⟨v',endIdx⟩ := pair
              rw [hval] at Hv
              obtain ⟨rfl, rfl, hj⟩ := Hv
              have he := ccVarintL_bound hval
              have hjn : sint.nat j = endIdx := by word
              wp_auto
              wp_for_post
              iframe
              iexists j, pt, _, pi, cs, ot, some v, oid, oc, us, uf
              simp only [ccOptCellW]
              iframe
              ipureintro
              refine ⟨⟨by omega, by omega⟩, Hwire, ?_⟩
              rw [Hres, hjn]
              apply ccWireAt_step (ccV1Field_advance _) ht
              rw [htag24]; simp only [ccV1Field, hval]; rfl
          · have hnot24 : uint.nat tag ≠ 24 := by word
            wp_if_destruct
            · have htag34 : uint.nat (W64 34) = 34 := by word
              wp_apply wp_bytes d dq bs start hrange.1 hrange.2 $$ [$Hd] as %v %j %ok ⟨Hd, Hv⟩
              rw [hkn]
              cases hval : ccFieldL bs k with
              | none =>
                dsimp only
                icases Hv with %Hfailed
                subst Hfailed
                wp_auto
                wp_for_post
                iapply HΦ
                have hv : ccV1Field bs (uint.nat (W64 34)) k ⟨ot.getD (W32 0), onode.getD (W64 0), oc.getD [], oid.getD (W64 0)⟩ = none := by
                  rw [htag34]; simp [ccV1Field, hval]
                rw [Hres, ccWireAt_bad_field _ ht hv]
                iframe
                isplitr
                · ipureintro; exact Herrn
                iapply ccV1_combine p Hpn
                iframe
              | some pair =>
                obtain ⟨bytes,endIdx⟩ := pair
                dsimp only
                icases Hv with ⟨%Hok, Hv⟩
                obtain ⟨rfl, hj⟩ := Hok
                have he := ccFieldL_bound hval
                have hjn : sint.nat j = endIdx := by word
                wp_auto
                wp_for_post
                iframe
                iexists j, pt, pn, pi, _, ot, onode, oid, some bytes, us, uf
                simp only [ccOptBytesW]
                iframe
                ipureintro
                refine ⟨⟨by omega, by omega⟩, Hwire, ?_⟩
                rw [Hres, hjn]
                apply ccWireAt_step (ccV1Field_advance _) ht
                rw [htag34]; simp only [ccV1Field, hval]; rfl
            · have hnot34 : uint.nat tag ≠ 34 := by word
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
                have hv : ccV1Field bs (uint.nat tag) k ⟨ot.getD (W32 0), onode.getD (W64 0), oc.getD [], oid.getD (W64 0)⟩ = none := by
                  unfold ccV1Field; split <;> first | contradiction | simp [hs]
                rw [Hres, ccWireAt_bad_field _ ht hv]
                iframe
                isplitr
                · ipureintro; exact Herrn
                iapply ccV1_combine p Hpn
                iframe
              | some endIdx =>
                dsimp only
                icases Hfield with ⟨%Hok, buf⟩
                obtain ⟨rfl, hj⟩ := Hok
                have he := ccSkipField_bound hbound.2 hs
                have hjn : sint.nat j = endIdx := by word
                wp_auto
                wp_for_post
                iframe
                iexists j, pt, pn, pi, cs, ot, onode, oid, oc, out, _
                iframe
                ipureintro
                refine ⟨⟨by omega, by omega⟩, ccUnknown_valid Hwire ht hs ?_, ?_⟩
                · simp [Routed, ccSchema]; omega
                · rw [Hres, hjn]
                  apply ccWireAt_step (ccV1Field_advance _) ht
                  unfold ccV1Field; split <;> first | contradiction | simp [hs]
  · have hend : sint.nat i = bs.length := by word
    rw [hend, ccWireAt_end] at Hres
    simp only [decide_eq_false Hif, Bool.false_eq_true, ↓reduceIte]
    iapply wp_fupd
    imod ccOptCellW_persist pt ot ⊤ $$ cT with #cT
    imod ccOptCellW_persist pn onode ⊤ $$ cN with #cN
    imod ccOptCellW_persist pi oid ⊤ $$ cI with #cI
    imod ccOptBytesW_persist cs oc ⊤ $$ cC with #cC
    have hs : ufWire (pbSchemaOf raftpb.ConfChange.ty) uf := by
      simpa [pbSchemaOf, raftpb.Entry.ty, raftpb.Message.ty, raftpb.Snapshot.ty,
        raftpb.SnapshotMetadata.ty, raftpb.ConfState.ty, raftpb.HardState.ty,
        raftpb.ConfChange.ty] using Hwire
    imod pbMsg_alloc raftpb.ConfChange p _ _ us uf ⊤ hs $$ [state sizeCache HU buf] with #Hpb
    · iframe
    wp_auto
    iapply HΦ
    rw [Hres]
    iframe
    isplitr
    · ipureintro; rfl
    unfold ownConfChange
    iexists pt, pn, pi, cs, uf
    isplitr
    · ipureintro; exact Hpn
    ihave #HcT : (cellRO pt (ot.getD (W32 0)) : IProp GF) $$ [cT]
    · rw [show W32 0 = zero_val w32 from rfl]; iapply (nx_optCell_cellRO pt ot); iexact cT
    ihave #HcN : (cellRO pn (onode.getD (W64 0)) : IProp GF) $$ [cN]
    · rw [show W64 0 = zero_val w64 from rfl]; iapply (nx_optCell_cellRO pn onode); iexact cN
    ihave #HcI : (cellRO pi (oid.getD (W64 0)) : IProp GF) $$ [cI]
    · rw [show W64 0 = zero_val w64 from rfl]; iapply (nx_optCell_cellRO pi oid); iexact cI
    simp only
    iframe HT HN HI HC Hpb HcT HcN HcI cC
end proof
end EtcdGrove
end Perennial
