-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/raftpb/UnmarshalConfChangeV2.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Proof of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/UnmarshalConfChangeV2.lean`: the part's own (raft without
hand-written axioms, `notes/raft-noax-part.md`).
-/
module

public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.UnmarshalConfChangeV2
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.consumeEnum
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.consumeField
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.consumeBytes
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.unmarshalConfChangeSingle
public import KvNet.Proof.go_etcd_io.raft.v3.raftpb.UnmarshalConfChangeV1

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

theorem ccV2_combine (p : Loc) (hp : p ≠ null) (st : google_golang_org.protobuf.internal.impl.MessageState)
    (pt : Loc) (chs cs us : GoSlice) (sc : w32) :
    (p.[raftpb.ConfChangeV2, go!"state"] ↦ st ∗ p.[raftpb.ConfChangeV2, go!"Transition"] ↦ pt ∗
      p.[raftpb.ConfChangeV2, go!"Changes"] ↦ chs ∗ p.[raftpb.ConfChangeV2, go!"Context"] ↦ cs ∗
      p.[raftpb.ConfChangeV2, go!"unknownFields"] ↦ us ∗
      p.[raftpb.ConfChangeV2, go!"sizeCache"] ↦ sc : IProp GF) ⊢
    ∃ x' : raftpb.ConfChangeV2, p ↦ x' := by
  iintro ⟨H1, H2, H3, H4, H5, H6⟩
  iexists raftpb.ConfChangeV2.mk st pt chs cs us sc
  iapply typedPointsto_combine _ _ _ hp
  simp only [TypedPointsto.typedPointstoDef]
  iframe

theorem raftpb.UnmarshalConfChangeV2.wp_proof
    (wp_tag : raftpb.consumeTag.spec (GF := GF) (hG := hG))
    (wp_enum : raftpb.consumeEnum.spec (GF := GF) (hG := hG))
    (wp_field : raftpb.consumeField.spec (GF := GF) (hG := hG))
    (wp_single : raftpb.unmarshalConfChangeSingle.spec (GF := GF) (hG := hG))
    (wp_bytes : raftpb.consumeBytes.spec (GF := GF) (hG := hG))
    (wp_unknown : raftpb.consumeUnknown.spec (GF := GF) (hG := hG)) :
    raftpb.UnmarshalConfChangeV2.spec (GF := GF) (hG := hG) := by
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
  icases fields with ⟨state, Transition, Changes, Context, unknownFields, sizeCache, -⟩
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  ihave Hcap : ownSliceCap (GF := GF) w8 slice.nil (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  ihave HnilCh : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
  · iapply ownSlice_nil
  ihave HcapCh : ownSliceCap (GF := GF) Loc slice.nil (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  ihave IH : iprop(∃ (i : w64) (pt : Loc) (sv cs : GoSlice) (ot : Option w32) (ls : List Loc)
      (acc : List ConfChangeSingleM) (oc : Option (List w8)) (us : GoSlice) (uf : List w8),
      "i" ∷ i_ptr ↦ i ∗ "HT" ∷ p.[raftpb.ConfChangeV2, go!"Transition"] ↦ pt ∗
      "HCh" ∷ p.[raftpb.ConfChangeV2, go!"Changes"] ↦ sv ∗ "HC" ∷ p.[raftpb.ConfChangeV2, go!"Context"] ↦ cs ∗
      "HU" ∷ p.[raftpb.ConfChangeV2, go!"unknownFields"] ↦ us ∗ "cT" ∷ ccOptCellW pt ot ∗
      "chbuf" ∷ sv ↦* ls ∗ "chcap" ∷ ownSliceCap Loc sv (DFrac.own 1) ∗ "#Hls" ∷ ([∗list] q;cc ∈ ls;acc, ccsRO q cc) ∗
      "cC" ∷ ccOptBytesW cs oc ∗ "buf" ∷ us ↦* uf ∗ "cap" ∷ ownSliceCap w8 us (DFrac.own 1) ∗
      "%Hidx" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ bs.length⌝ ∗ "%Hwire" ∷ ⌜ufWire cc2Schema uf⌝ ∗
      "%Hres" ∷ ⌜ccDecodeV2 bs = ccWireAt bs (ccV2Field bs) (sint.nat i)
        ⟨ot.getD (W32 0), acc, oc.getD []⟩⌝) $$ [i Transition Changes Context unknownFields Hnil Hcap HnilCh HcapCh]
  · iexists W64 0, null, slice.nil, slice.nil, none, [], [], none, slice.nil, []
    simp only [ccOptCellW, ccOptBytesW]
    iframe
    isplitr
    · iapply BigSepL2.bigSepL2_nil.2; iempintro
    ipureintro
    exact ⟨⟨by decide, by change (0:Int) ≤ _; omega⟩, .nil, rfl⟩
  irename «$res0» => resultErr
  wp_for_core
  icases IH with ⟨%i, %pt, %sv, %cs, %ot, %ls, %acc, %oc, %us, %uf,
    i, HT, HCh, HC, HU, cT, chbuf, chcap, #Hls, cC, buf, cap, %Hidx, %Hwire, %Hres⟩
  try wp_auto
  cleanup_bool_decide
  try wp_auto
  by_cases Hif : sint.Z i < sint.Z d.len
  · simp only [decide_eq_true Hif, ↓reduceIte]
    try simp only [decide_true, ↓reduceIte]
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
      iapply ccV2_combine p Hpn
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
        wp_apply wp_enum d dq bs start hrange.1 hrange.2 $$ [$Hd] as %v %j %ok ⟨Hd, %Hv⟩
        rw [hkn] at Hv
        cases hval : ccEnumL bs k with
        | none =>
          rw [hval] at Hv
          subst Hv
          wp_auto
          wp_for_post
          iapply HΦ
          have hv : ccV2Field bs (uint.nat (W64 8)) k ⟨ot.getD (W32 0), acc, oc.getD []⟩ = none := by
            rw [htag8]; simp [ccV2Field, hval]
          rw [Hres, ccWireAt_bad_field _ ht hv]
          iframe
          isplitr
          · ipureintro; exact Herrn
          iapply ccV2_combine p Hpn
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
          iexists j, _, sv, cs, some v, ls, acc, oc, us, uf
          simp only [ccOptCellW]
          iframe Hls
          iframe
          ipureintro
          refine ⟨⟨by omega, by omega⟩, Hwire, ?_⟩
          rw [Hres, hjn]
          apply ccWireAt_step (ccV2Field_advance _) ht
          rw [htag8]; simp only [ccV2Field, hval]; rfl
      · have hnot8 : uint.nat tag ≠ 8 := by word
        wp_if_destruct
        · have htag18 : uint.nat (W64 18) = 18 := rfl
          wp_apply wp_field d dq bs start hrange.1 hrange.2 $$ [$Hd] as %v %j %ok Hr
          rw [hkn]
          cases he : ccFieldL bs k with
          | none =>
            dsimp only
            icases Hr with ⟨%Hfail, Hd⟩
            subst Hfail
            wp_auto
            wp_for_post
            iapply HΦ
            have hv : ccV2Field bs 18 k ⟨ot.getD (W32 0), acc, oc.getD []⟩ = none := by simp [ccV2Field, he]
            rw [Hres, ccWireAt_bad_field _ ht hv]
            iframe
            isplitr
            · ipureintro; exact Herrn
            iapply ccV2_combine p Hpn
            iframe
          | some pair =>
            obtain ⟨bytes,endIdx⟩ := pair
            dsimp only
            icases Hr with ⟨%Hok, Hval, Hback⟩
            obtain ⟨rfl, hj⟩ := Hok
            have hb := ccFieldL_bound he
            have hjn : sint.nat j = endIdx := by word
            wp_auto
            wp_apply wp_single v dq bytes $$ [$Hval] as %sp %good ⟨Hval, Hsingle⟩
            ihave Hd := Hback $$ Hval
            cases hsingle : ccWireSingle bytes with
            | none =>
              dsimp only
              icases Hsingle with %Hfail
              subst Hfail
              wp_auto
              wp_for_post
              iapply HΦ
              have hv : ccV2Field bs 18 k ⟨ot.getD (W32 0), acc, oc.getD []⟩ = none := by
                simp only [ccV2Field, he]; change (ccWireSingle bytes).bind _ = _; rw [hsingle]; rfl
              rw [Hres, ccWireAt_bad_field _ ht hv]
              iframe
              isplitr
              · ipureintro; exact Herrn
              iapply ccV2_combine p Hpn
              iframe
            | some cc =>
              dsimp only
              icases Hsingle with ⟨%Hok2, #Hs⟩
              subst Hok2
              wp_auto
              wp_apply wp_slice_literal (V := Loc) [sp]
              isplitr
              · ipureintro; rfl
              iintro %sl ⟨Hsl, -⟩
              wp_apply wp_slice_append $$ [$chbuf $chcap $Hsl] as %out ⟨chbuf, chcap, -⟩
              wp_for_post
              iframe
              ihave #Hlist : ([∗list] q;x ∈ ls ++ [sp];acc ++ [cc], ccsRO (GF := GF) q x) $$ []
              · iapply BigSepL2.bigSepL2_snoc.2
                iframe Hls Hs
              iexists j, pt, out, cs, ot, ls ++ [sp], acc ++ [cc], oc, us, uf
              iframe Hlist
              iframe
              ipureintro
              refine ⟨⟨by omega, by omega⟩, Hwire, ?_⟩
              rw [Hres, hjn]
              apply ccWireAt_step (ccV2Field_advance _) ht
              rw [htag18]; simp only [ccV2Field, he]
              change (ccWireSingle bytes).bind _ = _; rw [hsingle]; rfl
        · have hnot18 : uint.nat tag ≠ 18 := by word
          wp_if_destruct
          · have htag26 : uint.nat (W64 26) = 26 := by word
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
              have hv : ccV2Field bs (uint.nat (W64 26)) k ⟨ot.getD (W32 0), acc, oc.getD []⟩ = none := by
                rw [htag26]; simp [ccV2Field, hval]
              rw [Hres, ccWireAt_bad_field _ ht hv]
              iframe
              isplitr
              · ipureintro; exact Herrn
              iapply ccV2_combine p Hpn
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
              iexists j, pt, sv, _, ot, ls, acc, some bytes, us, uf
              simp only [ccOptBytesW]
              iframe Hls
              iframe
              ipureintro
              refine ⟨⟨by omega, by omega⟩, Hwire, ?_⟩
              rw [Hres, hjn]
              apply ccWireAt_step (ccV2Field_advance _) ht
              rw [htag26]; simp only [ccV2Field, hval]; rfl
          · have hnot26 : uint.nat tag ≠ 26 := by word
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
              have hv : ccV2Field bs (uint.nat tag) k ⟨ot.getD (W32 0), acc, oc.getD []⟩ = none := by
                unfold ccV2Field; split <;> first | contradiction | simp [hs]
              rw [Hres, ccWireAt_bad_field _ ht hv]
              iframe
              isplitr
              · ipureintro; exact Herrn
              iapply ccV2_combine p Hpn
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
              iexists j, pt, sv, cs, ot, ls, acc, oc, out, _
              iframe Hls
              iframe
              ipureintro
              refine ⟨⟨by omega, by omega⟩, ccUnknown_valid Hwire ht hs ?_, ?_⟩
              · simp [Routed, cc2Schema]; omega
              · rw [Hres, hjn]
                apply ccWireAt_step (ccV2Field_advance _) ht
                unfold ccV2Field; split <;> first | contradiction | simp [hs]
  · have hend : sint.nat i = bs.length := by word
    rw [hend, ccWireAt_end] at Hres
    simp only [decide_eq_false Hif, Bool.false_eq_true, ↓reduceIte]
    try cleanup_bool_decide
    iapply wp_fupd
    imod ccOptCellW_persist pt ot ⊤ $$ cT with #cT
    imod ccOptBytesW_persist cs oc ⊤ $$ cC with #cC
    have hs : ufWire (pbSchemaOf raftpb.ConfChangeV2.ty) uf := by
      simpa [pbSchemaOf, raftpb.Entry.ty, raftpb.Message.ty, raftpb.Snapshot.ty,
        raftpb.SnapshotMetadata.ty, raftpb.ConfState.ty, raftpb.HardState.ty,
        raftpb.ConfChange.ty, raftpb.ConfChangeSingle.ty, raftpb.ConfChangeV2.ty] using Hwire
    imod pbMsg_alloc raftpb.ConfChangeV2 p _ _ us uf ⊤ hs $$ [state sizeCache HU buf] with #Hpb
    · iframe
    wp_auto
    iapply HΦ
    rw [Hres]
    iframe
    isplitr
    · ipureintro; rfl
    unfold ownConfChangeV2
    iexists pt, sv, ls, cs, uf
    isplitr
    · ipureintro; exact Hpn
    ihave #HcT : (cellRO pt (ot.getD (W32 0)) : IProp GF) $$ [cT]
    · rw [show W32 0 = zero_val w32 from rfl]; iapply (nx_optCell_cellRO pt ot); iexact cT
    simp only
    iframe HT HCh chbuf HC Hpb HcT Hls cC
end proof
end EtcdGrove
end Perennial
