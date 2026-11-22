-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/raftpb/MarshalConfChangeV2.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Proof of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/MarshalConfChangeV2.lean`: the part's own (raft without
hand-written axioms, `notes/raft-noax-part.md`).
-/
module

public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.MarshalConfChangeV2
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.appendEnum
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.appendBytes
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.marshalConfChangeSingle
public import KvNet.Proof.go_etcd_io.raft.v3.CCCodecLen

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

omit [GooseSemantics] [GooseInterp] go_gctx hlc GF hG sem package_sem in
theorem ccEncChanges_snoc (encs : List (List w8)) (e : List w8) :
    ccEncChanges (encs ++ [e]) = ccEncChanges encs ++ (W8 18 :: ccBytesEnc e) := by
  induction encs with
  | nil => simp [ccEncChanges]
  | cons x xs ih => simp only [List.cons_append, ccEncChanges, ih, List.append_assoc]

theorem raftpb.MarshalConfChangeV2.wp_proof
    (wp_appendEnum : raftpb.appendEnum.spec (GF := GF) (hG := hG))
    (wp_marshalConfChangeSingle : raftpb.marshalConfChangeSingle.spec (GF := GF) (hG := hG))
    (wp_appendBytes : raftpb.appendBytes.spec (GF := GF) (hG := hG)) :
    raftpb.MarshalConfChangeV2.spec (GF := GF) (hG := hG) := by
  intro p dq t chs ctx uf
  wp_start as Hc
  simp only [ccPtsCC]
  icases Hc with ⟨%p', %pt, %sc, %ls, %cs, %Hc, HT, #cT, HCh, Hch, #Hccs, HC, #Hcs, #Hpb⟩
  obtain ⟨Hc, Hnn⟩ := Hc
  have hp : p' = p := by simp at Hc; exact (GoGlobalContext.intoVal_inj_loc Hc).symm
  subst hp
  ihave #Hsaved : pbMsg raftpb.ConfChangeV2 p' uf $$ []
  · iexact Hpb
  iunfold pbMsg at Hpb
  icases Hpb with ⟨⟨%st, %scache, %us, -, -, #Hus, #Huf⟩, %Hwire⟩
  have Hschema : ufWire cc2Schema uf := by
    change ufWire (pbSchemaOf raftpb.ConfChangeV2.ty) uf at Hwire
    simpa [pbSchemaOf, raftpb.Entry.ty, raftpb.Message.ty, raftpb.Snapshot.ty,
      raftpb.SnapshotMetadata.ty, raftpb.ConfState.ty, raftpb.HardState.ty,
      raftpb.ConfChange.ty, raftpb.ConfChangeSingle.ty, raftpb.ConfChangeV2.ty] using Hwire
  ihave %Hcl := ownSlice_len $$ Hcs
  ihave %Hscl := ownSlice_len $$ Hch
  ihave %Hll := BigSepL2.bigSepL2_length $$ Hccs
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_slice_literal (V := w8) []
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, Hcap⟩
  wp_auto
  wp_join iprop(∃ (cur : GoSlice) (o1 : Option w32), "c" ∷ c_ptr ↦ p' ∗ "b" ∷ b_ptr ↦ cur ∗
      "Hb" ∷ cur ↦* (ccEncOpt (W8 8) ccEnumEnc o1) ∗ "Hcap" ∷ ownSliceCap w8 cur (DFrac.own 1) ∗
      "HT" ∷ p'.[raftpb.ConfChangeV2, go!"Transition"] ↦{dq} pt ∗
      "%Ho1" ∷ ⌜o1.getD (W32 0) = t⌝) with [c b Hsl Hcap HT] as ⟨%cur1, %o1, c, b, Hb, Hcap, HT, %Ho1⟩
  · icases cellRO_cases null t $$ cT with (%Hz | ⟨-, %Hn⟩)
    · iexists _, none
      simp only [ccEncOpt]
      iframe
      ipureintro; exact Hz.2.symm
    · exact absurd rfl Hn
  · icases cellRO_cases pt t $$ cT with (%Hz | ⟨#Hp, %Hn⟩)
    · exact absurd Hz.1 Hif
    wp_apply wp_slice_literal (V := w8) [_]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl2] as %b2 ⟨Hb2, Hcap, -⟩
    wp_apply wp_appendEnum $$ [$Hb2 $Hcap] as %b3 ⟨Hb3, Hcap⟩
    wp_join_done
    iexists b3, some t
    simp only [ccEncOpt, List.append_assoc, List.singleton_append]
    iframe
    ipureintro; rfl
  ihave IH : iprop(∃ (i : w64) (cur : GoSlice) (encs : List (List w8)) (sv : Loc),
      "i" ∷ i_ptr ↦ i ∗ "s" ∷ s_ptr ↦ sv ∗ "b" ∷ b_ptr ↦ cur ∗
      "Hb" ∷ cur ↦* (ccEncOpt (W8 8) ccEnumEnc o1 ++ ccEncChanges encs) ∗
      "Hcap" ∷ ownSliceCap w8 cur (DFrac.own 1) ∗ "Hch" ∷ sc ↦*{dq} ls ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ ls.length ∧
        List.Forall₂ (fun ch e => CCSingleWireEnc ch.1 ch.2 e ∧ e.length < 2^64) (chs.take (sint.nat i)) encs⌝)
      $$ [i s b Hb Hcap Hch]
  · iexists W64 0, cur1, [], _
    simp only [ccEncChanges, List.append_nil]
    iframe
    ipureintro
    have h0 : sint.Z (W64 0) = 0 := rfl
    have h0n : sint.nat (W64 0) = 0 := rfl
    refine ⟨by decide, by omega, ?_⟩
    rw [h0n, List.take_zero]; exact List.Forall₂.nil
  wp_for IH
  wp_if_destruct
  · have hlt : sint.nat i < ls.length := by word
    obtain ⟨q, hq⟩ : ∃ q, ls[sint.nat i]? = some q := ⟨_, List.getElem?_eq_getElem hlt⟩
    obtain ⟨ch, hch⟩ : ∃ ch, chs[sint.nat i]? = some ch :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    ihave #Hq := (BigSepL2.bigSepL2_lookup (Φ := fun _ q (ch : ConfChangeSingleM × List w8) =>
      (ccsRoC q ch.1 ch.2 : IProp GF)) hq hch) $$ Hccs
    simp only [show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sc.len from ⟨Hi.1, by word⟩]
    wp_apply wp_load_slice_index sc (sint.Z i) ls dq q Hi.1 $$ [Hch] as Hch
    · iframe; ipureintro; exact hq
    wp_apply wp_slice_literal (V := w8) [_]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl2] as %b2 ⟨Hb2, Hcap, -⟩
    wp_apply wp_marshalConfChangeSingle q ch.1 ch.2 $$ [$Hq] as %es %ebs ⟨Hes, %Hebs⟩
    ihave %Hlen := ownSlice_len $$ Hes
    have hlen : ebs.length < 2^64 := by word
    wp_apply wp_appendBytes $$ [$Hb2 $Hcap $Hes] as %b3 ⟨Hb3, Hcap, -⟩
    wp_for_post
    iframe
    iexists i + W64 1, b3, encs ++ [ebs], q
    rw [ccEncChanges_snoc]
    simp only [List.append_assoc, List.singleton_append] at *
    iframe
    ipureintro
    have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    refine ⟨by word, by word, ?_⟩
    rw [hi1, List.take_add_one, hch]
    simp only [Option.toList_some]
    exact forall₂_app Hi.2.2 (List.Forall₂.cons ⟨Hebs, hlen⟩ List.Forall₂.nil)
  · have hiE : sint.nat i = chs.length := by word
    rw [hiE, List.take_length] at Hi
    have HF := Hi.2.2
    wp_join iprop(∃ (cur : GoSlice) (o4 : Option (List w8)), "c" ∷ c_ptr ↦ p' ∗ "b" ∷ b_ptr ↦ cur ∗
        "Hb" ∷ cur ↦* (ccEncOpt (W8 8) ccEnumEnc o1 ++ ccEncChanges encs ++ ccEncOpt (W8 26) ccBytesEnc o4) ∗
        "Hcap" ∷ ownSliceCap w8 cur (DFrac.own 1) ∗ "HC" ∷ p'.[raftpb.ConfChangeV2, go!"Context"] ↦{dq} cs ∗
        "%Ho4" ∷ ⌜o4.getD [] = ctx ∧ ∀ x, o4 = some x → x.length < 2 ^ 64⌝) with [c b Hb Hcap HC]
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
      iexists b3, some ctx
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
    isplitl
    · iframe cT Hccs Hcs Hsaved
      ipureintro; exact ⟨rfl, Hnn⟩
    ipureintro
    have e1 := ccWireV2_enc o1 chs encs HF o4 Ho4.2 uf Hschema
    have e2 := ccEncodeV2_length_le o1 chs encs HF o4 Ho4.2 uf
    rw [Ho1, Ho4.1] at e1 e2
    exact ⟨e1, fun _ => e2⟩

end proof

end EtcdGrove
end Perennial
