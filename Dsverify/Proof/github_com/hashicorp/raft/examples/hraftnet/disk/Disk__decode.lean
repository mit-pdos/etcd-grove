/-
(hraft_robust R3) The proof of `disk.(*Disk).decode`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.reader__uint64
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.reader__bytes
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.reader__done
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__decode

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section pure
variable [GooseExts]

open github_com.hashicorp.raft.examples.hraftnet.disk

theorem dk_ent_drop (es : List DEnt) (k : Nat) (e : DEnt) (R : List w8) (h : es[k]? = some e) :
    (es.drop k).flatMap encEnt ++ R = encU64 e.idx ++ (encU64 e.term ++ (encU64 (W64 (uint.Z e.ty)) ++
      (encBytes e.data ++ (encBytes e.ext ++ ((es.drop (k + 1)).flatMap encEnt ++ R))))) := by
  rw [dk_flatMap_drop es encEnt k e h]; unfold encEnt; simp only [List.append_assoc]

theorem dk_kv_drop (ps : List (List w8 × List w8)) (k : Nat) (p : List w8 × List w8) (R : List w8)
    (h : ps[k]? = some p) :
    (ps.drop k).flatMap encKV ++ R = encBytes p.1 ++ (encBytes p.2 ++ ((ps.drop (k + 1)).flatMap encKV ++ R)) := by
  rw [dk_flatMap_drop ps encKV k p h]; unfold encKV; simp only [List.append_assoc]

theorem dk_ikv_drop (ps : List (List w8 × w64)) (k : Nat) (p : List w8 × w64) (R : List w8)
    (h : ps[k]? = some p) :
    (ps.drop k).flatMap encIKV ++ R = encBytes p.1 ++ (encU64 p.2 ++ ((ps.drop (k + 1)).flatMap encIKV ++ R)) := by
  rw [dk_flatMap_drop ps encIKV k p h]; unfold encIKV; simp only [List.append_assoc]

theorem dk_drop_all {α : Type} (l : List α) (f : α → List w8) (k : Nat) (R : List w8) (h : k = l.length) :
    (l.drop k).flatMap f ++ R = R := by
  rw [h, List.drop_length]; rfl

theorem dk_take_succ {α : Type} (l : List α) (k : Nat) (x : α) (h : l[k]? = some x) :
    l.take (k + 1) = l.take k ++ [x] := by
  rw [List.take_add_one, h]; rfl

theorem dk_w8_rt (x : w8) : W8 (uint.Z (W64 (uint.Z x))) = x := by word

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

open github_com.hashicorp.raft github_com.hashicorp.raft.examples.hraftnet.disk

theorem dk_rd_eq (r : Loc) (cs cs' : List w8) (h : cs = cs') :
    (readerSt r cs : IProp GF) ⊢ readerSt r cs' := by rw [h]

theorem github_com.hashicorp.raft.examples.hraftnet.disk.Disk.decode.wp_proof
    (wp_uint64 : github_com.hashicorp.raft.examples.hraftnet.disk.reader.uint64.spec (GF := GF) (hG := hG))
    (wp_bytes : github_com.hashicorp.raft.examples.hraftnet.disk.reader.bytes.spec (GF := GF) (hG := hG))
    (wp_done : github_com.hashicorp.raft.examples.hraftnet.disk.reader.done.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.disk.Disk.decode.spec (GF := GF) (hG := hG) := by
  intro d b I hok
  obtain ⟨_, _, _, ⟨hlE, hlK, hlI⟩, hentL, hkvL, hikvL⟩ := hok
  unfold encImg diskMem0
  simp only [List.append_assoc]
  rw [← List.append_nil (encU64 I.commit)]
  wp_start as ⟨⟨Hents, Hkeys, Hvals, Hikeys, Hivals, Hstaged, Hcommit⟩, #Hb⟩
  wp_auto
  ihave Hr : readerSt «$r0_ptr» _ $$ [«$r0»]
  · iunfold readerSt; iexists b; iframe; iexact Hb
  wp_apply wp_uint64 $$ [$Hr] as Hr
  ihave HI : (∃ (i : w64) (es : GoSlice) (lvs : List Log),
      "i" ∷ i_ptr ↦ i ∗ "Hents" ∷ d.[Disk, go!"ents"] ↦ es ∗ "Hes" ∷ es ↦* lvs ∗
      "Hescap" ∷ ownSliceCap Log es (DFrac.own 1) ∗
      "Hent" ∷ ([∗list] lv; e ∈ lvs; I.ents.take (uint.nat i), entRep lv e) ∗
      "Hr" ∷ readerSt «$r0_ptr» ((I.ents.drop (uint.nat i)).flatMap encEnt ++
        (encU64 (W64 I.kv.length) ++ (I.kv.flatMap encKV ++ (encU64 (W64 I.ikv.length) ++
          (I.ikv.flatMap encIKV ++ (encU64 I.commit ++ [])))))) ∗
      "%Hi" ∷ ⌜uint.nat i ≤ I.ents.length⌝ : IProp GF) $$ [i Hents Hr]
  · iexists W64 0, slice.nil, []
    simp only [show uint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero]
    iframe
    isplitl
    · iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    isplitl
    · iapply BigSepL2.bigSepL2_nil.2; itrivial
    ipureintro; exact Nat.zero_le _
  wp_for HI
  wp_if_destruct
  · have hil : uint.nat i < I.ents.length := dk_ulen_lt i _ hlE Hif
    list_elem I.ents (uint.nat i) as e
    have hel := hentL e (List.mem_of_getElem? He_lookup)
    iunfold readerSt at Hr
    icases Hr with ⟨%rb, Hr, #Hrb⟩
    wp_auto
    simp only [decide_true, ↓reduceIte]
    wp_auto
    ihave Hr : readerSt «$r0_ptr» _ $$ [Hr]
    · iunfold readerSt; iexists rb; iframe; iexact Hrb
    ihave Hr := dk_rd_eq _ _ _ (dk_ent_drop I.ents _ e _ He_lookup) $$ Hr
    wp_apply wp_uint64 $$ [$Hr] as Hr
    wp_apply wp_uint64 $$ [$Hr] as Hr
    wp_apply wp_uint64 $$ [$Hr] as Hr
    wp_apply wp_bytes _ _ _ hel.1 $$ [$Hr] as %sd ⟨Hr, Hsd, -⟩
    wp_apply wp_bytes _ _ _ hel.2 $$ [$Hr] as %sx ⟨Hr, Hsx, -⟩
    ipersist Hsd
    ipersist Hsx
    wp_apply (wp_slice_literal (V := Log))
    isplitr
    · ipureintro; rfl
    iintro %slp ⟨Hlit, -⟩
    wp_apply (wp_slice_append (V := Log)) $$ [$Hes $Hescap $Hlit] as %es2 ⟨Hes, Hescap, -⟩
    wp_for_post
    iframe
    iexists i + W64 1, es2, _
    iframe
    rw [dk_usucc i _ hlE hil, dk_take_succ I.ents _ e He_lookup]
    iframe
    isplitl
    · iapply BigSepL2.bigSepL2_singleton.2
      iunfold entRep
      isplitr
      · ipureintro; exact ⟨rfl, rfl, dk_w8_rt e.ty⟩
      iframe #
    ipureintro; exact hil
  · have hie := dk_ulen_eq i _ hlE Hi Hif
    ihave Hent := (show ([∗list] lv; e ∈ lvs; I.ents.take (uint.nat i), entRep lv e : IProp GF) ⊢
      [∗list] lv; e ∈ lvs; I.ents, entRep lv e by rw [hie, List.take_length]) $$ Hent
    ihave Hr := dk_rd_eq _ _ _ (dk_drop_all I.ents encEnt _ _ hie) $$ Hr
    wp_apply wp_uint64 $$ [$Hr] as Hr
    ihave HI2 : (∃ (i : w64) (ks vs : GoSlice) (kss vss : List GoSlice),
        "i" ∷ i_ptr ↦ i ∗
        "Hkeys" ∷ d.[Disk, go!"keys"] ↦ ks ∗ "Hks" ∷ ks ↦* kss ∗
        "Hkscap" ∷ ownSliceCap GoSlice ks (DFrac.own 1) ∗
        "Hkr" ∷ ([∗list] k; p ∈ kss; I.kv.take (uint.nat i), k ↦*□ p.1) ∗
        "Hvals" ∷ d.[Disk, go!"vals"] ↦ vs ∗ "Hvs" ∷ vs ↦* vss ∗
        "Hvscap" ∷ ownSliceCap GoSlice vs (DFrac.own 1) ∗
        "Hvr" ∷ ([∗list] v; p ∈ vss; I.kv.take (uint.nat i), v ↦*□ p.2) ∗
        "Hr" ∷ readerSt «$r0_ptr» ((I.kv.drop (uint.nat i)).flatMap encKV ++
          (encU64 (W64 I.ikv.length) ++ (I.ikv.flatMap encIKV ++ (encU64 I.commit ++ [])))) ∗
        "%Hi" ∷ ⌜uint.nat i ≤ I.kv.length⌝ : IProp GF) $$ [i Hkeys Hvals Hr]
    · iexists W64 0, slice.nil, slice.nil, [], []
      simp only [show uint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero]
      iframe
      isplitl
      · iapply ownSlice_nil
      isplitl
      · iapply ownSliceCap_nil
      isplitl
      · iapply BigSepL2.bigSepL2_nil.2; itrivial
      isplitl
      · iapply ownSlice_nil
      isplitl
      · iapply ownSliceCap_nil
      isplitl
      · iapply BigSepL2.bigSepL2_nil.2; itrivial
      ipureintro; exact Nat.zero_le _
    wp_for HI2
    wp_if_destruct
    · have hil : uint.nat i < I.kv.length := dk_ulen_lt i _ hlK Hif
      list_elem I.kv (uint.nat i) as p
      have hpl := hkvL p (List.mem_of_getElem? Hp_lookup)
      iunfold readerSt at Hr
      icases Hr with ⟨%rb, Hr, #Hrb⟩
      wp_auto
      simp only [decide_true, ↓reduceIte]
      wp_auto
      ihave Hr : readerSt «$r0_ptr» _ $$ [Hr]
      · iunfold readerSt; iexists rb; iframe; iexact Hrb
      ihave Hr := dk_rd_eq _ _ _ (dk_kv_drop I.kv _ p _ Hp_lookup) $$ Hr
      wp_apply wp_bytes _ _ _ hpl.1 $$ [$Hr] as %sk ⟨Hr, Hsk, -⟩
      ipersist Hsk
      wp_apply (wp_slice_literal (V := GoSlice))
      isplitr
      · ipureintro; rfl
      iintro %slp ⟨Hlit, -⟩
      wp_apply (wp_slice_append (V := GoSlice)) $$ [$Hks $Hkscap $Hlit] as %ks2 ⟨Hks, Hkscap, -⟩
      wp_apply wp_bytes _ _ _ hpl.2 $$ [$Hr] as %sv ⟨Hr, Hsv, -⟩
      ipersist Hsv
      wp_apply (wp_slice_literal (V := GoSlice))
      isplitr
      · ipureintro; rfl
      iintro %slp2 ⟨Hlit2, -⟩
      wp_apply (wp_slice_append (V := GoSlice)) $$ [$Hvs $Hvscap $Hlit2] as %vs2 ⟨Hvs, Hvscap, -⟩
      wp_for_post
      iframe
      iexists i + W64 1, ks2, vs2, _, _
      iframe
      rw [dk_usucc i _ hlK hil, dk_take_succ I.kv _ p Hp_lookup]
      iframe
      isplitl
      · iapply BigSepL2.bigSepL2_singleton.2; iexact Hsk
      isplitl
      · iapply BigSepL2.bigSepL2_singleton.2; iexact Hsv
      ipureintro; exact hil
    · have hie2 := dk_ulen_eq i _ hlK Hi Hif
      ihave Hkr := (show ([∗list] k; p ∈ kss; I.kv.take (uint.nat i), k ↦*□ p.1 : IProp GF) ⊢
        [∗list] k; p ∈ kss; I.kv, k ↦*□ p.1 by rw [hie2, List.take_length]) $$ Hkr
      ihave Hvr := (show ([∗list] v; p ∈ vss; I.kv.take (uint.nat i), v ↦*□ p.2 : IProp GF) ⊢
        [∗list] v; p ∈ vss; I.kv, v ↦*□ p.2 by rw [hie2, List.take_length]) $$ Hvr
      ihave Hr := dk_rd_eq _ _ _ (dk_drop_all I.kv encKV _ _ hie2) $$ Hr
      wp_apply wp_uint64 $$ [$Hr] as Hr
      ihave HI3 : (∃ (i : w64) (iks ivs : GoSlice) (ikss : List GoSlice),
          "i" ∷ i_ptr ↦ i ∗
          "Hikeys" ∷ d.[Disk, go!"ikeys"] ↦ iks ∗ "Hiks" ∷ iks ↦* ikss ∗
          "Hikscap" ∷ ownSliceCap GoSlice iks (DFrac.own 1) ∗
          "Hikr" ∷ ([∗list] k; p ∈ ikss; I.ikv.take (uint.nat i), k ↦*□ p.1) ∗
          "Hivals" ∷ d.[Disk, go!"ivals"] ↦ ivs ∗ "Hivs" ∷ ivs ↦* ((I.ikv.take (uint.nat i)).map Prod.snd) ∗
          "Hivscap" ∷ ownSliceCap w64 ivs (DFrac.own 1) ∗
          "Hr" ∷ readerSt «$r0_ptr» ((I.ikv.drop (uint.nat i)).flatMap encIKV ++ (encU64 I.commit ++ [])) ∗
          "%Hi" ∷ ⌜uint.nat i ≤ I.ikv.length⌝ : IProp GF) $$ [i Hikeys Hivals Hr]
      · iexists W64 0, slice.nil, slice.nil, []
        simp only [show uint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero, List.map_nil]
        iframe
        isplitl
        · iapply ownSlice_nil
        isplitl
        · iapply ownSliceCap_nil
        isplitl
        · iapply BigSepL2.bigSepL2_nil.2; itrivial
        isplitl
        · iapply ownSlice_nil
        isplitl
        · iapply ownSliceCap_nil
        ipureintro; exact Nat.zero_le _
      wp_for HI3
      wp_if_destruct
      · have hil : uint.nat i < I.ikv.length := dk_ulen_lt i _ hlI Hif
        list_elem I.ikv (uint.nat i) as p
        have hpl := hikvL p (List.mem_of_getElem? Hp_lookup)
        iunfold readerSt at Hr
        icases Hr with ⟨%rb, Hr, #Hrb⟩
        wp_auto
        simp only [decide_true, ↓reduceIte]
        wp_auto
        ihave Hr : readerSt «$r0_ptr» _ $$ [Hr]
        · iunfold readerSt; iexists rb; iframe; iexact Hrb
        ihave Hr := dk_rd_eq _ _ _ (dk_ikv_drop I.ikv _ p _ Hp_lookup) $$ Hr
        wp_apply wp_bytes _ _ _ hpl $$ [$Hr] as %sk ⟨Hr, Hsk, -⟩
        ipersist Hsk
        wp_apply (wp_slice_literal (V := GoSlice))
        isplitr
        · ipureintro; rfl
        iintro %slp ⟨Hlit, -⟩
        wp_apply (wp_slice_append (V := GoSlice)) $$ [$Hiks $Hikscap $Hlit] as %ks2 ⟨Hiks, Hikscap, -⟩
        wp_apply wp_uint64 $$ [$Hr] as Hr
        wp_apply (wp_slice_literal (V := w64))
        isplitr
        · ipureintro; rfl
        iintro %slp2 ⟨Hlit2, -⟩
        wp_apply (wp_slice_append (V := w64)) $$ [$Hivs $Hivscap $Hlit2] as %vs2 ⟨Hivs, Hivscap, -⟩
        wp_for_post
        iframe
        iexists i + W64 1, ks2, vs2, _
        iframe
        rw [dk_usucc i _ hlI hil, dk_take_succ I.ikv _ p Hp_lookup, List.map_append]
        iframe
        isplitl
        · iapply BigSepL2.bigSepL2_singleton.2; iexact Hsk
        ipureintro; exact hil
      · have hie3 := dk_ulen_eq i _ hlI Hi Hif
        ihave Hikr := (show ([∗list] k; p ∈ ikss; I.ikv.take (uint.nat i), k ↦*□ p.1 : IProp GF) ⊢
          [∗list] k; p ∈ ikss; I.ikv, k ↦*□ p.1 by rw [hie3, List.take_length]) $$ Hikr
        ihave Hivs := (show (ivs ↦* ((I.ikv.take (uint.nat i)).map Prod.snd) : IProp GF) ⊢
          ivs ↦* (I.ikv.map Prod.snd) by rw [hie3, List.take_length]) $$ Hivs
        ihave Hr := dk_rd_eq _ _ _ (dk_drop_all I.ikv encIKV _ _ hie3) $$ Hr
        wp_apply wp_uint64 $$ [$Hr] as Hr
        wp_apply wp_done $$ [$Hr] as Hr
        iapply HΦ
        iunfold diskMem
        iexists es, ks, vs, iks, ivs, lvs, kss, vss, ikss
        iframe

end proof

end Perennial
