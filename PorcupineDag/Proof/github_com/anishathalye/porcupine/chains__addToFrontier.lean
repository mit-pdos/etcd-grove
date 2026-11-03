/- Lean-first (no Rocq counterpart).

`(*chains).addToFrontier(c, consistency)`: the membership loop (never returns: `c` is not in the
frontier), then the insertion loop, which calls `Check` on `c`'s and each member's head operations
(`linOrder_unrelated`: `GeneralLikely`'s answer) and inserts `c` before the first member it is
`KeyGt` than (`pairwise_insert`, `insert_by_copy`), or appends it.
-/
module

public import PorcupineDag.Spec.github_com.anishathalye.porcupine.chains__addToFrontier
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.Consistency__Check
public import PorcupineDag.Proof.github_com.anishathalye.porcupine.FrontierLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

set_option hygiene false in
/-- The insertion at the loop index `k`, `c`'s head operation `KeyGt` than the member's (`hK`). -/
local macro "insert_at_k" : tactic => `(tactic| (
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %litp ⟨Hlit, -⟩
  wp_apply wp_slice_append $$ [Hfr Hcap Hlit] as %s1 ⟨Hfr, Hcap, -⟩
  · iframe Hfr Hcap Hlit
  ihave %Hl1 := ownSlice_len $$ Hfr
  ihave %Hc1 := ownSliceCap_wf $$ Hcap
  simp only [List.length_append, List.length_map, List.length_singleton] at Hl1
  have hs1a : 0 ≤ sint.Z (k + W64 1) ∧ sint.Z (k + W64 1) ≤ sint.Z s1.len ∧
      sint.Z s1.len ≤ sint.Z s1.cap := by word
  have hs1b : 0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z s1.len ∧ sint.Z s1.len ≤ sint.Z s1.cap := by word
  simp only [hs1a, _root_.and_self, ↓reduceIte]
  wp_auto
  simp only [hs1b, _root_.and_self, ↓reduceIte]
  wp_apply wp_slice_copy_within s1 _ (k + W64 1) s1.len k s1.len
    ⟨hs1a.1, hs1a.2.1, Int.le_refl _⟩ ⟨hs1b.1, hs1b.2.1, Int.le_refl _⟩ $$ [Hfr]
    as %n ⟨-, Hfr⟩
  · iexact Hfr
  have hs1c : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z s1.len := by word
  simp only [hs1c, _root_.and_self, ↓reduceIte]
  have hkl : sint.nat k < st.frontier.length := by word
  wp_apply wp_store_slice_index $$ [Hfr] as Hfr
  · iframe; ipureintro; simp only [List.length_append, List.length_take, List.length_map,
      List.length_drop, List.length_singleton, subslice]
    constructor <;> word
  rw [show (sint.Z k).toNat = sint.nat k by word,
    show sint.nat (k + W64 1) = sint.nat k + 1 by word,
    show sint.nat s1.len = (st.frontier.map (fun (c : Nat) => (W64 (c : Int) : w64))).length + 1
      by rw [List.length_map]; word,
    insert_by_copy _ _ _ _ (by rw [List.length_map]; exact hkl)]
  wp_for_post
  -- `c`'s struct back
  ihave Hcosc := Hcosc $$ HcoC
  ihave Hcls := (BigSepL.bigSepL_delete_cond hcvc).2 $$ [Hcosc Hfuc Hrest]
  · iframe Hrest
    iunfold clientOwn
    isplitr
    · ipureintro; exact Hcv
    iexists cosc
    iframe
    ipureintro; exact Hcoc
  iapply HΦ
  iexists st.frontier.take (sint.nat k) ++ sint.nat c :: st.frontier.drop (sint.nat k)
  isplitl
  · iexists { chV with frontier' := s1 }
    iframe Hch
    isplitr
    · ipureintro; exact Hcleq
    iexists cvs
    simp only [clientOwn_frontier]
    rw [List.map_append, List.map_cons, List.map_take, List.map_drop,
      show (W64 ((sint.nat c : Nat) : Int) : w64) = c by word]
    iframe
    ipureintro; exact Hcvs
  · ipureintro
    refine ⟨frontier_insert_sorted hsorted hx Hk.2.2 (by rw [hyc', hyv']; exact hK),
      fun y => mem_insert_iff⟩))

set_option hygiene false in
/-- The next iteration of the insertion loop: the member's head operation is `KeyGt` than `c`'s
(`hK`). -/
local macro "continue_at_k" : tactic => `(tactic| (
  wp_for_post
  iframe
  iexists k + W64 1, _, _
  iframe
  ipureintro
  refine ⟨by word, by word, fun j y hj hy => ?_⟩
  rcases Nat.lt_or_ge j (sint.nat k) with h1 | h1
  · exact Hk.2.2 j y h1 hy
  · have hjk : j = sint.nat k := by word
    subst hjk
    rw [hx] at hy
    cases hy
    rw [hyv', hyc']; exact hK))

set_option maxHeartbeats 1600000 in
theorem chains.addToFrontier.wp_proof
    (wp_Check : Consistency.Check.spec (GF := GF) (hG := hG)) :
    chains.addToFrontier.spec (GF := GF) (hG := hG) :=
    fun ch cl h cs st c cons hok hshape hcs hc0 hclt hhd hnotin hmem hsorted => by
  wp_start as ⟨Hch, #Hlin⟩
  unfold chainsOwnCl chainsRepr
  icases Hch with ⟨%chV, Hch, %Hcleq, %cvs, Hcl, %Hcvs, Hfr, Hcap, Hcls⟩
  icases clients_facts h cs st cvs $$ Hcls with ⟨Hcls, %Hfacts⟩
  ihave %Hlen := ownSlice_len $$ Hfr
  ihave %Hwf := ownSlice_wf $$ Hfr
  ihave %Hcll := ownSlice_len $$ Hcl
  have hfrl : st.frontier.length = sint.nat chV.frontier'.len := by
    rw [List.length_map] at Hlen; exact Hlen.1
  wp_auto
  -- the membership loop: `c` is not in the frontier
  ihave HI : (∃ (k vv : w64), "i" ∷ i_ptr ↦ k ∗ "v" ∷ v_ptr ↦ vv ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z chV.frontier'.len⌝ : IProp GF) $$ [i v]
  · iexists W64 0, _
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · have Hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z chV.frontier'.len := ⟨Hk.1, Hif⟩
    simp only [Hb, _root_.and_self, ↓reduceIte]
    obtain ⟨x, hx⟩ : ∃ x, st.frontier[sint.nat k]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    have hxm : (st.frontier.map (fun (c : Nat) => (W64 (c : Int) : w64)))[(sint.Z k).toNat]? =
        some (W64 (x : Int)) := by
      rw [show (sint.Z k).toNat = sint.nat k by word, List.getElem?_map, hx]; rfl
    wp_apply wp_load_slice_index chV.frontier' (sint.Z k) _ _ (W64 (x : Int)) Hk.1 $$ [Hfr] as Hfr
    · iframe; ipureintro; exact hxm
    have hxb := (hmem x (List.mem_of_getElem? hx)).1
    wp_if_destruct
    · exfalso
      apply hnotin
      rw [show sint.nat (W64 (x : Int)) = x by word]
      exact List.mem_of_getElem? hx
    · wp_for_post
      iframe
      iexists k + W64 1, _
      iframe
      ipureintro; constructor <;> word
  -- the insertion loop
  clear Hk Hif k vv
  rename_i ig_ptr
  irename : (ig_ptr ↦ zero_val w64 : IProp GF) => ig
  obtain ⟨cvc, hcvc⟩ : ∃ cv, cvs[sint.nat c]? = some cv :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨-, hcvc_hd, hcvc_len, hcvc_len0⟩ := Hfacts _ _ hcvc
  icases (BigSepL.bigSepL_delete_cond hcvc).1 $$ Hcls with ⟨Hc, Hrest⟩
  iunfold clientOwn at Hc
  icases Hc with ⟨%Hcv, %cosc, Hcosc, %Hcoc, Hfuc⟩
  obtain ⟨coC, hcoC⟩ : ∃ co, cosc[st.head (sint.nat c)]? = some co :=
    ⟨_, List.getElem?_eq_getElem (by rw [Hcoc.1]; exact hhd)⟩
  icases ownSlice_elem_acc' (st.head (sint.nat c) : Int) coC cvc.cltOps' _ cosc (by omega)
    (by simpa using hcoC) $$ Hcosc with ⟨HcoC, Hcosc⟩
  ihave HI : (∃ (k vv kk : w64), "i" ∷ i_ptr ↦ k ∗ "v" ∷ v_ptr ↦ vv ∗ "ig" ∷ ig_ptr ↦ kk ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z chV.frontier'.len ∧
        ∀ j y, j < sint.nat k → st.frontier[j]? = some y →
          KeyGt h cs (hdOp cs st y) (hdOp cs st (sint.nat c))⌝ : IProp GF) $$ [i v ig]
  · iexists W64 0, _, _
    iframe
    ipureintro; refine ⟨by word, by word, fun j y hj _ => absurd hj (by word)⟩
  wp_for HI
  wp_if_destruct
  · have Hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z chV.frontier'.len := ⟨Hk.1, Hif⟩
    simp only [Hb, _root_.and_self, ↓reduceIte]
    obtain ⟨x, hx⟩ : ∃ x, st.frontier[sint.nat k]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    have hxm : (st.frontier.map (fun (c : Nat) => (W64 (c : Int) : w64)))[(sint.Z k).toNat]? =
        some (W64 (x : Int)) := by
      rw [show (sint.Z k).toNat = sint.nat k by word, List.getElem?_map, hx]; rfl
    wp_apply wp_load_slice_index chV.frontier' (sint.Z k) _ _ (W64 (x : Int)) Hk.1 $$ [Hfr] as Hfr
    · iframe; ipureintro; exact hxm
    obtain ⟨hxlt, hxhd, hnp1, hnp2⟩ := hmem x (List.mem_of_getElem? hx)
    have hxc : x ≠ sint.nat c := fun e => hnotin (e ▸ List.mem_of_getElem? hx)
    obtain ⟨cvv, hcvv⟩ : ∃ cv, cvs[x]? = some cv :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨-, hcvv_hd, hcvv_len, hcvv_len0⟩ := Hfacts _ _ hcvv
    -- `c`'s client struct
    icases ownSlice_elem_acc' (sint.Z c) cvc chV.clients' _ cvs hc0 (by simpa using hcvc) $$ Hcl
      with ⟨Hel, Hcl⟩
    have hb1 : 0 ≤ sint.Z c ∧ sint.Z c < sint.Z chV.clients'.len := ⟨hc0, by word⟩
    simp only [hb1, _root_.and_self, ↓reduceIte]
    wp_auto
    simp only [hb1, _root_.and_self, ↓reduceIte]
    wp_auto
    have hb2 : 0 ≤ sint.Z cvc.head' ∧ sint.Z cvc.head' < sint.Z cvc.cltOps'.len := by
      rw [hcvc_hd]; constructor <;> word
    simp only [hb2, _root_.and_self, ↓reduceIte]
    wp_auto
    -- the member's client struct
    ihave Hcl := Hcl $$ Hel
    have hxw : sint.Z (W64 (x : Int)) = (x : Int) := by word
    simp only [hxw]
    icases ownSlice_elem_acc' (x : Int) cvv chV.clients' _ cvs (by omega) (by simpa using hcvv) $$ Hcl
      with ⟨Hel, Hcl⟩
    have hb3 : 0 ≤ (x : Int) ∧ (x : Int) < sint.Z chV.clients'.len := ⟨by omega, by word⟩
    simp only [hb3, _root_.and_self, ↓reduceIte]
    wp_auto
    simp only [hxw, hb3, _root_.and_self, ↓reduceIte]
    wp_auto
    have hb4 : 0 ≤ sint.Z cvv.head' ∧ sint.Z cvv.head' < sint.Z cvv.cltOps'.len := by
      rw [hcvv_hd]; constructor <;> word
    simp only [hb4, _root_.and_self, ↓reduceIte]
    wp_auto
    ihave Hcl := Hcl $$ Hel
    icases (BigSepL.bigSepL_delete_cond hcvv).1 $$ Hrest with ⟨Hv, Hrest⟩
    simp only [hxc, ↓reduceIte]
    iunfold clientOwn at Hv
    icases Hv with ⟨%Hcvv', %cosv, Hcosv, %Hcov, Hfuv⟩
    obtain ⟨coV, hcoV⟩ : ∃ co, cosv[st.head x]? = some co :=
      ⟨_, List.getElem?_eq_getElem (by rw [Hcov.1]; exact hxhd)⟩
    icases ownSlice_elem_acc' (st.head x : Int) coV cvv.cltOps' _ cosv (by omega)
      (by simpa using hcoV) $$ Hcosv with ⟨HcoV, Hcosv⟩
    rw [hcvc_hd, hcvv_hd]
    wp_apply wp_Check $$ [$Hpkg $consistency $Hlin $HcoC $HcoV] as ⟨consistency, HcoC, HcoV⟩
    -- `Check`'s answer, `GeneralLikely`'s on these unrelated operations
    obtain ⟨yc, oc, hyc, hoc, -, -, -, hcallc, hretc, -⟩ := Hcoc.2 _ _ hcoC
    obtain ⟨yv, ov, hyv, hov, -, -, -, hcallv, hretv, -⟩ := Hcov.2 _ _ hcoV
    have hyc' : hdOp cs st (sint.nat c) = yc := by
      unfold hdOp; rw [opAt_eq hhd]; exact (List.getElem?_eq_some_iff.mp hyc).2
    have hyv' : hdOp cs st x = yv := by
      unfold hdOp; rw [opAt_eq hxhd]; exact (List.getElem?_eq_some_iff.mp hyv).2
    have hord : linOrder coC.Op' coV.Op' = glOrder coC.Op' coV.Op' := by
      apply linOrder_unrelated
      · intro hlt; apply hnp1; rw [hyc', hyv']; exact ⟨oc, ov, hoc, hov, by omega⟩
      · intro hlt; apply hnp2; rw [hyc', hyv']; exact ⟨ov, oc, hov, hoc, by omega⟩
    have hclc : clientOf cs yc = sint.nat c := by rw [← hyc']; exact clientOf_opAt hok hclt hhd
    have hclv : clientOf cs yv = x := by rw [← hyv']; exact clientOf_opAt hok hxlt hxhd
    have hcac : callOf h yc = oc.call := by unfold callOf; rw [hoc]; rfl
    have hcav : callOf h yv = ov.call := by unfold callOf; rw [hov]; rfl
    rw [hord]
    -- the member's struct back
    ihave Hcosv := Hcosv $$ HcoV
    ihave Hrest := (BigSepL.bigSepL_delete_cond hcvv).2 $$ [Hcosv Hfuv Hrest]
    · iframe Hrest
      simp only [hxc, ↓reduceIte]
      iunfold clientOwn
      isplitr
      · ipureintro; exact Hcvv'
      iexists cosv
      iframe
      ipureintro; exact Hcov
    have hxw' : sint.nat (W64 (x : Int)) = x := by word
    have hkey1 : KeyGt h cs yc yv ↔ sint.Z coV.Op'.Call' < sint.Z coC.Op'.Call' ∨
        (sint.Z coC.Op'.Call' = sint.Z coV.Op'.Call' ∧ x < sint.nat c) := by
      unfold KeyGt; rw [hcac, hcav, hclc, hclv, hcallc, hcallv]
    have hkey2 : KeyGt h cs yv yc ↔ sint.Z coC.Op'.Call' < sint.Z coV.Op'.Call' ∨
        (sint.Z coC.Op'.Call' = sint.Z coV.Op'.Call' ∧ sint.nat c < x) := by
      unfold KeyGt; rw [hcac, hcav, hclc, hclv, hcallc, hcallv]; omega
    repeat' wp_if_destruct
    · have hK : KeyGt h cs yc yv := hkey1.2 (Or.inl (glOrder_eq_one.1 Hif))
      insert_at_k
    · exact absurd ‹_ = W64 3› glOrder_ne_three
    · exact absurd ‹_ = W64 3› glOrder_ne_three
    · have hK : KeyGt h cs yc yv := hkey1.2 (Or.inr ⟨glOrder_eq_zero.1 ‹_›, by word⟩)
      insert_at_k
    · have hK : KeyGt h cs yv yc := hkey2.2 (Or.inr ⟨glOrder_eq_zero.1 ‹_›, by
        have := hxc; word⟩)
      continue_at_k
    · have hK : KeyGt h cs yv yc := by
        rename_i _ h1 _
        rcases glOrder_cases coC.Op' coV.Op' with e | e | e
        · apply hkey2.2; left
          unfold glOrder at e; split at e
          · assumption
          · split at e <;> exact absurd e (by decide)
        · exact absurd e h1
        · exact absurd e Hif
      continue_at_k
  · -- every member is `KeyGt` than `c`: append it
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %litp ⟨Hlit, -⟩
    wp_apply wp_slice_append $$ [Hfr Hcap Hlit] as %s1 ⟨Hfr, Hcap, -⟩
    · iframe Hfr Hcap Hlit
    ihave Hcosc := Hcosc $$ HcoC
    ihave Hcls := (BigSepL.bigSepL_delete_cond hcvc).2 $$ [Hcosc Hfuc Hrest]
    · iframe Hrest
      iunfold clientOwn
      isplitr
      · ipureintro; exact Hcv
      iexists cosc
      iframe
      ipureintro; exact Hcoc
    wp_auto
    iapply HΦ
    iexists st.frontier ++ [sint.nat c]
    isplitl
    · iexists { chV with frontier' := s1 }
      iframe Hch
      isplitr
      · ipureintro; exact Hcleq
      iexists cvs
      simp only [clientOwn_frontier]
      rw [List.map_append, List.map_cons, List.map_nil,
        show (W64 ((sint.nat c : Nat) : Int) : w64) = c by word]
      iframe
      ipureintro; exact Hcvs
    · ipureintro
      refine ⟨frontier_append_sorted hsorted (fun j y hj hy => Hk.2.2 j y (by word) hy),
        fun y => ?_⟩
      simp only [List.mem_append, List.mem_singleton]
      exact Or.comm

end proof

end porcupine
end EtcdGrove
end Perennial
