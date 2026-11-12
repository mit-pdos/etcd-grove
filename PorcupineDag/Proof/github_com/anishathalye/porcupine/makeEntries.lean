/- Lean-first (no Rocq counterpart). Proof of `Spec/github_com/anishathalye/porcupine/makeEntries.lean`.

v1.3.1's proof, adapted to PR #46. The range loop appends each operation's call and return entries
(memory only: nothing reads them) and its `clientOperation` to its client's slice: after `n`
iterations client `c`'s slice holds the chain `chK ops n c` (`OpsLemmas.lean`), fresh (`CoFresh`).
The per-client slices are a `bigSepL2` with their contents (`coss`), so that one of them can grow
(`bigSepL2_insert_acc`). `sort.Sort(byTime(entries))` permutes the entries.
-/
module

public import PorcupineDag.Spec.github_com.anishathalye.porcupine.makeEntries
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.newclientOperation
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.byTime__Len
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.byTime__Less
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.byTime__Swap
public import PorcupineDag.Proof.github_com.anishathalye.porcupine.Entries
public import PorcupineDag.Proof.github_com.anishathalye.porcupine.OpsLemmas
public import Spec.sort.Sort

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine
  github_com.anishathalye.porcupine.Theory

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

omit package_sem in
/-- `byTime` over the slice `sl` sorts the entries it holds by `entryLt`. -/
theorem byTime_sorter
    (hLen : byTime.Len.spec (GF := GF) (hG := hG))
    (hLess : byTime.Less.spec (GF := GF) (hG := hG))
    (hSwap : byTime.Swap.spec (GF := GF) (hG := hG)) (sl : GoSlice) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ⊢
      sorterSpec (interface.mk github_com.anishathalye.porcupine.byTime.ty #sl)
        (fun es => iprop(sl ↦* es)) entryLt := by
  iintro #Hpkg
  unfold sorterSpec
  isplitr
  · imodintro
    iintro %l
    iintro !> %Φ Hs HΦ
    wp_apply (hLen sl l (DFrac.own 1)) $$ [$Hs] as Hs
    iapply HΦ $$ Hs
  isplitr
  · imodintro
    iintro %l %i %j %a %b %Hij
    iintro !> %Φ Hs HΦ
    wp_apply (hLess sl l (DFrac.own 1) i j a b) $$ [$Hs] as Hs
    · ipureintro; exact Hij
    iapply HΦ $$ Hs
  imodintro
  iintro %l %i %j %a %b %Hij
  iintro !> %Φ Hs HΦ
  wp_apply (hSwap sl l i j a b) $$ [$Hs] as Hs
  · ipureintro; exact Hij
  iapply HΦ $$ Hs

omit package_sem in
/-- `n` empty client slices. -/
theorem cos_replicate_nil (n : Nat) :
    ⊢ [∗list] sl;cos ∈ List.replicate n (zero_val GoSlice);
        List.replicate n ([] : List clientOperation),
      (sl ↦* cos ∗ ownSliceCap clientOperation sl (DFrac.own 1) : IProp GF) := by
  induction n with
  | zero => simp only [List.replicate_zero]; iapply BigSepL2.bigSepL2_nil.2; iempintro
  | succ n ih =>
    simp only [List.replicate_succ]
    iapply BigSepL2.bigSepL2_cons.2
    isplitr
    · isplitr
      · iapply ownSlice_nil
      · iapply ownSliceCap_nil
    · iapply ih

omit package_sem in
/-- The client slices, each with its contents. -/
theorem bigSepL2_exists_l {A B : Type} (Φ : A → B → IProp GF) :
    ∀ (l1 : List A) (l2 : List B),
      ([∗list] x;y ∈ l1;l2, Φ x y) ⊢ [∗list] k ↦ x ∈ l1, ∃ y, ⌜l2[k]? = some y⌝ ∗ Φ x y
  | [], _ => by iintro _; iapply BigSepL.bigSepL_nil.2; iempintro
  | _ :: _, [] => by
    iintro H
    ihave %Hl := BigSepL2.bigSepL2_length $$ H
    simp at Hl
  | x :: xs, y :: ys => by
    iintro H
    icases BigSepL2.bigSepL2_cons.1 $$ H with ⟨Hxy, H⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hxy]
    · iexists y; iframe; ipureintro; rfl
    · simp only [List.getElem?_cons_succ]
      iapply bigSepL2_exists_l Φ xs ys $$ H

theorem makeEntries.wp_proof
    (hSort : sort.«Sort».spec (GF := GF) (hG := hG))
    (hLen : byTime.Len.spec (GF := GF) (hG := hG))
    (hLess : byTime.Less.spec (GF := GF) (hG := hG))
    (hSwap : byTime.Swap.spec (GF := GF) (hG := hG))
    (wp_newclientOperation : newclientOperation.spec (GF := GF) (hG := hG)) :
    makeEntries.spec (GF := GF) (hG := hG) :=
  fun sl ops dq nc hok hnc halloc hids => by
  wp_start as Hs
  wp_auto
  have hn := hok.1
  wp_apply wp_slice_make2 (V := GoSlice) nc as %ohs ⟨Hoh, -⟩
  · ipureintro; exact hnc
  ihave Hnil : (slice.nil ↦* ([] : List entry)) $$ []
  · iapply ownSlice_nil
  ihave Hcap : ownSliceCap entry slice.nil (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  ihave Hcos0 := cos_replicate_nil (GF := GF) (sint.nat nc)
  ihave %Hslen := ownSlice_len $$ Hs
  ihave IH : iprop(∃ (n : w64) (s' : GoSlice) (x : Operation) (es : List entry)
      (sls : List GoSlice) (coss : List (List clientOperation)),
      "i" ∷ i_ptr ↦ n ∗
      "entries" ∷ entries_ptr ↦ s' ∗
      "id" ∷ id_ptr ↦ n ∗
      "elem" ∷ elem_ptr ↦ x ∗
      "He" ∷ s' ↦* es ∗
      "Hcap" ∷ ownSliceCap entry s' (DFrac.own 1) ∗
      "Hoh" ∷ ohs ↦* sls ∗
      "Hcos" ∷ ([∗list] sl;cos ∈ sls;coss,
        (sl ↦* cos ∗ ownSliceCap clientOperation sl (DFrac.own 1) : IProp GF)) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ops.length : Int) ∧ es.length = 2 * sint.nat n ∧
        sls.length = sint.nat nc ∧ coss.length = sint.nat nc ∧
        ∀ (c : Nat) cos, coss[c]? = some cos → CoFresh (histOf ops) (chK ops (sint.nat n) c) cos⌝)
    $$ [i entries id elem Hnil Hcap Hoh Hcos0]
  · iexists W64 0, slice.nil, zero_val Operation, [], _,
      List.replicate (sint.nat nc) ([] : List clientOperation)
    simp only [named]
    iframe
    isplitl [Hcos0]
    · iexact Hcos0
    ipureintro
    refine ⟨by word, by word, rfl, by simp, by simp, fun c cos hc => ?_⟩
    rw [List.getElem?_replicate] at hc
    split at hc
    · cases hc
      rw [show sint.nat (W64 0) = 0 from rfl, chK_zero]
      exact coFresh_nil _
    · cases hc
  iclear Hcos0
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < ops.length := by word
    obtain ⟨o, Ho⟩ : ∃ o, ops[sint.nat n]? = some o := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, by word⟩
    simp only [Hbnd', and_self]
    wp_apply wp_load_slice_index sl (sint.Z n) _ _ o Hn.1 $$ [Hs] with Hs
    · iframe Hs; ipureintro; rw [show (sint.Z n).toNat = sint.nat n from rfl]; exact Ho
    wp_apply wp_slice_literal (V := entry)
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [$He $Hcap $Hsl2] as %s3 ⟨He, Hcap, -⟩
    wp_apply wp_slice_literal (V := entry)
    isplitr
    · ipureintro; rfl
    iintro %sl4 ⟨Hsl4, -⟩
    wp_apply wp_slice_append $$ [$He $Hcap $Hsl4] as %s5 ⟨He, Hcap, -⟩
    wp_apply wp_newclientOperation o nc n
    have Hoc := hids o (List.mem_of_getElem? Ho)
    ihave %Hohlen := ownSlice_len $$ Hoh
    have Hcl : sint.nat o.ClientId' < sls.length := by rw [Hn.2.2.2.1]; word
    have Hcl' : sint.nat o.ClientId' < coss.length := by rw [Hn.2.2.2.2.1]; word
    obtain ⟨slc, Hslc⟩ : ∃ x, sls[sint.nat o.ClientId']? = some x :=
      ⟨_, List.getElem?_eq_getElem Hcl⟩
    obtain ⟨cos0, Hcos0⟩ : ∃ x, coss[sint.nat o.ClientId']? = some x :=
      ⟨_, List.getElem?_eq_getElem Hcl'⟩
    have Hb : 0 ≤ sint.Z o.ClientId' ∧ sint.Z o.ClientId' < sint.Z ohs.len := ⟨Hoc.1, by word⟩
    simp only [Hb, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index ohs (sint.Z o.ClientId') _ _ slc Hoc.1 $$ [Hoh] with Hoh
    · iframe Hoh; ipureintro; exact Hslc
    icases BigSepL2.bigSepL2_insert_acc Hslc Hcos0 $$ Hcos with ⟨⟨Hslc, Hcapc⟩, Hcos⟩
    wp_auto
    wp_apply wp_slice_literal (V := clientOperation)
    isplitr
    · ipureintro; rfl
    iintro %sl6 ⟨Hsl6, -⟩
    wp_apply wp_slice_append $$ [$Hslc $Hcapc $Hsl6] as %s7 ⟨Hslc, Hcapc, -⟩
    simp only [Hb, and_self, ↓reduceIte]
    wp_apply wp_store_slice_index ohs (sint.Z o.ClientId') sls s7 $$ [Hoh] as Hoh
    · iframe Hoh; ipureintro; word
    ihave Hcos := Hcos $$ %s7 %_ [Hslc Hcapc]
    · iframe
    wp_for_post
    have Hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    have HcidN : ((sint.nat o.ClientId' : Nat) : Int) = sint.Z o.ClientId' := by word
    have Hcid : (sint.Z o.ClientId').toNat = sint.nat o.ClientId' := rfl
    rw [Hcid]
    iframe
    iexists n + W64 1, s5, o, _, _, _
    simp only [named]
    iframe
    ipureintro
    refine ⟨by word, by word, by simp only [List.length_append, List.length_singleton]; word,
      by rw [List.length_set]; exact Hn.2.2.2.1, by rw [List.length_set]; exact Hn.2.2.2.2.1,
      fun c cos hc => ?_⟩
    rw [Hn1, chK_succ, Ho]
    simp only [Option.map_some, Option.some.injEq]
    by_cases hcc : sint.nat o.ClientId' = c
    · subst hcc
      rw [List.getElem?_set_self Hcl'] at hc
      cases hc
      simp only [HcidN, ↓reduceIte]
      refine coFresh_snoc (Hn.2.2.2.2.2 _ _ Hcos0)
        (by rw [histOf_getElem?, Ho]; rfl) (by word) (by word) rfl rfl rfl rfl rfl
    · rw [List.getElem?_set_ne hcc] at hc
      have hne : ¬ sint.Z o.ClientId' = (c : Int) := by
        intro h; apply hcc; omega
      simp only [hne, ↓reduceIte, List.append_nil]
      exact Hn.2.2.2.2.2 _ _ hc
  · have Hn' : sint.nat n = ops.length := by word
    ihave #Hpsort : isPkgInit (PROP := IProp GF) pkg_id.sort $$ []
    · iPkgInit
    ihave #Hsorter := byTime_sorter hLen hLess hSwap s' $$ Hpkg
    wp_apply (hSort entry _ (fun es => iprop(s' ↦* es)) entryLt es entryLt_swo)
      $$ [He] as %l' ⟨He, -⟩
    · iframe #
      iframe He
      ipureintro
      rw [Hn.2.2.1]
      word
    iapply HΦ
    iframe Hs
    isplitl [He]
    · iexists l'; iexact He
    unfold ohistOwn
    iexists sls
    iframe Hoh
    isplitr
    · ipureintro; rw [chainsOf_length]; exact Hn.2.2.2.1
    ihave Hcos := bigSepL2_exists_l _ sls coss $$ Hcos
    iapply BigSepL.bigSepL_mono _ $$ Hcos
    intro c slc Hc
    iintro ⟨%cos, %Hcc, Hslc, -⟩
    iexists cos
    iframe Hslc
    ipureintro
    have hcn : c < sint.nat nc := by
      have := (List.getElem?_eq_some_iff.1 Hc).1
      omega
    rw [chain_chainsOf hcn, ← Hn']
    exact Hn.2.2.2.2.2 c cos Hcc

end proof

end porcupine
end EtcdGrove
end Perennial
