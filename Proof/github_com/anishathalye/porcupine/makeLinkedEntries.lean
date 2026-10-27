/- Lean-first (no Rocq counterpart).

`makeLinkedEntries(entries)`: a loop from the last entry to the first, each node inserted at the
front of the list built so far; `match` maps an id to its return's node (a return is after its
call, so it is built first).
-/
module

public import Spec.github_com.anishathalye.porcupine.makeLinkedEntries
public import Spec.github_com.anishathalye.porcupine.insertBefore

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

theorem makeLinkedEntries.wp_proof (wp_insertBefore : insertBefore.spec (GF := GF) (hG := hG)) :
    makeLinkedEntries.spec (GF := GF) (hG := hG) := fun hsl es dq h hes hlen => by
  wp_start as Hsl
  ihave %Hsl_len := ownSlice_len $$ Hsl
  wp_auto
  obtain ⟨hlen2, hok, hent⟩ := hes
  obtain ⟨Hsl_len, Hsl_nn⟩ := Hsl_len
  have hnd : (es.map entryOf).Nodup := entriesOk_nodup hok (by simpa using hlen2)
  wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %mref HM
  ihave HI : (∃ (i : w64) (M : GMap w64 Loc) (loc : Entry → Loc),
      "i" ∷ i_ptr ↦ i ∗
      "root" ∷ root_ptr ↦ headLoc loc ((es.map entryOf).drop (sint.nat (i + 1))) ∗
      "HM" ∷ mref ↦$ M ∗
      "Hl" ∷ linked loc (valOf h) null ((es.map entryOf).drop (sint.nat (i + 1))) ∗
      "%Hi" ∷ ⌜-1 ≤ sint.Z i ∧ sint.Z i < sint.Z hsl.len ∧
        (∀ e ∈ (es.map entryOf).drop (sint.nat (i + 1)), loc e ≠ null) ∧
        (∀ y, (⟨true, y⟩ : Entry) ∈ (es.map entryOf).drop (sint.nat (i + 1)) →
          M !! W64 y = some (loc ⟨true, y⟩))⌝ : IProp GF) $$ [i root HM]
  · iexists hsl.len - W64 1, _, (fun _ => null)
    have hd0 : (es.map entryOf).drop (sint.nat (hsl.len - W64 1 + 1)) = [] := by
      rw [show sint.nat (hsl.len - W64 1 + 1) = (es.map entryOf).length by
        rw [List.length_map]; word]
      exact List.drop_length
    rw [hd0]
    simp only [headLoc, linked]
    iframe
    ipureintro
    have h1 : sint.Z (hsl.len - W64 1) = sint.Z hsl.len - 1 := by clear hent; word
    refine ⟨trivial, by omega, by omega, by simp, by simp⟩
  irename «match» => Hmatch
  wp_for HI
  wp_if_destruct
  · obtain ⟨Hi1, Hi2, Hi3, Hi4⟩ := Hi
    have hi0 : 0 ≤ sint.Z i := Hif
    have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z hsl.len := ⟨hi0, Hi2⟩
    simp only [Hb, _root_.and_self, ↓reduceIte]
    list_elem es (sint.nat i) as ge
    wp_apply wp_load_slice_index hsl (sint.Z i) es dq ge hi0 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hge_lookup
    -- the entry, abstractly
    have hk : (es.map entryOf)[sint.nat i]? = some (entryOf ge) := by
      rw [List.getElem?_map, Hge_lookup]; rfl
    have hdrop : (es.map entryOf).drop (sint.nat i) =
        entryOf ge :: (es.map entryOf).drop (sint.nat (i + 1)) := by
      rw [show sint.nat (i + 1) = sint.nat i + 1 by word]
      exact List.drop_eq_getElem_cons (by simpa using (List.getElem?_eq_some_iff.mp hk).1) |>.trans
        (by rw [(List.getElem?_eq_some_iff.mp hk).2])
    obtain ⟨hid0, o, ho, hval⟩ := hent ge (List.mem_of_getElem? Hge_lookup)
    have hidw : W64 (entryOf ge).id = ge.id' := by simp only [entryOf]; word
    have hvalOf : valOf h (entryOf ge) = ge.value' := by
      simp only [valOf, entryOf, ho]
      by_cases hkind : ge.kind' = true
      · simp only [hkind, ↓reduceIte] at hval ⊢; exact hval.1.symm
      · simp only [hkind, Bool.false_eq_true, ↓reduceIte] at hval ⊢; exact hval.1.symm
    have hk1 : sint.nat (i - W64 1 + 1) = sint.nat i := by word
    have hndk : ((es.map entryOf).drop (sint.nat i)).Nodup := hnd.sublist (List.drop_sublist _ _)
    rw [hdrop] at hndk
    have hnot : entryOf ge ∉ (es.map entryOf).drop (sint.nat (i + 1)) := (List.nodup_cons.mp hndk).1
    have hrc := entriesOk_retClosed_drop hok (sint.nat (i + 1))
    have hidlt : ∀ e ∈ es.map entryOf, e.id < h.length := fun e he => (hok.2.1 e).mp he
    have hage : (entryOf ge).id < h.length := hidlt _ (List.mem_of_getElem? hk)
    have hnode_ret : ge.kind' = true → ∀ n nx : Loc,
        (⟨ge.value', null, ge.id', nx, null⟩ : node) =
          linkedNode (upd loc (entryOf ge) n) (valOf h) null (entryOf ge) nx := by
      intro hr n nx
      have : (entryOf ge).isRet = true := hr
      unfold linkedNode
      rw [hvalOf, hidw]
      simp only [this, ↓reduceIte]
    have hbounds : -1 ≤ sint.Z (i - W64 1) ∧ sint.Z (i - W64 1) < sint.Z hsl.len := by
      constructor <;> word
    have hnn' : ∀ n : Loc, n ≠ null → ∀ e ∈ entryOf ge :: (es.map entryOf).drop (sint.nat (i + 1)),
        upd loc (entryOf ge) n e ≠ null := by
      intro n hn e he
      by_cases hea : e = entryOf ge
      · subst hea; rw [upd_self]; exact hn
      · rw [upd_ne hea]; exact Hi3 e ((List.mem_cons.mp he).resolve_left hea)
    have hsub : ∀ e ∈ (es.map entryOf).drop (sint.nat (i + 1)), e ∈ es.map entryOf :=
      fun e he => List.mem_of_mem_drop he
    have hmap_ret : ge.kind' = true → ∀ (n : Loc) (y : Nat),
        (⟨true, y⟩ : Entry) ∈ entryOf ge :: (es.map entryOf).drop (sint.nat (i + 1)) →
        (<[ge.id' := n]> M) !! W64 y = some (upd loc (entryOf ge) n ⟨true, y⟩) := by
      intro hr n y hy
      rw [GMap.lookup_insert_eq_iff]
      by_cases hya : (⟨true, y⟩ : Entry) = entryOf ge
      · have : ge.id' = W64 y := by rw [← hidw, ← hya]
        rw [ite_eq_left this, ← hya, upd_self]
      · have hy' := (List.mem_cons.mp hy).resolve_left hya
        have hyl : y < h.length := hidlt _ (hsub _ hy')
        have hne : y ≠ (entryOf ge).id := fun h' => hya (by
          simp only [entryOf, Entry.mk.injEq] at h' ⊢; exact ⟨hr.symm, h'⟩)
        have : ge.id' ≠ W64 y := by
          rw [← hidw]; intro h'; apply hne
          have := congrArg (fun x : w64 => uint.Z x) h'
          word
        rw [ite_eq_right this, upd_ne hya]
        exact Hi4 y hy'
    have hmap_call : ge.kind' = false → ∀ (n : Loc) (y : Nat),
        (⟨true, y⟩ : Entry) ∈ entryOf ge :: (es.map entryOf).drop (sint.nat (i + 1)) →
        M !! W64 y = some (upd loc (entryOf ge) n ⟨true, y⟩) := by
      intro hc n y hy
      have hya : (⟨true, y⟩ : Entry) ≠ entryOf ge := by
        simp only [entryOf, ne_eq, Entry.mk.injEq, not_and]; intro h'; rw [hc] at h'; cases h'
      rw [upd_ne hya]
      exact Hi4 y ((List.mem_cons.mp hy).resolve_left hya)
    wp_if_destruct
    · -- a return
      irename «$r0» => Hn
      ihave %Hnn := typedPointsto_not_null $$ Hn
      wp_apply wp_mapInsert $$ HM as HM
      rcases hs : (es.map entryOf).drop (sint.nat (i + 1)) with _ | ⟨b, l⟩
      · rw [show headLoc loc [] = null from rfl]
        wp_apply wp_insertBefore «$r0_ptr» _ null (zero_val node) $$ [Hn] as (⟨-, Hn⟩ | ⟨-, Hm⟩)
        · iframe; ileft; ipureintro; rfl
        · wp_auto
          wp_for_post
          iframe
          iexists i - W64 1, _, upd loc (entryOf ge) «$r0_ptr»
          rw [hk1, hdrop, hs]
          rw [hnode_ret Hif «$r0_ptr» null]
          iclear Hl
          ihave Hl := linked_prepend loc (valOf h) (entryOf ge) «$r0_ptr» [] (by simp)
            (fun _ h => by simp at h) $$ [Hn]
          · iframe; simp only [linked]; itrivial
          rw [show headLoc (upd loc (entryOf ge) «$r0_ptr») [entryOf ge] = «$r0_ptr» from upd_self _ _ _]
          iframe
          ipureintro
          have h3 := hnn' _ Hnn
          have h4 := hmap_ret Hif «$r0_ptr»
          rw [hs] at h3 h4
          exact ⟨hbounds.1, hbounds.2, h3, h4⟩
        · ihave %Hc := typedPointsto_not_null $$ Hm
          exact absurd rfl Hc
      · rw [hs] at hnot hrc hnn' hmap_ret Hi3
        rw [show headLoc loc (b :: l) = loc b from rfl]
        simp only [linked]
        icases Hl with ⟨Hb, Hl⟩
        wp_apply wp_insertBefore «$r0_ptr» _ (loc b) _ $$ [Hn Hb] as (⟨%Hc, -⟩ | ⟨Hn, Hb⟩)
        · iframe; iright; iframe; ipureintro; rfl
        · exact absurd Hc (Hi3 b (by simp))
        · wp_auto
          wp_for_post
          iframe
          iexists i - W64 1, _, upd loc (entryOf ge) «$r0_ptr»
          rw [hk1, hdrop, hs]
          isimp at Hn
          rw [hnode_ret Hif «$r0_ptr» (loc b), linkedNode_prev]
          ihave Hl := linked_prepend loc (valOf h) (entryOf ge) «$r0_ptr» (b :: l) hnot hrc
            $$ [Hn Hb Hl]
          · rw [show headLoc loc (b :: l) = loc b from rfl]
            simp only [linked]
            iframe
          rw [show headLoc (upd loc (entryOf ge) «$r0_ptr») (entryOf ge :: b :: l) = «$r0_ptr» from
            upd_self _ _ _]
          iframe
          ipureintro
          exact ⟨hbounds.1, hbounds.2, hnn' _ Hnn, hmap_ret Hif _⟩
    · -- a call
      have hc : ge.kind' = false := by simpa using Hif
      have hae : entryOf ge = ⟨false, (entryOf ge).id⟩ := by simp only [entryOf, hc]
      -- its return is later
      have hrin : (⟨true, (entryOf ge).id⟩ : Entry) ∈ (es.map entryOf).drop (sint.nat (i + 1)) := by
        have h1 := entriesOk_retClosed_drop hok (sint.nat i) (entryOf ge).id
          (by rw [hdrop, ← hae]; exact List.mem_cons_self ..)
        rw [hdrop] at h1
        refine (List.mem_cons.mp h1).resolve_left ?_
        intro h'; rw [hae] at h'; cases h'
      have hlook : (M !! ge.id').getD (zero_val Loc) = loc ⟨true, (entryOf ge).id⟩ := by
        rw [← hidw, Hi4 _ hrin]; rfl
      have hra : (⟨true, (entryOf ge).id⟩ : Entry) ≠ entryOf ge := by
        intro h'; rw [hae] at h'; cases h'
      have hnode_call : ∀ n nx : Loc,
          (⟨ge.value', loc ⟨true, (entryOf ge).id⟩, ge.id', nx, null⟩ : node) =
            linkedNode (upd loc (entryOf ge) n) (valOf h) null (entryOf ge) nx := by
        intro n nx
        have : (entryOf ge).isRet = false := hc
        unfold linkedNode
        rw [hvalOf, hidw, upd_ne hra]
        simp only [this, Bool.false_eq_true, ↓reduceIte]
      wp_apply (wp_map_lookup1 (K := w64) (V := Loc)) $$ HM as HM
      rw [hlook]
      irename «$r0» => Hn
      ihave %Hnn := typedPointsto_not_null $$ Hn
      rcases hs : (es.map entryOf).drop (sint.nat (i + 1)) with _ | ⟨b, l⟩
      · rw [hs] at hrin; cases hrin
      · rw [hs] at hnot hrc hnn' hmap_call Hi3
        rw [show headLoc loc (b :: l) = loc b from rfl]
        simp only [linked]
        icases Hl with ⟨Hb, Hl⟩
        wp_apply wp_insertBefore «$r0_ptr» _ (loc b) _ $$ [Hn Hb] as (⟨%Hc, -⟩ | ⟨Hn, Hb⟩)
        · iframe; iright; iframe; ipureintro; rfl
        · exact absurd Hc (Hi3 b (by simp))
        · wp_auto
          wp_for_post
          iframe
          iexists i - W64 1, _, upd loc (entryOf ge) «$r0_ptr»
          rw [hk1, hdrop, hs]
          isimp at Hn
          rw [hnode_call «$r0_ptr» (loc b), linkedNode_prev]
          ihave Hl := linked_prepend loc (valOf h) (entryOf ge) «$r0_ptr» (b :: l) hnot hrc
            $$ [Hn Hb Hl]
          · rw [show headLoc loc (b :: l) = loc b from rfl]
            simp only [linked]
            iframe
          rw [show headLoc (upd loc (entryOf ge) «$r0_ptr») (entryOf ge :: b :: l) = «$r0_ptr» from
            upd_self _ _ _]
          iframe
          ipureintro
          exact ⟨hbounds.1, hbounds.2, hnn' _ Hnn, hmap_call hc _⟩
  · obtain ⟨Hi1, Hi2, Hi3, Hi4⟩ := Hi
    have hi : sint.nat (i + 1) = 0 := by
      have : ¬ (0 ≤ sint.Z i) := Hif
      word
    rw [hi, List.drop_zero]
    rw [hi, List.drop_zero] at Hi3
    iapply HΦ
    iframe
    ipureintro
    exact ⟨rfl, Hi3⟩

end proof

end porcupine
end EtcdGrove
end Perennial
