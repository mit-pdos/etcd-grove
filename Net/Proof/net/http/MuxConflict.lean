/-
net/http's Go 1.22 conflict check (`pattern.conflictsWith`, the closure `registerErr` passes to
`possiblyConflictingPatterns`) on literal path patterns (`litPat`, `MuxTree.lean`): two distinct
literal patterns never conflict.

* `Rel`: the five `relationship`s, `Rel.s` their strings; `cmpSeg`/`comb` model `compareSegments`
  and `combineRelationships` (`wp_compareSegments` on `segVal`s, `wp_combineRelationships`).
* `wp_comparePaths`: two distinct literal patterns are neither `equivalent` nor `overlaps`. The
  loop's invariant (`cpInv`): the segments compared so far are equal (`equivalent`), or the first
  pattern's are used up after its trailing multi (`moreGeneral`), or the second's (`moreSpecific`);
  a multi is only last (`pathSegs_multi_last`), and equal segment lists are equal patterns
  (`segsStr_pathSegs`).
* `wp_conflictsWith_lit`: so `conflictsWith` is `false` (same empty host and method).
-/
module

public import Net.Proof.net.http.MuxRegister

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http

section pure
variable [GooseExts]

/-- net/http's `relationship`s. -/
inductive Rel | eq | mg | ms | dis | ov
  deriving DecidableEq

/-- A `relationship`'s string (`equivalent`, ...). -/
def Rel.s : Rel → GoString
  | .eq => go!"equivalent"
  | .mg => go!"moreGeneral"
  | .ms => go!"moreSpecific"
  | .dis => go!"disjoint"
  | .ov => go!"overlaps"

theorem Rel.s_inj (a b : Rel) : a.s = b.s ↔ a = b := by
  constructor
  · intro h; cases a <;> cases b <;> first | rfl | (simp [Rel.s] at h)
  · rintro rfl; rfl

/-- `compareSegments` of two literal-pattern segments. -/
def cmpSeg : Seg → Seg → Rel
  | .multi, .multi => .eq
  | .multi, .lit _ => .mg
  | .lit _, .multi => .ms
  | .lit a, .lit b => if a = b then .eq else .dis

/-- `combineRelationships`. -/
def comb : Rel → Rel → Rel
  | .eq, r => r
  | .dis, _ => .dis
  | .ov, r => if r = .dis then .dis else .ov
  | .mg, r => match r with | .eq => .mg | .ms => .ov | r => r
  | .ms, r => match r with | .eq => .ms | .mg => .ov | r => r

theorem pathSegs_ne_nil (p : List w8) (hp : litPat p) : pathSegs p ≠ [] := by
  obtain ⟨t, rfl⟩ : ∃ t, p = W8 47 :: t := by
    cases p with
    | nil => simp [litPat] at hp
    | cons c t => have := hp.1; simp at this; subst this; exact ⟨t, rfl⟩
  by_cases ht : t = []
  · subst ht; rw [pathSegs_slash]; simp
  · rw [pathSegs_cons t ht]; simp

/-- A multi in a literal pattern's segments is its last. -/
theorem multi_at_last (p : List w8) (hp : litPat p) (k : Nat)
    (hk : (pathSegs p)[k]? = some .multi) : (pathSegs p).length = k + 1 := by
  have hlt : k < (pathSegs p).length := by
    rcases Nat.lt_or_ge k (pathSegs p).length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hk; simp at hk
  have hsplit : pathSegs p = (pathSegs p).take k ++ .multi :: (pathSegs p).drop (k + 1) := by
    have hg : (pathSegs p)[k] = .multi := by
      rw [List.getElem?_eq_getElem hlt] at hk; exact Option.some.inj hk
    rw [← hg, ← List.drop_eq_getElem_cons hlt, List.take_append_drop]
  have := pathSegs_multi_last p (.inr hp.1) _ _ hsplit
  have hl := congrArg List.length this
  simp at hl; omega

theorem pathSegs_inj (p q : List w8) (hp : litPat p) (hq : litPat q) (h : pathSegs p = pathSegs q) :
    p = q := by
  rw [← segsStr_pathSegs p (.inr hp.1), ← segsStr_pathSegs q (.inr hq.1), h]

/-- `comparePaths`' loop invariant (see the file header). -/
def cpInv (L1 L2 : List Seg) (k : Nat) (r : Rel) : Prop :=
  k ≤ L1.length ∧ k ≤ L2.length ∧
  ((r = .eq ∧ L1.take k = L2.take k) ∨ (r = .mg ∧ L1.length = k) ∨ (r = .ms ∧ L2.length = k))

theorem take_succ_eq {α : Type} (l1 l2 : List α) (k : Nat) (h1 : k < l1.length) (h2 : k < l2.length)
    (ht : l1.take k = l2.take k) (he : l1[k] = l2[k]) : l1.take (k + 1) = l2.take (k + 1) := by
  rw [List.take_succ, List.take_succ, ht, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, he]

theorem cpInv_step (p1 p2 : List w8) (hp1 : litPat p1) (hp2 : litPat p2) (k : Nat)
    (hc1 : k < (pathSegs p1).length) (hc2 : k < (pathSegs p2).length)
    (ht : (pathSegs p1).take k = (pathSegs p2).take k)
    (hnd : cmpSeg (pathSegs p1)[k] (pathSegs p2)[k] ≠ .dis) :
    cpInv (pathSegs p1) (pathSegs p2) (k + 1) (cmpSeg (pathSegs p1)[k] (pathSegs p2)[k]) := by
  refine ⟨hc1, hc2, ?_⟩
  have g1 : (pathSegs p1)[k]? = some (pathSegs p1)[k] := List.getElem?_eq_getElem hc1
  have g2 : (pathSegs p2)[k]? = some (pathSegs p2)[k] := List.getElem?_eq_getElem hc2
  revert hnd g1 g2
  generalize (pathSegs p1)[k] = a
  generalize (pathSegs p2)[k] = b
  intro hnd g1 g2
  have htk : (pathSegs p1).take (k + 1) = (pathSegs p1).take k ++ [a] := by rw [List.take_succ, g1]; rfl
  have htk2 : (pathSegs p2).take (k + 1) = (pathSegs p2).take k ++ [b] := by rw [List.take_succ, g2]; rfl
  cases a with
  | lit x =>
    cases b with
    | lit y =>
      by_cases hxy : x = y
      · subst hxy
        left; refine ⟨by simp [cmpSeg], ?_⟩
        rw [htk, htk2, ht]
      · exact absurd (by simp [cmpSeg, hxy]) hnd
    | multi => right; right; exact ⟨rfl, multi_at_last p2 hp2 k g2⟩
  | multi =>
    cases b with
    | lit y => right; left; exact ⟨rfl, multi_at_last p1 hp1 k g1⟩
    | multi =>
      left; refine ⟨rfl, ?_⟩
      rw [htk, htk2, ht]

theorem cp_end_both (p1 p2 : List w8) (hp1 : litPat p1) (hp2 : litPat p2) (hne : p1 ≠ p2)
    (k : Nat) (r : Rel) (he1 : (pathSegs p1).length = k) (he2 : (pathSegs p2).length = k)
    (hinv : r = .eq ∧ (pathSegs p1).take k = (pathSegs p2).take k ∨
      r = .mg ∧ (pathSegs p1).length = k ∨ r = .ms ∧ (pathSegs p2).length = k) :
    r ≠ .eq ∧ r ≠ .ov := by
  rcases hinv with ⟨rfl, ht⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exfalso; apply hne; apply pathSegs_inj p1 p2 hp1 hp2
    rw [← List.take_of_length_le (Nat.le_of_eq he1), ← List.take_of_length_le (l := pathSegs p2) (Nat.le_of_eq he2), ht]
  · decide
  · decide

end pure

section wp
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]

theorem wp_compareSegments (a b : Seg) :
    {{ (True : IProp GF) }}
      (App (App (Val (@! net.http.compareSegments)) (Val #(segVal a))) (Val #(segVal b)))
    {{ RET #(cmpSeg a b).s; True }} := by
  wp_start
  cases a <;> cases b <;> simp only [segVal, cmpSeg, Rel.s]
  all_goals simp only [net.http.equivalent, net.http.moreGeneral, net.http.moreSpecific,
    net.http.disjoint, net.http.overlaps]
  all_goals wp_auto
  all_goals try wp_if_destruct
  all_goals try wp_auto
  all_goals try simp only [*, ↓reduceIte]
  all_goals first | (iapply HΦ; done) | (iapply HΦ; ipureintro; trivial)

theorem wp_inverseRelationship (r : Rel) :
    {{ (True : IProp GF) }}
      (App (Val (@! net.http.inverseRelationship)) (Val #r.s))
    {{ RET #(match r with | .mg => Rel.ms | .ms => Rel.mg | r => r).s; True }} := by
  wp_start
  cases r <;> simp only [Rel.s]
  all_goals simp only [net.http.equivalent, net.http.moreGeneral, net.http.moreSpecific,
    net.http.disjoint, net.http.overlaps]
  all_goals wp_auto
  all_goals try wp_if_destruct
  all_goals try wp_auto
  all_goals try simp only [*, ↓reduceIte]
  all_goals first | (iapply HΦ; done) | (iapply HΦ; ipureintro; trivial)

theorem wp_inverseRelationship_mg :
    {{ (True : IProp GF) }}
      (App (Val (@! net.http.inverseRelationship)) (Val #(go!"moreGeneral")))
    {{ RET #(go!"moreSpecific"); True }} := wp_inverseRelationship .mg

theorem wp_inverseRelationship_ms :
    {{ (True : IProp GF) }}
      (App (Val (@! net.http.inverseRelationship)) (Val #(go!"moreSpecific")))
    {{ RET #(go!"moreGeneral"); True }} := wp_inverseRelationship .ms

theorem wp_combineRelationships (r1 r2 : Rel) :
    {{ (True : IProp GF) }}
      (App (App (Val (@! net.http.combineRelationships)) (Val #r1.s)) (Val #r2.s))
    {{ RET #(comb r1 r2).s; True }} := by
  cases r1 <;> cases r2 <;> simp only [comb, ↓reduceIte, reduceCtorEq]
  all_goals wp_start
  all_goals simp only [Rel.s, net.http.equivalent, net.http.moreGeneral, net.http.moreSpecific,
    net.http.disjoint, net.http.overlaps]
  all_goals wp_auto
  all_goals try (first | wp_apply wp_inverseRelationship_mg | wp_apply wp_inverseRelationship_ms)
  all_goals try wp_auto
  all_goals first | (iapply HΦ; done) | (iapply HΦ; ipureintro; trivial)

theorem wp_combineRelationships_mg (r : Rel) :
    {{ (True : IProp GF) }}
      (App (App (Val (@! net.http.combineRelationships)) (Val #r.s)) (Val #(go!"moreGeneral")))
    {{ RET #(comb r .mg).s; True }} := wp_combineRelationships r .mg

theorem wp_combineRelationships_ms (r : Rel) :
    {{ (True : IProp GF) }}
      (App (App (Val (@! net.http.combineRelationships)) (Val #r.s)) (Val #(go!"moreSpecific")))
    {{ RET #(comb r .ms).s; True }} := wp_combineRelationships r .ms

set_option hygiene false in
/-- `comparePaths` after its first check: the loop and the end (see `wp_comparePaths`). -/
local macro "cp_rest" : tactic => `(tactic| (
    simp only [net.http.equivalent, net.http.disjoint, net.http.moreGeneral, net.http.moreSpecific]
    wp_auto
    ihave HI : (∃ (k : Nat) (s1 s2 : GoSlice) (r : Rel),
        "segs1" ∷ segs1_ptr ↦ s1 ∗ "segs2" ∷ segs2_ptr ↦ s2 ∗ "rel" ∷ rel_ptr ↦ r.s ∗
        "#Hs1" ∷ s1 ↦*□ ((pathSegs p1).drop k).map segVal ∗
        "#Hs2" ∷ s2 ↦*□ ((pathSegs p2).drop k).map segVal ∗
        "%Hk" ∷ ⌜cpInv (pathSegs p1) (pathSegs p2) k r⌝ : IProp GF) $$ [segs1 segs2 rel]
    · iexists 0, sl1, sl2, .eq
      simp only [List.drop_zero, Rel.s]
      iframe; iframe #
      ipureintro; exact ⟨Nat.zero_le _, Nat.zero_le _, .inl ⟨rfl, rfl⟩⟩
    wp_for HI
    ihave %Hl1 := ownSlice_len _ _ _ $$ Hs1
    ihave %Hl2 := ownSlice_len _ _ _ $$ Hs2
    simp only [List.length_map, List.length_drop] at Hl1 Hl2
    obtain ⟨hk1, hk2, hinv⟩ := Hk
    by_cases hc : k < (pathSegs p1).length ∧ k < (pathSegs p2).length
    · rw [decide_eq_true (show sint.Z (W64 0) < sint.Z s1.len by word)]
      wp_auto
      rw [decide_eq_true (show sint.Z (W64 0) < sint.Z s2.len by word)]
      rw [decide_eq_true (rfl : (#true : val) = #true), if_pos rfl]
      wp_auto
      obtain ⟨hc1, hc2⟩ := hc
      have h01 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z s1.len := ⟨by word, by word⟩
      rw [ite_cond_eq_true _ _ (eq_true h01)]
      wp_apply wp_load_slice_index s1 (sint.Z (W64 0)) _ _ (segVal (pathSegs p1)[k]) h01.1 $$ [Hs1] as -
      · iframe #; ipureintro
        rw [show (sint.Z (W64 0)).toNat = 0 by rfl]
        simp [List.getElem?_drop, hc1]
      have h02 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z s2.len := ⟨by word, by word⟩
      rw [ite_cond_eq_true _ _ (eq_true h02)]
      wp_apply wp_load_slice_index s2 (sint.Z (W64 0)) _ _ (segVal (pathSegs p2)[k]) h02.1 $$ [Hs2] as -
      · iframe #; ipureintro
        rw [show (sint.Z (W64 0)).toNat = 0 by rfl]
        simp [List.getElem?_drop, hc2]
      wp_apply wp_compareSegments
      wp_apply wp_combineRelationships
      have hr : r = .eq := by
        rcases hinv with h | h | h
        · exact h.1
        · omega
        · omega
      subst hr
      wp_if_destruct
      · wp_for_post
        try wp_auto
        iapply HΦ
        ipureintro
        have := (Rel.s_inj _ Rel.dis).1 Hif
        rw [this]; decide
      · wp_for_post
        ihave %Hwf1 := ownSlice_wf _ _ _ $$ Hs1
        ihave %Hwf2 := ownSlice_wf _ _ _ $$ Hs2
        have hb1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z s1.len ∧ sint.Z s1.len ≤ sint.Z s1.cap :=
          ⟨by word, by word, by word⟩
        rw [ite_cond_eq_true _ _ (eq_true hb1)]
        wp_auto
        have hb2 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z s2.len ∧ sint.Z s2.len ≤ sint.Z s2.cap :=
          ⟨by word, by word, by word⟩
        rw [ite_cond_eq_true _ _ (eq_true hb2)]
        wp_auto
        icases (ownSlice_slice (W64 1) s1.len s1 DFrac.discard _ ⟨hb1.1, hb1.2.1, by word⟩).1 $$ Hs1
          with ⟨-, #Hs1', -⟩
        icases (ownSlice_slice (W64 1) s2.len s2 DFrac.discard _ ⟨hb2.1, hb2.2.1, by word⟩).1 $$ Hs2
          with ⟨-, #Hs2', -⟩
        have hsub1 : subslice (sint.nat (W64 1)) (sint.nat s1.len) (List.map segVal (List.drop k (pathSegs p1))) =
            List.map segVal (List.drop (k + 1) (pathSegs p1)) := by
          rw [show sint.nat (W64 1) = 1 by word, show sint.nat s1.len = (pathSegs p1).length - k by word]
          simp only [subslice, List.map_drop]
          rw [List.take_of_length_le (by simp), List.drop_drop, Nat.add_comm]
        have hsub2 : subslice (sint.nat (W64 1)) (sint.nat s2.len) (List.map segVal (List.drop k (pathSegs p2))) =
            List.map segVal (List.drop (k + 1) (pathSegs p2)) := by
          rw [show sint.nat (W64 1) = 1 by word, show sint.nat s2.len = (pathSegs p2).length - k by word]
          simp only [subslice, List.map_drop]
          rw [List.take_of_length_le (by simp), List.drop_drop, Nat.add_comm]
        rw [hsub1] at *
        rw [hsub2] at *
        iframe
        iexists k + 1, _, _, comb .eq (cmpSeg (pathSegs p1)[k] (pathSegs p2)[k])
        iframe; iframe #
        ipureintro
        have ht : (pathSegs p1).take k = (pathSegs p2).take k := by
          rcases hinv with h | h | h
          · exact h.2
          · omega
          · omega
        exact cpInv_step p1 p2 hp1 hp2 k hc1 hc2 ht (fun h => Hif (by rw [show comb Rel.eq _ = _ from rfl, h]; rfl))
    · have hex : (pathSegs p1).length = k ∨ (k < (pathSegs p1).length ∧ (pathSegs p2).length = k) := by
        omega
      rcases hex with he | ⟨he1, he2⟩
      · rw [decide_eq_false (show ¬ sint.Z (W64 0) < sint.Z s1.len by word)]
        wp_auto
        simp only [decide_eq_false false_neq_true, Bool.false_eq_true, ↓reduceIte,
          _root_.decide_true]
        wp_auto
        rw [decide_eq_true (show s1.len = W64 0 by word)]
        wp_auto
        by_cases he2 : (pathSegs p2).length = k
        · rw [decide_eq_true (show s2.len = W64 0 by word)]
          wp_auto
          iapply HΦ; ipureintro
          exact cp_end_both p1 p2 hp1 hp2 hne k r he he2 hinv
        · rw [decide_eq_false (show s2.len ≠ W64 0 by word)]
          wp_auto
          rw [decide_eq_true (show sint.Z s1.len < sint.Z s2.len by word)]
          wp_auto
          wp_apply (wp_lastSegment pp1 p1 _ hx1)
          · iunfold patRep; iexists sl1, loc1; iframe #
          cases hm1 : (pathSegs p1).getLast hne1 with
          | multi =>
            simp only [segVal]
            wp_auto
            wp_apply wp_combineRelationships_mg
            iapply HΦ; ipureintro
            rcases hinv with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, h⟩
            · decide
            · decide
            · omega
          | lit s =>
            simp only [segVal]
            wp_auto
            rw [decide_eq_false (show ¬ sint.Z s2.len < sint.Z s1.len by word)]
            wp_auto
            rw [show (#(go!"disjoint") : val) = #Rel.dis.s from rfl]
            iapply HΦ; ipureintro; decide
      · rw [decide_eq_true (show sint.Z (W64 0) < sint.Z s1.len by word)]
        wp_auto
        rw [decide_eq_false (show ¬ sint.Z (W64 0) < sint.Z s2.len by word)]
        simp only [decide_eq_false false_neq_true, Bool.false_eq_true, ↓reduceIte,
          _root_.decide_true]
        wp_auto
        rw [decide_eq_false (show s1.len ≠ W64 0 by word)]
        wp_auto
        rw [decide_eq_false (show ¬ sint.Z s1.len < sint.Z s2.len by word)]
        wp_auto
        rw [decide_eq_true (show sint.Z s2.len < sint.Z s1.len by word)]
        wp_auto
        wp_apply (wp_lastSegment pp2 p2 _ hx2)
        · iunfold patRep; iexists sl2, loc2; iframe #
        cases hm2 : (pathSegs p2).getLast hne2 with
        | multi =>
          simp only [segVal]
          wp_auto
          wp_apply wp_combineRelationships_ms
          iapply HΦ; ipureintro
          rcases hinv with ⟨rfl, _⟩ | ⟨rfl, h⟩ | ⟨rfl, _⟩
          · decide
          · omega
          · decide
        | lit s =>
          simp only [segVal]
          wp_auto
          rw [show (#(go!"disjoint") : val) = #Rel.dis.s from rfl]
          iapply HΦ; ipureintro; decide
  ))

theorem wp_comparePaths (pp1 pp2 : Loc) (p1 p2 : List w8) (hp1 : litPat p1) (hp2 : litPat p2)
    (hne : p1 ≠ p2) :
    {{ patRep (GF := GF) (hG := hG) pp1 p1 ∗ patRep (GF := GF) (hG := hG) pp2 p2 }}
      (App (Val (pp1 @!! go.GoType.PointerType net.http.pattern.ty @!! go!"comparePaths")) (Val #pp2))
    {{ (r : Rel), RET #r.s; ⌜r ≠ .eq ∧ r ≠ .ov⌝ }} := by
  wp_start as ⟨#H1, #H2⟩
  iunfold patRep at H1 H2
  icases H1 with ⟨%sl1, %loc1, #Hp1, #Hsl1⟩
  icases H2 with ⟨%sl2, %loc2, #Hp2, #Hsl2⟩
  ihave %Hlen1 := ownSlice_len _ _ _ $$ Hsl1
  ihave %Hlen2 := ownSlice_len _ _ _ $$ Hsl2
  iStructNamedPrefix Hp1 "P1"
  iStructNamedPrefix Hp2 "P2"
  wp_auto
  have hne1 := pathSegs_ne_nil p1 hp1
  have hne2 := pathSegs_ne_nil p2 hp2
  have hx1 : (pathSegs p1).getLast? = some ((pathSegs p1).getLast hne1) := List.getLast?_eq_getLast _
  have hx2 : (pathSegs p2).getLast? = some ((pathSegs p2).getLast hne2) := List.getLast?_eq_getLast _
  by_cases hl : sl1.len = sl2.len
  · simp only [hl, _root_.decide_true, Bool.not_true]
    wp_auto
    cp_rest
  · simp only [hl, _root_.decide_false, Bool.not_false]
    wp_auto
    wp_apply (wp_lastSegment pp1 p1 _ hx1)
    · iunfold patRep; iexists sl1, loc1; iframe #
    cases hm1 : (pathSegs p1).getLast hne1 with
    | multi =>
      simp only [segVal]
      wp_auto
      cp_rest
    | lit s =>
      simp only [segVal]
      wp_auto
      wp_apply (wp_lastSegment pp2 p2 _ hx2)
      · iunfold patRep; iexists sl2, loc2; iframe #
      cases hm2 : (pathSegs p2).getLast hne2 with
      | multi =>
        simp only [segVal]
        wp_auto
        cp_rest
      | lit s' =>
        simp only [segVal]
        wp_auto
        simp only [net.http.disjoint]
        wp_auto
        rw [show (#(go!"disjoint") : val) = #Rel.dis.s from rfl]
        iapply HΦ; ipureintro; decide

theorem wp_compareMethods (pp1 pp2 : Loc) (p1 p2 : List w8) :
    {{ patRep (GF := GF) (hG := hG) pp1 p1 ∗ patRep (GF := GF) (hG := hG) pp2 p2 }}
      (App (Val (pp1 @!! go.GoType.PointerType net.http.pattern.ty @!! go!"compareMethods")) (Val #pp2))
    {{ RET #Rel.eq.s; True }} := by
  wp_start as ⟨#H1, #H2⟩
  iunfold patRep at H1 H2
  icases H1 with ⟨%sl1, %loc1, #Hp1, #Hsl1⟩
  icases H2 with ⟨%sl2, %loc2, #Hp2, #Hsl2⟩
  iStructNamedPrefix Hp1 "P1"
  iStructNamedPrefix Hp2 "P2"
  wp_auto
  simp only [net.http.equivalent]
  wp_auto
  rw [show (#(go!"equivalent") : val) = #Rel.eq.s from rfl]
  iapply HΦ; ipureintro; trivial

theorem wp_comparePathsAndMethods (pp1 pp2 : Loc) (p1 p2 : List w8) (hp1 : litPat p1) (hp2 : litPat p2) (hne : p1 ≠ p2) :
    {{ patRep (GF := GF) (hG := hG) pp1 p1 ∗ patRep (GF := GF) (hG := hG) pp2 p2 }}
      (App (Val (pp1 @!! go.GoType.PointerType net.http.pattern.ty @!! go!"comparePathsAndMethods")) (Val #pp2))
    {{ (r : Rel), RET #r.s; ⌜r ≠ .eq ∧ r ≠ .ov⌝ }} := by
  wp_start as ⟨#H1, #H2⟩
  wp_auto
  wp_apply (wp_compareMethods pp1 pp2 p1 p2) $$ [$H1 $H2]
  wp_apply (wp_comparePaths pp1 pp2 p1 p2 hp1 hp2 hne) $$ [$H1 $H2] as %r %hr
  wp_apply wp_combineRelationships
  iapply HΦ; ipureintro; exact hr

/-- Two distinct literal patterns do not conflict. -/
theorem wp_conflictsWith_lit (pp1 pp2 : Loc) (p1 p2 : List w8) (hp1 : litPat p1) (hp2 : litPat p2)
    (hne : p1 ≠ p2) :
    {{ patRep (GF := GF) (hG := hG) pp1 p1 ∗ patRep (GF := GF) (hG := hG) pp2 p2 }}
      (App (Val (pp1 @!! go.GoType.PointerType net.http.pattern.ty @!! go!"conflictsWith")) (Val #pp2))
    {{ RET #false; True }} := by
  wp_start as ⟨#H1, #H2⟩
  ihave #H1' := H1
  ihave #H2' := H2
  iunfold patRep at H1' H2'
  icases H1' with ⟨%sl1, %loc1, #Hp1, #Hsl1⟩
  icases H2' with ⟨%sl2, %loc2, #Hp2, #Hsl2⟩
  iStructNamedPrefix Hp1 "P1"
  iStructNamedPrefix Hp2 "P2"
  wp_auto
  wp_apply (wp_comparePathsAndMethods pp1 pp2 p1 p2 hp1 hp2 hne) $$ [$H1 $H2] as %r %hr
  rw [decide_eq_false (show r.s ≠ go!"equivalent" from fun h => hr.1 ((Rel.s_inj r .eq).1 h))]
  simp only [net.http.overlaps]
  wp_auto
  rw [decide_eq_false (show r.s ≠ go!"overlaps" from fun h => hr.2 ((Rel.s_inj r .ov).1 h))]
  iapply HΦ; ipureintro; trivial

end wp

end net.http
end Perennial
