/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/deployment/compatible.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.compatible
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.alone
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.needsSoleWriter
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.writesKeys
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.needsNoExpiry

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : deployment.Assumptions]

theorem compatible.wp_proof
    (hAlone : etcd_dist.alone.spec (GF := GF) (hG := hG))
    (hSole : etcd_dist.needsSoleWriter.spec (GF := GF) (hG := hG))
    (hWrites : etcd_dist.writesKeys.spec (GF := GF) (hG := hG))
    (hNoExp : etcd_dist.needsNoExpiry.spec (GF := GF) (hG := hG)) :
    etcd_dist.compatible.spec (GF := GF) (hG := hG) := by
  intro sl ws
  wp_start as #Hsl
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Bool)) as %m Hm
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  rw [List.length_map] at Hlen
  ihave HI : (∃ (j : Nat) (wv : deployment.Workload) (mp : GMap w64 Bool) (hE hN : Bool),
      "i" ∷ i_ptr ↦ W64 j ∗ "w" ∷ w_ptr ↦ wv ∗ "Hm" ∷ m ↦$ mp ∗
      "hasExpiry" ∷ hasExpiry_ptr ↦ hE ∗ "hasNoExpiry" ∷ hasNoExpiry_ptr ↦ hN ∗
      "%Hj" ∷ ⌜j ≤ ws.length ∧ ((ws.take j).map Workload.kind).Nodup ∧
        (∀ k, mp !! k = if k ∈ (ws.take j).map Workload.kind then some true else none) ∧
        (∀ w ∈ ws.take j, kindAlone w.kind = true → ws.length = 1) ∧
        (hE = true ↔ ∃ w ∈ ws.take j, w.kind = W64 9) ∧
        (hN = true ↔ ∃ w ∈ ws.take j, kindNeedsNoExpiry w.kind = true)⌝ : IProp GF)
    $$ [i w Hm hasExpiry hasNoExpiry]
  · iexists 0, _, ∅, false, false
    iframe
    ipureintro
    refine ⟨by omega, List.nodup_nil, fun k => by simp, fun w hw => by simp at hw, by simp, by simp⟩
  wp_for HI
  obtain ⟨Hj1, Hj2, Hj3, Hj4, Hj5, Hj6⟩ := Hj
  wp_if_destruct
  · have hj : j < ws.length := by word
    have hc : sint.Z (W64 (j : Int)) < sint.Z sl.len := by word
    have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
    simp only [h0, hc, and_self, ↓reduceIte]
    have hsj : (sint.Z (W64 (j : Int))).toNat = j := by word
    obtain ⟨x, hx⟩ : ∃ x, ws[j]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
    wp_apply (wp_load_slice_index sl (sint.Z (W64 (j : Int))) (ws.map Workload.val) DFrac.discard x.val h0) $$ [] as -
    · iframe #; ipureintro; rw [hsj, List.getElem?_map, hx]; rfl
    have hxm : x ∈ ws := List.mem_of_getElem? hx
    have htake : ws.take (j + 1) = ws.take j ++ [x] := by rw [List.take_add_one, hx]; rfl
    have hw : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
    wp_apply (wp_map_lookup1 _ _ m mp x.kind) $$ [Hm] as Hm
    · iframe
    by_cases hdup : x.kind ∈ (ws.take j).map Workload.kind
    · rw [Hj3 x.kind, if_pos hdup]
      simp only [Option.getD_some]
      wp_auto
      wp_for_post
      iapply HΦ
      ipureintro; intro h; cases h
    · rw [Hj3 x.kind, if_neg hdup]
      simp only [Option.getD_none]
      rw [show (zero_val Bool) = false from rfl]
      wp_auto
      wp_apply wp_mapInsert $$ [Hm] as Hm
      · iframe
      have hnd' : ((ws.take (j + 1)).map Workload.kind).Nodup := by
        rw [htake, List.map_append, List.nodup_append]
        refine ⟨Hj2, by simp, ?_⟩
        intro a ha b hb hab
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
        subst hb; subst hab; exact hdup ha
      have hmp' : ∀ k, (<[x.kind := true]> mp) !! k =
          if k ∈ (ws.take (j + 1)).map Workload.kind then some true else none := by
        intro k
        rw [htake, List.map_append]
        by_cases hk : k = x.kind
        · subst hk; simp
        · rw [lookup_insert_ne mp true (Ne.symm hk), Hj3 k]; simp [hk]
      wp_apply hAlone
      by_cases ha : kindAlone x.kind = true
      · rw [ha]
        wp_auto
        wp_if_destruct
        · have hl1 : ws.length = 1 := by word
          wp_if_destruct
          all_goals wp_apply hNoExp
          all_goals (by_cases hn : kindNeedsNoExpiry x.kind = true <;>
            simp only [hn, Bool.not_eq_true] <;> wp_auto)
          all_goals (wp_for_post; iframe; iexists (j + 1), x.val, _, _, _; rw [hw]; iframe; ipureintro)
          all_goals (
            refine ⟨by omega, hnd', hmp', ?_, ?_, ?_⟩
            · intro w hw hal
              rw [htake, List.mem_append, List.mem_singleton] at hw
              rcases hw with hw | rfl
              · exact Hj4 w hw hal
              · first | assumption | (rw [ha] at hal; cases hal)
            · rw [htake]
              first
                | (exact ⟨fun _ => ⟨x, List.mem_append_right _ (List.mem_singleton_self _), by assumption⟩,
                    fun _ => rfl⟩)
                | (rw [Hj5]
                   constructor
                   · rintro ⟨w, hw, hk⟩; exact ⟨w, List.mem_append_left _ hw, hk⟩
                   · rintro ⟨w, hw, hk⟩
                     rcases List.mem_append.1 hw with hw | hw
                     · exact ⟨w, hw, hk⟩
                     · rw [List.mem_singleton] at hw; subst hw
                       first | exact absurd hk ‹_› | (rw [‹kindNeedsNoExpiry _ = false›] at hk; cases hk))
            · rw [htake]
              first
                | (exact ⟨fun _ => ⟨x, List.mem_append_right _ (List.mem_singleton_self _), by assumption⟩,
                    fun _ => rfl⟩)
                | (rw [Hj6]
                   constructor
                   · rintro ⟨w, hw, hk⟩; exact ⟨w, List.mem_append_left _ hw, hk⟩
                   · rintro ⟨w, hw, hk⟩
                     rcases List.mem_append.1 hw with hw | hw
                     · exact ⟨w, hw, hk⟩
                     · rw [List.mem_singleton] at hw; subst hw
                       first | exact absurd hk ‹_› | (rw [‹kindNeedsNoExpiry _ = false›] at hk; cases hk)))
        · wp_for_post
          iapply HΦ
          ipureintro; intro h; cases h
      · rw [Bool.not_eq_true] at ha
        rw [ha]
        wp_auto
        wp_if_destruct
        all_goals wp_apply hNoExp
        all_goals (by_cases hn : kindNeedsNoExpiry x.kind = true <;>
          simp only [hn, Bool.not_eq_true] <;> wp_auto)
        all_goals (wp_for_post; iframe; iexists (j + 1), x.val, _, _, _; rw [hw]; iframe; ipureintro)
        all_goals (
          refine ⟨by omega, hnd', hmp', ?_, ?_, ?_⟩
          · intro w hw hal
            rw [htake, List.mem_append, List.mem_singleton] at hw
            rcases hw with hw | rfl
            · exact Hj4 w hw hal
            · first | assumption | (rw [ha] at hal; cases hal)
          · rw [htake]
            first
              | (exact ⟨fun _ => ⟨x, List.mem_append_right _ (List.mem_singleton_self _), by assumption⟩,
                  fun _ => rfl⟩)
              | (rw [Hj5]
                 constructor
                 · rintro ⟨w, hw, hk⟩; exact ⟨w, List.mem_append_left _ hw, hk⟩
                 · rintro ⟨w, hw, hk⟩
                   rcases List.mem_append.1 hw with hw | hw
                   · exact ⟨w, hw, hk⟩
                   · rw [List.mem_singleton] at hw; subst hw
                     first | exact absurd hk ‹_› | (rw [‹kindNeedsNoExpiry _ = false›] at hk; cases hk))
          · rw [htake]
            first
              | (exact ⟨fun _ => ⟨x, List.mem_append_right _ (List.mem_singleton_self _), by assumption⟩,
                  fun _ => rfl⟩)
              | (rw [Hj6]
                 constructor
                 · rintro ⟨w, hw, hk⟩; exact ⟨w, List.mem_append_left _ hw, hk⟩
                 · rintro ⟨w, hw, hk⟩
                   rcases List.mem_append.1 hw with hw | hw
                   · exact ⟨w, hw, hk⟩
                   · rw [List.mem_singleton] at hw; subst hw
                     first | exact absurd hk ‹_› | (rw [‹kindNeedsNoExpiry _ = false›] at hk; cases hk)))
  · have hjl : j = ws.length := by word
    subst hjl
    rw [List.take_length] at Hj2 Hj3 Hj4 Hj5 Hj6
    rename_i gi_ptr
    irename : (gi_ptr ↦ zero_val w64 : IProp GF) => gi
    ihave HO : (∃ (a : Nat) (wv : deployment.Workload) (gi : w64),
        "i" ∷ i_ptr ↦ W64 a ∗ "w" ∷ w_ptr ↦ wv ∗ "gi" ∷ gi_ptr ↦ gi ∗
        "%Ha" ∷ ⌜a ≤ ws.length ∧ ∀ (i' j' : Nat) (w x : Workload), i' < a → ws[i']? = some w →
          ws[j']? = some x → i' ≠ j' → kindNeedsSoleWriter w.kind = true →
          kindWritesKeys x.kind = false⌝ : IProp GF) $$ [i w gi]
    · iexists 0, _, _
      iframe
      ipureintro
      exact ⟨by omega, fun i' j' w x h => absurd h (by omega)⟩
    wp_for HO
    obtain ⟨Ha1, Ha2⟩ := Ha
    wp_if_destruct
    · have ha : a < ws.length := by word
      have hc : sint.Z (W64 (a : Int)) < sint.Z sl.len := by word
      have h0 : 0 ≤ sint.Z (W64 (a : Int)) := by word
      simp only [h0, hc, and_self, ↓reduceIte]
      have hsa : (sint.Z (W64 (a : Int))).toNat = a := by word
      obtain ⟨y, hy⟩ : ∃ y, ws[a]? = some y := ⟨_, List.getElem?_eq_getElem ha⟩
      wp_apply (wp_load_slice_index sl (sint.Z (W64 (a : Int))) (ws.map Workload.val) DFrac.discard y.val h0) $$ [] as -
      · iframe #; ipureintro; rw [hsa, List.getElem?_map, hy]; rfl
      have hwa : W64 (a : Int) + W64 1 = W64 ((a + 1 : Nat) : Int) := by word
      wp_apply hSole
      by_cases hs : kindNeedsSoleWriter y.kind = true
      · rw [hs]
        wp_auto
        ihave HJ : (∃ (b : Nat) (xv : deployment.Workload) (jv : w64),
            "i" ∷ i_ptr ↦ W64 b ∗ "x" ∷ x_ptr ↦ xv ∗ "j" ∷ j_ptr ↦ jv ∗
            "%Hb" ∷ ⌜b ≤ ws.length ∧ ∀ (j' : Nat) (z : Workload), j' < b → a ≠ j' → ws[j']? = some z →
              kindWritesKeys z.kind = false⌝ : IProp GF) $$ [i x j]
        · iexists 0, _, _
          iframe
          ipureintro
          exact ⟨by omega, fun j' z h => absurd h (by omega)⟩
        wp_for HJ
        obtain ⟨Hb1, Hb2⟩ := Hb
        wp_if_destruct
        · have hb : b < ws.length := by word
          have hcb : sint.Z (W64 (b : Int)) < sint.Z sl.len := by word
          have h0b : 0 ≤ sint.Z (W64 (b : Int)) := by word
          simp only [h0b, hcb, and_self, ↓reduceIte]
          have hsb : (sint.Z (W64 (b : Int))).toNat = b := by word
          obtain ⟨z, hz⟩ : ∃ z, ws[b]? = some z := ⟨_, List.getElem?_eq_getElem hb⟩
          wp_apply (wp_load_slice_index sl (sint.Z (W64 (b : Int))) (ws.map Workload.val) DFrac.discard z.val h0b) $$ [] as -
          · iframe #; ipureintro; rw [hsb, List.getElem?_map, hz]; rfl
          have hwb : W64 (b : Int) + W64 1 = W64 ((b + 1 : Nat) : Int) := by word
          by_cases hab : a = b
          · subst hab
            simp only [decide_true, Bool.not_true]
            wp_auto
            wp_for_post
            iframe
            iexists (a + 1), _, _
            rw [hwb]
            iframe
            ipureintro
            refine ⟨by omega, fun j' z' hj' hne hz' => ?_⟩
            exact Hb2 j' z' (by omega) hne hz'
          · have hW : W64 (a : Int) ≠ W64 (b : Int) := by intro h; apply hab; word
            simp only [hW, decide_false, Bool.not_false]
            wp_auto
            wp_apply hWrites
            by_cases hwk : kindWritesKeys z.kind = true
            · rw [hwk]
              wp_auto
              wp_for_post
              wp_for_post
              iapply HΦ
              ipureintro; intro h; cases h
            · rw [Bool.not_eq_true] at hwk
              rw [hwk]
              wp_auto
              wp_for_post
              iframe
              iexists (b + 1), _, _
              rw [hwb]
              iframe
              ipureintro
              refine ⟨by omega, fun j' z' hj' hne hz' => ?_⟩
              by_cases hjb : j' = b
              · subst hjb; rw [hz] at hz'; cases hz'; exact hwk
              · exact Hb2 j' z' (by omega) hne hz'
        · have hbl : b = ws.length := by word
          subst hbl
          wp_for_post
          iframe
          iexists (a + 1), _, _
          rw [hwa]
          iframe
          ipureintro
          refine ⟨by omega, ?_⟩
          intro i' j' w x hi' hw hx hne hsw
          by_cases hia : i' = a
          · subst hia; rw [hy] at hw; cases hw
            exact Hb2 j' x (List.getElem?_eq_some_iff.1 hx).1 hne hx
          · exact Ha2 i' j' w x (by omega) hw hx hne hsw
      · rw [Bool.not_eq_true] at hs
        rw [hs]
        wp_auto
        wp_for_post
        iframe
        iexists (a + 1), _, _
        rw [hwa]
        iframe
        ipureintro
        refine ⟨by omega, ?_⟩
        intro i' j' w x hi' hw hx hne hsw
        by_cases hia : i' = a
        · subst hia; rw [hy] at hw; cases hw; rw [hs] at hsw; cases hsw
        · exact Ha2 i' j' w x (by omega) hw hx hne hsw
    · have hal : a = ws.length := by word
      subst hal
      have hcomp : (!(hE && hN)) = true → goCompatible ws := by
        intro hr
        refine ⟨Hj2, Hj4, ?_, ?_⟩
        · intro i' j' w x hw hx hne hsw
          exact Ha2 i' j' w x (List.getElem?_eq_some_iff.1 hw).1 hw hx hne hsw
        · rintro ⟨he, hn⟩
          have h1 := Hj5.2 he
          have h2 := Hj6.2 hn
          subst h1; subst h2
          cases hr
      cases hE <;> wp_auto <;> iapply HΦ <;> ipureintro <;> exact hcomp

end proof

end etcd_dist
end EtcdGrove
end Perennial
