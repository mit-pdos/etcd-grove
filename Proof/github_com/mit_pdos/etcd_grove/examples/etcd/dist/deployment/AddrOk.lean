/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/AddrOk.lean`: the first loop follows `scanGo` (the pieces between the separators into `parts`), the second runs `decimal` on each piece (`decimalM`), the result is `goAddrOk a`, which is `addrOk a` (`goAddrOk_eq`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.AddrOk
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.decimal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Assumptions]

set_option hygiene false in
/-- `AddrOk`'s first loop at a separator it takes (`hstep`: the scan past it; `hn5`: at most four
pieces done after it): the piece stored in `parts[n]`, `n` and `start` moved on. -/
local macro "addrok_store" : tactic => `(tactic| (
  rw [if_pos ⟨Hst0, by word, by word⟩]
  try wp_auto
  obtain ⟨xn, hxn⟩ : ∃ x, arr[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  icases array_acc (GF := GF) _ (sint.Z n) _ _ (array.mk 5 arr : GoArray GoString 5) xn Hn0
    hxn $$ parts with ⟨Hel, Hcl⟩
  try wp_auto
  rw [if_pos ⟨Hn0, by word⟩]
  try wp_auto
  ihave parts := Hcl $$ Hel
  wp_for_post
  iframe
  iexists i + W64 1, n + W64 1, i + W64 1, _
  iframe
  ipureintro
  have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
  refine ⟨by simp [Hlen5], by word, by word, by word, by word, fun _ => ⟨Nat.le_refl _, by omega, ?_⟩,
    fun h => absurd h (by omega)⟩
  rw [hi1, hn1, hstep, Nat.sub_self, List.take_zero,
    show (sint.Z n).toNat = sint.nat n from rfl, take_set_succ arr _ _ (by omega)]))

private theorem addr_close (Φ : val → IProp GF) (b1 b2 : Bool) (h : b1 = b2) :
    (True -∗ Φ #b1) ⊢ Φ #b2 := by
  rw [h]
  iintro H
  iapply H
  itrivial

theorem AddrOk.wp_proof (wp_decimal : etcd_dist.decimal.spec (GF := GF) (hG := hG)) : etcd_dist.AddrOk.spec (GF := GF) (hG := hG) := by
  intro a ha
  wp_start
  try wp_auto
  ihave HI : (∃ (i n st : w64) (arr : List GoString),
      "i" ∷ i_ptr ↦ i ∗ "n" ∷ n_ptr ↦ n ∗ "start" ∷ start_ptr ↦ st ∗
      "parts" ∷ parts_ptr ↦ (array.mk 5 arr : GoArray GoString 5) ∗
      "%Hinv" ∷ ⌜arr.length = 5 ∧ 0 ≤ sint.Z i ∧ 0 ≤ sint.Z n ∧ 0 ≤ sint.Z st ∧
        sint.nat i ≤ a.length + 1 ∧
        (sint.nat i ≤ a.length → sint.nat st ≤ sint.nat i ∧ sint.nat n ≤ 4 ∧
          scanGo a 0 [] [] = scanGo (a.drop (sint.nat i)) (sint.nat n)
            ((a.drop (sint.nat st)).take (sint.nat i - sint.nat st)) (arr.take (sint.nat n))) ∧
        (a.length < sint.nat i → scanGo a 0 [] [] = some arr)⌝ : IProp GF)
    $$ [i n start parts]
  · iexists W64 0, W64 0, W64 0, List.replicate 5 []
    iframe
    ipureintro
    have h0 : sint.nat (W64 0) = 0 := rfl
    refine ⟨rfl, by decide, by decide, by decide, ?_, fun _ => ⟨?_, ?_, ?_⟩, fun h => ?_⟩
    all_goals rw [h0] at *
    all_goals first | omega | (simp; done)
  wp_for HI
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  wp_if_destruct
  · obtain ⟨Hlen5, Hi0, Hn0, Hst0, Hile, Hrun, -⟩ := Hinv
    have Hc : sint.Z i ≤ sint.Z (W64 (a.length : Int)) := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    have hil : sint.nat i ≤ a.length := by word
    obtain ⟨Hsti, Hn4, Hscan⟩ := Hrun hil
    try wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    try wp_auto
    by_cases hend : sint.nat i = a.length
    · rw [decide_eq_true (show i = W64 (a.length : Int) by word)]
      try wp_auto
      rw [decide_eq_false (show ¬ sint.Z (W64 5) ≤ sint.Z n by word)]
      try wp_auto
      wp_if_destruct
      · rw [if_pos ⟨Hst0, by word, by word⟩]
        try wp_auto
        obtain ⟨x4, hx4⟩ : ∃ x, arr[4]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        icases array_acc (GF := GF) _ (sint.Z (W64 4)) _ _ (array.mk 5 arr : GoArray GoString 5) x4 (by decide)
          (by rw [show (sint.Z (W64 4)).toNat = 4 from rfl]; exact hx4) $$ parts with ⟨Hel, Hcl⟩
        try wp_auto
        ihave parts := Hcl $$ Hel
        wp_for_post
        iframe
        iexists i + W64 1, W64 4 + W64 1, i + W64 1, _
        iframe
        ipureintro
        have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
        rw [show (sint.Z (W64 4)).toNat = 4 from rfl]
        refine ⟨by simp [Hlen5], by word, by word, by word, by word, fun h => absurd h (by word), fun _ => ?_⟩
        have h4 : sint.nat (W64 4) = 4 := rfl
        rw [Hscan, hend, List.drop_length, scanGo.eq_1, if_pos h4,
          List.set_eq_take_append_cons_drop, h4]
        simp [Hlen5, show arr.drop 5 = [] from List.drop_eq_nil_of_le (by omega)]
      · have hn4 : sint.nat n ≠ 4 := fun h => Hif (by word)
        have hbad : addrOk a = false := by
          rw [← goAddrOk_eq, goAddrOk_scan_none]
          rw [Hscan, hend, List.drop_length, scanGo.eq_1, if_neg hn4]
        try wp_auto
        wp_for_post
        rw [hbad]
        iapply HΦ
        itrivial
    · have hilt : sint.nat i < a.length := by omega
      obtain ⟨c, hc⟩ : ∃ c, a[sint.nat i]? = some c := ⟨_, List.getElem?_eq_getElem hilt⟩
      have hdrop : a.drop (sint.nat i) = c :: a.drop (sint.nat i + 1) := by
        rw [List.drop_eq_getElem_cons hilt]
        rw [List.getElem?_eq_getElem hilt] at hc
        rw [Option.some.inj hc]
      rw [decide_eq_false (show ¬ i = W64 (a.length : Int) by intro h; apply hend; subst h; word)]
      repeat (first | (simp only [Hi0, ↓reduceIte, hc]) | wp_auto)
      have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      by_cases h46 : c = W8 46
      · rw [decide_eq_true h46]
        repeat (first | (simp only [Hi0, ↓reduceIte, hc]) | wp_auto)
        rw [decide_eq_false (show ¬ sint.Z (W64 5) ≤ sint.Z n by word)]
        repeat (first | (simp only [Hi0, ↓reduceIte, hc, decide_eq_true h46]) | wp_auto)
        by_cases hn3 : 3 ≤ sint.nat n
        · rw [decide_eq_true (show sint.Z (W64 3) ≤ sint.Z n by word)]
          have hbad : addrOk a = false := by
            rw [← goAddrOk_eq, goAddrOk_scan_none]
            rw [Hscan, hdrop, scanGo.eq_2, if_pos (show c = 46 from h46), if_pos hn3]
          repeat (first | (simp only [Hi0, ↓reduceIte, hc]) | wp_auto)
          wp_for_post
          rw [hbad]
          iapply HΦ
          itrivial
        · rw [decide_eq_false (show ¬ sint.Z (W64 3) ≤ sint.Z n by word)]
          have h58 : c ≠ W8 58 := by rw [h46]; decide
          repeat (first | (simp only [Hi0, ↓reduceIte, hc, decide_eq_false h58]) | wp_auto)
          have hstep : scanGo a 0 [] [] = scanGo (a.drop (sint.nat i + 1)) (sint.nat n + 1) []
              (arr.take (sint.nat n) ++ [(a.drop (sint.nat st)).take (sint.nat i - sint.nat st)]) := by
            rw [Hscan, hdrop, show c = 46 from h46, scanGo_dot _ _ _ _ (by omega)]
          have hn5 : sint.nat n + 1 ≤ 4 := by omega
          addrok_store
      · rw [decide_eq_false h46]
        repeat (first | (simp only [Hi0, ↓reduceIte, hc]) | wp_auto)
        by_cases h58 : c = W8 58
        · rw [decide_eq_true h58]
          repeat (first | (simp only [Hi0, ↓reduceIte, hc]) | wp_auto)
          rw [decide_eq_false (show ¬ sint.Z (W64 5) ≤ sint.Z n by word)]
          repeat (first | (simp only [Hi0, ↓reduceIte, hc, decide_eq_false h46, decide_eq_true h58]) | wp_auto)
          wp_if_destruct
          · -- `n = 3`
            repeat (first | (simp only [Hi0, ↓reduceIte, hc]) | wp_auto)
            generalize hN : (W64 3 : w64) = n at *
            have hn3 : sint.nat n = 3 := by rw [← hN]; rfl
            have hstep : scanGo a 0 [] [] = scanGo (a.drop (sint.nat i + 1)) (sint.nat n + 1) []
                (arr.take (sint.nat n) ++ [(a.drop (sint.nat st)).take (sint.nat i - sint.nat st)]) := by
              rw [Hscan, hdrop, show c = 58 from h58, scanGo_colon _ _ _ _ hn3]
            have hn5 : sint.nat n + 1 ≤ 4 := by omega
            addrok_store
          · have hn3 : sint.nat n ≠ 3 := fun h => Hif (by word)
            have hbad : addrOk a = false := by
              rw [← goAddrOk_eq, goAddrOk_scan_none]
              rw [Hscan, hdrop, scanGo.eq_2, if_neg (show ¬ c = 46 from h46), if_pos (show c = 58 from h58),
                if_pos hn3]
            repeat (first | (simp only [Hi0, ↓reduceIte, hc]) | wp_auto)
            wp_for_post
            rw [hbad]
            iapply HΦ
            itrivial
        · rw [decide_eq_false h58]
          repeat (first | (simp only [Hi0, ↓reduceIte, hc]) | wp_auto)
          wp_for_post
          iframe
          iexists i + W64 1, n, st, arr
          iframe
          ipureintro
          have hcst : (a.drop (sint.nat st))[sint.nat i - sint.nat st]? = some c := by
            rw [List.getElem?_drop, show sint.nat st + (sint.nat i - sint.nat st) = sint.nat i by omega]
            exact hc
          refine ⟨Hlen5, by word, Hn0, Hst0, by omega, fun _ => ⟨by omega, Hn4, ?_⟩,
            fun h => absurd h (by omega)⟩
          rw [hi1, show sint.nat i + 1 - sint.nat st = (sint.nat i - sint.nat st) + 1 by omega,
            take_succ_of _ _ _ hcst, Hscan, hdrop, scanGo.eq_2, if_neg (show ¬ c = 46 from h46),
            if_neg (show ¬ c = 58 from h58)]
  · obtain ⟨Hlen5, Hi0, Hn0, Hst0, Hile, -, Hdone⟩ := Hinv
    have Hge : ¬ sint.Z i ≤ sint.Z (W64 (a.length : Int)) := by
      first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
    rw [decide_eq_false Hge]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have Hsome : scanGo a 0 [] [] = some arr := Hdone (by word)
    match arr, Hlen5, Hsome with
    | [x0, x1, x2, x3, x4], _, Hsome =>
    try wp_auto
    ipersist parts
    ihave HI2 : (∃ (k : w64) (vs : List w64),
        "i" ∷ i_ptr ↦ k ∗ "v" ∷ v_ptr ↦ (array.mk 5 vs : GoArray w64 5) ∗
        "%Hk" ∷ ⌜vs.length = 5 ∧ 0 ≤ sint.Z k ∧ sint.Z k ≤ 5 ∧
          ∀ q, q < sint.nat k → ∃ x w, [x0, x1, x2, x3, x4][q]? = some x ∧ vs[q]? = some w ∧
            decimalM x 65535 = some (uint.nat w)⌝ : IProp GF)
      $$ [i v]
    · iexists W64 0, List.replicate 5 (W64 0)
      iframe
      ipureintro
      refine ⟨rfl, by decide, by decide, fun q hq => absurd hq (by simp [show sint.nat (W64 0) = 0 from rfl])⟩
    wp_for HI2
    wp_if_destruct
    · obtain ⟨Hvl, Hk0, Hk5, Hpre⟩ := Hk
      have Hk5' : sint.nat k < 5 := by word
      obtain ⟨xk, hxk⟩ : ∃ x, [x0, x1, x2, x3, x4][sint.nat k]? = some x :=
        ⟨_, List.getElem?_eq_getElem (by simp only [List.length_cons, List.length_nil]; omega)⟩
      icases array_acc (GF := GF) _ (sint.Z k) _ _ (array.mk 5 [x0, x1, x2, x3, x4] : GoArray GoString 5) xk Hk0
        hxk $$ parts with ⟨#Hel, -⟩
      try wp_auto
      rw [if_pos ⟨Hk0, by word⟩]
      try wp_auto
      wp_apply wp_decimal as %w %ok %Hdec
      try wp_auto
      cases ok
      · -- `decimal` refused the piece
        have hbad : addrOk a = false := by
          rw [← goAddrOk_eq]
          exact goAddrOk_dec_none Hsome (List.mem_of_getElem? hxk) (by simpa using Hdec.symm)
        repeat (first | (simp only [Bool.not_false]) | wp_auto)
        wp_for_post
        rw [hbad]
        iapply HΦ
        itrivial
      · simp only [Bool.not_true]
        try wp_auto
        obtain ⟨wk, hwk⟩ : ∃ w, vs[sint.nat k]? = some w := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        icases array_acc (GF := GF) _ (sint.Z k) _ _ (array.mk 5 vs : GoArray w64 5) wk Hk0
          hwk $$ v with ⟨Hvk, Hcl⟩
        try wp_auto
        rw [if_pos ⟨Hk0, by word⟩]
        try wp_auto
        ihave v := Hcl $$ Hvk
        wp_for_post
        iframe
        iexists k + W64 1, _
        iframe
        ipureintro
        have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
        refine ⟨by simp [Hvl], by word, by word, ?_⟩
        intro q hq
        rw [hk1] at hq
        rcases (show q < sint.nat k ∨ q = sint.nat k by omega) with hq | rfl
        · obtain ⟨x, w', h1, h2, h3⟩ := Hpre q hq
          refine ⟨x, w', h1, ?_, h3⟩
          rw [show (sint.Z k).toNat = sint.nat k from rfl, List.getElem?_set_ne (by omega)]
          exact h2
        · refine ⟨xk, w, hxk, ?_, by simpa using Hdec.symm⟩
          rw [show (sint.Z k).toNat = sint.nat k from rfl, List.getElem?_set_self (by show sint.nat k < vs.length; omega)]
    · obtain ⟨Hvl, Hk0, Hk5, Hpre⟩ := Hk
      have hk5 : sint.nat k = 5 := by word
      rw [hk5] at Hpre
      obtain ⟨y0, w0, h0x, h0w, h0d⟩ := Hpre 0 (by omega)
      obtain ⟨y1, w1, h1x, h1w, h1d⟩ := Hpre 1 (by omega)
      obtain ⟨y2, w2, h2x, h2w, h2d⟩ := Hpre 2 (by omega)
      obtain ⟨y3, w3, h3x, h3w, h3d⟩ := Hpre 3 (by omega)
      obtain ⟨y4, w4, h4x, h4w, h4d⟩ := Hpre 4 (by omega)
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h0x h1x h2x h3x h4x
      subst h0x h1x h2x h3x h4x
      have hres : addrOk a = addrCond [uint.nat w0, uint.nat w1, uint.nat w2, uint.nat w3, uint.nat w4] := by
        rw [← goAddrOk_eq]; exact goAddrOk_all Hsome h0d h1d h2d h3d h4d
      have b0 := (decimalM_some h0d).2
      have b1 := (decimalM_some h1d).2
      have b2 := (decimalM_some h2d).2
      have b3 := (decimalM_some h3d).2
      have b4 := (decimalM_some h4d).2
      ipersist v
      icases array_acc (GF := GF) _ (sint.Z (W64 0)) _ _ (array.mk 5 vs : GoArray w64 5) w0 (by decide) h0w $$ v
        with ⟨#Hv0, -⟩
      icases array_acc (GF := GF) _ (sint.Z (W64 1)) _ _ (array.mk 5 vs : GoArray w64 5) w1 (by decide) h1w $$ v
        with ⟨#Hv1, -⟩
      icases array_acc (GF := GF) _ (sint.Z (W64 2)) _ _ (array.mk 5 vs : GoArray w64 5) w2 (by decide) h2w $$ v
        with ⟨#Hv2, -⟩
      icases array_acc (GF := GF) _ (sint.Z (W64 3)) _ _ (array.mk 5 vs : GoArray w64 5) w3 (by decide) h3w $$ v
        with ⟨#Hv3, -⟩
      icases array_acc (GF := GF) _ (sint.Z (W64 4)) _ _ (array.mk 5 vs : GoArray w64 5) w4 (by decide) h4w $$ v
        with ⟨#Hv4, -⟩
      repeat (first | wp_if_destruct | wp_auto)
      all_goals
        iapply (addr_close Φ (addrOk a) _ (by
          rw [hres]
          first
            | (simp only [addrCond, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]; word)
            | (simp only [addrCond, Bool.and_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_true,
                decide_eq_true_eq, Bool.or_eq_true, Bool.or_eq_false_iff]; word)
            | (simp only [addrCond]; simp_all; word))) $$ HΦ

end proof

end etcd_dist
end EtcdGrove
end Perennial
