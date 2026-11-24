/-
The proof of `jsoncodec.Scan` (`Net/Spec/models_lab/jsoncodec/Scan.lean`): the loop against
`JsonScan.goL`, over `SkipSpace`'s spec. Ported from dsverify-lab's `wp_Scan`
(`examples/vr/proof/VsrProof/Proof/jsoncodec/GoScan.lean`, lab master 915f964).
-/
module

public import Net.Spec.models_lab.jsoncodec.Scan
public import Net.Spec.models_lab.jsoncodec.SkipSpace
public import Net.Proof.models_lab.jsoncodec.ScanScalar

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace models_lab.jsoncodec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : models_lab.jsoncodec.Assumptions]

set_option goose.wp.extras true

set_option hygiene false in
/-- `Scan`'s state 1: closing the innermost container (`goL_close1`). -/
local macro "scan_pop1" : tactic => `(tactic| (
  ihave %Hwf := ownSlice_wf $$ Hst
  have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (sl.len - W64 1) ∧
      sint.Z (sl.len - W64 1) ≤ sint.Z sl.len := by word
  rw [if_pos (by word)]
  ihave Hsp := ownSlice_slice_with_cap (W64 0) (sl.len - W64 1) sl _ hb $$ [Hst Hcap]
  · iframe
  icases Hsp with ⟨-, Hst, Hcap⟩
  wp_auto
  rw [JsonScan.goL_close1 (hc := by decide)] at hNi
  have hsub : ∀ t : w8, subslice (sint.nat (W64 0)) (sint.nat (sl.len - W64 1))
      (t :: stk').reverse = stk'.reverse := by
    intro t
    rw [show sint.nat (sl.len - W64 1) = stk'.length by word,
      show sint.nat (W64 0) = 0 from rfl]
    simp [subslice]
  rw [hsub]
  wp_if_destruct
  · have hst' : stk' = [] := by apply List.eq_nil_of_length_eq_zero; word
    simp only [hst', if_true, ite_true] at hNi
    wp_for_post
    fin_ret hNi
  · have hst' : stk' ≠ [] := by
      intro h; subst h; apply Hif; simp at Hsl2; word
    simp only [hst', if_false, ite_false] at hNi
    wp_for_post
    iframe
    iexists _, _, stk', _, _
    iframe
    ipureintro
    refine ⟨by word, by simp at hdep; omega, by word, fun _ => hst', fun _ => hst',
      fun _ => heF, ?_⟩
    rw [hNi, show uint.nat (W64 (i1 : Int) + W64 1) = i1 + 1 by word]; rfl))

set_option hygiene false in
/-- `Scan`'s state 1: a byte that neither separates nor closes. -/
local macro "scan_bad1" : tactic => `(tactic| (
  rw [JsonScan.goL_bad1 _ _ _ _ _ _ eof hsc hc44 (by
    intro h; rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      first | (revert h1; decide) | (revert h2; decide) | (apply Hif; rw [h2]; rfl) |
        (apply Hif; rw [h1]; rfl) | simp_all)] at hNi
  wp_for_post
  fin_ret hNi))

set_option maxHeartbeats 2000000 in
theorem Scan.wp_proof (wp_SkipSpace : SkipSpace.spec (GF := GF) (hG := hG)) :
    Scan.spec (GF := GF) (hG := hG) := by
  intro b dq bs eof
  simp only [JsonScan.scanF]
  wp_start as Hs
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := len_lt b bs Hlen
  generalize hN : JsonScan.scanL bs eof = N
  simp only [models_lab.jsoncodec.Done, models_lab.jsoncodec.More,
    models_lab.jsoncodec.Bad]
  wp_auto
  wp_apply (wp_SkipSpace b dq bs (W64 0) (by simp)) $$ Hs as Hs
  have hN0 : N = JsonScan.goL (bs.drop 0) 0 [] 0 false eof := by rw [← hN]; rfl
  rw [JsonScan.goL_skip] at hN0
  have hsk := JsonScan.skipEnd_le bs 0 (by simp)
  rw [show uint.nat (W64 0) = 0 from rfl]
  generalize JsonScan.skipEnd bs 0 = i0 at hN0 hsk ⊢
  wp_if_destruct
  · have : bs.length ≤ i0 := by word
    rw [List.drop_eq_nil_of_le this, JsonScan.goL_nil] at hN0
    fin_ret hN0
  ihave Hst := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
  ihave Hcap := ownSliceCap_nil (V := w8) (GF := GF)
  ihave IH : iprop(∃ (iw : w64) (sl : GoSlice) (stk : List w8) (st : w64) (eOK : Bool),
      "i" ∷ i_ptr ↦ iw ∗ "stack" ∷ stack_ptr ↦ sl ∗ "Hst" ∷ sl ↦* stk.reverse ∗
      "Hcap" ∷ ownSliceCap w8 sl (DFrac.own 1) ∗ "state" ∷ state_ptr ↦ st ∗
      "emptyOK" ∷ emptyOK_ptr ↦ eOK ∗
      "%Hinv" ∷ ⌜uint.nat iw ≤ bs.length ∧ stk.length ≤ JsonScan.maxDepth ∧ uint.nat st ≤ 3 ∧
        (eOK = true → stk ≠ []) ∧ (uint.nat st ≠ 0 → stk ≠ []) ∧
        (uint.nat st = 1 ∨ uint.nat st = 3 → eOK = false) ∧
        N = JsonScan.goL (bs.drop (uint.nat iw)) (uint.nat iw) stk (uint.nat st) eOK eof⌝)
      $$ [i stack Hst Hcap state emptyOK]
  · iexists _, _, [], _, _
    simp only [List.reverse_nil, show (zero_val GoSlice : GoSlice) = slice.nil from rfl]
    iframe
    isplitl []
    · iexact Hst
    isplitl []
    · iexact Hcap
    ipureintro
    refine ⟨by word, by simp, by word, by simp, by simp, (by intro h; first | rfl | (exfalso; rcases h with h | h <;> revert h <;> decide)), ?_⟩
    rw [hN0, show uint.nat (W64 (i0 : Int)) = i0 by word]; rfl
  wp_for IH
  obtain ⟨hiw, hdep, hst3, heok, hstne, h13, hNi⟩ := Hinv
  wp_apply (wp_SkipSpace b dq bs iw hiw) $$ Hs as Hs
  rw [JsonScan.goL_skip] at hNi
  have hsk := JsonScan.skipEnd_le bs (uint.nat iw) hiw
  have hns : ∀ c, bs[JsonScan.skipEnd bs (uint.nat iw)]? = some c → JsonScan.spB c = false :=
    fun c h => JsonScan.skipEnd_ns bs _ c h
  generalize JsonScan.skipEnd bs (uint.nat iw) = i1 at hNi hsk hns ⊢
  wp_if_destruct
  · wp_for_post
    have : bs.length ≤ i1 := by word
    rw [List.drop_eq_nil_of_le this, JsonScan.goL_nil] at hNi
    fin_ret hNi
  have hz : uint.nat (W64 (i1 : Int)) = i1 := by word
  ldidx (W64 (i1 : Int)), c, Hc
  rw [hz] at Hc
  have hsc := hns c Hc
  rw [JsonScan.drop_cons_of bs _ c Hc] at hNi
  ihave %Hsl := ownSlice_len $$ Hst
  simp only [List.length_reverse] at Hsl
  wp_if_destruct
  · -- state 0
    rw [show uint.nat (W64 0) = 0 from rfl] at hNi
    wp_if_destruct
    rotate_left
    have hc1 : c ≠ 91#8 := by intro h; apply Hif; rw [h]; rfl
    wp_if_destruct
    rotate_left
    · have hc2 : c ≠ 123#8 := by intro h; apply Hif; rw [h]; rfl
      have hNi' : N = JsonScan.goL (bs.drop i1) i1 stk 0 eOK eof := by
        rw [JsonScan.drop_cons_of bs _ c Hc]; exact hNi
      clear hNi
      wp_if_destruct
      rotate_left
      have hns3 : ¬(c = 93#8 ∧ eOK = true ∧ stk.head? = some 91#8) :=
        fun h => Hif (by rw [h.1]; try rfl)
      rotate_left
      wp_if_destruct
      have hns3 : ¬(W8 93 = 93#8 ∧ false = true ∧ stk.head? = some 91#8) := by simp
      rotate_left
      obtain ⟨top, stk', rfl⟩ : ∃ top stk', stk = top :: stk' := by
        cases stk with
        | nil => exact absurd rfl (heok rfl)
        | cons t s' => exact ⟨t, s', rfl⟩
      have Hsl2 := Hsl
      simp only [List.length_cons] at Hsl2
      rw [if_pos (by word)]
      wp_apply wp_load_slice_index sl (sint.Z (sl.len - W64 1)) ((top :: stk').reverse) _ top
        (by word) $$ [Hst] as Hst
      · iframe; ipureintro
        rw [show (sint.Z (sl.len - W64 1)).toNat = stk'.length by word]
        try simp
      wp_if_destruct
      · ihave %Hwf := ownSlice_wf $$ Hst
        have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (sl.len - W64 1) ∧
            sint.Z (sl.len - W64 1) ≤ sint.Z sl.len := by word
        rw [if_pos (by word)]
        ihave Hsp := ownSlice_slice_with_cap (W64 0) (sl.len - W64 1) sl _ hb $$ [Hst Hcap]
        · iframe
        icases Hsp with ⟨-, Hst, Hcap⟩
        wp_auto
        rw [JsonScan.drop_cons_of bs _ _ Hc] at hNi'
        simp only [show (W8 93 : w8) = 93#8 from by decide, show (W8 91 : w8) = 91#8 from by decide,
          JsonScan.goL_close0] at hNi'
        have hsub : subslice (sint.nat (W64 0)) (sint.nat (sl.len - W64 1))
            (91#8 :: stk').reverse = stk'.reverse := by
          rw [show sint.nat (sl.len - W64 1) = stk'.length by word,
            show sint.nat (W64 0) = 0 from rfl]
          simp [subslice]
        rw [show (W8 91 : w8) = 91#8 from by decide, hsub]
        wp_if_destruct
        · have hst' : stk' = [] := by apply List.eq_nil_of_length_eq_zero; word
          simp only [hst', if_true, ite_true] at hNi'
          wp_for_post
          fin_ret hNi'
        · have hst' : stk' ≠ [] := by
            intro h; subst h; apply Hif; simp at Hsl; word
          simp only [hst', if_false, ite_false] at hNi'
          wp_for_post
          iframe
          iexists _, _, stk', _, _
          iframe
          ipureintro
          refine ⟨by word, by simp at hdep; omega, by word, by simp, fun _ => hst', (by intro h; first | rfl | (exfalso; rcases h with h | h <;> revert h <;> decide)), ?_⟩
          rw [hNi', show uint.nat (W64 (i1 : Int) + W64 1) = i1 + 1 by word]; rfl
      have hns3 : ¬(W8 93 = 93#8 ∧ true = true ∧ (top :: stk').head? = some 91#8) := by
        simp only [List.head?_cons, Option.some.injEq]; intro h; apply Hif; rw [h.2.2]; rfl
      generalize hstkdef : top :: stk' = stk at *
      all_goals
        rw [JsonScan.goL_scalar_idx bs i1 stk _ eof _ Hc hsc hc1 hc2 hns3] at hNi'
        have hemp : decide (sl.len = W64 0) = stk.isEmpty := by
          rw [Bool.eq_iff_iff, decide_eq_true_iff, List.isEmpty_iff]
          constructor
          · intro h; rw [h] at Hsl; apply List.eq_nil_of_length_eq_zero; rw [Hsl.1]; rfl
          · intro h; rw [h] at Hsl; simp at Hsl; word
        wp_join (Q := fun v => iprop(⌜v = #(eof && stk.isEmpty)⌝ ∗ stack_ptr ↦ sl)) with [stack]
        · iframe
        · iframe; ipureintro; rw [Bool.true_and, ← hemp]
        iintro ⟨%Hv, stack⟩
        subst Hv
        wp_auto
        have hi1 : i1 < bs.length := by word
        have hPb := JsonScan.scalarL_bd (bs.drop i1) i1 (eof && stk.isEmpty)
        simp only [List.length_drop] at hPb
        wp_apply wp_scanScalar b dq bs (W64 (i1 : Int)) _ (by rw [hz]; exact hi1) $$ Hs as Hs
        rw [hz]
        have hPs := JsonScan.scalarL_st (bs.drop i1) i1 (eof && stk.isEmpty)
        generalize JsonScan.scalarL (bs.drop i1) i1 (eof && stk.isEmpty) = P at hNi' hPb hPs ⊢
        by_cases hP0 : P.1 = 0
        · have hw : decide (W64 (P.1 : Int) = W64 0) = true := by simp [hP0]
          rw [hw]
          wp_auto
          simp only [hP0, ne_eq, not_true_eq_false, if_false, ite_false] at hNi'
          wp_if_destruct
          · have hstk : stk = [] := by
              apply List.eq_nil_of_length_eq_zero; rw [Hsl.1, Hif]; rfl
            simp only [hstk, if_true, ite_true] at hNi'
            wp_for_post
            fin_ret hNi'
          · have hstk : stk ≠ [] := by
              intro h; apply Hif; rw [h] at Hsl; simp at Hsl; word
            simp only [hstk, if_false, ite_false] at hNi'
            wp_for_post
            iframe
            iexists _, _, stk, _, _
            iframe
            ipureintro
            refine ⟨by word, hdep, by word, by simp, fun _ => hstk, (by intro h; first | rfl | (exfalso; rcases h with h | h <;> revert h <;> decide)), ?_⟩
            rw [hNi', show uint.nat (W64 (P.2 : Int)) = P.2 by word]; rfl
        · have hw : decide (W64 (P.1 : Int) = W64 0) = false := by simp; word
          rw [hw]
          wp_auto
          simp only [hP0, ne_eq, not_false_eq_true, if_true, ite_true] at hNi'
          wp_for_post
          fin_ret hNi'
    all_goals
      wp_if_destruct
      · wp_for_post
        have hdeep : JsonScan.maxDepth ≤ stk.length := by simp only [JsonScan.maxDepth]; word
        have e : N = (2, i1) := by
          rw [hNi, JsonScan.goL.eq_def]
          simp only [hsc, Bool.false_eq_true, if_false, ite_false, if_true, ite_true]
          simp [hdeep]
        fin_ret e
      have hdeep : stk.length < JsonScan.maxDepth := by simp only [JsonScan.maxDepth]; word
      rw [JsonScan.goL_open (hc := by decide) (hd := hdeep)] at hNi
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := w8) (t := go.byte) [_]
      wp_auto
      rw [show go.arrayLiteralSize
        [KeyedElement none (ElementExpression go.byte #_)] = 1 from rfl]
      isplitl []
      · ipureintro; rfl
      iintro %sl_ptr ⟨Hc_sl, -⟩
      wp_apply wp_slice_append $$ [Hst Hcap Hc_sl] as %sl' ⟨Hst, Hcap, -⟩
      · iframe
      wp_auto
      wp_for_post
      iframe
      iexists _, _, ((bs[i1]?.getD 0#8) :: stk), _, _
      rw [Hc]
      simp only [Option.getD_some, List.reverse_cons]
      iframe
      ipureintro
      refine ⟨by word, by simp; omega, by word, by simp, by simp, (by intro h; first | rfl | (exfalso; rcases h with h | h <;> revert h <;> decide)), ?_⟩
      rw [hNi, show uint.nat (W64 (i1 : Int) + W64 1) = i1 + 1 by word]
      first | rfl | (simp (config := {decide := true})) | (congr 1; decide)
  · have hst0 : uint.nat st ≠ 0 := by intro h; apply Hif; word
    obtain ⟨top, stk', rfl⟩ : ∃ top stk', stk = top :: stk' := by
      cases h : stk with
      | nil => exact absurd h (hstne hst0)
      | cons t s' => exact ⟨t, s', rfl⟩
    have Hsl2 := Hsl
    simp only [List.length_cons] at Hsl2
    wp_if_destruct
    · -- state 1
      rw [show uint.nat (W64 1) = 1 from rfl] at hNi
      rw [if_pos (by word)]
      wp_apply wp_load_slice_index sl (sint.Z (sl.len - W64 1)) ((top :: stk').reverse) _ top
        (by word) $$ [Hst] as Hst
      · iframe; ipureintro
        rw [show (sint.Z (sl.len - W64 1)).toNat = stk'.length by word]
        try simp
      wp_if_destruct
      · -- a comma
        rw [show (W8 44 : w8) = 44#8 from by decide, JsonScan.goL_comma] at hNi
        wp_if_destruct
        all_goals
          wp_for_post
          iframe
          iexists _, _, (_ :: stk'), _, _
          iframe
          ipureintro
          refine ⟨by word, hdep, by word, fun _ => by simp, fun _ => by simp, (by intro h; first | rfl | (exfalso; rcases h with h | h <;> revert h <;> decide)), ?_⟩
          rw [hNi, show uint.nat (W64 (i1 : Int) + W64 1) = i1 + 1 by word]
          (try rw [if_neg (fun h => Hif (by rw [h]; try rfl))])
          first | rfl | (simp (config := {decide := true}))
      have hc44 : c ≠ 44#8 := fun h => Hif (by rw [h]; try rfl)
      have heF : eOK = false := h13 (Or.inl (by word))
      wp_if_destruct
      · wp_if_destruct
        · scan_pop1
        · scan_bad1
      · wp_if_destruct
        · wp_if_destruct
          · scan_pop1
          · scan_bad1
        · scan_bad1
    have hst1 : uint.nat st ≠ 1 := by intro h; apply Hif; word
    wp_if_destruct
    · -- state 2
      rw [show uint.nat (W64 2) = 2 from rfl] at hNi
      wp_if_destruct
      · wp_if_destruct
        · -- `}` with a member before: bad
          rw [JsonScan.goL_bad2 _ _ _ _ _ eof hsc (by simp) (by decide)] at hNi
          wp_for_post
          fin_ret hNi
        · -- closing an empty object
          ihave %Hwf := ownSlice_wf $$ Hst
          have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (sl.len - W64 1) ∧
              sint.Z (sl.len - W64 1) ≤ sint.Z sl.len := by word
          rw [if_pos (by word)]
          ihave Hsp := ownSlice_slice_with_cap (W64 0) (sl.len - W64 1) sl _ hb $$ [Hst Hcap]
          · iframe
          icases Hsp with ⟨-, Hst, Hcap⟩
          wp_auto
          rw [show (W8 125 : w8) = 125#8 from by decide, JsonScan.goL_close2] at hNi
          have hsub : subslice (sint.nat (W64 0)) (sint.nat (sl.len - W64 1))
              (top :: stk').reverse = stk'.reverse := by
            rw [show sint.nat (sl.len - W64 1) = stk'.length by word,
              show sint.nat (W64 0) = 0 from rfl]
            simp [subslice]
          rw [hsub]
          wp_if_destruct
          · have hst' : stk' = [] := by apply List.eq_nil_of_length_eq_zero; word
            simp only [hst', if_true, ite_true] at hNi
            wp_for_post
            fin_ret hNi
          · have hst' : stk' ≠ [] := by
              intro h; subst h; apply Hif; simp at Hsl2; word
            simp only [hst', if_false, ite_false] at hNi
            wp_for_post
            iframe
            iexists _, _, stk', _, _
            iframe
            ipureintro
            refine ⟨by word, by simp at hdep; omega, by word, fun _ => hst', fun _ => hst',
              fun _ => rfl, ?_⟩
            rw [hNi, show uint.nat (W64 (i1 : Int) + W64 1) = i1 + 1 by word]; rfl
      have h125 : ¬(c = 125#8 ∧ eOK = true) := fun h => Hif (by rw [h.1]; try rfl)
      wp_if_destruct
      · rw [show (W8 34 : w8) = 34#8 from by decide, JsonScan.goL_key] at hNi
        have hi1 : i1 < bs.length := by word
        have hQb := JsonScan.strL_bd (bs.drop (i1 + 1)) (i1 + 1)
        have hQs := JsonScan.strL_st (bs.drop (i1 + 1)) (i1 + 1)
        simp only [List.length_drop] at hQb
        wp_apply wp_scanString b dq bs (W64 (i1 : Int)) (by rw [hz]; exact hi1) $$ Hs as Hs
        rw [hz]
        simp only at hNi
        generalize JsonScan.strL (bs.drop (i1 + 1)) (i1 + 1) = Q at hNi hQb hQs ⊢
        by_cases hQ0 : Q.1 = 0
        · have hw : decide (W64 (Q.1 : Int) = W64 0) = true := by simp [hQ0]
          rw [hw]
          wp_auto
          simp only [hQ0, ne_eq, not_true_eq_false, if_false, ite_false] at hNi
          rw [JsonScan.drop_after bs i1 Q.2 (by omega)] at hNi
          wp_for_post
          iframe
          iexists _, _, (top :: stk'), _, _
          iframe
          ipureintro
          refine ⟨by word, hdep, by word, fun _ => by simp, fun _ => by simp, fun _ => rfl, ?_⟩
          rw [hNi, show uint.nat (W64 (Q.2 : Int)) = Q.2 by word]; rfl
        · have hw : decide (W64 (Q.1 : Int) = W64 0) = false := by simp; word
          rw [hw]
          wp_auto
          simp only [hQ0, ne_eq, not_false_eq_true, if_true, ite_true] at hNi
          wp_for_post
          fin_ret hNi
      rw [JsonScan.goL_bad2 _ _ _ _ _ eof hsc h125 (fun h => Hif (by rw [h]; try rfl))] at hNi
      wp_for_post
      fin_ret hNi
    · -- state 3
      have hs3 : uint.nat st = 3 := by
        have : uint.nat st ≠ 2 := by intro h; apply Hif; word
        omega
      rw [hs3] at hNi
      wp_if_destruct
      · rw [show (W8 58 : w8) = 58#8 from by decide, JsonScan.goL_colon] at hNi
        wp_for_post
        iframe
        iexists _, _, (top :: stk'), _, _
        iframe
        ipureintro
        refine ⟨by word, hdep, by word, fun _ => by simp, fun _ => by simp,
          (by intro h; first | rfl | (exfalso; rcases h with h | h <;> revert h <;> decide)), ?_⟩
        rw [hNi, show uint.nat (W64 (i1 : Int) + W64 1) = i1 + 1 by word]; rfl
      rw [JsonScan.goL_bad3 _ _ _ _ _ eof hsc (fun h => Hif (by rw [h]; try rfl))] at hNi
      wp_for_post
      fin_ret hNi

end proof

end models_lab.jsoncodec
end Perennial
