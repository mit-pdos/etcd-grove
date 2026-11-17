/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `parseID`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.parseID
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

/-- The decimal value of a prefix (`parseID`'s fold). -/
def decStep (acc : Nat) (c : Char) : Nat := acc * 10 + (c.toNat - '0'.toNat)

theorem decStep_foldl_ge : ∀ (l : List Char) (a : Nat), a ≤ l.foldl decStep a
  | [], _ => Nat.le_refl _
  | c :: l, a => by
    simp only [List.foldl_cons]
    exact Nat.le_trans (by unfold decStep; omega) (decStep_foldl_ge l _)

/-- An ASCII character's byte, compared as the Go does. -/
theorem byte_lt_iff (c : Char) (hc : c.toNat < 128) (k : Nat) (hk : k < 256) :
    (BitVec.ofNat 8 c.toNat : w8) < BitVec.ofNat 8 k ↔ c.toNat < k := by
  rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem byte_uZ (c : Char) (hc : c.toNat < 128) : uint.Z (BitVec.ofNat 8 c.toNat : w8) = (c.toNat : Int) := by
  simp only [uint.Z, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]

theorem isDigit_iff (c : Char) : c.isDigit = true ↔ 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  unfold Char.isDigit
  simp only [Bool.and_eq_true, decide_eq_true_eq, UInt32.le_iff_toNat_le]
  rfl

/-- `parseID` when its first checks passed: the digits' value if all digits and below `2^64`. -/
theorem parseID_body (s : String) (h : ¬ (Bool.or (Bool.or s.toList.isEmpty (decide (s.toList.length > 20)))
    (decide (s.toList.length > 1) && (s.toList.head? == some '0'))) = true) :
    parseID s = if s.toList.all Char.isDigit then
      (if s.toList.foldl decStep 0 < 2 ^ 64 then some (s.toList.foldl decStep 0) else none) else none := by
  unfold parseID
  dsimp only
  rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
  rfl

theorem parseID_none (s : String) (h : (Bool.or (Bool.or s.toList.isEmpty (decide (s.toList.length > 20)))
    (decide (s.toList.length > 1) && (s.toList.head? == some '0'))) = true) : parseID s = none := by
  unfold parseID
  dsimp only
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]

-- The digits' loop, the first checks having passed (`hnf`; hygiene off).
set_option hygiene false in
local macro "pid_loop" : tactic => `(tactic| (
  try wp_auto
  ihave IH : iprop(∃ (k idv : w64), "k" ∷ k_ptr ↦ k ∗ "id" ∷ id_ptr ↦ idv ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (s.toList.length : Int) ∧
        (s.toList.take (sint.nat k)).all Char.isDigit = true ∧
        uint.nat idv = (s.toList.take (sint.nat k)).foldl decStep 0⌝) $$ [k id]
  · iexists _, _
    iframe
    ipureintro
    rw [show sint.nat (W64 0) = 0 from rfl, show sint.Z (W64 0) = 0 from rfl]
    refine ⟨Int.le_refl _, by omega, by simp, rfl⟩
  wp_for IH
  obtain ⟨hk0, hk1, hkd, hkv⟩ := Hk
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  rw [hLz, hlen]
  wp_if_destruct
  · have hkl0 : sint.Z k < (s.toList.length : Int) := of_decide_eq_true (go.intoVal_inj Hif)
    have hkl : sint.nat k < s.toList.length := by clear Hif; word
    obtain ⟨c, hc⟩ : ∃ c, s.toList[sint.nat k]? = some c := ⟨_, List.getElem?_eq_getElem hkl⟩
    have hcasc : c.toNat < 128 := hasc c (List.mem_of_getElem? hc)
    have hgk : gs[sint.nat k]? = some (BitVec.ofNat 8 c.toNat : w8) := by
      rw [hgs, List.getElem?_map, hc]; rfl
    simp only [hk0, ite_true, hgk]
    wp_auto
    have hstep : s.toList.take (sint.nat (k + W64 1)) = s.toList.take (sint.nat k) ++ [c] := by
      rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word, List.take_add_one, hc]; rfl
    rw [byte_uZ c hcasc, show uint.Z (W8 48) = 48 from rfl]
    by_cases hlo : c.toNat < 48
    · rw [decide_eq_true (show (c.toNat : Int) < 48 by omega)]
      wp_auto
      wp_for_post
      try wp_auto
      iapply HΦ'; ipureintro
      rw [parseID_body s hnf]
      have : s.toList.all Char.isDigit = false := by
        rw [List.all_eq_false]; exact ⟨c, List.mem_of_getElem? hc, by rw [isDigit_iff]; omega⟩
      rw [this]; rfl
    rw [decide_eq_false (show ¬ (c.toNat : Int) < 48 by omega)]
    wp_auto
    rw [byte_uZ c hcasc, show uint.Z (W8 57) = 57 from rfl]
    by_cases hhi : 57 < c.toNat
    · rw [decide_eq_true (show (57 : Int) < c.toNat by omega)]
      wp_auto
      wp_for_post
      try wp_auto
      iapply HΦ'; ipureintro
      rw [parseID_body s hnf]
      have : s.toList.all Char.isDigit = false := by
        rw [List.all_eq_false]; exact ⟨c, List.mem_of_getElem? hc, by rw [isDigit_iff]; omega⟩
      rw [this]; rfl
    rw [decide_eq_false (show ¬ (57 : Int) < c.toNat by omega)]
    wp_auto
    have hdig : c.isDigit = true := (isDigit_iff c).2 ⟨by omega, by omega⟩
    have hb8 : uint.Z (BitVec.ofNat 8 c.toNat - W8 48 : w8) = (c.toNat : Int) - 48 := by
      have := byte_uZ c hcasc
      have h48 : (48 : Int) ≤ uint.Z (BitVec.ofNat 8 c.toNat : w8) := by rw [this]; omega
      rw [← this]; word
    have hdz : uint.Z (W64 (uint.Z (BitVec.ofNat 8 c.toNat - W8 48 : w8))) = (c.toNat : Int) - 48 := by
      rw [hb8]; word
    have hov : uint.Z ((~~~W64 0 - W64 (uint.Z (BitVec.ofNat 8 c.toNat - W8 48 : w8))) / W64 10) =
        (2 ^ 64 - 1 - ((c.toNat : Int) - 48)) / 10 := by
      have : 0 ≤ (c.toNat : Int) - 48 ∧ (c.toNat : Int) - 48 ≤ 9 := by omega
      rw [← hdz] at this ⊢; word
    rw [hov]
    have hidz : uint.Z idv = ((s.toList.take (sint.nat k)).foldl decStep 0 : Nat) := by
      rw [← hkv]
    have hfold1 : (s.toList.take (sint.nat (k + W64 1))).foldl decStep 0 =
        decStep ((s.toList.take (sint.nat k)).foldl decStep 0) c := by
      rw [hstep, List.foldl_append]; rfl
    by_cases hof : (2 ^ 64 - 1 - ((c.toNat : Int) - 48)) / 10 < uint.Z idv
    · rw [decide_eq_true hof]
      wp_auto
      wp_for_post
      try wp_auto
      have hnone : parseID s = none := by
        rw [parseID_body s hnf]
        by_cases hall : s.toList.all Char.isDigit = true
        · have hge : decStep ((s.toList.take (sint.nat k)).foldl decStep 0) c ≤ s.toList.foldl decStep 0 := by
            rw [← hfold1]
            conv => rhs; rw [← List.take_append_drop (sint.nat (k + W64 1)) s.toList]
            rw [List.foldl_append]; exact decStep_foldl_ge _ _
          have hdec : decStep ((s.toList.take (sint.nat k)).foldl decStep 0) c =
              (s.toList.take (sint.nat k)).foldl decStep 0 * 10 + (c.toNat - 48) := rfl
          have : ¬ s.toList.foldl decStep 0 < 2 ^ 64 := by
            rw [hidz] at hof; omega
          simp only [hall, ite_true, this, ite_false]
        · simp only [hall, Bool.false_eq_true, ite_false]
      iapply HΦ'; ipureintro
      rw [hnone]
    rw [decide_eq_false hof]
    wp_auto
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro
    have hk2 : sint.nat (k + W64 1) = sint.nat k + 1 := by clear Hif; word
    refine ⟨by clear Hif; word, by clear Hif; word, ?_, ?_⟩
    · rw [hstep, List.all_append, hkd]; simp [hdig]
    · rw [hfold1]
      have hle : uint.Z idv * 10 + ((c.toNat : Int) - 48) < 2 ^ 64 := by omega
      unfold decStep
      have : uint.nat (idv * W64 10 + W64 (uint.Z (BitVec.ofNat 8 c.toNat - W8 48 : w8))) =
          uint.nat idv * 10 + (c.toNat - 48) := by
        have h1 := hdz
        word
      rw [this, hkv]; rfl
  · have hnot : ¬ sint.Z k < (s.toList.length : Int) := fun h => Hif (by rw [decide_eq_true h])
    have hkx : sint.nat k = s.toList.length := by clear Hif; word
    rw [hkx, List.take_length] at hkd hkv
    rw [decide_eq_false hnot]
    simp only [Bool.false_eq_true, ite_false]
    try wp_auto
    iapply HΦ'; ipureintro
    rw [parseID_body s hnf, hkd]
    simp only [ite_true]
    rw [← hkv]
    have hlt : uint.nat idv < 2 ^ 64 := idv.isLt
    simp [hlt]))

theorem parseID.wp_proof : parseID.spec (GF := GF) (hG := hG) := by
  intro gs s
  wp_start as %Hs
  obtain ⟨hasc, hgs⟩ := Hs
  ihave HΦ' : (∀ (id : w64) (ok : Bool), ⌜match parseID s with
       | none => ok = false
       | some n => ok = true ∧ uint.nat id = n⌝ -∗ Φ (PairV #id #ok)) $$ [HΦ]
  · iintro %id %ok %h; iapply HΦ; ipureintro; exact h
  have hlen : gs.length = s.toList.length := by rw [hgs, List.length_map]
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hsl
  have hLz : sint.Z (W64 gs.length) = gs.length := by word
  by_cases h0 : s.toList.length = 0
  · rw [decide_eq_true (show W64 gs.length = W64 0 by rw [hlen, h0]; rfl)]
    wp_auto
    iapply HΦ'; ipureintro
    have hnil : s.toList = [] := List.length_eq_zero_iff.1 h0
    have : parseID s = none := parseID_none s (by rw [hnil]; rfl)
    rw [this]
  rw [decide_eq_false (show ¬ W64 gs.length = W64 0 by
    intro e; apply h0; rw [← hlen]; have := congrArg (fun w : w64 => sint.Z w) e
    rw [hLz, show sint.Z (W64 0) = 0 from rfl] at this
    exact_mod_cast this)]
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  rw [hLz]
  by_cases h20 : s.toList.length > 20
  · rw [decide_eq_true (show sint.Z (W64 20) < (gs.length : Int) by rw [hlen]; have : sint.Z (W64 20) = 20 := rfl; omega)]
    wp_auto
    iapply HΦ'; ipureintro
    have : parseID s = none := parseID_none s (by simp [h20])
    rw [this]
  rw [decide_eq_false (show ¬ sint.Z (W64 20) < (gs.length : Int) by rw [hlen]; have : sint.Z (W64 20) = 20 := rfl; omega)]
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  rw [hLz]
  obtain ⟨c0, hc0⟩ : ∃ c, s.toList[0]? = some c := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hhead : s.toList.head? = some c0 := by rw [List.head?_eq_getElem?, hc0]
  by_cases h1 : s.toList.length > 1
  · rw [decide_eq_true (show sint.Z (W64 1) < (gs.length : Int) by rw [hlen]; have : sint.Z (W64 1) = 1 := rfl; omega)]
    wp_auto
    have hc0asc : c0.toNat < 128 := hasc c0 (List.mem_of_getElem? hc0)
    have hg0 : gs[0]? = some (BitVec.ofNat 8 c0.toNat : w8) := by
      rw [hgs, List.getElem?_map, hc0]; rfl
    rw [hg0]
    wp_auto
    have hz : (BitVec.ofNat 8 c0.toNat : w8) = W8 48 ↔ c0 = '0' := by
      constructor
      · intro e
        have h := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h
        exact Char.toNat_inj.1 (by rw [h]; rfl)
      · intro e; subst e; rfl
    rw [decide_eq_decide.2 hz]
    by_cases hz0 : c0 = '0'
    · rw [decide_eq_true hz0]
      wp_auto
      iapply HΦ'; ipureintro
      have : parseID s = none := parseID_none s (by simp [h1, hhead, hz0])
      rw [this]
    rw [decide_eq_false hz0]
    have hnf : ¬ (Bool.or (Bool.or s.toList.isEmpty (decide (s.toList.length > 20)))
        (decide (s.toList.length > 1) && (s.toList.head? == some '0'))) = true := by
      have hisE : s.toList.isEmpty = false := by
        cases hl : s.toList with
        | nil => rw [hl] at h0; exact absurd rfl h0
        | cons _ _ => rfl
      simp [hisE, h20, hhead, hz0]
    pid_loop
  rw [decide_eq_false (show ¬ sint.Z (W64 1) < (gs.length : Int) by rw [hlen]; have : sint.Z (W64 1) = 1 := rfl; omega)]
  have hnf : ¬ (Bool.or (Bool.or s.toList.isEmpty (decide (s.toList.length > 20)))
      (decide (s.toList.length > 1) && (s.toList.head? == some '0'))) = true := by
    have hisE : s.toList.isEmpty = false := by
      cases hl : s.toList with
      | nil => rw [hl] at h0; exact absurd rfl h0
      | cons _ _ => rfl
    simp [hisE, h20, h1]
  pid_loop

end proof

end Etcdraft
end EtcdGrove
end Perennial
