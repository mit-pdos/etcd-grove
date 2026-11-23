/-
`Model()` (kit.go) meets the key-value map's porcupine model spec `kvS` (notes/dsv-vr.md, step 3):
the state's helpers `lookup`, `set`, `has`, `erase`, `push`, `equalPairs` and `step` over read-only
slices of `Pair`s, and the pure `stepG_pSeq`, `rep_eq` (`ModelSet.lean`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.ModelSet

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace github_com.tangledbytes.go_vsr.examples.vsrnet

open EtcdGrove EtcdGrove.linkv

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.tangledbytes.go_vsr.examples.vsrnet.Assumptions]
variable [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet

set_option goose.wp.extras true

/-- A pair list as `Pair`s. -/
def pairsOf (p : List (GoString × GoString)) : List Pair' := p.map (fun x => Pair'.mk x.1 x.2)

/-- `lookup` on a pair list: the first value of the key. -/
def lkP : List Pair' → GoString → Option GoString
  | [], _ => none
  | e :: t, k => if e.K' = k then some e.V' else lkP t k

theorem lkP_pairsOf (p : List (GoString × GoString)) (k : GoString) : lkP (pairsOf p) k = lk p k := by
  induction p with
  | nil => rfl
  | cons x t ih =>
    obtain ⟨a, b⟩ := x
    simp only [pairsOf, List.map_cons, lkP, lk] at ih ⊢
    rw [ih]
    by_cases h : a = k
    · subst h; simp
    · simp [h, Ne.symm h]

theorem lkP_append (L R : List Pair') (k : GoString) :
    lkP (L ++ R) k = (match lkP L k with | some v => some v | none => lkP R k) := by
  induction L with
  | nil => rfl
  | cons e t ih =>
    simp only [List.cons_append, lkP]
    split <;> simp_all

theorem take_succ_of (P : List Pair') (n : Nat) (x : Pair') (hx : P[n]? = some x) :
    P.take (n + 1) = P.take n ++ [x] := by
  rw [List.take_add_one, hx, Option.toList_some]

theorem lkP_take_none (P : List Pair') (n : Nat) (k : GoString) (x : Pair') (hx : P[n]? = some x)
    (h : lkP (P.take n) k = none) (hk : x.K' ≠ k) : lkP (P.take (n + 1)) k = none := by
  rw [take_succ_of P n x hx, lkP_append, h]
  simp [lkP, hk]

theorem lkP_take_some (P : List Pair') (n : Nat) (k : GoString) (x : Pair') (hx : P[n]? = some x)
    (h : lkP (P.take n) k = none) (hk : x.K' = k) : lkP P k = some x.V' := by
  have hn : n < P.length := (List.getElem?_eq_some_iff.1 hx).1
  have e : P = P.take (n + 1) ++ P.drop (n + 1) := (List.take_append_drop (n + 1) P).symm
  rw [e, lkP_append, take_succ_of P n x hx, lkP_append, h]
  simp [lkP, hk]

theorem wp_lookup (p : GoSlice) (P : List Pair') (k : GoString) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ p ↦*□ P }}
      (App (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.lookup')) (Val #p)) (Val #k))
    {{ RET (PairV #((lkP P k).getD []) #(decide ((lkP P k).isSome))); True }} := by
  wp_start as #Hp
  ihave %Hl := ownSlice_len _ _ _ $$ Hp
  wp_auto
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z p.len ∧ lkP (P.take (sint.nat i)) k = none⌝ : IProp GF)
      $$ [i]
  · iexists W64 0
    iframe
    ipureintro
    have h0 : sint.nat (W64 0) = 0 := rfl
    refine ⟨by word, by word, ?_⟩
    rw [h0]; rfl
  wp_for HI
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z p.len := Hif
    list_elem P (sint.nat i) as x
    rw [ite_eq_left ⟨Hi.1, hlt⟩]
    wp_apply wp_load_slice_index p (sint.Z i) P _ x Hi.1 $$ [Hp] as -
    · iframe Hp; ipureintro; exact Hx_lookup
    wp_if_destruct
    · wp_for_post
      have := lkP_take_some P (sint.nat i) _ x Hx_lookup Hi.2.2 (by first | rfl | assumption)
      rw [this]
      simp only [Option.getD_some, Option.isSome_some, decide_true]
      iapply HΦ
      itrivial
    · wp_for_post
      iframe
      iexists i + W64 1
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      have hs : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      rw [hs]
      exact lkP_take_none P (sint.nat i) k x Hx_lookup Hi.2.2 Hif
  · have heq : sint.Z i = sint.Z p.len := by omega
    have hv : lkP P k = none := by
      have := Hi.2.2
      rwa [show sint.nat i = P.length by rw [Hl.1]; show (sint.Z i).toNat = _; rw [heq],
        List.take_length] at this
    rw [hv]
    simp only [Option.getD_none, Option.isSome_none, Bool.false_eq_true, decide_false]
    iapply HΦ
    itrivial

theorem pair_eq_iff (e x : Pair') : (e.K' = x.K' ∧ e.V' = x.V') ↔ e = x := by
  cases e; cases x; simp

instance Pair'.decEq : DecidableEq Pair' := fun a b => decidable_of_iff _ (pair_eq_iff a b)

theorem wp_has (p : GoSlice) (P : List Pair') (x : Pair') :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ p ↦*□ P }}
      (App (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.has)) (Val #p)) (Val #x))
    {{ RET #(decide (x ∈ P)); True }} := by
  wp_start as #Hp
  ihave %Hl := ownSlice_len _ _ _ $$ Hp
  wp_auto
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z p.len ∧ x ∉ P.take (sint.nat i)⌝ : IProp GF)
      $$ [i]
  · iexists W64 0
    iframe
    ipureintro
    have h0 : sint.nat (W64 0) = 0 := rfl
    refine ⟨by word, by word, ?_⟩
    rw [h0]; simp
  wp_for HI
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z p.len := Hif
    list_elem P (sint.nat i) as e
    rw [ite_eq_left ⟨Hi.1, hlt⟩]
    wp_apply wp_load_slice_index p (sint.Z i) P _ e Hi.1 $$ [Hp] as -
    · iframe Hp; ipureintro; exact He_lookup
    have hnext : e ≠ x → x ∉ P.take (sint.nat (i + W64 1)) := by
      intro hne
      have hs : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      rw [hs, take_succ_of P _ e He_lookup]
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨Hi.2.2, fun h => hne h.symm⟩
    wp_if_destruct
    · wp_if_destruct
      · wp_for_post
        have hex : e = x := (pair_eq_iff e x).1 ⟨by assumption, by assumption⟩
        have : x ∈ P := hex ▸ List.mem_of_getElem? He_lookup
        rw [show decide (x ∈ P) = true from decide_eq_true this]
        iapply HΦ
        itrivial
      · wp_for_post
        iframe
        iexists i + W64 1
        iframe
        ipureintro
        refine ⟨by word, by word, hnext fun h => by subst h; contradiction⟩
    · wp_for_post
      iframe
      iexists i + W64 1
      iframe
      ipureintro
      refine ⟨by word, by word, hnext fun h => by subst h; contradiction⟩
  · have heq : sint.Z i = sint.Z p.len := by omega
    have hv : x ∉ P := by
      have := Hi.2.2
      rwa [show sint.nat i = P.length by rw [Hl.1]; show (sint.Z i).toNat = _; rw [heq],
        List.take_length] at this
    rw [show decide (x ∈ P) = false from decide_eq_false hv]
    iapply HΦ
    itrivial

theorem wp_push (p : GoSlice) (P : List Pair') (x : Pair') (hP : P.length < 2 ^ 60) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ p ↦*□ P }}
      (App (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.push)) (Val #p)) (Val #x))
    {{ (q : GoSlice), RET #q; q ↦* (P ++ [x]) }} := by
  wp_start as #Hp
  ihave %Hl := ownSlice_len _ _ _ $$ Hp
  wp_auto
  wp_apply wp_slice_make2 (V := Pair') $$ [] as %q ⟨Hq, -⟩
  · ipureintro; word
  wp_apply wp_slice_copy $$ [$Hq $Hp] as %n ⟨-, Hq, -⟩
  have hn : sint.nat (p.len + W64 1) = P.length + 1 := by rw [Hl.1]; word
  rw [hn, List.take_of_length_le (by simp), List.drop_replicate,
    show P.length + 1 - P.length = 1 by omega, List.replicate_one]
  ihave %Hql := ownSlice_len _ _ _ $$ Hq
  have hb : 0 ≤ sint.Z p.len ∧ sint.Z p.len < sint.Z q.len := by
    have := Hql.1; simp only [List.length_append, List.length_singleton] at this; word
  rw [ite_eq_left hb]
  wp_apply wp_store_slice_index q (sint.Z p.len) _ x $$ [Hq] as Hq
  · iframe Hq; ipureintro; simp only [List.length_append, List.length_singleton]; word
  rw [show (sint.Z p.len).toNat = P.length by rw [Hl.1],
    List.set_append_right _ _ (by omega), Nat.sub_self, List.set_cons_zero]
  wp_auto
  iapply HΦ
  iexact Hq

theorem erase_take_succ (P : List Pair') (v x : Pair') (n : Nat) (hx : P[n]? = some x)
    (f : Bool) (hf : f = false → v ∉ P.take n) (hf2 : f = true → v ∈ P.take n) :
    (if (!f && decide (x = v)) then P.take n else
      (if f then (P.take n).erase v else P.take n) ++ [x]) =
    (if (f || decide (x = v)) then (P.take (n + 1)).erase v else P.take (n + 1)) := by
  rw [List.take_add_one, hx, Option.toList_some]
  cases f
  · have hv := hf rfl
    by_cases h : x = v
    · subst h
      simp [List.erase_append_right _ hv]
    · simp [h]
  · have hv := hf2 rfl
    simp [List.erase_append_left _ hv]

theorem wp_erase (p : GoSlice) (P : List Pair') (v : Pair') :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ p ↦*□ P }}
      (App (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.erase)) (Val #p)) (Val #v))
    {{ (q : GoSlice), RET #q; q ↦* P.erase v }} := by
  wp_start as #Hp
  ihave %Hl := ownSlice_len _ _ _ $$ Hp
  wp_auto
  wp_apply (wp_slice_make3 (V := Pair') (W64 0) p.len (by word)) as %q0 ⟨Hq, Hcap, -⟩
  rw [List.replicate_zero]
  ihave HI : (∃ (i : w64) (f : Bool) (q : GoSlice), "i" ∷ i_ptr ↦ i ∗ "found" ∷ found_ptr ↦ f ∗
      "q" ∷ q_ptr ↦ q ∗
      "Hq" ∷ q ↦* (if f then (P.take (sint.nat i)).erase v else P.take (sint.nat i)) ∗
      "Hcap" ∷ ownSliceCap Pair' q (DFrac.own 1) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z p.len ∧ (f = false → v ∉ P.take (sint.nat i)) ∧
        (f = true → v ∈ P.take (sint.nat i))⌝ : IProp GF) $$ [i found q Hq Hcap]
  · iexists W64 0, false, q0
    have h0 : sint.nat (W64 0) = 0 := rfl
    rw [h0]
    simp only [Bool.false_eq_true, ↓reduceIte, List.take_zero]
    iframe
    ipureintro
    refine ⟨by word, by word, fun _ => by simp, fun h => by cases h⟩
  wp_for HI
  obtain ⟨Hi0, Hil, hf1, hf2⟩ := Hi
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z p.len := by assumption
    list_elem P (sint.nat i) as x
    have e := erase_take_succ P v x (sint.nat i) Hx_lookup f hf1 hf2
    have hs : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z p.len from ⟨Hi0, hlt⟩)]
    wp_apply wp_load_slice_index p (sint.Z i) P _ x Hi0 $$ [Hp] as -
    · iframe Hp; ipureintro; exact Hx_lookup
    have post : ∀ (f' : Bool) (q' : GoSlice),
        f' = (f || decide (x = v)) →
        q' ↦* (if (!f && decide (x = v)) then P.take (sint.nat i) else
          (if f then (P.take (sint.nat i)).erase v else P.take (sint.nat i)) ++ [x]) -∗
        ownSliceCap Pair' q' (DFrac.own 1) -∗ i_ptr ↦ (i + W64 1) -∗ found_ptr ↦ f' -∗ q_ptr ↦ q' -∗
        (∃ (i : w64) (f : Bool) (q : GoSlice), "i" ∷ i_ptr ↦ i ∗ "found" ∷ found_ptr ↦ f ∗
          "q" ∷ q_ptr ↦ q ∗
          "Hq" ∷ q ↦* (if f then (P.take (sint.nat i)).erase v else P.take (sint.nat i)) ∗
          "Hcap" ∷ ownSliceCap Pair' q (DFrac.own 1) ∗
          "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z p.len ∧ (f = false → v ∉ P.take (sint.nat i)) ∧
            (f = true → v ∈ P.take (sint.nat i))⌝ : IProp GF) := by
      intro f' q' hf'
      iintro Hq Hcap Hi Hf Hqp
      iexists i + W64 1, f', q'
      rw [hs, hf', ← e]
      iframe
      ipureintro
      refine ⟨by word, by word, fun h => ?_, fun h => ?_⟩
      · simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
        rw [take_succ_of P _ x Hx_lookup]
        simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨hf1 h.1, Ne.symm h.2⟩
      · rw [take_succ_of P _ x Hx_lookup]
        simp only [Bool.or_eq_true, decide_eq_true_eq] at h
        rcases h with h | h
        · exact List.mem_append_left _ (hf2 h)
        · subst h; simp
    cases f
    · by_cases hxv : x = v
      · subst hxv
        wp_auto
        wp_for_post
        iframe
        iapply (post true q (by simp)) $$ [Hq] Hcap i found q
        simp
        first | iexact Hq' | iexact Hq
      · by_cases hK : x.K' = v.K'
        · have hV : x.V' ≠ v.V' := fun h => hxv ((pair_eq_iff x v).1 ⟨hK, h⟩)
          wp_auto
          rw [decide_eq_true hK]
          wp_auto
          rw [decide_eq_false hV]
          wp_auto
          wp_apply wp_slice_literal (V := Pair') [x]
          isplitr
          · ipureintro; rfl
          iintro %sl ⟨Hsl, -⟩
          wp_auto
          wp_apply wp_slice_append (V := Pair') $$ [$Hq $Hcap $Hsl] as %q' ⟨Hq', Hcap', -⟩
          wp_for_post
          iframe
          iapply (post false q' (by simp [hxv])) $$ [Hq'] Hcap' i found q
          simp [hxv]
          first | iexact Hq' | iexact Hq
        · wp_auto
          rw [decide_eq_false hK]
          wp_auto
          wp_apply wp_slice_literal (V := Pair') [x]
          isplitr
          · ipureintro; rfl
          iintro %sl ⟨Hsl, -⟩
          wp_auto
          wp_apply wp_slice_append (V := Pair') $$ [$Hq $Hcap $Hsl] as %q' ⟨Hq', Hcap', -⟩
          wp_for_post
          iframe
          iapply (post false q' (by simp [hxv])) $$ [Hq'] Hcap' i found q
          simp [hxv]
          first | iexact Hq' | iexact Hq
    · wp_auto
      wp_apply wp_slice_literal (V := Pair') [x]
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_auto
      wp_apply wp_slice_append (V := Pair') $$ [$Hq $Hcap $Hsl] as %q' ⟨Hq', Hcap', -⟩
      wp_for_post
      iframe
      iapply (post true q' (by simp)) $$ [Hq'] Hcap' i found q
      simp
      first | iexact Hq' | iexact Hq
  · have heq : sint.Z i = sint.Z p.len := by omega
    have hn : sint.nat i = P.length := by
      rw [Hl.1]; show (sint.Z i).toNat = _; rw [heq]
    rw [hn, List.take_length]
    iapply HΦ
    cases f
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hv : v ∉ P := by
        have := hf1 rfl
        rwa [hn, List.take_length] at this
      rw [List.erase_of_not_mem hv]
      iexact Hq
    · simp only [↓reduceIte]
      iexact Hq

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
