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

/-- `set`'s element map. -/
def setG (k v : GoString) (e : Pair') : Pair' := if e.K' = k then Pair'.mk k v else e

/-- `set` on a `Pair` list. -/
def setL (P : List Pair') (k v : GoString) : List Pair' :=
  if P.any (fun e => decide (e.K' = k)) then P.map (setG k v) else P ++ [Pair'.mk k v]

theorem pairsOf_setP (p : List (GoString × GoString)) (k v : GoString) :
    pairsOf (setP p k v) = setL (pairsOf p) k v := by
  unfold setP setL pairsOf setG
  have ha : ((p.map (fun x => Pair'.mk x.1 x.2)).any (fun e => decide (e.K' = k))) =
      p.any (fun x => decide (x.1 = k)) := by simp [List.any_map, Function.comp_def]
  rw [ha]
  split
  · simp only [List.map_map]
    congr 1
    funext x
    simp only [Function.comp_apply]
    split <;> simp_all
  · simp

theorem map_setG_id (P : List Pair') (k v : GoString)
    (h : P.any (fun e => decide (e.K' = k)) = false) : P.map (setG k v) = P := by
  induction P with
  | nil => rfl
  | cons e t ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    simp [setG, h.1, ih h.2]

theorem wp_set (p : GoSlice) (P : List Pair') (k v : GoString) (hP : P.length < 2 ^ 60) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ p ↦*□ P }}
      (App (App (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.set)) (Val #p)) (Val #k))
        (Val #v))
    {{ (q : GoSlice), RET #q; q ↦* setL P k v }} := by
  wp_start as #Hp
  ihave %Hl := ownSlice_len _ _ _ $$ Hp
  wp_auto
  wp_apply (wp_slice_make3 (V := Pair') (W64 0) (p.len + W64 1) (by word)) as %q0 ⟨Hq, Hcap, -⟩
  rw [List.replicate_zero]
  ihave HI : (∃ (i : w64) (q : GoSlice), "i" ∷ i_ptr ↦ i ∗
      "found" ∷ found_ptr ↦ (P.take (sint.nat i)).any (fun e => decide (e.K' = k)) ∗
      "q" ∷ q_ptr ↦ q ∗
      "Hq" ∷ q ↦* (P.take (sint.nat i)).map (setG k v) ∗
      "Hcap" ∷ ownSliceCap Pair' q (DFrac.own 1) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z p.len⌝ : IProp GF) $$ [i found q Hq Hcap]
  · iexists W64 0, q0
    have h0 : sint.nat (W64 0) = 0 := rfl
    rw [h0]
    simp only [List.take_zero, List.any_nil, List.map_nil]
    iframe
    ipureintro
    exact ⟨by word, by word⟩
  wp_for HI
  obtain ⟨Hi0, Hil⟩ := Hi
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z p.len := by assumption
    list_elem P (sint.nat i) as x
    have hs : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z p.len from ⟨Hi0, hlt⟩)]
    wp_apply wp_load_slice_index p (sint.Z i) P _ x Hi0 $$ [Hp] as -
    · iframe Hp; ipureintro; exact Hx_lookup
    wp_if_destruct
    · wp_apply wp_slice_literal (V := Pair') [Pair'.mk x.K' v]
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_auto
      wp_apply wp_slice_append (V := Pair') $$ [$Hq $Hcap $Hsl] as %q' ⟨Hq', Hcap', -⟩
      wp_for_post
      iframe
      iexists i + W64 1, q'
      rw [hs, take_succ_of P _ x Hx_lookup]
      simp only [List.any_append, List.any_cons, List.any_nil, decide_true, Bool.or_true, Bool.true_or,
        List.map_append, List.map_cons, List.map_nil, setG, ↓reduceIte]
      iframe
      ipureintro
      exact ⟨by word, by word⟩
    · wp_apply wp_slice_literal (V := Pair') [x]
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_auto
      wp_apply wp_slice_append (V := Pair') $$ [$Hq $Hcap $Hsl] as %q' ⟨Hq', Hcap', -⟩
      wp_for_post
      iframe
      iexists i + W64 1, q'
      rw [hs, take_succ_of P _ x Hx_lookup]
      have hxk : x.K' ≠ k := by assumption
      simp only [List.any_append, List.any_cons, List.any_nil, hxk, decide_false, Bool.or_false,
        List.map_append, List.map_cons, List.map_nil, setG, ↓reduceIte]
      iframe
      ipureintro
      exact ⟨by word, by word⟩
  · have heq : sint.Z i = sint.Z p.len := by omega
    have hn : sint.nat i = P.length := by
      rw [Hl.1]; show (sint.Z i).toNat = _; rw [heq]
    rw [hn, List.take_length]
    unfold setL
    cases ha : P.any (fun e => decide (e.K' = k))
    · wp_auto
      wp_apply wp_slice_literal (V := Pair') [Pair'.mk k v]
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_auto
      wp_apply wp_slice_append (V := Pair') $$ [$Hq $Hcap $Hsl] as %q' ⟨Hq', Hcap', -⟩
      iapply HΦ
      rw [map_setG_id P k v ha]
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexact Hq'
    · wp_auto
      iapply HΦ
      simp only [↓reduceIte]
      iexact Hq

theorem wp_equalPairs (a b : GoSlice) (A B : List Pair') :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ a ↦*□ A ∗ b ↦*□ B }}
      (App (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.equalPairs)) (Val #a))
        (Val #b))
    {{ (r : Bool), RET #r; ⌜r = true → A = B⌝ }} := by
  wp_start as ⟨#Ha, #Hb⟩
  ihave %HA := ownSlice_len _ _ _ $$ Ha
  ihave %HB := ownSlice_len _ _ _ $$ Hb
  wp_auto
  wp_if_destruct
  · have h3 : a.len = b.len := by assumption
    have hAB : A.length = B.length := by rw [HA.1, HB.1, h3]
    ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z a.len ∧
          A.take (sint.nat i) = B.take (sint.nat i)⌝ : IProp GF) $$ [i]
    · iexists W64 0
      iframe
      ipureintro
      have h0 : sint.nat (W64 0) = 0 := rfl
      refine ⟨by word, by word, by rw [h0]; simp⟩
    wp_for HI
    obtain ⟨Hi0, Hil, Ht⟩ := Hi
    wp_if_destruct
    · have hlt : sint.Z i < sint.Z a.len := by assumption
      list_elem A (sint.nat i) as x
      list_elem B (sint.nat i) as y
      rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z a.len from ⟨Hi0, hlt⟩)]
      wp_apply wp_load_slice_index a (sint.Z i) A _ x Hi0 $$ [Ha] as -
      · iframe Ha; ipureintro; exact Hx_lookup
      rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z b.len from ⟨Hi0, h3 ▸ hlt⟩)]
      wp_apply wp_load_slice_index b (sint.Z i) B _ y Hi0 $$ [Hb] as -
      · iframe Hb; ipureintro; exact Hy_lookup
      by_cases hxy : x = y
      · subst hxy
        wp_auto
        wp_for_post
        iframe
        iexists i + W64 1
        iframe
        ipureintro
        have hs : sint.nat (i + W64 1) = sint.nat i + 1 := by word
        refine ⟨by word, by word, ?_⟩
        rw [hs, take_succ_of A _ x Hx_lookup, take_succ_of B _ x Hy_lookup, Ht]
      · by_cases hK : x.K' = y.K'
        · have hV : x.V' ≠ y.V' := fun h => hxy ((pair_eq_iff x y).1 ⟨hK, h⟩)
          rw [decide_eq_true hK]
          wp_auto
          rw [decide_eq_false hV]
          wp_auto
          wp_for_post
          iapply HΦ; ipureintro; intro h; cases h
        · rw [decide_eq_false hK]
          wp_auto
          wp_for_post
          iapply HΦ; ipureintro; intro h; cases h
    · have heq : sint.Z i = sint.Z a.len := by omega
      have hn : sint.nat i = A.length := by
        rw [HA.1]; show (sint.Z i).toNat = _; rw [heq]
      have e : A = B := by
        rw [hn, List.take_length, hAB, List.take_length] at Ht
        exact Ht
      iapply HΦ
      ipureintro; intro _; exact e
  · iapply HΦ; ipureintro; intro h; cases h

/-- A pending put as the model's `Pair`. -/
def pairK (x : KIn) : Pair' := Pair'.mk (inFields x.1).2.1 (inFields x.1).2.2

/-- Every pending input is a put. -/
def AllPut (Pend : List KIn) : Prop := ∀ x ∈ Pend, kvB.isWrite x = true

theorem pairK_eq (x : KIn) (hx : kvB.isWrite x = true) (k w : GoString) :
    pairK x = Pair'.mk k w ↔ x.1 = .put k w := by
  rcases x with ⟨xi, hxi⟩
  cases xi with
  | get k0 => simp [kvB] at hx
  | put k0 v0 => simp [pairK, inFields]

theorem mem_pairK {Pend : List KIn} (hP : AllPut Pend) (k w : GoString) :
    Pair'.mk k w ∈ Pend.map pairK ↔
      (Pend.find? (fun x => decide (x.1 = .put k w))).isSome := by
  rw [List.find?_isSome]
  constructor
  · intro h
    obtain ⟨x, hx, e⟩ := List.mem_map.1 h
    exact ⟨x, hx, by simpa using (pairK_eq x (hP x hx) k w).1 e⟩
  · rintro ⟨x, hx, e⟩
    exact List.mem_map.2 ⟨x, hx, (pairK_eq x (hP x hx) k w).2 (by simpa using e)⟩

theorem erase_pairK {Pend : List KIn} (hP : AllPut Pend) {k w : GoString} {x : KIn}
    (hf : Pend.find? (fun x => decide (x.1 = .put k w)) = some x) :
    (Pend.map pairK).erase (Pair'.mk k w) = (Pend.erase x).map pairK := by
  induction Pend with
  | nil => cases hf
  | cons y t ih =>
    have hy := hP y List.mem_cons_self
    have hP' : AllPut t := fun z hz => hP z (List.mem_cons_of_mem _ hz)
    by_cases e : y.1 = .put k w
    · have hyk : pairK y = Pair'.mk k w := (pairK_eq y hy k w).2 e
      simp only [List.find?_cons, e, decide_true] at hf
      cases hf
      simp [hyk]
    · simp only [List.find?_cons, e, decide_false] at hf
      have hne : pairK y ≠ Pair'.mk k w := fun h => e ((pairK_eq y hy k w).1 h)
      have hyx : y ≠ x := by
        intro h; subst h; exact e (by simpa using List.find?_some hf)
      simp only [List.map_cons, List.erase_cons, beq_iff_eq, hne, hyx, ↓reduceIte, ih hP' hf]

/-- An answer's `Out` fields `(Unknown, Done, Found, V)`. -/
def ansFields : Ans KOut → Bool × Bool × Bool × GoString
  | .err => (true, false, false, [])
  | .ok o => (false, (outFields o.1).1, (outFields o.1).2.1, (outFields o.1).2.2)

theorem ansV_fields (a : Ans KOut) :
    ansV a = outVal (ansFields a).1 (ansFields a).2.1 (ansFields a).2.2.1 (ansFields a).2.2.2 := by
  cases a <;> rfl

theorem wp_stepGo (cur pend : GoSlice) (Cur : List (GoString × GoString)) (Pend : List KIn)
    (hc : Cur.length < 2 ^ 60) (hp : Pend.length < 2 ^ 60) (hP : AllPut Pend) (i : KIn) (a : Ans KOut) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ cur ↦*□ pairsOf Cur ∗ pend ↦*□ Pend.map pairK }}
      (App (App (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.step))
        (Val #(State.mk cur pend)))
        (Val #(In.mk (inFields i.1).1 (inFields i.1).2.1 (inFields i.1).2.2)))
        (Val #(Out.mk (ansFields a).1 (ansFields a).2.1 (ansFields a).2.2.1 (ansFields a).2.2.2)))
    {{ (ok : Bool) (s' : State), RET (PairV #ok #s'); ∃ (cur' pend' : GoSlice),
        ⌜ok = (stepG Cur Pend i a).1 ∧ s' = State.mk cur' pend'⌝ ∗
        cur' ↦*□ pairsOf (stepG Cur Pend i a).2.1 ∗
        pend' ↦*□ (stepG Cur Pend i a).2.2.map pairK }} := by
  wp_start as ⟨#Hc, #Hp⟩
  have hcm : (pairsOf Cur).length < 2 ^ 60 := by simpa [pairsOf] using hc
  have hpm : (Pend.map pairK).length < 2 ^ 60 := by simpa using hp
  obtain ⟨ii, hii⟩ := i
  cases a with
  | err =>
    cases ii with
    | put k v =>
      simp only [ansFields, inFields]
      wp_auto
      wp_apply +noauto wp_push pend (Pend.map pairK) (Pair'.mk k v) hpm $$ [$Hp] as %q Hq
      iapply fupd_wp
      imod ownSlice_persist _ _ _ $$ Hq with #Hq
      imodintro
      wp_auto
      iapply HΦ
      iexists cur, q
      simp only [stepG, kvB, ↓reduceIte, List.map_append, List.map_cons, List.map_nil, pairK,
        inFields]
      iframe Hc Hq
      ipureintro; simp
    | get k =>
      simp only [ansFields, inFields]
      wp_auto
      iapply HΦ
      iexists cur, pend
      simp only [stepG, kvB, Bool.false_eq_true, ↓reduceIte]
      iframe Hc Hp
      ipureintro; simp
  | ok o =>
    obtain ⟨oo, hoo⟩ := o
    cases ii with
    | put k v =>
      cases oo with
      | done =>
        simp only [ansFields, inFields, outFields]
        wp_auto
        wp_apply +noauto wp_set cur (pairsOf Cur) k v hcm $$ [$Hc] as %q Hq
        iapply fupd_wp
        imod ownSlice_persist _ _ _ $$ Hq with #Hq
        imodintro
        wp_auto
        iapply HΦ
        iexists q, pend
        rw [← pairsOf_setP]
        simp only [stepG]
        iframe Hq Hp
        ipureintro; simp
      | got w =>
        cases w <;>
        · simp only [ansFields, inFields, outFields]
          wp_auto
          iapply HΦ
          iexists cur, pend
          simp only [stepG]
          iframe Hc Hp
          ipureintro; simp
    | get k =>
      cases oo with
      | done =>
        simp only [ansFields, inFields, outFields]
        wp_auto
        iapply HΦ
        iexists cur, pend
        simp only [stepG]
        iframe Hc Hp
        ipureintro; simp
      | got w =>
        cases w with
        | none =>
          simp only [ansFields, inFields, outFields]
          wp_auto
          wp_apply wp_lookup cur (pairsOf Cur) k $$ [$Hc]
          rw [lkP_pairsOf]
          iapply HΦ
          iexists cur, pend
          simp only [stepG]
          iframe Hc Hp
          ipureintro
          cases lk Cur k <;> simp
        | some w =>
          simp only [ansFields, inFields, outFields]
          wp_auto
          wp_apply wp_lookup cur (pairsOf Cur) k $$ [$Hc]
          rw [lkP_pairsOf]
          have hcase : (lk Cur k = some w) ∨ (lk Cur k ≠ some w) := Classical.em _
          rcases hcase with hl | hl
          · rw [hl]
            simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
            wp_auto
            iapply HΦ
            iexists cur, pend
            simp only [stepG, hl, ↓reduceIte]
            iframe Hc Hp
            ipureintro; simp
          · cases e : lk Cur k with
            | none =>
              simp only [Option.isSome_none, decide_false, Bool.false_eq_true, Option.getD_none]
              wp_auto
              wp_apply wp_has pend (Pend.map pairK) (Pair'.mk k w) $$ [$Hp]
              have hst : lk Cur k = some w ↔ False := ⟨hl, False.elim⟩
              cases hf : Pend.find? (fun x => decide (x.1 = .put k w)) with
              | none =>
                have hm : Pair'.mk k w ∉ Pend.map pairK := fun h => by
                  have := (mem_pairK hP k w).1 h; rw [hf] at this; cases this
                rw [decide_eq_false hm]
                wp_auto
                iapply HΦ
                iexists cur, pend
                simp only [stepG, hst, ↓reduceIte, hf]
                iframe Hc Hp
                ipureintro; simp
              | some x =>
                have hm : Pair'.mk k w ∈ Pend.map pairK := (mem_pairK hP k w).2 (by rw [hf]; rfl)
                rw [decide_eq_true hm]
                wp_auto
                wp_apply +noauto wp_set cur (pairsOf Cur) k w hcm $$ [$Hc] as %r Hr
                iapply fupd_wp
                imod ownSlice_persist _ _ _ $$ Hr with #Hr
                imodintro
                wp_auto
                wp_apply +noauto wp_erase pend (Pend.map pairK) (Pair'.mk k w) $$ [$Hp] as %q Hq
                iapply fupd_wp
                imod ownSlice_persist _ _ _ $$ Hq with #Hq
                imodintro
                wp_auto
                iapply HΦ
                iexists r, q
                rw [← pairsOf_setP, erase_pairK hP hf]
                simp only [stepG, hst, ↓reduceIte, hf]
                iframe Hr Hq
                ipureintro; simp
            | some v =>
              have hvw : v ≠ w := fun h => hl (by rw [e, h])
              simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
              wp_auto
              rw [decide_eq_false hvw]
              wp_auto
              wp_apply wp_has pend (Pend.map pairK) (Pair'.mk k w) $$ [$Hp]
              have hst : lk Cur k = some w ↔ False := ⟨hl, False.elim⟩
              cases hf : Pend.find? (fun x => decide (x.1 = .put k w)) with
              | none =>
                have hm : Pair'.mk k w ∉ Pend.map pairK := fun h => by
                  have := (mem_pairK hP k w).1 h; rw [hf] at this; cases this
                rw [decide_eq_false hm]
                wp_auto
                iapply HΦ
                iexists cur, pend
                simp only [stepG, hst, ↓reduceIte, hf]
                iframe Hc Hp
                ipureintro; simp
              | some x =>
                have hm : Pair'.mk k w ∈ Pend.map pairK := (mem_pairK hP k w).2 (by rw [hf]; rfl)
                rw [decide_eq_true hm]
                wp_auto
                wp_apply +noauto wp_set cur (pairsOf Cur) k w hcm $$ [$Hc] as %r Hr
                iapply fupd_wp
                imod ownSlice_persist _ _ _ $$ Hr with #Hr
                imodintro
                wp_auto
                wp_apply +noauto wp_erase pend (Pend.map pairK) (Pair'.mk k w) $$ [$Hp] as %q Hq
                iapply fupd_wp
                imod ownSlice_persist _ _ _ $$ Hq with #Hq
                imodintro
                wp_auto
                iapply HΦ
                iexists r, q
                rw [← pairsOf_setP, erase_pairK hP hf]
                simp only [stepG, hst, ↓reduceIte, hf]
                iframe Hr Hq
                ipureintro; simp

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
