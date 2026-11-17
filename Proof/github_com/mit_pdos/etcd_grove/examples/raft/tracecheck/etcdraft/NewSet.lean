/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `NewSet`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.NewSet

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section pure

/-- `insertSorted id S` at the first position `k` whose element is not below `id`: `S` itself
when that element is `id`. -/
theorem insertSorted_at_eq (id : Nat) : ∀ (S : List Nat) (k : Nat),
    (∀ j < k, ∀ y, S[j]? = some y → y < id) → S[k]? = some id → insertSorted id S = S
  | [], k, _, h => by simp at h
  | x :: xs, 0, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; simp [insertSorted]
  | x :: xs, k + 1, hlt, h => by
    have hx : x < id := hlt 0 (by omega) x rfl
    have := insertSorted_at_eq id xs k (fun j hj y hy => hlt (j + 1) (by omega) y hy) h
    simp only [insertSorted, Nat.not_lt_of_lt hx, ite_false, Nat.ne_of_gt hx, this]

/-- `insertSorted id S` at the first position `k` whose element is not below `id`, that element
not `id`: `id` inserted there. -/
theorem insertSorted_at_ne (id : Nat) : ∀ (S : List Nat) (k : Nat), k ≤ S.length →
    (∀ j < k, ∀ y, S[j]? = some y → y < id) → (∀ y, S[k]? = some y → ¬ y < id) →
    S[k]? ≠ some id → insertSorted id S = S.take k ++ id :: S.drop k
  | [], k, _, _, _, _ => by simp [insertSorted]
  | x :: xs, 0, _, _, hge, hne => by
    have h1 : ¬ x < id := hge x rfl
    have h2 : x ≠ id := fun h => hne (by rw [h]; rfl)
    have h3 : id < x := by omega
    simp [insertSorted, h3]
  | x :: xs, k + 1, hk, hlt, hge, hne => by
    have hx : x < id := hlt 0 (by omega) x rfl
    have := insertSorted_at_ne id xs k (by simp at hk; omega)
      (fun j hj y hy => hlt (j + 1) (by omega) y hy) hge hne
    simp only [insertSorted, Nat.not_lt_of_lt hx, ite_false, Nat.ne_of_gt hx, this,
      List.take_succ_cons, List.drop_succ_cons, List.cons_append]

/-- What `append(s, zero)` and then `copy(s[i+1:], s[i:])` leave, with element `i` then set to
`x`: `x` inserted before element `i` (as bbolt's `Write.insert_copy_list`). -/
theorem insert_copy_list {A : Type} (ins : List A) (z x : A) (i : Nat) (hi : i ≤ ins.length) :
    ((ins ++ [z]).take (i + 1) ++
        ((subslice i (ins.length + 1) (ins ++ [z])).take (ins.length + 1 - (i + 1)) ++
          (subslice (i + 1) (ins.length + 1) (ins ++ [z])).drop (ins.length + 1 - i)) ++
        (ins ++ [z]).drop (ins.length + 1)).set i x =
      ins.take i ++ x :: ins.drop i := by
  have h1 : subslice i (ins.length + 1) (ins ++ [z]) = (ins ++ [z]).drop i := by
    simp only [subslice]; rw [List.take_of_length_le (by simp)]
  have h2 : (subslice (i + 1) (ins.length + 1) (ins ++ [z])).drop (ins.length + 1 - i) = [] := by
    apply List.drop_of_length_le; simp [subslice]; omega
  have h3 : (ins ++ [z]).drop (ins.length + 1) = [] := List.drop_of_length_le (by simp)
  have h4 : ((ins ++ [z]).drop i).take (ins.length + 1 - (i + 1)) = ins.drop i := by
    rw [List.drop_append_of_le_length hi]
    exact List.take_left' (by simp)
  obtain ⟨y, hy⟩ : ∃ y, (ins ++ [z])[i]? = some y :=
    ⟨_, List.getElem?_eq_getElem (by simp; omega)⟩
  have h5 : (ins ++ [z]).take (i + 1) = ins.take i ++ [y] := by
    rw [List.take_add_one, hy, List.take_append_of_le_length hi]; rfl
  rw [h1, h2, h3, h4, h5, List.append_nil, List.append_nil, List.append_assoc]
  rw [List.set_append_right _ _ (by simp; omega)]
  simp only [List.length_take, Nat.min_eq_left hi, Nat.sub_self, List.singleton_append,
    List.set_cons_zero]

/-- The length of what `insert_copy_list` sets. -/
theorem insert_copy_list_length {A : Type} (ins : List A) (z : A) (i : Nat) (hi : i ≤ ins.length) :
    ((ins ++ [z]).take (i + 1) ++
        ((subslice i (ins.length + 1) (ins ++ [z])).take (ins.length + 1 - (i + 1)) ++
          (subslice (i + 1) (ins.length + 1) (ins ++ [z])).drop (ins.length + 1 - i)) ++
        (ins ++ [z]).drop (ins.length + 1)).length = ins.length + 1 := by
  have := congrArg List.length (insert_copy_list ins z z i hi)
  rw [List.length_set] at this
  rw [this]; simp; omega

/-- `SetIds.mk` of one more element: inserted. -/
theorem mk_take_succ (xs : List w64) (n : Nat) (y : w64) (Hy : xs[n]? = some y) :
    SetIds.mk ((xs.take (n + 1)).map (fun x => uint.nat x)) =
      insertSorted (uint.nat y) (SetIds.mk ((xs.take n).map (fun x => uint.nat x))) := by
  rw [List.take_add_one, Hy]
  simp [SetIds.mk, List.foldl_append]

/-- `NewSet`'s step, `id` already in `out` (at `k`): `out` unchanged. -/
theorem newSet_step_eq (xs L : List w64) (n : Nat) (y : w64) (kv : Nat) (Hy : xs[n]? = some y)
    (hnL : L.map (fun x => uint.nat x) = SetIds.mk ((xs.take n).map (fun x => uint.nat x)))
    (hkl : ∀ j < kv, ∀ z, L[j]? = some z → uint.nat z < uint.nat y) (hf : L[kv]? = some y) :
    L.map (fun x => uint.nat x) = SetIds.mk ((xs.take (n + 1)).map (fun x => uint.nat x)) := by
  rw [mk_take_succ xs n y Hy, ← hnL]
  refine (insertSorted_at_eq _ _ kv ?_ ?_).symm
  · intro j hj z hz
    rw [List.getElem?_map] at hz
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 hz
    exact hkl j hj w hw
  · rw [List.getElem?_map, hf]; rfl

/-- `NewSet`'s step, `id` not in `out`: inserted at `k`. -/
theorem newSet_step_ne (xs L : List w64) (n : Nat) (y : w64) (kv : Nat) (Hy : xs[n]? = some y)
    (hnL : L.map (fun x => uint.nat x) = SetIds.mk ((xs.take n).map (fun x => uint.nat x)))
    (hk1 : kv ≤ L.length)
    (hkl : ∀ j < kv, ∀ z, L[j]? = some z → uint.nat z < uint.nat y)
    (hge : ∀ w, L[kv]? = some w → ¬ uint.nat w < uint.nat y) (hne : L[kv]? ≠ some y) :
    (L.take kv ++ y :: L.drop kv).map (fun x => uint.nat x) =
      SetIds.mk ((xs.take (n + 1)).map (fun x => uint.nat x)) := by
  rw [mk_take_succ xs n y Hy, ← hnL]
  rw [insertSorted_at_ne _ _ kv (by simpa using hk1) ?_ ?_ ?_]
  · simp [List.map_take, List.map_drop]
  · intro j hj z hz
    rw [List.getElem?_map] at hz
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 hz
    exact hkl j hj w hw
  · intro z hz
    rw [List.getElem?_map] at hz
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 hz
    exact hge w hw
  · intro hz
    rw [List.getElem?_map] at hz
    obtain ⟨w, hw, hwy⟩ := Option.map_eq_some_iff.1 hz
    have : w = y := by
      apply word.unsigned_inj; have := congrArg (fun n : Nat => (n : Int)) hwy; simpa using this
    exact hne (this ▸ hw)

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

-- `id` not in `out`, at the first position `k` not below it (`hge`, `hne`): `append(out, 0)`,
-- `copy(out[k+1:], out[k:])`, `out[k] = id`, then the next round (hygiene off: it names the
-- proof's hypotheses).
set_option hygiene false in
local macro "newset_insert" : tactic => `(tactic| (
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl0 ⟨Hsl0, -⟩
    wp_apply wp_slice_append $$ [Hout Hcap Hsl0] as %s1 ⟨Hs, Hcap, -⟩
    · iframe
    try wp_auto
    ihave %Hsl1 := ownSlice_len _ _ _ $$ Hs
    ihave %Hcw1 := ownSliceCap_wf _ _ $$ Hcap
    simp only [List.length_append, List.length_singleton] at Hsl1
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (kv + W64 1) ∧
      sint.Z (kv + W64 1) ≤ sint.Z s1.len ∧ sint.Z s1.len ≤ sint.Z s1.cap from
      ⟨by word, by word, Hcw1.2⟩))]
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z kv ∧
      sint.Z kv ≤ sint.Z s1.len ∧ sint.Z s1.len ≤ sint.Z s1.cap from
      ⟨hk0, by word, Hcw1.2⟩))]
    try wp_auto
    wp_apply wp_slice_copy_within s1 _ (kv + W64 1) s1.len kv s1.len
      ⟨by word, by word, by word⟩
      ⟨hk0, by word, by word⟩ $$ [Hs] as %k' ⟨_, Hs⟩
    · iframe
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z kv ∧ sint.Z kv < sint.Z s1.len from
      ⟨hk0, by word⟩))]
    rw [show sint.nat (kv + W64 1) = sint.nat kv + 1 by word,
      show sint.nat s1.len = L.length + 1 by omega]
    wp_apply wp_store_slice_index s1 (sint.Z kv) _ y $$ [Hs] as Hs
    · iframe Hs; ipureintro
      refine ⟨hk0, ?_⟩
      rw [insert_copy_list_length L _ _ hk1]
      word
    rw [show (sint.Z kv).toNat = sint.nat kv from rfl,
      insert_copy_list L (W64 0) y (sint.nat kv) hk1]
    try wp_auto
    wp_for_post
    iframe
    iexists _, _, _, _
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word]
    exact newSet_step_ne xs L _ y _ Hy hnL hk1 hkl hge hne))

theorem NewSet.wp_proof : NewSet.spec (GF := GF) (hG := hG) := by
  intro sl xs
  wp_start as #Hxs
  iapply wp_fupd
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hxs
  ihave #Hnil := ownSlice_nil (V := w64) (GF := GF) (DFrac.own 1)
  ihave Hcap0 := ownSliceCap_nil (V := w64) (GF := GF)
  ihave IH : iprop(∃ (n x : w64) (osl : GoSlice) (L : List w64),
      "i" ∷ i_ptr ↦ n ∗ "id" ∷ id_ptr ↦ x ∗ "out" ∷ out_ptr ↦ osl ∗ "Hout" ∷ osl ↦* L ∗
      "Hcap" ∷ ownSliceCap w64 osl (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧
        L.map (fun x => uint.nat x) = SetIds.mk ((xs.take (sint.nat n)).map (fun x => uint.nat x))⌝)
      $$ [i id out Hcap0]
  · iexists _, _, slice.nil, []
    iframe
    isplitr
    · iexact Hnil
    isplitr
    · iexact Hcap0
    ipureintro
    refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp [SetIds.mk]⟩
  wp_for IH
  obtain ⟨hn0, hn1, hnL⟩ := Hn
  ihave %HlenL := ownSlice_len $$ Hout
  wp_if_destruct
  · have Hlt : sint.nat n < xs.length := by rw [Hlen.1]; word
    obtain ⟨y, Hy⟩ : ∃ y, xs[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index sl (sint.Z n) xs DFrac.discard y hn0 $$ [Hxs] as -
    · isplitr
      · iexact Hxs
      ipureintro; exact Hy
    try wp_auto
    ihave IK : iprop(∃ kv : w64, "k" ∷ k_ptr ↦ kv ∗ "out" ∷ out_ptr ↦ osl ∗ "Hout" ∷ osl ↦* L ∗
        "%Hk" ∷ ⌜0 ≤ sint.Z kv ∧ sint.nat kv ≤ L.length ∧
          ∀ j < sint.nat kv, ∀ z, L[j]? = some z → uint.nat z < uint.nat y⌝) $$ [k out Hout]
    · iexists _
      iframe
      ipureintro
      refine ⟨by word, by word, fun j hj => by rw [show sint.nat (W64 0) = 0 from rfl] at hj; omega⟩
    wp_for IK
    obtain ⟨hk0, hk1, hkl⟩ := Hk
    wp_if_destruct
    · have Hlt2 : sint.nat kv < L.length := by rw [HlenL.1]; word
      obtain ⟨z, Hz⟩ : ∃ z, L[sint.nat kv]? = some z := ⟨_, List.getElem?_eq_getElem Hlt2⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z kv ∧ sint.Z kv < sint.Z osl.len from ⟨hk0, Hif⟩))]
      wp_apply wp_load_slice_index osl (sint.Z kv) L (DFrac.own 1) z hk0 $$ [Hout] as Hout
      · iframe Hout; ipureintro; exact Hz
      by_cases hzy : uint.Z z < uint.Z y
      · simp only [hzy, decide_true, ite_true]
        wp_auto
        wp_for_post
        iframe
        iexists _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        have h1 : sint.nat (kv + W64 1) = sint.nat kv + 1 := by word
        rw [h1]
        intro j hj w hw
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · exact hkl j hj w hw
        · subst hj; rw [Hz] at hw; cases hw; word
      · simp only [hzy, decide_false]
        rw [show decide ((#false : val) = #true) = false from
          decide_eq_false (fun h => absurd (GoGlobalContext.intoVal_inj_bool h) (by decide))]
        simp only [Bool.false_eq_true, ite_false, decide_true, ite_true]
        try wp_auto
        rw [decide_eq_true Hif]
        try wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z kv ∧ sint.Z kv < sint.Z osl.len from ⟨hk0, Hif⟩))]
        wp_apply wp_load_slice_index osl (sint.Z kv) L (DFrac.own 1) z hk0 $$ [Hout] as Hout
        · iframe Hout; ipureintro; exact Hz
        try wp_auto
        have hge : ∀ w, L[sint.nat kv]? = some w → ¬ uint.nat w < uint.nat y := by
          intro w hw; rw [Hz] at hw; cases hw; word
        wp_if_destruct
        · -- `id` already there: the next round, `out` unchanged
          wp_for_post
          iframe
          iexists _, _, _, _
          iframe
          ipureintro
          refine ⟨by word, by word, ?_⟩
          rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word]
          exact newSet_step_eq xs L _ y _ Hy hnL hkl (Hif ▸ Hz)
        · have hne : L[sint.nat kv]? ≠ some y := by rw [Hz]; simpa using Hif
          try wp_auto
          newset_insert
    · have hkeq : sint.nat kv = L.length := by rw [HlenL.1]; word
      have hge : ∀ w, L[sint.nat kv]? = some w → ¬ uint.nat w < uint.nat y :=
        fun w hw => by rw [List.getElem?_eq_none (by omega)] at hw; cases hw
      have hne : L[sint.nat kv]? ≠ some y := by rw [List.getElem?_eq_none (by omega)]; simp
      try wp_auto
      rw [decide_eq_false Hif]
      try wp_auto
      newset_insert
  · have hnx : sint.nat n = xs.length := by rw [Hlen.1]; word
    rw [hnx, List.take_length] at hnL
    imod ownSlice_persist $$ Hout with #Hout
    imodintro
    iapply HΦ
    iunfold setRO
    iexists L
    iframe Hout
    ipureintro; exact hnL

end proof

end Etcdraft
end EtcdGrove
end Perennial
