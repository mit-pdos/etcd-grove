/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/jsoncodec/Inj.lean (lab master 915f964;
notes/dsv-vr.md).
-/
/-
The kit's encodings are injective (on plain strings) and frame uniquely: an event's encoding
is never a strict prefix of another's followed by a newline (`lines_prefix`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.jsoncodec.Facts

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace VsrJson

open JsonScan

open Perennial VsrModel

theorem decN_length (n : Nat) : (n < 10 → (decN n).length = 1) ∧ (10 ≤ n → 2 ≤ (decN n).length) := by
  constructor
  · intro h; rw [decN_eq]; simp [h]
  · intro h; rw [decN_eq]; simp [show ¬ n < 10 by omega]
    have := decN_ne_nil (n / 10)
    cases hh : decN (n / 10) with
    | nil => exact absurd hh this
    | cons _ _ => simp

theorem ofNat48_inj (a b : Nat) (ha : a < 10) (hb : b < 10)
    (h : BitVec.ofNat 8 (48 + a) = BitVec.ofNat 8 (48 + b)) : a = b := by
  have := congrArg BitVec.toNat h
  simp at this
  omega

theorem decN_inj (a b : Nat) (h : decN a = decN b) : a = b := by
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    have la := decN_length a
    have lb := decN_length b
    by_cases ha : a < 10 <;> by_cases hb : b < 10
    · rw [decN_eq a, decN_eq b] at h; simp [ha, hb] at h; exact ofNat48_inj a b ha hb h
    · have := la.1 ha; have := lb.2 (by omega); rw [h] at *; omega
    · have := la.2 (by omega); have := lb.1 hb; rw [h] at *; omega
    · rw [decN_eq a, decN_eq b] at h; simp only [ha, hb, if_false, ite_false] at h
      obtain ⟨h1, h2⟩ := List.append_inj' h rfl
      have e1 := ih (a / 10) (by omega) (b / 10) h1
      simp at h2
      have e2 := ofNat48_inj (a % 10) (b % 10) (by omega) (by omega) (by simpa using h2)
      omega

theorem split_q (k k' Z Z' : List w8) (hk : ∀ c ∈ k, okB c) (hk' : ∀ c ∈ k', okB c)
    (h : k ++ 34#8 :: Z = k' ++ 34#8 :: Z') : k = k' ∧ Z = Z' := by
  induction k generalizing k' with
  | nil =>
    cases k' with
    | nil => simpa using h
    | cons c k' =>
      simp at h; exact absurd h.1.symm (okB_ne_q (hk' c (by simp)))
  | cons c k ih =>
    cases k' with
    | nil => simp at h; exact absurd h.1 (okB_ne_q (hk c (by simp)))
    | cons c' k' =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨h1, h2⟩ := ih k' (fun x hx => hk x (by simp [hx])) (fun x hx => hk' x (by simp [hx])) h
      exact ⟨by rw [h1], h2⟩

theorem split_v (v w : JV) (X X' : List w8) (hv : v.ok) (hw : w.ok) (dv : v.depth ≤ maxDepth)
    (dw : w.depth ≤ maxDepth) (tv : termOK v X) (tw : termOK w X') (h : ser v ++ X = ser w ++ X') :
    ser v = ser w ∧ X = X' := by
  have e1 := top_v v hv X 0 false true dv tv
  have e2 := top_v w hw X' 0 false true dw tw
  rw [h, e2] at e1
  simp at e1
  exact List.append_inj h e1.symm

/-- The constructor of a value, from its first byte. -/
def tag : JV → Nat
  | .num _ => 0
  | .str _ => 1
  | .obj _ => 2
  | .arr _ => 3

theorem ser_head (v : JV) : (ser v).head? =
    match v with
    | .num n => (decN n).head?
    | .str _ => some 34#8
    | .obj _ => some 123#8
    | .arr _ => some 91#8 := by
  cases v <;> simp [ser]

theorem tag_eq (v w : JV) (h : ser v = ser w) : tag v = tag w := by
  have hh := congrArg List.head? h
  rw [ser_head, ser_head] at hh
  have hd : ∀ n, ∃ c, (decN n).head? = some c ∧ isDig c = true := by
    intro n
    cases e : decN n with
    | nil => exact absurd e (decN_ne_nil n)
    | cons c r => exact ⟨c, rfl, decN_digits n c (by rw [e]; simp)⟩
  cases v <;> cases w <;> simp [tag] at hh ⊢
  all_goals first
    | (obtain ⟨c, hc, hdc⟩ := hd _; rw [hc] at hh; simp at hh; subst hh; revert hdc; decide)
    | (obtain ⟨c, hc, hdc⟩ := hd _; rw [hc] at hh; simp at hh; rw [← hh] at hdc; revert hdc; decide)

mutual
theorem ser_inj (v w : JV) (hv : v.ok) (hw : w.ok) (dv : v.depth ≤ maxDepth)
    (dw : w.depth ≤ maxDepth) (h : ser v = ser w) : v = w := by
  have ht := tag_eq v w h
  match v, w with
  | .num a, .num b => rw [ser_num, ser_num] at h; rw [decN_inj a b h]
  | .str a, .str b => rw [ser_str, ser_str] at h; simp at h; rw [h]
  | .obj a, .obj b =>
    rw [ser_obj, ser_obj] at h; simp at h
    simp only [JV.ok] at hv hw
    simp only [JV.depth] at dv dw
    rw [serMs_inj a b hv hw (by omega) (by omega) h]
  | .arr a, .arr b =>
    rw [ser_arr, ser_arr] at h; simp at h
    simp only [JV.ok] at hv hw
    simp only [JV.depth] at dv dw
    rw [serVs_inj a b hv hw (by omega) (by omega) h]
  | .num _, .str _ | .num _, .obj _ | .num _, .arr _ | .str _, .num _ | .str _, .obj _
  | .str _, .arr _ | .obj _, .num _ | .obj _, .str _ | .obj _, .arr _ | .arr _, .num _
  | .arr _, .str _ | .arr _, .obj _ => simp [tag] at ht

theorem serMs_inj (a b : JMs) (ha : a.ok) (hb : b.ok) (da : a.depth < maxDepth)
    (db : b.depth < maxDepth) (h : serMs a = serMs b) : a = b := by
  match a, b with
  | .nil, .nil => rfl
  | .nil, .cons _ _ _ => rw [serMs_nil, serMs_cons] at h; simp at h
  | .cons _ _ _, .nil => rw [serMs_nil, serMs_cons] at h; simp at h
  | .cons k v a', .cons k' v' b' =>
    simp only [JMs.ok] at ha hb
    simp only [JMs.depth] at da db
    rw [serMs_cons, serMs_cons] at h
    simp only [List.cons.injEq, true_and] at h
    obtain ⟨rfl, h3⟩ := split_q _ _ _ _ ha.1 hb.1 h
    simp only [List.cons.injEq, true_and] at h3
    have h' : ser v ++ (serMsT a' ++ [125#8]) = ser v' ++ (serMsT b' ++ [125#8]) := by
      rw [← List.append_assoc, ← List.append_assoc, h3]
    obtain ⟨h1, h2⟩ := split_v v v' _ _ ha.2.1 hb.2.1 (by omega) (by omega)
      (termOK_msT v a') (termOK_msT v' b') h'
    rw [ser_inj v v' ha.2.1 hb.2.1 (by omega) (by omega) h1,
      serMsT_inj a' b' ha.2.2 hb.2.2 (by omega) (by omega) (by simpa using h2)]

theorem serMsT_inj (a b : JMs) (ha : a.ok) (hb : b.ok) (da : a.depth < maxDepth)
    (db : b.depth < maxDepth) (h : serMsT a = serMsT b) : a = b := by
  match a, b with
  | .nil, .nil => rfl
  | .nil, .cons _ _ _ => rw [serMsT_nil, serMsT_cons] at h; simp at h
  | .cons _ _ _, .nil => rw [serMsT_nil, serMsT_cons] at h; simp at h
  | .cons k v a', .cons k' v' b' =>
    simp only [JMs.ok] at ha hb
    simp only [JMs.depth] at da db
    rw [serMsT_cons, serMsT_cons] at h
    simp only [List.cons.injEq, true_and] at h
    obtain ⟨rfl, h3⟩ := split_q _ _ _ _ ha.1 hb.1 h
    simp only [List.cons.injEq, true_and] at h3
    have h' : ser v ++ (serMsT a' ++ [125#8]) = ser v' ++ (serMsT b' ++ [125#8]) := by
      rw [← List.append_assoc, ← List.append_assoc, h3]
    obtain ⟨h1, h2⟩ := split_v v v' _ _ ha.2.1 hb.2.1 (by omega) (by omega)
      (termOK_msT v a') (termOK_msT v' b') h'
    rw [ser_inj v v' ha.2.1 hb.2.1 (by omega) (by omega) h1,
      serMsT_inj a' b' ha.2.2 hb.2.2 (by omega) (by omega) (by simpa using h2)]

theorem serVs_inj (a b : JVs) (ha : a.ok) (hb : b.ok) (da : a.depth < maxDepth)
    (db : b.depth < maxDepth) (h : serVs a = serVs b) : a = b := by
  match a, b with
  | .nil, .nil => rfl
  | .nil, .cons v _ =>
    rw [serVs_nil, serVs_cons] at h
    obtain ⟨c, r, hc, -, -⟩ := first_ne v; rw [hc] at h; simp at h
  | .cons v _, .nil =>
    rw [serVs_nil, serVs_cons] at h
    obtain ⟨c, r, hc, -, -⟩ := first_ne v; rw [hc] at h; simp at h
  | .cons v a', .cons v' b' =>
    simp only [JVs.ok] at ha hb
    simp only [JVs.depth] at da db
    rw [serVs_cons, serVs_cons] at h
    have h' : ser v ++ (serVsT a' ++ [93#8]) = ser v' ++ (serVsT b' ++ [93#8]) := by
      rw [← List.append_assoc, ← List.append_assoc, h]
    obtain ⟨h1, h2⟩ := split_v v v' _ _ ha.1 hb.1 (by omega) (by omega)
      (termOK_vsT v a') (termOK_vsT v' b') h'
    rw [ser_inj v v' ha.1 hb.1 (by omega) (by omega) h1,
      serVsT_inj a' b' ha.2 hb.2 (by omega) (by omega) (by simpa using h2)]

theorem serVsT_inj (a b : JVs) (ha : a.ok) (hb : b.ok) (da : a.depth < maxDepth)
    (db : b.depth < maxDepth) (h : serVsT a = serVsT b) : a = b := by
  match a, b with
  | .nil, .nil => rfl
  | .nil, .cons _ _ => rw [serVsT_nil, serVsT_cons] at h; simp at h
  | .cons _ _, .nil => rw [serVsT_nil, serVsT_cons] at h; simp at h
  | .cons v a', .cons v' b' =>
    simp only [JVs.ok] at ha hb
    simp only [JVs.depth] at da db
    rw [serVsT_cons, serVsT_cons] at h
    simp only [List.cons.injEq, true_and] at h
    have h' : ser v ++ (serVsT a' ++ [93#8]) = ser v' ++ (serVsT b' ++ [93#8]) := by
      rw [← List.append_assoc, ← List.append_assoc, h]
    obtain ⟨h1, h2⟩ := split_v v v' _ _ ha.1 hb.1 (by omega) (by omega)
      (termOK_vsT v a') (termOK_vsT v' b') h'
    rw [ser_inj v v' ha.1 hb.1 (by omega) (by omega) h1,
      serVsT_inj a' b' ha.2 hb.2 (by omega) (by omega) (by simpa using h2)]
end

end VsrJson
