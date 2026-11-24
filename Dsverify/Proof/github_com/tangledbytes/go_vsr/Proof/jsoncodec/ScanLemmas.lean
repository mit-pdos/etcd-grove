/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/jsoncodec/ScanLemmas.lean (lab master 915f964;
notes/dsv-vr.md).
-/
/-
The scanner on the kit's encodings: strings, numbers, and every `JV` value (`goL` on `ser v`
followed by anything, and on a prefix of `ser v`).
-/
module

public import Net.Proof.models_lab.jsoncodec.Scan.Steps
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.jsoncodec.Enc

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace VsrJson

open JsonScan

open Perennial

/-! ## Bytes -/

theorem okB_ne_q {c : w8} (h : okB c) : c ≠ 34#8 := h.2.2.1
theorem okB_ne_bs {c : w8} (h : okB c) : c ≠ 92#8 := h.2.2.2
theorem okB_not_lt {c : w8} (h : okB c) : ¬ c < 32#8 := by
  intro hc; have := h.1; rw [BitVec.lt_def] at hc; simp at hc; omega

/-! ## Strings -/

theorem strL_q_cons (cs : List w8) (j : Nat) : strL (34#8 :: cs) j = (0, j + 1) := by
  rw [strL.eq_def]; simp

theorem strL_ok (c : w8) (cs : List w8) (hc : okB c) (j : Nat) :
    strL (c :: cs) j = strL cs (j + 1) := by
  rw [strL.eq_def]; simp [okB_ne_q hc, okB_not_lt hc, okB_ne_bs hc]

theorem strL_full (s rest : List w8) (hs : ∀ c ∈ s, okB c) (j : Nat) :
    strL (s ++ 34#8 :: rest) j = (0, j + s.length + 1) := by
  induction s generalizing j with
  | nil => simp [strL_q_cons]
  | cons c s ih =>
    have hc := hs c (by simp)
    simp only [List.cons_append, strL_ok c _ hc]
    rw [ih (fun x hx => hs x (by simp [hx]))]
    simp; omega

theorem strL_part (s : List w8) (hs : ∀ c ∈ s, okB c) (j : Nat) :
    strL s j = (1, j + s.length) := by
  induction s generalizing j with
  | nil => rw [strL.eq_def]; simp
  | cons c s ih =>
    have hc := hs c (by simp)
    rw [strL_ok c _ hc]
    rw [ih (fun x hx => hs x (by simp [hx]))]
    simp; omega

/-! ## Numbers -/

theorem decN_eq (n : Nat) :
    decN n = if n < 10 then [BitVec.ofNat 8 (48 + n)]
      else decN (n / 10) ++ [BitVec.ofNat 8 (48 + n % 10)] := by
  rw [decN]

theorem isDig_ofNat (d : Nat) (h : d < 10) : isDig (BitVec.ofNat 8 (48 + d)) = true := by
  have : ∀ d, d < 10 → isDig (BitVec.ofNat 8 (48 + d)) = true := by decide
  exact this d h

theorem decN_digits (n : Nat) : ∀ c ∈ decN n, isDig c = true := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [decN_eq]
    split
    · simp; exact isDig_ofNat n (by omega)
    · intro c hc
      simp at hc
      rcases hc with hc | rfl
      · exact ih (n / 10) (by omega) c hc
      · exact isDig_ofNat _ (by omega)

theorem decN_ne_nil (n : Nat) : decN n ≠ [] := by
  rw [decN_eq]; split <;> simp

theorem decN_head (n : Nat) (h : n ≠ 0) : ∃ c r, decN n = c :: r ∧ c ≠ 48#8 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [decN_eq]
    split
    · refine ⟨_, [], rfl, ?_⟩
      intro hc
      have : (BitVec.ofNat 8 (48 + n)).toNat = (48#8 : w8).toNat := by rw [hc]
      simp at this; omega
    · obtain ⟨c, r, h1, h2⟩ := ih (n / 10) (by omega) (by omega)
      exact ⟨c, r ++ _, by rw [h1]; rfl, h2⟩

theorem decN_zero : decN 0 = [48#8] := by rw [decN_eq]; rfl

theorem digitsL_digits (ds rest : List w8) (hd : ∀ c ∈ ds, isDig c = true)
    (hr : ∀ c ∈ rest.head?, isDig c = false) (j : Nat) :
    digitsL (ds ++ rest) j = (j + ds.length, rest) := by
  induction ds generalizing j with
  | nil =>
    cases rest with
    | nil => simp [digitsL]
    | cons c r => simp at hr; simp [digitsL, hr]
  | cons c ds ih =>
    simp only [List.cons_append, digitsL, hd c (by simp), if_true]
    rw [ih (fun x hx => hd x (by simp [hx]))]
    simp; omega

/-- A byte that ends a number (after its digits). -/
def numEnd (c : w8) : Prop := isDig c = false ∧ c ≠ 46#8 ∧ c ≠ 101#8 ∧ c ≠ 69#8

theorem numL_full (n : Nat) (c : w8) (r : List w8) (hc : numEnd c) (i : Nat) (eof : Bool) :
    numL (decN n ++ c :: r) i eof = (0, i + (decN n).length) := by
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hc
  by_cases hn : n = 0
  · subst hn
    rw [decN_zero]
    simp [numL, intL, fracL, expL, hc2, hc3, hc4]
  · obtain ⟨d, ds, hdn, hd⟩ := decN_head n hn
    have hdig := decN_digits n
    rw [hdn] at hdig ⊢
    have hd45 : d ≠ 45#8 := by
      intro h; have := hdig d (by simp); rw [h] at this; exact absurd this (by decide)
    have hdl := digitsL_digits (d :: ds) (c :: r) hdig (by simpa using hc1) i
    simp only [List.cons_append] at hdl
    simp only [List.cons_append, numL, hd45, if_false, intL, hd, hdl]
    simp [fracL, expL, hc2, hc3, hc4]

theorem numL_part (p : List w8) (hp : p ≠ []) (hd : ∀ c ∈ p, isDig c = true)
    (h0 : p.head? = some 48#8 → p.length = 1) (i : Nat) :
    numL p i false = (1, i + p.length) := by
  obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil hp
  have hd45 : d ≠ 45#8 := by
    intro h; have := hd d (by simp); rw [h] at this; exact absurd this (by decide)
  by_cases h48 : d = 48#8
  · have := h0 (by simp [h48]); simp at this; subst this; subst h48
    simp [numL, intL, endS]
  · have hdl := digitsL_digits (d :: ds) [] hd (by simp) i
    simp only [List.append_nil] at hdl
    simp only [numL, hd45, if_false, intL, h48, hdl]
    simp [endS]

end VsrJson

namespace VsrJson

open JsonScan
open Perennial

/-- What may follow a value inside a container: after a number, a byte that ends it. -/
def termOK : JV → List w8 → Prop
  | .num _, rest => ∃ c r, rest = c :: r ∧ numEnd c
  | _, _ => True

theorem numEnd_comma : numEnd 44#8 := by unfold numEnd; decide
theorem numEnd_rb : numEnd 125#8 := by unfold numEnd; decide
theorem numEnd_rs : numEnd 93#8 := by unfold numEnd; decide

theorem isDig_ne (c : w8) (h : isDig c = true) :
    spB c = false ∧ c ≠ 91#8 ∧ c ≠ 123#8 ∧ c ≠ 93#8 ∧ c ≠ 34#8 ∧ c ≠ 45#8 := by
  simp only [isDig, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [spB, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_false_iff,
    beq_eq_false_iff_ne, ne_eq]
  obtain ⟨h1, h2⟩ := h
  and_intros <;> bv_omega

/-- The end of a container: done at the top, else after a value in the enclosing one. -/
def closeR (stk0 rest : List w8) (j : Nat) (eof : Bool) : Nat × Nat :=
  if stk0 = [] then (0, j) else goL rest j stk0 1 false eof

theorem ser_num (n : Nat) : ser (.num n) = decN n := by simp [ser]
theorem ser_str (s : List w8) : ser (.str s) = 34#8 :: s ++ [34#8] := by simp [ser]
theorem ser_obj (ms : JMs) : ser (.obj ms) = 123#8 :: serMs ms ++ [125#8] := by simp [ser]
theorem ser_arr (vs : JVs) : ser (.arr vs) = 91#8 :: serVs vs ++ [93#8] := by simp [ser]
theorem serMs_nil : serMs .nil = [] := by simp [serMs]
theorem serMs_cons (k : List w8) (v : JV) (ms : JMs) :
    serMs (.cons k v ms) = 34#8 :: (k ++ 34#8 :: 58#8 :: (ser v ++ serMsT ms)) := by
  simp [serMs]
theorem serMsT_nil : serMsT .nil = [] := by simp [serMsT]
theorem serMsT_cons (k : List w8) (v : JV) (ms : JMs) :
    serMsT (.cons k v ms) = 44#8 :: 34#8 :: (k ++ 34#8 :: 58#8 :: (ser v ++ serMsT ms)) := by
  simp [serMsT]
theorem serVs_nil : serVs .nil = [] := by simp [serVs]
theorem serVs_cons (v : JV) (vs : JVs) : serVs (.cons v vs) = ser v ++ serVsT vs := by
  simp [serVs]
theorem serVsT_nil : serVsT .nil = [] := by simp [serVsT]
theorem serVsT_cons (v : JV) (vs : JVs) : serVsT (.cons v vs) = 44#8 :: (ser v ++ serVsT vs) := by
  simp [serVsT]

/-- A member's key and colon, then what follows. -/
theorem goL_member (k rest : List w8) (hk : ∀ c ∈ k, okB c) (i : Nat) (stk : List w8)
    (eOK eof : Bool) :
    goL (34#8 :: (k ++ 34#8 :: 58#8 :: rest)) i stk 2 eOK eof =
      goL rest (i + k.length + 3) stk 0 false eof := by
  rw [goL_key]
  simp only [strL_full k _ hk]
  simp only [ne_eq, not_true_eq_false, if_false, ite_false]
  have e2 : (k ++ 34#8 :: 58#8 :: rest).drop (i + 1 + k.length + 1 - i - 1) = 58#8 :: rest := by
    rw [show i + 1 + k.length + 1 - i - 1 = k.length + 1 by omega]
    simp [List.drop_append]
  rw [e2, goL_colon]
  congr 1; omega

mutual
theorem full_v (v : JV) (hv : v.ok) (rest : List w8) (i : Nat) (stk : List w8) (eOK eof : Bool)
    (hstk : stk ≠ []) (hd : stk.length + v.depth ≤ maxDepth) (ht : termOK v rest) :
    goL (ser v ++ rest) i stk 0 eOK eof = goL rest (i + (ser v).length) stk 1 false eof := by
  match v with
  | .num n =>
    obtain ⟨c, r, rfl, hc⟩ := ht
    obtain ⟨d, ds, hdn⟩ : ∃ d ds, decN n = d :: ds := by
      cases h : decN n with
      | nil => exact absurd h (decN_ne_nil n)
      | cons d ds => exact ⟨d, ds, rfl⟩
    have hdd : isDig d = true := decN_digits n d (by rw [hdn]; simp)
    obtain ⟨hsp, h1, h2, h3, h34, -⟩ := isDig_ne d hdd
    have hnum := numL_full n c r hc i (eof && stk.isEmpty)
    rw [ser_num, hdn] at *
    simp only [List.cons_append]
    rw [goL_scalar (hs := hsp) (hc1 := h1) (hc2 := h2) (hc3 := h3)]
    simp only [scalarL, h34, hdd, or_true, if_true, if_false, ite_false, ite_true]
    simp only [List.cons_append] at hnum
    rw [hnum]
    simp only [ne_eq, not_true_eq_false, if_false, ite_false, hstk]
    congr 1
    · simp [List.drop_append]
  | .str s =>
    have hs : ∀ c ∈ s, okB c := by simpa [JV.ok] using hv
    rw [ser_str]
    simp only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append]
    rw [goL_scalar (hs := by decide) (hc1 := by decide) (hc2 := by decide) (hc3 := by decide)]
    simp only [scalarL, if_true, ite_true, strL_full s _ hs]
    simp only [ne_eq, not_true_eq_false, if_false, ite_false, hstk]
    have e2 : (s ++ 34#8 :: rest).drop (i + 1 + s.length + 1 - i - 1) = rest := by
      rw [show i + 1 + s.length + 1 - i - 1 = s.length + 1 by omega]
      simp [List.drop_append]
    rw [e2]; congr 1; simp; omega
  | .obj ms =>
    have hms : ms.ok := by simpa [JV.ok] using hv
    have hdep : JV.depth (.obj ms) = ms.depth + 1 := by simp [JV.depth]
    rw [ser_obj]
    simp only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append]
    rw [goL_open (hc := by decide) (hd := by omega)]
    simp only [if_true, ite_true]
    rw [full_ms ms hms rest (i + 1) stk eof (by omega)]
    simp only [closeR, hstk, if_false, ite_false]
    congr 1; simp; omega
  | .arr vs =>
    have hvs : vs.ok := by simpa [JV.ok] using hv
    have hdep : JV.depth (.arr vs) = vs.depth + 1 := by simp [JV.depth]
    rw [ser_arr]
    simp only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append]
    rw [goL_open (hc := by decide) (hd := by omega)]
    simp only [show (91#8 : w8) ≠ 123#8 by decide, if_false, ite_false]
    rw [full_vs vs hvs rest (i + 1) stk eof (by omega)]
    simp only [closeR, hstk, if_false, ite_false]
    congr 1; simp; omega

theorem full_ms (ms : JMs) (hms : ms.ok) (rest : List w8) (i : Nat) (stk0 : List w8) (eof : Bool)
    (hd : stk0.length + 1 + ms.depth ≤ maxDepth) :
    goL (serMs ms ++ 125#8 :: rest) i (123#8 :: stk0) 2 true eof =
      closeR stk0 rest (i + (serMs ms).length + 1) eof := by
  match ms with
  | .nil =>
    rw [serMs_nil]; simp only [List.nil_append, goL_close2, closeR]; simp
  | .cons k v ms' =>
    simp only [JMs.ok] at hms
    simp only [JMs.depth] at hd
    rw [serMs_cons]
    simp only [List.append_assoc, List.cons_append]
    rw [goL_member k _ hms.1, full_v v hms.2.1 _ _ _ _ _ (by simp) (by simp; omega)]
    · rw [full_msT ms' hms.2.2 rest _ stk0 eof (by omega)]
      congr 1; simp; omega
    · cases v <;> simp [termOK]
      cases ms' <;> simp [serMsT] <;> first | exact numEnd_comma | exact numEnd_rb

theorem full_msT (ms : JMs) (hms : ms.ok) (rest : List w8) (i : Nat) (stk0 : List w8) (eof : Bool)
    (hd : stk0.length + 1 + ms.depth ≤ maxDepth) :
    goL (serMsT ms ++ 125#8 :: rest) i (123#8 :: stk0) 1 false eof =
      closeR stk0 rest (i + (serMsT ms).length + 1) eof := by
  match ms with
  | .nil =>
    rw [serMsT_nil]; simp only [List.nil_append]
    rw [goL_close1 (hc := Or.inr ⟨rfl, rfl⟩)]; simp [closeR]
  | .cons k v ms' =>
    simp only [JMs.ok] at hms
    simp only [JMs.depth] at hd
    rw [serMsT_cons]
    simp only [List.cons_append, List.append_assoc]
    rw [goL_comma]
    simp only [if_true, ite_true]
    rw [goL_member k _ hms.1, full_v v hms.2.1 _ _ _ _ _ (by simp) (by simp; omega)]
    · rw [full_msT ms' hms.2.2 rest _ stk0 eof (by omega)]
      congr 1; simp; omega
    · cases v <;> simp [termOK]
      cases ms' <;> simp [serMsT] <;> first | exact numEnd_comma | exact numEnd_rb

theorem full_vs (vs : JVs) (hvs : vs.ok) (rest : List w8) (i : Nat) (stk0 : List w8) (eof : Bool)
    (hd : stk0.length + 1 + vs.depth ≤ maxDepth) :
    goL (serVs vs ++ 93#8 :: rest) i (91#8 :: stk0) 0 true eof =
      closeR stk0 rest (i + (serVs vs).length + 1) eof := by
  match vs with
  | .nil =>
    rw [serVs_nil]; simp only [List.nil_append, goL_close0, closeR]; simp
  | .cons v vs' =>
    simp only [JVs.ok] at hvs
    simp only [JVs.depth] at hd
    rw [serVs_cons]
    simp only [List.append_assoc]
    rw [full_v v hvs.1 _ _ _ _ _ (by simp) (by simp; omega)]
    · rw [full_vsT vs' hvs.2 rest _ stk0 eof (by omega)]
      congr 1; simp; omega
    · cases v <;> simp [termOK]
      cases vs' <;> simp [serVsT] <;> first | exact numEnd_comma | exact numEnd_rs

theorem full_vsT (vs : JVs) (hvs : vs.ok) (rest : List w8) (i : Nat) (stk0 : List w8) (eof : Bool)
    (hd : stk0.length + 1 + vs.depth ≤ maxDepth) :
    goL (serVsT vs ++ 93#8 :: rest) i (91#8 :: stk0) 1 false eof =
      closeR stk0 rest (i + (serVsT vs).length + 1) eof := by
  match vs with
  | .nil =>
    rw [serVsT_nil]; simp only [List.nil_append]
    rw [goL_close1 (hc := Or.inl ⟨rfl, rfl⟩)]; simp [closeR]
  | .cons v vs' =>
    simp only [JVs.ok] at hvs
    simp only [JVs.depth] at hd
    rw [serVsT_cons]
    simp only [List.cons_append, List.append_assoc]
    rw [goL_comma]
    simp only [show (91#8 : w8) ≠ 123#8 by decide, if_false, ite_false]
    rw [full_v v hvs.1 _ _ _ _ _ (by simp) (by simp; omega)]
    · rw [full_vsT vs' hvs.2 rest _ stk0 eof (by omega)]
      congr 1; simp; omega
    · cases v <;> simp [termOK]
      cases vs' <;> simp [serVsT] <;> first | exact numEnd_comma | exact numEnd_rs
end

end VsrJson
