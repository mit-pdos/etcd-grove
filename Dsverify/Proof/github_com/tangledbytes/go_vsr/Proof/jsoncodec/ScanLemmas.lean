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

end VsrJson

namespace VsrJson

open JsonScan
open Perennial

/-- What may follow a value inside a container: after a number, a byte that ends it. -/
def termOK : JV → List w8 → Prop
  | .num _, rest => ∃ c r, rest = c :: r ∧ numEnd c
  | _, _ => True

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
