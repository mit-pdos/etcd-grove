/-
The round trip of a member record through the encoding/json model (#24 J2, for #34's bootstrap): the
JSON `json.Marshal(*Member)` writes (`membership.memberJsonM`, the bytes of `memberJson` at a non-nil
peer-URL slice) decodes, by `membership.ccDecode`, into a zero `ConfigChangeContext`, back to the
member with `IsPromote` false (`membership.ccDecode_memberJsonM`), when its name and URLs are plain
(`membership.memberPlain`: `JsonScan.plainEnc` bytes, written as they are).

The general facts it rests on: the scanner (`JsonScan.scanL`) accepts the compact JSON of any object
of plain keys and values (`membership.scanL_jobj`); the JSON of such objects is injective
(`membership.jobj_inj`), so `ccDecode` of the JSON of an object it covers is that object's decoding
(`membership.ccDecode_jobj`). The scanner lemmas follow kaashoek's `dsv-vr`
`Dsverify/.../go_vsr/Proof/jsoncodec/ScanLemmas.lean` and `Inj.lean` (`full_v`, `split_v`,
`split_q`, `decN_inj`), over membership's flat values (`JVal`: no nested objects; booleans and
`null`). Pure.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.JsonDec
public import Net.Proof.models_lab.jsoncodec.Scan.Steps
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Json

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open JsonScan

/-! ## Values, tails -/

/-- Every string of the value is plain. -/
def membership.JVal.ok : membership.JVal → Prop
  | .str s => membership.plainStr s
  | .arr xs => ∀ x ∈ xs, membership.plainStr x
  | _ => True

/-- What may follow a value inside a container: after a number, a byte that ends it. -/
def membership.termOK : membership.JVal → List w8 → Prop
  | .num _, rest => ∃ c r, rest = c :: r ∧ numEnd c
  | _, _ => True

/-- The strings after the first, each after a `,`. -/
def membership.jstrsT : List (List w8) → List w8
  | [] => []
  | x :: xs => 44#8 :: (membership.jquoted x ++ membership.jstrsT xs)

/-- The members after the first, each after a `,`. -/
def membership.jmemT : List (List w8 × membership.JVal) → List w8
  | [] => []
  | (k, v) :: ms => 44#8 :: (membership.jquoted k ++ 58#8 :: (v.json ++ membership.jmemT ms))

theorem membership.jstrs_cons' (x : List w8) (xs : List (List w8)) :
    membership.jstrs (x :: xs) = membership.jquoted x ++ membership.jstrsT xs := by
  cases xs with
  | nil => simp [membership.jstrs, membership.jstrsT]
  | cons y ys =>
    rw [membership.jstrs]
    simp only [membership.jstrsT, List.append_cancel_left_eq, List.cons.injEq, true_and]
    exact membership.jstrs_cons' y ys
    simp

theorem membership.jmembers_cons' (k : List w8) (v : membership.JVal)
    (ms : List (List w8 × membership.JVal)) :
    membership.jmembers ((k, v) :: ms) =
      membership.jquoted k ++ 58#8 :: (v.json ++ membership.jmemT ms) := by
  cases ms with
  | nil => simp [membership.jmembers, membership.jmemT]
  | cons p ms =>
    obtain ⟨k', v'⟩ := p
    rw [membership.jmembers]
    simp only [membership.jmemT, List.append_cancel_left_eq, List.cons.injEq, true_and]
    exact membership.jmembers_cons' k' v' ms
    simp

theorem membership.jmemT_append (a b : List (List w8 × membership.JVal)) :
    membership.jmemT (a ++ b) = membership.jmemT a ++ membership.jmemT b := by
  induction a with
  | nil => rfl
  | cons p a ih => obtain ⟨k, v⟩ := p; simp [membership.jmemT, ih]

/-! ## The scanner on a value -/

/-- The end of a container: done at the top, else after a value in the enclosing one. -/
def membership.closeR (stk0 rest : List w8) (j : Nat) (eof : Bool) : Nat × Nat :=
  if stk0 = [] then (0, j) else goL rest j stk0 1 false eof

theorem membership.str_elem (s rest : List w8) (hs : membership.plainStr s) (i : Nat)
    (stk : List w8) (eOK eof : Bool) (hstk : stk ≠ []) :
    goL (membership.jquoted s ++ rest) i stk 0 eOK eof =
      goL rest (i + s.length + 2) stk 1 false eof := by
  unfold membership.jquoted
  simp only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append]
  rw [goL_scalar (hs := by decide) (hc1 := by decide) (hc2 := by decide) (hc3 := by decide)]
  simp only [scalarL, ite_true, strL_full s _ hs]
  simp only [ne_eq, not_true_eq_false, ite_false, hstk]
  have e2 : (s ++ 34#8 :: rest).drop (i + 1 + s.length + 1 - i - 1) = rest := by
    rw [show i + 1 + s.length + 1 - i - 1 = s.length + 1 by omega]
    simp [List.drop_append]
  rw [e2]; congr 1; omega

theorem membership.arr_tail (xs : List (List w8)) (hxs : ∀ x ∈ xs, membership.plainStr x)
    (rest : List w8) (i : Nat) (stk0 : List w8) (eof : Bool) :
    goL (membership.jstrsT xs ++ 93#8 :: rest) i (91#8 :: stk0) 1 false eof =
      membership.closeR stk0 rest (i + (membership.jstrsT xs).length + 1) eof := by
  induction xs generalizing i with
  | nil =>
    simp only [membership.jstrsT, List.nil_append]
    rw [goL_close1 (hc := Or.inl ⟨rfl, rfl⟩)]; simp [membership.closeR]
  | cons x xs ih =>
    simp only [membership.jstrsT, List.cons_append, List.append_assoc]
    rw [goL_comma]
    simp only [show (91#8 : w8) ≠ 123#8 by decide, ite_false]
    rw [membership.str_elem x _ (hxs x (by simp)) _ _ _ _ (by simp),
      ih (fun y hy => hxs y (by simp [hy]))]
    congr 1; simp [membership.jquoted]; omega

theorem membership.arr_head (xs : List (List w8)) (hxs : ∀ x ∈ xs, membership.plainStr x)
    (rest : List w8) (i : Nat) (stk0 : List w8) (eof : Bool) :
    goL (membership.jstrs xs ++ 93#8 :: rest) i (91#8 :: stk0) 0 true eof =
      membership.closeR stk0 rest (i + (membership.jstrs xs).length + 1) eof := by
  cases xs with
  | nil => simp only [membership.jstrs, List.nil_append, goL_close0, membership.closeR]; simp
  | cons x xs =>
    rw [membership.jstrs_cons']
    simp only [List.append_assoc]
    rw [membership.str_elem x _ (hxs x (by simp)) _ _ _ _ (by simp),
      membership.arr_tail xs (fun y hy => hxs y (by simp [hy]))]
    congr 1; simp [membership.jquoted]; omega

theorem membership.json_true : (membership.JVal.bool true).json = [116#8, 114#8, 117#8, 101#8] := rfl
theorem membership.json_false :
    (membership.JVal.bool false).json = [102#8, 97#8, 108#8, 115#8, 101#8] := rfl
theorem membership.json_null : membership.JVal.null.json = [110#8, 117#8, 108#8, 108#8] := rfl

theorem membership.full_v (v : membership.JVal) (hv : v.ok) (rest : List w8) (i : Nat)
    (stk : List w8) (eOK eof : Bool) (hstk : stk ≠ []) (hd : stk.length < maxDepth)
    (ht : membership.termOK v rest) :
    goL (v.json ++ rest) i stk 0 eOK eof = goL rest (i + v.json.length) stk 1 false eof := by
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
    simp only [membership.JVal.json]
    rw [hdn] at hnum ⊢
    simp only [List.cons_append]
    rw [goL_scalar (hs := hsp) (hc1 := h1) (hc2 := h2) (hc3 := h3)]
    simp only [scalarL, h34, hdd, or_true, ite_true, ite_false, ite_true]
    simp only [List.cons_append] at hnum
    rw [hnum]
    simp only [ne_eq, not_true_eq_false, ite_false, hstk]
    congr 1
    simp [List.drop_append]
  | .str s =>
    simp only [membership.JVal.json]
    rw [membership.str_elem s rest hv i stk eOK eof hstk]
    simp [membership.jquoted]; congr 1
  | .bool true =>
    rw [membership.json_true]
    simp only [List.cons_append, List.nil_append]
    rw [goL_scalar (hs := by decide) (hc1 := by decide) (hc2 := by decide) (hc3 := by decide)]
    simp [scalarL, litL, isDig, hstk]
    rw [show i + 1 + 1 + 1 + 1 - i - 1 = 3 by omega, show i + 1 + 1 + 1 + 1 = i + 4 by omega]; rfl
  | .bool false =>
    rw [membership.json_false]
    simp only [List.cons_append, List.nil_append]
    rw [goL_scalar (hs := by decide) (hc1 := by decide) (hc2 := by decide) (hc3 := by decide)]
    simp [scalarL, litL, isDig, hstk]
    rw [show i + 1 + 1 + 1 + 1 + 1 - i - 1 = 4 by omega, show i + 1 + 1 + 1 + 1 + 1 = i + 5 by omega]; rfl
  | .null =>
    rw [membership.json_null]
    simp only [List.cons_append, List.nil_append]
    rw [goL_scalar (hs := by decide) (hc1 := by decide) (hc2 := by decide) (hc3 := by decide)]
    simp [scalarL, litL, isDig, hstk]
    rw [show i + 1 + 1 + 1 + 1 - i - 1 = 3 by omega, show i + 1 + 1 + 1 + 1 = i + 4 by omega]; rfl
  | .arr xs =>
    simp only [membership.JVal.json, List.cons_append, List.append_assoc, List.singleton_append, List.nil_append]
    rw [goL_open (hc := by decide) (hd := hd)]
    simp only [show (91#8 : w8) ≠ 123#8 by decide, ite_false]
    rw [membership.arr_head xs hv rest (i + 1) stk eof]
    simp only [membership.closeR, hstk, ite_false]
    congr 1; simp; omega

/-- **The scanner on a value at the top**: one whole value, then anything that may follow it. -/
theorem membership.top_v (v : membership.JVal) (hv : v.ok) (rest : List w8) (i : Nat)
    (eOK eof : Bool) (ht : membership.termOK v rest) :
    goL (v.json ++ rest) i [] 0 eOK eof = (0, i + v.json.length) := by
  match v with
  | .num n =>
    obtain ⟨c, r, rfl, hc⟩ := ht
    simp only [membership.JVal.json]; exact goL_num_top n c r hc i eOK eof
  | .str s =>
    simp only [membership.JVal.json, membership.jquoted, List.cons_append, List.append_assoc,
      List.singleton_append, List.nil_append]
    rw [goL_str_top s rest hv i eOK eof]; simp; omega
  | .bool true =>
    rw [membership.json_true]
    simp only [List.cons_append, List.nil_append]
    rw [goL_scalar (hs := by decide) (hc1 := by decide) (hc2 := by decide) (hc3 := by decide)]
    simp [scalarL, litL, isDig]
  | .bool false =>
    rw [membership.json_false]
    simp only [List.cons_append, List.nil_append]
    rw [goL_scalar (hs := by decide) (hc1 := by decide) (hc2 := by decide) (hc3 := by decide)]
    simp [scalarL, litL, isDig]
  | .null =>
    rw [membership.json_null]
    simp only [List.cons_append, List.nil_append]
    rw [goL_scalar (hs := by decide) (hc1 := by decide) (hc2 := by decide) (hc3 := by decide)]
    simp [scalarL, litL, isDig]
  | .arr xs =>
    simp only [membership.JVal.json, List.cons_append, List.append_assoc, List.singleton_append, List.nil_append]
    rw [goL_open (hc := by decide) (hd := by decide)]
    simp only [show (91#8 : w8) ≠ 123#8 by decide, ite_false]
    rw [membership.arr_head xs hv rest (i + 1) [] eof]
    simp only [membership.closeR, ite_true]
    congr 1; simp; omega

/-! ## The scanner on an object -/

/-- Every key and value of the object is plain. -/
def membership.msOk (ms : List (List w8 × membership.JVal)) : Prop :=
  ∀ p ∈ ms, membership.plainStr p.1 ∧ p.2.ok

theorem membership.termOK_memT (v : membership.JVal) (ms : List (List w8 × membership.JVal))
    (rest : List w8) : membership.termOK v (membership.jmemT ms ++ 125#8 :: rest) := by
  cases v <;> simp only [membership.termOK]
  cases ms with
  | nil => exact ⟨_, _, rfl, numEnd_rb⟩
  | cons p ms => obtain ⟨k, v⟩ := p; exact ⟨_, _, rfl, numEnd_comma⟩

theorem membership.goL_member (k rest : List w8) (hk : membership.plainStr k) (i : Nat)
    (stk : List w8) (eOK eof : Bool) :
    goL (membership.jquoted k ++ 58#8 :: rest) i stk 2 eOK eof =
      goL rest (i + k.length + 3) stk 0 false eof := by
  simp only [membership.jquoted, List.cons_append, List.append_assoc, List.singleton_append, List.nil_append]
  rw [goL_key]
  simp only [strL_full k _ hk]
  simp only [ne_eq, not_true_eq_false, ite_false]
  have e2 : (k ++ 34#8 :: 58#8 :: rest).drop (i + 1 + k.length + 1 - i - 1) = 58#8 :: rest := by
    rw [show i + 1 + k.length + 1 - i - 1 = k.length + 1 by omega]
    simp [List.drop_append]
  rw [e2, goL_colon]
  congr 1; omega

theorem membership.mem_tail (ms : List (List w8 × membership.JVal)) (hms : membership.msOk ms)
    (rest : List w8) (i : Nat) (stk0 : List w8) (eof : Bool) (hd : stk0.length + 1 < maxDepth) :
    goL (membership.jmemT ms ++ 125#8 :: rest) i (123#8 :: stk0) 1 false eof =
      membership.closeR stk0 rest (i + (membership.jmemT ms).length + 1) eof := by
  induction ms generalizing i with
  | nil =>
    simp only [membership.jmemT, List.nil_append]
    rw [goL_close1 (hc := Or.inr ⟨rfl, rfl⟩)]; simp [membership.closeR]
  | cons p ms ih =>
    obtain ⟨k, v⟩ := p
    have h0 := hms (k, v) (by simp)
    simp only [membership.jmemT, List.cons_append, List.append_assoc]
    rw [goL_comma]
    simp only [ite_true]
    rw [membership.goL_member k _ h0.1,
      membership.full_v v h0.2 _ _ _ _ _ (by simp) (by simpa using hd)
        (membership.termOK_memT v ms rest),
      ih (fun q hq => hms q (by simp [hq]))]
    congr 1; simp [membership.jquoted]; omega

theorem membership.mem_head (ms : List (List w8 × membership.JVal)) (hms : membership.msOk ms)
    (rest : List w8) (i : Nat) (stk0 : List w8) (eof : Bool) (hd : stk0.length + 1 < maxDepth) :
    goL (membership.jmembers ms ++ 125#8 :: rest) i (123#8 :: stk0) 2 true eof =
      membership.closeR stk0 rest (i + (membership.jmembers ms).length + 1) eof := by
  cases ms with
  | nil => simp only [membership.jmembers, List.nil_append, goL_close2, membership.closeR]; simp
  | cons p ms =>
    obtain ⟨k, v⟩ := p
    have h0 := hms (k, v) (by simp)
    rw [membership.jmembers_cons']
    simp only [List.append_assoc, List.cons_append]
    rw [membership.goL_member k _ h0.1,
      membership.full_v v h0.2 _ _ _ _ _ (by simp) (by simpa using hd)
        (membership.termOK_memT v ms rest),
      membership.mem_tail ms (fun q hq => hms q (by simp [hq])) rest _ stk0 eof hd]
    congr 1; simp [membership.jquoted]; omega

/-- **The scanner accepts the JSON of an object of plain keys and values**, as one value. -/
theorem membership.scanL_jobj (ms : List (List w8 × membership.JVal)) (hms : membership.msOk ms) :
    scanL (membership.jobj ms) true = (0, (membership.jobj ms).length) := by
  unfold scanL membership.jobj
  rw [goL_open (hc := by decide) (hd := by decide)]
  simp only [ite_true]
  rw [membership.mem_head ms hms [] 1 [] true (by decide)]
  simp [membership.closeR]; omega

/-! ## Injectivity -/

theorem membership.decN_length (n : Nat) :
    (n < 10 → (decN n).length = 1) ∧ (10 ≤ n → 2 ≤ (decN n).length) := by
  constructor
  · intro h; rw [decN_eq]; simp [h]
  · intro h; rw [decN_eq]; simp [show ¬ n < 10 by omega]
    have := decN_ne_nil (n / 10)
    cases hh : decN (n / 10) with
    | nil => exact absurd hh this
    | cons _ _ => simp

theorem membership.ofNat48_inj (a b : Nat) (ha : a < 10) (hb : b < 10)
    (h : BitVec.ofNat 8 (48 + a) = BitVec.ofNat 8 (48 + b)) : a = b := by
  have := congrArg BitVec.toNat h
  simp at this
  omega

theorem membership.decN_inj (a b : Nat) (h : decN a = decN b) : a = b := by
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    have la := membership.decN_length a
    have lb := membership.decN_length b
    by_cases ha : a < 10 <;> by_cases hb : b < 10
    · rw [decN_eq a, decN_eq b] at h; simp [ha, hb] at h
      exact membership.ofNat48_inj a b ha hb h
    · have := la.1 ha; have := lb.2 (by omega); rw [h] at *; omega
    · have := la.2 (by omega); have := lb.1 hb; rw [h] at *; omega
    · rw [decN_eq a, decN_eq b] at h; simp only [ha, hb, ite_false] at h
      obtain ⟨h1, h2⟩ := List.append_inj' h rfl
      have e1 := ih (a / 10) (by omega) (b / 10) h1
      simp at h2
      have e2 := membership.ofNat48_inj (a % 10) (b % 10) (by omega) (by omega) (by simpa using h2)
      omega

theorem membership.split_q (k k' Z Z' : List w8) (hk : membership.plainStr k)
    (hk' : membership.plainStr k') (h : k ++ 34#8 :: Z = k' ++ 34#8 :: Z') : k = k' ∧ Z = Z' := by
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

theorem membership.split_v (v w : membership.JVal) (X X' : List w8) (hv : v.ok) (hw : w.ok)
    (tv : membership.termOK v X) (tw : membership.termOK w X') (h : v.json ++ X = w.json ++ X') :
    v.json = w.json ∧ X = X' := by
  have e1 := membership.top_v v hv X 0 false true tv
  have e2 := membership.top_v w hw X' 0 false true tw
  rw [h, e2] at e1
  simp at e1
  exact List.append_inj h e1.symm

theorem membership.jstrsT_inj (xs ys : List (List w8)) (hx : ∀ x ∈ xs, membership.plainStr x)
    (hy : ∀ y ∈ ys, membership.plainStr y) (h : membership.jstrsT xs = membership.jstrsT ys) :
    xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons _ _ => simp [membership.jstrsT] at h
  | cons x xs ih => cases ys with
    | nil => simp [membership.jstrsT] at h
    | cons y ys =>
      simp only [membership.jstrsT, membership.jquoted, List.cons.injEq, true_and,
        List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] at h
      obtain ⟨rfl, h2⟩ := membership.split_q _ _ _ _ (hx x (by simp)) (hy y (by simp)) h
      rw [ih ys (fun z hz => hx z (by simp [hz])) (fun z hz => hy z (by simp [hz])) h2]

theorem membership.jstrs_inj (xs ys : List (List w8)) (hx : ∀ x ∈ xs, membership.plainStr x)
    (hy : ∀ y ∈ ys, membership.plainStr y) (h : membership.jstrs xs = membership.jstrs ys) :
    xs = ys := by
  cases xs with
  | nil => cases ys with
    | nil => rfl
    | cons y ys => rw [membership.jstrs_cons'] at h; simp [membership.jstrs, membership.jquoted] at h
  | cons x xs => cases ys with
    | nil => rw [membership.jstrs_cons'] at h; simp [membership.jstrs, membership.jquoted] at h
    | cons y ys =>
      have : membership.jstrsT (x :: xs) = membership.jstrsT (y :: ys) := by
        simp only [membership.jstrsT]; rw [← membership.jstrs_cons', ← membership.jstrs_cons', h]
      exact membership.jstrsT_inj _ _ hx hy this

theorem membership.json_inj (v w : membership.JVal) (hv : v.ok) (hw : w.ok)
    (h : v.json = w.json) : v = w := by
  have hd : ∀ n, ∃ c r, decN n = c :: r ∧ isDig c = true := by
    intro n
    cases e : decN n with
    | nil => exact absurd e (decN_ne_nil n)
    | cons c r => exact ⟨c, r, rfl, decN_digits n c (by rw [e]; simp)⟩
  cases v with
  | num a =>
    cases w with
    | num b => simp only [membership.JVal.json] at h; rw [membership.decN_inj a b h]
    | _ =>
      exfalso
      obtain ⟨c, r, hc, hdc⟩ := hd a
      simp only [membership.JVal.json, hc] at h
      first
        | (cases ‹Bool› <;> simp [membership.JVal.json] at h <;> (obtain ⟨rfl, -⟩ := h; revert hdc; decide))
        | (simp [membership.jquoted] at h; obtain ⟨rfl, -⟩ := h; revert hdc; decide)
        | (simp at h; obtain ⟨rfl, -⟩ := h; revert hdc; decide)
  | str a =>
    cases w with
    | str b => simp [membership.JVal.json, membership.jquoted] at h; rw [h]
    | num b =>
      exfalso; obtain ⟨c, r, hc, hdc⟩ := hd b
      simp [membership.JVal.json, membership.jquoted, hc] at h; obtain ⟨rfl, -⟩ := h; revert hdc; decide
    | bool b => cases b <;> simp [membership.JVal.json, membership.jquoted] at h
    | _ => simp [membership.JVal.json, membership.jquoted] at h
  | bool a =>
    cases w with
    | num b =>
      exfalso; obtain ⟨c, r, hc, hdc⟩ := hd b
      cases a <;> simp [membership.JVal.json, hc] at h <;> (obtain ⟨rfl, -⟩ := h; revert hdc; decide)
    | bool b => cases a <;> cases b <;> simp [membership.JVal.json] at h ⊢
    | _ => cases a <;> simp [membership.JVal.json, membership.jquoted] at h
  | null =>
    cases w with
    | num b =>
      exfalso; obtain ⟨c, r, hc, hdc⟩ := hd b
      simp [membership.JVal.json, hc] at h; obtain ⟨rfl, -⟩ := h; revert hdc; decide
    | bool b => cases b <;> simp [membership.JVal.json] at h
    | null => rfl
    | _ => simp [membership.JVal.json, membership.jquoted] at h
  | arr a =>
    cases w with
    | arr b =>
      simp [membership.JVal.json] at h
      rw [membership.jstrs_inj a b hv hw h]
    | num b =>
      exfalso; obtain ⟨c, r, hc, hdc⟩ := hd b
      simp [membership.JVal.json, hc] at h; obtain ⟨rfl, -⟩ := h; revert hdc; decide
    | bool b => cases b <;> simp [membership.JVal.json] at h
    | _ => simp [membership.JVal.json, membership.jquoted] at h

theorem membership.jmemT_inj (a b : List (List w8 × membership.JVal)) (ha : membership.msOk a)
    (hb : membership.msOk b) (h : membership.jmemT a ++ [125#8] = membership.jmemT b ++ [125#8]) :
    a = b := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons p b => obtain ⟨k, v⟩ := p; simp [membership.jmemT] at h
  | cons p a ih => cases b with
    | nil => obtain ⟨k, v⟩ := p; simp [membership.jmemT] at h
    | cons q b =>
      obtain ⟨k, v⟩ := p
      obtain ⟨k', v'⟩ := q
      have h0 := ha (k, v) (by simp)
      have h0' := hb (k', v') (by simp)
      simp only [membership.jmemT, membership.jquoted, List.cons_append, List.append_assoc,
        List.singleton_append, List.nil_append, List.cons.injEq, true_and] at h
      obtain ⟨rfl, h3⟩ := membership.split_q _ _ _ _ h0.1 h0'.1 h
      have h' : v.json ++ (membership.jmemT a ++ [125#8]) =
          v'.json ++ (membership.jmemT b ++ [125#8]) := by simpa using h3
      obtain ⟨h1, h2⟩ := membership.split_v v v' _ _ h0.2 h0'.2
        (membership.termOK_memT v a []) (membership.termOK_memT v' b []) h'
      rw [membership.json_inj v v' h0.2 h0'.2 h1,
        ih b (fun r hr => ha r (by simp [hr])) (fun r hr => hb r (by simp [hr])) h2]

/-- **The JSON of objects of plain keys and values is injective.** -/
theorem membership.jobj_inj (a b : List (List w8 × membership.JVal)) (ha : membership.msOk a)
    (hb : membership.msOk b) (h : membership.jobj a = membership.jobj b) : a = b := by
  unfold membership.jobj at h
  simp only [List.cons.injEq, true_and] at h
  cases a with
  | nil => cases b with
    | nil => rfl
    | cons q b =>
      obtain ⟨k', v'⟩ := q
      rw [membership.jmembers_cons'] at h; simp [membership.jmembers, membership.jquoted] at h
  | cons p a => cases b with
    | nil =>
      obtain ⟨k, v⟩ := p
      rw [membership.jmembers_cons'] at h; simp [membership.jmembers, membership.jquoted] at h
    | cons q b =>
      obtain ⟨k, v⟩ := p
      obtain ⟨k', v'⟩ := q
      apply membership.jmemT_inj _ _ ha hb
      simp only [membership.jmemT, List.cons_append]
      rw [← membership.jmembers_cons', ← membership.jmembers_cons', h]

/-! ## `ccDecode` of an object's JSON -/

theorem membership.ccSet_ok {k : List w8} {v : membership.JVal} {r r' : membership.CcM}
    (h : membership.ccSet k v r = some r') : membership.plainStr k ∧ v.ok := by
  refine ⟨membership.ccSet_key_plain h, ?_⟩
  unfold membership.ccSet at h
  cases v with
  | str s =>
    by_cases h4 : k = go!"name"
    · subst h4
      simp only [show (go!"name" : List w8) ≠ go!"id" by decide,
        show (go!"name" : List w8) ≠ go!"peerURLs" by decide,
        show (go!"name" : List w8) ≠ go!"isLearner" by decide, ite_false, ite_true] at h
      simp only [membership.JVal.ok]
      by_cases hp : membership.plainStr s
      · exact hp
      · rw [if_neg hp] at h; cases h
    · simp only [membership.strsOf, h4, ite_false, Option.map_none] at h
      repeat (first | (split at h <;> try cases h) | cases h)
  | arr xs =>
    simp only [membership.JVal.ok]
    by_cases hp : ∀ x ∈ xs, membership.plainStr x
    · exact hp
    · simp only [membership.strsOf] at h
      rw [if_neg hp] at h
      repeat (first | (split at h <;> try cases h) | cases h)
  | _ => simp [membership.JVal.ok]

theorem membership.ccFold_ok (ms : List (List w8 × membership.JVal)) (r r' : membership.CcM)
    (h : membership.ccFold ms r = some r') : membership.msOk ms := by
  induction ms generalizing r with
  | nil => intro p hp; cases hp
  | cons p ms ih =>
    obtain ⟨k, v⟩ := p
    simp only [membership.ccFold] at h
    cases hs : membership.ccSet k v r with
    | none => rw [hs] at h; cases h
    | some r1 =>
      rw [hs] at h
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact membership.ccSet_ok hs
      · exact ih r1 h q hq

theorem membership.ccObjOk_msOk {ms : List (List w8 × membership.JVal)}
    (h : membership.ccObjOk ms) : membership.msOk ms := by
  obtain ⟨-, hs⟩ := h
  cases hf : membership.ccFold ms membership.ccZero with
  | none => rw [hf] at hs; cases hs
  | some r => exact membership.ccFold_ok ms _ r hf

/-- **`ccDecode` of the JSON of an object it covers is that object's decoding.** -/
theorem membership.ccDecode_jobj (ms : List (List w8 × membership.JVal))
    (h : membership.ccObjOk ms) :
    membership.ccDecode (membership.jobj ms) = membership.ccFold ms membership.ccZero := by
  have hok := membership.ccObjOk_msOk h
  have hh : JsonScan.scanL (membership.jobj ms) true = (0, (membership.jobj ms).length) ∧
      ∃ ms', membership.ccObjOk ms' ∧ membership.jobj ms' = membership.jobj ms :=
    ⟨membership.scanL_jobj ms hok, ms, h, rfl⟩
  unfold membership.ccDecode
  rw [dif_pos hh]
  have hc := Classical.choose_spec hh.2
  rw [membership.jobj_inj _ _ (membership.ccObjOk_msOk hc.1) hok hc.2]

/-! ## A member's JSON -/

/-- The name and every URL of the member are plain (`JsonScan.plainEnc` bytes, which the encoder
writes as they are). -/
def membership.memberPlain (m : apply.MemberM) : Prop :=
  (∀ c ∈ m.name, plainEnc c) ∧ (∀ u ∈ m.peerURLs, ∀ c ∈ u, plainEnc c) ∧
    (∀ u ∈ m.clientURLs, ∀ c ∈ u, plainEnc c)

/-- The members of `json.Marshal(*Member)`'s object, at a non-nil peer-URL slice: `id`,
`peerURLs`, `isLearner` if set, `name` if not empty, `clientURLs` if any. -/
def membership.memberMs (m : apply.MemberM) : List (List w8 × membership.JVal) :=
  [(go!"id", .num (uint.nat m.id)), (go!"peerURLs", .arr m.peerURLs)] ++
    (if m.isLearner then [(go!"isLearner", .bool true)] else []) ++
    (if m.name = [] then [] else [(go!"name", .str m.name)]) ++
    (if m.clientURLs = [] then [] else [(go!"clientURLs", .arr m.clientURLs)])

/-- **`json.Marshal(*Member)` of a member record** whose peer-URL slice is not nil (and whose
client-URL slice is not nil when it holds some): `memberJson` of a value with these fields
(`membership.memberJson_eq_M`). -/
def membership.memberJsonM (m : apply.MemberM) : List w8 := membership.jobj (membership.memberMs m)

theorem membership.plainEnc_okB {c : w8} (h : plainEnc c) : okB c := by
  obtain ⟨h1, h2, h3, h4, -⟩ := h
  refine ⟨h1, h2, ?_, ?_⟩
  · intro e; subst e; exact h3 rfl
  · intro e; subst e; exact h4 rfl

theorem membership.ccFold_append (a b : List (List w8 × membership.JVal)) (r : membership.CcM) :
    membership.ccFold (a ++ b) r = (membership.ccFold a r).bind (membership.ccFold b) := by
  induction a generalizing r with
  | nil => rfl
  | cons p a ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.cons_append, membership.ccFold]
    cases membership.ccSet k v r with
    | none => rfl
    | some r1 => simp only [Option.bind_some]; exact ih r1

theorem membership.ccFold_memberMs (m : apply.MemberM) (h : membership.memberPlain m) :
    membership.ccFold (membership.memberMs m) membership.ccZero = some ⟨m, false⟩ := by
  obtain ⟨hn, hp, hc⟩ := h
  have pn : membership.plainStr m.name := fun c hc' => membership.plainEnc_okB (hn c hc')
  have pp : ∀ x ∈ m.peerURLs, membership.plainStr x :=
    fun x hx c hc' => membership.plainEnc_okB (hp x hx c hc')
  have pc : ∀ x ∈ m.clientURLs, membership.plainStr x :=
    fun x hx c hc' => membership.plainEnc_okB (hc x hx c hc')
  have hid : uint.nat m.id < 2 ^ 64 := by word
  have hid2 : W64 ((uint.nat m.id : Nat) : Int) = m.id := by word
  obtain ⟨id, ps, il, nm, cs⟩ := m
  simp only at pn pp pc hid hid2
  unfold membership.memberMs
  simp only [membership.ccFold_append]
  simp only [membership.ccFold, membership.ccSet, ite_true, hid, hid2, membership.strsOf,
    Option.map_some, Option.bind_some]
  rw [if_pos pp]
  simp only [Option.map_some, Option.bind_some]
  cases il <;> by_cases hnm : nm = [] <;> by_cases hcs : cs = [] <;>
    simp [hnm, hcs, membership.ccFold, membership.ccSet, membership.strsOf, membership.ccZero,
      if_pos pn, if_pos pc]

theorem membership.memberMs_ccObjOk (m : apply.MemberM) (h : membership.memberPlain m) :
    membership.ccObjOk (membership.memberMs m) := by
  refine ⟨?_, by rw [membership.ccFold_memberMs m h]; rfl⟩
  unfold membership.memberMs
  cases m.isLearner <;> by_cases hnm : m.name = [] <;> by_cases hcs : m.clientURLs = [] <;>
    simp only [hnm, hcs, ite_true, ite_false, Bool.false_eq_true, List.nil_append, List.append_nil,
      List.cons_append, List.map_cons, List.map_nil] <;> decide

/-- **The round trip**: `json.Unmarshal` of `json.Marshal(*Member)` into a zero
`ConfigChangeContext` gives back the member, `IsPromote` false, when its strings are plain. -/
theorem membership.ccDecode_memberJsonM (m : apply.MemberM) (h : membership.memberPlain m) :
    membership.ccDecode (membership.memberJsonM m) = some ⟨m, false⟩ := by
  unfold membership.memberJsonM
  rw [membership.ccDecode_jobj _ (membership.memberMs_ccObjOk m h), membership.ccFold_memberMs m h]

theorem membership.ccContextOf_memberJsonM (m : apply.MemberM) (h : membership.memberPlain m) :
    membership.ccContextOf (membership.memberJsonM m) = some (m.id, false) := by
  unfold membership.ccContextOf; rw [membership.ccDecode_memberJsonM m h]; rfl

theorem membership.ccMemberOf_memberJsonM (m : apply.MemberM) (h : membership.memberPlain m) :
    membership.ccMemberOf (membership.memberJsonM m) = m := by
  unfold membership.ccMemberOf; rw [membership.ccDecode_memberJsonM m h]; rfl

/-! ## The encoder's bytes -/

theorem membership.jsonStrs_plain (xs : List GoString) (h : ∀ u ∈ xs, ∀ c ∈ u, plainEnc c) :
    membership.jsonStrs xs = membership.jstrs xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [membership.jsonStrs_cons, membership.jstrs_cons,
      models_lab.jsoncodec.jsonQuote_plain x (h x (by simp)), ih (fun u hu => h u (by simp [hu]))]
    simp [membership.jquoted]

theorem membership.jsonStrSlice_plain (xs : List GoString) (h : ∀ u ∈ xs, ∀ c ∈ u, plainEnc c) :
    membership.jsonStrSlice false xs = (membership.JVal.arr xs).json := by
  simp [membership.jsonStrSlice, membership.JVal.json, membership.jsonStrs_plain xs h]

/-- **`memberJsonM` is the encoder's bytes** (`json.Marshal(*Member)`, `memberJson`) of a member
value whose fields are `m`'s, at a non-nil peer-URL slice (and a non-nil client-URL slice when it
holds some). -/
theorem membership.memberJson_eq_M [GooseExts]
    (v : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member) (ps cs : List GoString)
    (hp : v.RaftAttributes'.PeerURLs' ≠ slice.nil) (hc : cs ≠ [] → v.Attributes'.ClientURLs' ≠ slice.nil)
    (h : membership.memberPlain ⟨v.ID', ps, v.RaftAttributes'.IsLearner', v.Attributes'.Name', cs⟩) :
    membership.memberJson v ps cs =
      membership.memberJsonM ⟨v.ID', ps, v.RaftAttributes'.IsLearner', v.Attributes'.Name', cs⟩ := by
  obtain ⟨hn, hps, hcs⟩ := h
  simp only at hn hps hcs
  have hq := models_lab.jsoncodec.jsonQuote_plain _ hn
  unfold membership.memberJson membership.memberFieldsJson membership.memberJsonM membership.jobj
    membership.memberMs
  simp only [decide_eq_false hp, membership.jsonStrSlice_plain ps hps,
    models_lab.jsoncodec.decU64_eq_decN]
  by_cases hcs0 : cs = []
  · subst hcs0
    rcases hb : v.RaftAttributes'.IsLearner' with _ | _ <;>
      by_cases hnm : v.Attributes'.Name' = [] <;>
      simp [hnm, hq, membership.jmembers, membership.jquoted, membership.JVal.json]
  · rw [decide_eq_false (hc hcs0), membership.jsonStrSlice_plain cs hcs]
    rcases hb : v.RaftAttributes'.IsLearner' with _ | _ <;>
      by_cases hnm : v.Attributes'.Name' = [] <;>
      simp [hnm, hcs0, hq, membership.jmembers, membership.jquoted, membership.JVal.json]

end EtcdGrove
end Perennial
