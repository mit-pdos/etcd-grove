/-
# kvnet's addresses, pure (2026-11-21)

The pure models of `examples/raft/kvnet/addrs.go`, which the specs of its functions are stated in,
and their laws:

* `splitAddrs s` (`SplitAddrs`): `s` split at every comma, the net extension's `splitBy 44`;
  `joinAddrs l` (`JoinAddrs`): the addresses joined by commas. `splitAddrs_joinAddrs`: splitting
  gives back a nonempty list of comma-free addresses.
* `decimalM s m` (`decimal`): the value of `s` as a canonical decimal numeral of at most five
  digits, at most `m`; `decimalM_iff`: for `m = 65535` it is the net extension's `decNat`, bounded.
* `scanGo` (`AddrOk`'s first loop: the address's pieces between its three dots and one colon, in
  that order) and `goAddrOk a` (what `AddrOk` computes); `goAddrOk_eq`: it is the net extension's
  `addrOk a` (`GooseLang/Ext/Net/Impl.lean`), the net extension's condition on an address.
* `validAddrs`, `validCluster` (`ValidAddrs`, `ValidCluster`) and `runNodeOk` (`RunNode`'s check, with
  the id and the directory's length).
-/
module

public import GooseLang.Ext.Net.Deploy

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove.raft_kvnet

open Net

/-! ## Splitting and joining -/

/-- `SplitAddrs`: `s` split at every comma. -/
def splitAddrs (s : GoString) : List GoString := splitBy 44 s []

/-- `JoinAddrs`: the addresses joined by commas. -/
def joinAddrs (l : List GoString) : GoString := List.intercalate [(44 : w8)] l

/-- (2026-11-22) **`M` maps replica `i` (ids from `1`) to the `i`-th address of `l`, and nothing else**:
`RunNode`'s address map. -/
def addrMapOk (l : List GoString) (M : GMap w64 GoString) : Prop :=
  ∀ i : w64, M !! i = if 1 ≤ uint.nat i then l[uint.nat i - 1]? else none

theorem w8_toNat_eq_iff (c d : w8) : c.toNat = d.toNat ↔ c = d := BitVec.toNat_inj

/-- Splitting a piece free of the separator moves it into the current piece. -/
theorem splitBy_append_free (sep : w8) : ∀ (x y cur : GoString), sep ∉ x →
    splitBy sep (x ++ y) cur = splitBy sep y (x.reverse ++ cur)
  | [], y, cur, _ => by simp
  | c :: x, y, cur, h => by
    have hc : c ≠ sep := fun e => h (e ▸ List.mem_cons_self)
    have hx : sep ∉ x := fun m => h (List.mem_cons_of_mem _ m)
    rw [List.cons_append, splitBy.eq_2, if_neg (fun e => hc ((w8_toNat_eq_iff _ _).mp e)),
      splitBy_append_free sep x y (c :: cur) hx]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem splitBy_free (sep : w8) (x : GoString) (h : sep ∉ x) : splitBy sep x [] = [x] := by
  have := splitBy_append_free sep x [] [] h
  simp only [List.append_nil] at this
  rw [this]; simp [splitBy]

theorem splitBy_free_sep (sep : w8) (x y : GoString) (h : sep ∉ x) :
    splitBy sep (x ++ sep :: y) [] = x :: splitBy sep y [] := by
  rw [splitBy_append_free sep x (sep :: y) [] h, splitBy.eq_2, if_pos rfl]
  simp only [List.append_nil, List.reverse_reverse]

theorem splitBy_intercalate (sep : w8) : ∀ (l : List GoString), l ≠ [] → (∀ x ∈ l, sep ∉ x) →
    splitBy sep (List.intercalate [sep] l) [] = l
  | [], h, _ => (h rfl).elim
  | [x], _, hf => by
    simp only [List.intercalate_singleton]
    exact splitBy_free sep x (hf x List.mem_cons_self)
  | x :: y :: r, _, hf => by
    rw [List.intercalate_cons_cons, List.append_assoc, List.singleton_append,
      splitBy_free_sep sep x _ (hf x List.mem_cons_self),
      splitBy_intercalate sep (y :: r) (List.cons_ne_nil _ _)
        (fun z hz => hf z (List.mem_cons_of_mem _ hz))]

/-- What `splitBy` returns: nonempty pieces free of the separator, which give back the string. -/
theorem splitBy_shape (sep : w8) : ∀ (s cur : GoString), sep ∉ cur →
    splitBy sep s cur ≠ [] ∧ cur.reverse ++ s = List.intercalate [sep] (splitBy sep s cur) ∧
      ∀ x ∈ splitBy sep s cur, sep ∉ x
  | [], cur, h => by
    simp only [splitBy, ne_eq, reduceCtorEq, not_false_eq_true, List.append_nil,
      List.intercalate_singleton, List.mem_cons, List.not_mem_nil, or_false, forall_eq, true_and]
    exact fun m => h (List.mem_reverse.mp m)
  | c :: s, cur, h => by
    unfold splitBy
    split
    · rename_i hc
      have hc' : c = sep := (w8_toNat_eq_iff _ _).mp hc
      subst hc'
      obtain ⟨h1, h2, h3⟩ := splitBy_shape c s [] (List.not_mem_nil)
      refine ⟨List.cons_ne_nil _ _, ?_, ?_⟩
      · simp only [List.reverse_nil, List.nil_append] at h2
        obtain ⟨y, r, hyr⟩ := List.exists_cons_of_ne_nil h1
        rw [hyr] at h2 ⊢
        rw [List.intercalate_cons_cons, ← h2]
        simp
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact fun m => h (List.mem_reverse.mp m)
        · exact h3 x hx
    · rename_i hc
      have hc' : c ≠ sep := fun e => hc ((w8_toNat_eq_iff _ _).mpr e)
      have hcur : sep ∉ c :: cur := by
        intro m
        rcases List.mem_cons.mp m with e | m
        · exact hc' e.symm
        · exact h m
      obtain ⟨h1, h2, h3⟩ := splitBy_shape sep s (c :: cur) hcur
      refine ⟨h1, ?_, h3⟩
      rw [← h2]; simp

theorem splitBy_shape0 (sep : w8) (s : GoString) :
    s = List.intercalate [sep] (splitBy sep s []) ∧ ∀ x ∈ splitBy sep s [], sep ∉ x := by
  obtain ⟨-, h2, h3⟩ := splitBy_shape sep s [] List.not_mem_nil
  exact ⟨by simpa using h2, h3⟩

/-- `SplitAddrs` reads back what `JoinAddrs` wrote, for a nonempty list of comma-free addresses. -/
theorem splitAddrs_joinAddrs (l : List GoString) (hne : l ≠ []) (hf : ∀ a ∈ l, (44 : w8) ∉ a) :
    splitAddrs (joinAddrs l) = l :=
  splitBy_intercalate 44 l hne hf

/-- `JoinAddrs`' loop, one more address. -/
theorem intercalate_snoc (sep : List w8) (l : List GoString) (x : GoString) :
    List.intercalate sep (l ++ [x]) = (if l = [] then x else List.intercalate sep l ++ sep ++ x) := by
  induction l with
  | nil => simp
  | cons y r ih =>
    simp only [List.cons_append, reduceCtorEq, ↓reduceIte]
    cases r with
    | nil => simp [List.intercalate_cons_cons]
    | cons z r' =>
      rw [List.cons_append, List.intercalate_cons_cons, ← List.cons_append, ih]
      simp [List.intercalate_cons_cons, List.append_assoc]

/-! ## Decimal numerals -/

/-- `decimal(s, max)`: the value of `s` as a canonical decimal numeral (digits, at least one and
at most five, no leading zero), if it is at most `m`. -/
def decimalM (s : GoString) (m : Nat) : Option Nat :=
  if s.length = 0 ∨ 5 < s.length ∨ (1 < s.length ∧ s.head? = some (48 : w8)) then none
  else match digitsVal s 0 with
    | some n => if n ≤ m then some n else none
    | none => none

theorem digitsVal_append : ∀ (t r : GoString) (acc : Nat),
    digitsVal (t ++ r) acc = (digitsVal t acc).bind (digitsVal r ·)
  | [], r, acc => by simp [digitsVal]
  | c :: t, r, acc => by
    rw [List.cons_append]
    simp only [digitsVal]
    split
    · exact digitsVal_append t r _
    · rfl

theorem digitsVal_snoc (t : GoString) (c : w8) (acc v : Nat) (h : digitsVal t acc = some v)
    (hc : isDigit c = true) : digitsVal (t ++ [c]) acc = some (v * 10 + (c.toNat - 48)) := by
  rw [digitsVal_append, h]; simp [digitsVal, hc]

theorem digitsVal_bad (t r : GoString) (c : w8) (acc : Nat) (hc : isDigit c = false) :
    digitsVal (t ++ c :: r) acc = none := by
  rw [digitsVal_append]
  cases digitsVal t acc with
  | none => rfl
  | some v => simp [digitsVal, hc]

theorem decimalM_guard (s : GoString) (m : Nat)
    (h : s.length = 0 ∨ 5 < s.length ∨ (1 < s.length ∧ s.head? = some (48 : w8))) :
    decimalM s m = none := by
  unfold decimalM; rw [if_pos h]

theorem decimalM_ok (s : GoString) (m : Nat)
    (h : ¬(s.length = 0 ∨ 5 < s.length ∨ (1 < s.length ∧ s.head? = some (48 : w8)))) :
    decimalM s m = match digitsVal s 0 with
      | some n => if n ≤ m then some n else none
      | none => none := by
  unfold decimalM; rw [if_neg h]

theorem isDigit_false_of {d : w8} (h : d.toNat < 48 ∨ 57 < d.toNat) : isDigit d = false := by
  unfold isDigit
  rcases h with h | h <;> simp <;> omega

theorem isDigit_true_of {d : w8} (h1 : 48 ≤ d.toNat) (h2 : d.toNat ≤ 57) : isDigit d = true := by
  unfold isDigit; simp; omega

theorem list_split_at (s : List w8) (i : Nat) (d : w8) (hd : s[i]? = some d) :
    s = s.take i ++ d :: s.drop (i + 1) := by
  have hil : i < s.length := (List.getElem?_eq_some_iff.mp hd).1
  have h1 : s[i] = d := by rw [List.getElem?_eq_getElem hil] at hd; exact Option.some.inj hd
  calc s = s.take i ++ s.drop i := (List.take_append_drop i s).symm
    _ = _ := by rw [List.drop_eq_getElem_cons hil, h1]

theorem take_succ_gs (s : List GoString) (i : Nat) (d : GoString) (hd : s[i]? = some d) :
    s.take (i + 1) = s.take i ++ [d] := by
  rw [List.take_add_one, hd]; rfl

theorem take_succ_of (s : List w8) (i : Nat) (d : w8) (hd : s[i]? = some d) :
    s.take (i + 1) = s.take i ++ [d] := by
  rw [List.take_add_one, hd]; rfl

theorem digitsVal_digits : ∀ (s : GoString) (acc n : Nat), digitsVal s acc = some n →
    ∀ c ∈ s, isDigit c = true
  | [], _, _, _ => by simp
  | c :: s, acc, n, h => by
    unfold digitsVal at h
    split at h
    · rename_i hc
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hc
      · exact digitsVal_digits s _ n h d hd
    · cases h

theorem decNat_digits {s : GoString} {n : Nat} (h : decNat s = some n) : ∀ c ∈ s, isDigit c = true := by
  match s, h with
  | [], h => simp [decNat] at h
  | [c], h => exact digitsVal_digits [c] 0 n h
  | c :: d :: t, h =>
    simp only [decNat] at h
    split at h
    · cases h
    · exact digitsVal_digits _ 0 n h

theorem isDigit_ne {c : w8} (h : isDigit c = true) (d : w8) (hd : isDigit d = false) : d ∉ [c] := by
  intro m; rw [List.mem_singleton.mp m] at hd; rw [h] at hd; cases hd

theorem digits_free {s : GoString} (h : ∀ c ∈ s, isDigit c = true) (d : w8) (hd : isDigit d = false) :
    d ∉ s := fun m => by rw [h d m] at hd; cases hd

theorem decimalM_iff (s : GoString) (m v : Nat) (hm : m < 10 ^ 5) :
    decimalM s m = some v ↔ decNat s = some v ∧ v ≤ m := by
  unfold decimalM
  constructor
  · intro h
    split at h
    · cases h
    · rename_i hs
      split at h
      · rename_i n hn
        split at h
        · rename_i hnm
          simp only [Option.some.injEq] at h
          subst h
          refine ⟨?_, hnm⟩
          match s, hs, hn with
          | [], hs, _ => simp at hs
          | [c], _, hn => exact hn
          | c :: d :: t, hs, hn =>
            simp only [decNat]
            rw [if_neg]
            · exact hn
            · intro e
              apply hs
              right; right
              refine ⟨by simp, ?_⟩
              simp only [List.head?_cons, Option.some.injEq]
              exact (w8_toNat_eq_iff _ _).mp (by rw [e]; rfl)
        · cases h
      · cases h
  · rintro ⟨h, hv⟩
    have hlen := decNat_len (k := 5) h (by omega)
    rw [if_neg]
    · have hd : digitsVal s 0 = some v := by
        match s, h with
        | [], h => simp [decNat] at h
        | [c], h => exact h
        | c :: d :: t, h =>
          simp only [decNat] at h
          split at h
          · cases h
          · exact h
      rw [hd]; simp [hv]
    · intro hc
      rcases hc with h0 | h5 | ⟨h1, hz⟩
      · match s, h with
        | [], h => simp [decNat] at h
        | _ :: _, _ => simp at h0
      · omega
      · match s, h with
        | [], h => simp [decNat] at h
        | [c], _ => simp at h1
        | c :: d :: t, h =>
          simp only [List.head?_cons, Option.some.injEq] at hz
          subst hz
          simp [decNat] at h

/-! ## `AddrOk` -/

/-- `AddrOk`'s first loop: from the state `n` pieces done (`ps`), the current piece `cur`, the
rest of the address `s`: the five pieces between three dots and then one colon, or `none`. -/
def scanGo : GoString → Nat → GoString → List GoString → Option (List GoString)
  | [], n, cur, ps => if n = 4 then some (ps ++ [cur]) else none
  | c :: s, n, cur, ps =>
    if c = 46 then (if 3 ≤ n then none else scanGo s (n + 1) [] (ps ++ [cur]))
    else if c = 58 then (if n ≠ 3 then none else scanGo s (n + 1) [] (ps ++ [cur]))
    else scanGo s n (cur ++ [c]) ps

/-- `AddrOk`'s condition on the five values. -/
def addrCond : List Nat → Bool
  | [v0, v1, v2, v3, v4] => decide (1 ≤ v0) && decide (v0 < 224) && decide (v1 ≤ 255) &&
      decide (v2 ≤ 255) && decide (v3 ≤ 255) && decide (1 ≤ v4) &&
      (decide (v4 < 32768) || decide (60999 < v4))
  | _ => false

/-- What `AddrOk` computes. -/
def goAddrOk (a : GoString) : Bool :=
  match scanGo a 0 [] [] with
  | some xs => match xs.mapM (decimalM · 65535) with
    | some vs => addrCond vs
    | none => false
  | none => false

/-- The separators of the five pieces after `n` are done. -/
def seps : List w8 := [46, 46, 46, 58]

def joinSeps : List GoString → List w8 → GoString
  | [q], [] => q
  | q :: qs, sep :: ss => q ++ sep :: joinSeps qs ss
  | _, _ => []

def clean (q : GoString) : Prop := (46 : w8) ∉ q ∧ (58 : w8) ∉ q

theorem scanGo_shape : ∀ (s : GoString) (n : Nat) (cur : GoString) (ps xs : List GoString),
    scanGo s n cur ps = some xs → n ≤ 4 ∧ ∃ qs : List GoString, qs.length = 5 - n ∧
      (∀ q ∈ qs, clean q) ∧ s = joinSeps qs (seps.drop n) ∧
      xs = ps ++ (cur ++ qs.headD []) :: qs.tail
  | [], n, cur, ps, xs, h => by
    simp only [scanGo] at h
    split at h
    · rename_i hn
      subst hn
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨by decide, [[]], rfl, ?_, rfl, by simp⟩
      intro q hq; rw [List.mem_singleton.mp hq]; exact ⟨List.not_mem_nil, List.not_mem_nil⟩
    · cases h
  | c :: s, n, cur, ps, xs, h => by
    simp only [scanGo] at h
    by_cases h46 : c = 46
    · rw [if_pos h46] at h
      split at h
      · cases h
      · rename_i hn
        obtain ⟨hn', qs, hl, hc, hs, hx⟩ := scanGo_shape s (n + 1) [] (ps ++ [cur]) xs h
        refine ⟨by omega, [] :: qs, by simp [hl]; omega, ?_, ?_, ?_⟩
        · intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact ⟨List.not_mem_nil, List.not_mem_nil⟩
          · exact hc q hq
        · have : seps.drop n = 46 :: seps.drop (n + 1) := by
            rcases (show n = 0 ∨ n = 1 ∨ n = 2 by omega) with rfl | rfl | rfl <;> rfl
          obtain ⟨q0, qr, rfl⟩ := List.exists_cons_of_length_pos (show 0 < qs.length by omega)
          rw [this, h46, hs]
          simp [joinSeps]
        · obtain ⟨q0, qr, rfl⟩ := List.exists_cons_of_length_pos (show 0 < qs.length by omega)
          rw [hx]; simp
    · rw [if_neg h46] at h
      by_cases h58 : c = 58
      · rw [if_pos h58] at h
        split at h
        · cases h
        · rename_i hn
          have hn3 : n = 3 := by omega
          subst hn3
          obtain ⟨hn', qs, hl, hc, hs, hx⟩ := scanGo_shape s 4 [] (ps ++ [cur]) xs h
          refine ⟨by omega, [] :: qs, by simp [hl], ?_, ?_, ?_⟩
          · intro q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact ⟨List.not_mem_nil, List.not_mem_nil⟩
            · exact hc q hq
          · obtain ⟨q0, qr, rfl⟩ := List.exists_cons_of_length_pos (show 0 < qs.length by omega)
            rw [h58, hs]
            simp [joinSeps, seps]
          · obtain ⟨q0, qr, rfl⟩ := List.exists_cons_of_length_pos (show 0 < qs.length by omega)
            rw [hx]; simp
      · rw [if_neg h58] at h
        obtain ⟨hn', qs, hl, hc, hs, hx⟩ := scanGo_shape s n (cur ++ [c]) ps xs h
        obtain ⟨q0, qr, rfl⟩ := List.exists_cons_of_length_pos (show 0 < qs.length by omega)
        refine ⟨hn', (c :: q0) :: qr, by simpa using hl, ?_, ?_, ?_⟩
        · intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · obtain ⟨h1, h2⟩ := hc q0 List.mem_cons_self
            refine ⟨?_, ?_⟩ <;> intro m <;> rcases List.mem_cons.mp m with e | m
            · exact h46 e.symm
            · exact h1 m
            · exact h58 e.symm
            · exact h2 m
          · exact hc q (List.mem_cons_of_mem _ hq)
        · rw [hs]
          rcases qr with _ | ⟨q1, qr⟩
          · cases hsd : seps.drop n with
            | nil => simp [joinSeps]
            | cons sp ss => simp [joinSeps]
          · cases hsd : seps.drop n with
            | nil =>
              have := congrArg List.length hsd
              simp only [seps, List.length_drop, List.length_cons, List.length_nil] at this hl
              omega
            | cons sp ss => simp [joinSeps]
        · rw [hx]; simp

theorem scanGo_clean : ∀ (x y : GoString) (n : Nat) (cur : GoString) (ps : List GoString), clean x →
    scanGo (x ++ y) n cur ps = scanGo y n (cur ++ x) ps
  | [], y, n, cur, ps, _ => by simp
  | c :: x, y, n, cur, ps, ⟨h1, h2⟩ => by
    have hc46 : c ≠ 46 := fun e => h1 (e ▸ List.mem_cons_self)
    have hc58 : c ≠ 58 := fun e => h2 (e ▸ List.mem_cons_self)
    rw [List.cons_append]
    simp only [scanGo, if_neg hc46, if_neg hc58]
    rw [scanGo_clean x y n (cur ++ [c]) ps
      ⟨fun m => h1 (List.mem_cons_of_mem _ m), fun m => h2 (List.mem_cons_of_mem _ m)⟩]
    simp

theorem scanGo_dot (y : GoString) (n : Nat) (cur : GoString) (ps : List GoString) (h : n < 3) :
    scanGo (46 :: y) n cur ps = scanGo y (n + 1) [] (ps ++ [cur]) := by
  rw [scanGo.eq_2, if_pos rfl, if_neg (by omega)]

theorem scanGo_colon (y : GoString) (n : Nat) (cur : GoString) (ps : List GoString) (h : n = 3) :
    scanGo (58 :: y) n cur ps = scanGo y (n + 1) [] (ps ++ [cur]) := by
  rw [scanGo.eq_2, if_neg (by decide), if_pos rfl, if_neg (by omega)]

theorem scanGo_of_shape (x0 x1 x2 x3 x4 : GoString) (h0 : clean x0) (h1 : clean x1)
    (h2 : clean x2) (h3 : clean x3) (h4 : clean x4) :
    scanGo (x0 ++ 46 :: (x1 ++ 46 :: (x2 ++ 46 :: (x3 ++ 58 :: x4)))) 0 [] [] =
      some [x0, x1, x2, x3, x4] := by
  rw [scanGo_clean _ _ _ _ _ h0, scanGo_dot _ _ _ _ (by decide), scanGo_clean _ _ _ _ _ h1,
    scanGo_dot _ _ _ _ (by decide), scanGo_clean _ _ _ _ _ h2, scanGo_dot _ _ _ _ (by decide),
    scanGo_clean _ _ _ _ _ h3, scanGo_colon _ _ _ _ rfl, ← List.append_nil x4,
    scanGo_clean x4 [] _ _ _ h4, scanGo.eq_1]
  simp

theorem isDigit_46 : isDigit (46 : w8) = false := by decide
theorem isDigit_58 : isDigit (58 : w8) = false := by decide

theorem clean_of_decNat {x : GoString} {n : Nat} (h : decNat x = some n) : clean x :=
  ⟨digits_free (decNat_digits h) _ isDigit_46, digits_free (decNat_digits h) _ isDigit_58⟩

theorem decimalM_some {x : GoString} {v : Nat} (h : decimalM x 65535 = some v) :
    decNat x = some v ∧ v ≤ 65535 := (decimalM_iff x 65535 v (by decide)).mp h

/-- **`AddrOk` computes the net extension's `addrOk`.** -/
theorem goAddrOk_eq (a : GoString) : goAddrOk a = addrOk a := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · -- what `AddrOk` accepts is a valid address
    unfold goAddrOk
    intro h
    split at h
    · rename_i xs hs
      split at h
      · rename_i vs hv
        obtain ⟨-, qs, hl, hc, ha, hx⟩ := scanGo_shape a 0 [] [] xs hs
        match qs, hl, hc, ha, hx with
        | [x0, x1, x2, x3, x4], _, hc, ha, hx =>
          simp only [List.nil_append, List.headD_cons, List.tail_cons] at hx
          subst hx
          simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind] at hv
          cases e0 : decimalM x0 65535 <;> rw [e0] at hv <;> simp at hv
          cases e1 : decimalM x1 65535 <;> rw [e1] at hv <;> simp at hv
          cases e2 : decimalM x2 65535 <;> rw [e2] at hv <;> simp at hv
          cases e3 : decimalM x3 65535 <;> rw [e3] at hv <;> simp at hv
          cases e4 : decimalM x4 65535 <;> rw [e4] at hv <;> simp at hv
          rename_i v0 v1 v2 v3 v4
          subst hv
          obtain ⟨d0, b0⟩ := decimalM_some e0
          obtain ⟨d1, b1⟩ := decimalM_some e1
          obtain ⟨d2, b2⟩ := decimalM_some e2
          obtain ⟨d3, b3⟩ := decimalM_some e3
          obtain ⟨d4, b4⟩ := decimalM_some e4
          have c0 := clean_of_decNat d0
          have c1 := clean_of_decNat d1
          have c2 := clean_of_decNat d2
          have c3 := clean_of_decNat d3
          have c4 := clean_of_decNat d4
          have hip : splitBy 46 (x0 ++ 46 :: (x1 ++ 46 :: (x2 ++ 46 :: x3))) [] = [x0, x1, x2, x3] := by
            rw [splitBy_free_sep _ _ _ c0.1, splitBy_free_sep _ _ _ c1.1, splitBy_free_sep _ _ _ c2.1,
              splitBy_free _ _ c3.1]
          have hip58 : (58 : w8) ∉ x0 ++ 46 :: (x1 ++ 46 :: (x2 ++ 46 :: x3)) := by
            simp only [List.mem_append, List.mem_cons, not_or]
            exact ⟨c0.2, by decide, c1.2, by decide, c2.2, by decide, c3.2⟩
          have ha' : a = (x0 ++ 46 :: (x1 ++ 46 :: (x2 ++ 46 :: x3))) ++ 58 :: x4 := by
            rw [ha]; simp [joinSeps, seps]
          have hsp : splitBy 58 a [] = [x0 ++ 46 :: (x1 ++ 46 :: (x2 ++ 46 :: x3)), x4] := by
            rw [ha', splitBy_free_sep _ _ _ hip58, splitBy_free _ _ c4.2]
          unfold addrOk parseAddr
          rw [hsp]
          simp only [hip, d0, d1, d2, d3, d4]
          simp only [addrCond, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
          simp only [portOk, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
          omega
      · cases h
    · cases h
  · -- a valid address is one `AddrOk` accepts
    intro h
    unfold addrOk at h
    split at h
    · rename_i n1 n2 n3 n4 p hp
      obtain ⟨ip, ps, x1, x2, x3, x4, hs, hs', d1, d2, d3, d4, d5⟩ := parseAddr_some hp
      simp only [Bool.and_eq_true, decide_eq_true_eq, portOk, Bool.or_eq_true] at h
      obtain ⟨ha, hf⟩ := splitBy_shape0 58 a
      obtain ⟨hip, hf'⟩ := splitBy_shape0 46 ip
      rw [hs] at ha hf
      rw [hs'] at hip hf'
      have c1 := clean_of_decNat d1
      have c2 := clean_of_decNat d2
      have c3 := clean_of_decNat d3
      have c4 := clean_of_decNat d4
      have c5 := clean_of_decNat d5
      have ha' : a = x1 ++ 46 :: (x2 ++ 46 :: (x3 ++ 46 :: (x4 ++ 58 :: ps))) := by
        rw [ha, hip]
        simp [List.intercalate_cons_cons, List.append_assoc]
      unfold goAddrOk
      rw [ha', scanGo_of_shape _ _ _ _ _ c1 c2 c3 c4 c5]
      have e1 := (decimalM_iff x1 65535 n1 (by decide)).mpr ⟨d1, by omega⟩
      have e2 := (decimalM_iff x2 65535 n2 (by decide)).mpr ⟨d2, by omega⟩
      have e3 := (decimalM_iff x3 65535 n3 (by decide)).mpr ⟨d3, by omega⟩
      have e4 := (decimalM_iff x4 65535 n4 (by decide)).mpr ⟨d4, by omega⟩
      have e5 := (decimalM_iff ps 65535 p (by decide)).mpr ⟨d5, by omega⟩
      simp only [List.mapM_cons, List.mapM_nil, e1, e2, e3, e4, e5, Option.bind_eq_bind,
        Option.bind_some, Option.pure_def]
      simp only [addrCond, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
      omega
    · cases h

/-! ### What `AddrOk`'s loops conclude -/

theorem goAddrOk_scan_none {a : GoString} (h : scanGo a 0 [] [] = none) : goAddrOk a = false := by
  unfold goAddrOk; rw [h]

theorem mapM_none_of {f : GoString → Option Nat} : ∀ {xs : List GoString} {x : GoString},
    x ∈ xs → f x = none → xs.mapM f = none
  | [], _, hx, _ => by simp at hx
  | y :: ys, x, hx, hf => by
    rw [List.mapM_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [hf]; rfl
    · cases f y with
      | none => rfl
      | some v => simp [mapM_none_of hx hf]

theorem goAddrOk_dec_none {a : GoString} {xs : List GoString} {x : GoString}
    (h : scanGo a 0 [] [] = some xs) (hx : x ∈ xs) (hd : decimalM x 65535 = none) :
    goAddrOk a = false := by
  unfold goAddrOk; rw [h]; simp only []; rw [mapM_none_of (f := fun x => decimalM x 65535) hx hd]

theorem goAddrOk_all {a : GoString} {x0 x1 x2 x3 x4 : GoString} {v0 v1 v2 v3 v4 : Nat}
    (h : scanGo a 0 [] [] = some [x0, x1, x2, x3, x4]) (h0 : decimalM x0 65535 = some v0)
    (h1 : decimalM x1 65535 = some v1) (h2 : decimalM x2 65535 = some v2)
    (h3 : decimalM x3 65535 = some v3) (h4 : decimalM x4 65535 = some v4) :
    goAddrOk a = addrCond [v0, v1, v2, v3, v4] := by
  unfold goAddrOk
  rw [h]
  simp [List.mapM_cons, h0, h1, h2, h3, h4]

theorem take_set_succ (l : List GoString) (k : Nat) (x : GoString) (h : k < l.length) :
    (l.set k x).take (k + 1) = l.take k ++ [x] := by
  rw [List.set_eq_take_append_cons_drop, if_pos h, List.take_append]
  have : (l.take k).length = k := by simp; omega
  rw [List.take_of_length_le (by omega), this, Nat.add_sub_cancel_left]
  simp

theorem scanGo_length : ∀ (s : GoString) (n : Nat) (cur : GoString) (ps xs : List GoString),
    scanGo s n cur ps = some xs → xs.length = ps.length + 5 - n
  | s, n, cur, ps, xs, h => by
    obtain ⟨hn, qs, hl, -, -, hx⟩ := scanGo_shape s n cur ps xs h
    obtain ⟨q0, qr, rfl⟩ := List.exists_cons_of_length_pos (show 0 < qs.length by omega)
    rw [hx]; simp at hl ⊢; omega

/-! ## `ValidAddrs`, `ValidCluster` -/

/-- `ValidAddrs(addrs, voters)`: every address valid and none twice, fewer than `2^32` of them, and
the bootstrap voters `1..voters` among them. -/
def validAddrs (l : List GoString) (voters : Nat) : Bool :=
  decide ((∀ a ∈ l, addrOk a = true) ∧ l.Nodup ∧ l.length < 2 ^ 32 ∧ 1 ≤ voters ∧ voters ≤ l.length)

theorem validAddrs_bad (l : List GoString) (v : Nat) (a : GoString) (ha : a ∈ l)
    (hb : addrOk a = false) : validAddrs l v = false := by
  unfold validAddrs
  apply decide_eq_false
  rintro ⟨h, -⟩
  rw [h a ha] at hb; cases hb

theorem mem_take_of_getElem? {l : List GoString} {m j : Nat} {y : GoString} (hm : m < j)
    (h : l[m]? = some y) : y ∈ l.take j := by
  apply List.mem_iff_getElem?.mpr
  exact ⟨m, by rw [List.getElem?_take_of_lt hm]; exact h⟩

theorem validAddrs_dup (l : List GoString) (v : Nat) (y : GoString) (m j : Nat) (hm : m < j)
    (h1 : l[m]? = some y) (h2 : l[j]? = some y) : validAddrs l v = false := by
  unfold validAddrs
  apply decide_eq_false
  rintro ⟨-, hn, -⟩
  have hs : (l.take (j + 1)).Nodup := hn.sublist (List.take_sublist _ _)
  rw [List.take_add_one, h2] at hs
  have := (List.nodup_append.mp hs).2.2
  exact this y (mem_take_of_getElem? hm h1) y (List.mem_singleton_self y) rfl

theorem not_mem_take_of {l : List GoString} {j : Nat} {y : GoString}
    (h : ∀ q, q < j → l[q]? ≠ some y) : y ∉ l.take j := by
  intro hm
  obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp hm
  have hqj : q < j := by
    have := (List.getElem?_eq_some_iff.mp hq).1
    simp at this; omega
  rw [List.getElem?_take_of_lt hqj] at hq
  exact h q hqj hq

/-- `ValidCluster(addrs, voters, maxSizePerMsg, maxCommittedSizePerReady, maxInflightMsgs)`. -/
def validCluster (l : List GoString) (voters msz mcs mif : Nat) : Bool :=
  validAddrs l voters && !(msz = 0 && mcs = 0) && decide (0 < mif) && decide (mif < 2 ^ 62)

/-- **`RunNode`'s check**: what `RunNode` checks before it runs a replica (else it returns at once):
the cluster valid (`ValidCluster`), the id one of its replicas (`1 ≤ id ≤ len(addrs)`), and the
directory's name shorter than `MaxDirLen = 2^39` bytes. -/
def runNodeOk (l : List GoString) (id : Nat) (dir : GoString) (voters msz mcs mif : Nat) : Prop :=
  validCluster l voters msz mcs mif = true ∧ 1 ≤ id ∧ id ≤ l.length ∧ dir.length < 2 ^ 39

instance (l : List GoString) (id : Nat) (dir : GoString) (voters msz mcs mif : Nat) :
    Decidable (runNodeOk l id dir voters msz mcs mif) := by
  unfold runNodeOk; infer_instance

end EtcdGrove.raft_kvnet
end Perennial
