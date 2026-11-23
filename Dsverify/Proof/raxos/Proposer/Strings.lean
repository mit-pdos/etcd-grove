/-
Package `proposer`: the recorder addresses are distinct (evaluating `toString` and `toUTF8`).
-/
module

public import Dsverify.Proof.raxos.Proto

@[expose] public section

namespace Perennial.raxos.prop

theorem ba_toList_loop (bs : ByteArray) (i : Nat) (r : List UInt8) (hi : i ≤ bs.size) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  induction h : bs.size - i generalizing i r with
  | zero =>
    have : i = bs.size := by omega
    subst this
    rw [ByteArray.toList.loop]; simp
  | succ n ih =>
    rw [ByteArray.toList.loop]
    have hlt : i < bs.size := by omega
    simp only [hlt, ↓reduceIte]
    rw [ih (i+1) _ (by omega) (by omega)]
    simp [ByteArray.get!]
    have hl : i < bs.data.toList.length := by rw [Array.length_toList]; exact hlt
    rw [List.drop_eq_getElem_cons hl]
    have hl' : i < bs.data.size := by simpa using hl
    simp only [List.cons.injEq, and_true]
    rw [getElem!_pos bs.data i hl']
    simp

theorem toUTF8_toList_ofList (s : String) (cs : List Char) (h : s = String.ofList cs) :
    s.toUTF8.toList = cs.flatMap String.utf8EncodeChar := by
  rw [h, String.toUTF8_eq_toByteArray, String.toByteArray_ofList, ByteArray.toList,
    ba_toList_loop _ _ _ (Nat.zero_le _)]
  simp [List.utf8Encode]

theorem toString_teen (d : Nat) (c : Char) (hd : d < 10) (hc : Nat.digitChar d = c) :
    toString (10 + d) = String.ofList ['1', c] := by
  rw [Nat.toString_eq_ofList_toDigits, Nat.toDigits_of_base_le (by omega) (by omega),
    Nat.toDigits_of_lt_base (by omega)]
  have h1 : (10 + d) / 10 = 1 := by omega
  have h2 : (10 + d) % 10 = d := by omega
  rw [h1, h2, hc, Nat.digitChar_eq_one.2 rfl]
  rfl

/-- A two-digit number's decimal string. -/
theorem toString_two (a d : Nat) (ca cd : Char) (ha : 1 ≤ a ∧ a < 10) (hd : d < 10)
    (hca : Nat.digitChar a = ca) (hcd : Nat.digitChar d = cd) :
    toString (10 * a + d) = String.ofList [ca, cd] := by
  rw [Nat.toString_eq_ofList_toDigits, Nat.toDigits_of_base_le (by omega) (by omega),
    Nat.toDigits_of_lt_base (by omega)]
  have h1 : (10 * a + d) / 10 = a := by omega
  have h2 : (10 * a + d) % 10 = d := by omega
  rw [h1, h2, hca, hcd]
  rfl

theorem decStr_two (n a d : Nat) (ca cd : Char) (hn : n = 10 * a + d) (ha : 1 ≤ a ∧ a < 10)
    (hd : d < 10) (hca : Nat.digitChar a = ca) (hcd : Nat.digitChar d = cd) :
    decStr n = ([ca, cd].flatMap String.utf8EncodeChar).map (fun b => BitVec.ofNat 8 b.toNat) := by
  unfold decStr
  rw [toUTF8_toList_ofList _ _ (hn ▸ toString_two a d ca cd ha hd hca hcd)]

/-- A four-digit number's decimal string. -/
theorem toString_four (n a b c d : Nat) (hn : n = 1000 * a + 100 * b + 10 * c + d)
    (ha : 1 ≤ a ∧ a < 10) (hb : b < 10) (hc : c < 10) (hd : d < 10) :
    toString n = String.ofList [Nat.digitChar a, Nat.digitChar b, Nat.digitChar c,
      Nat.digitChar d] := by
  subst hn
  rw [Nat.toString_eq_ofList_toDigits, Nat.toDigits_of_base_le (by omega) (by omega)]
  rw [show (1000 * a + 100 * b + 10 * c + d) / 10 = 100 * a + 10 * b + c by omega,
    show (1000 * a + 100 * b + 10 * c + d) % 10 = d by omega]
  rw [Nat.toDigits_of_base_le (by omega) (by omega)]
  rw [show (100 * a + 10 * b + c) / 10 = 10 * a + b by omega,
    show (100 * a + 10 * b + c) % 10 = c by omega]
  rw [Nat.toDigits_of_base_le (by omega) (by omega)]
  rw [show (10 * a + b) / 10 = a by omega, show (10 * a + b) % 10 = b by omega]
  rw [Nat.toDigits_of_lt_base (by omega)]
  rfl

theorem decStr_four (n a b c d : Nat) (ca cb cc cd : Char) (hn : n = 1000 * a + 100 * b + 10 * c + d)
    (ha : 1 ≤ a ∧ a < 10) (hb : b < 10) (hc : c < 10) (hd : d < 10)
    (hca : Nat.digitChar a = ca) (hcb : Nat.digitChar b = cb) (hcc : Nat.digitChar c = cc)
    (hcd : Nat.digitChar d = cd) :
    decStr n = ([ca, cb, cc, cd].flatMap String.utf8EncodeChar).map
      (fun b => BitVec.ofNat 8 b.toNat) := by
  unfold decStr
  rw [toUTF8_toList_ofList _ _ (toString_four n a b c d hn ha hb hc hd), hca, hcb, hcc, hcd]

theorem recAddr_1 : recAddr 1 = go!"127.0.0.1:7627" := by
  unfold recAddr portAddr
  rw [decStr_four _ 7 6 2 7 '7' '6' '2' '7' rfl (by omega) (by omega)
    (by omega) (by omega) (by simp) (by simp) (by simp) (by simp)]
  decide

theorem recAddr_2 : recAddr 2 = go!"127.0.0.1:7628" := by
  unfold recAddr portAddr
  rw [decStr_four _ 7 6 2 8 '7' '6' '2' '8' rfl (by omega) (by omega)
    (by omega) (by omega) (by simp) (by simp) (by simp) (by simp)]
  decide

theorem recAddr_3 : recAddr 3 = go!"127.0.0.1:7629" := by
  unfold recAddr portAddr
  rw [decStr_four _ 7 6 2 9 '7' '6' '2' '9' rfl (by omega) (by omega)
    (by omega) (by omega) (by simp) (by simp) (by simp) (by simp)]
  decide

theorem recAddr_4 : recAddr 4 = go!"127.0.0.1:7630" := by
  unfold recAddr portAddr
  rw [decStr_four _ 7 6 3 0 '7' '6' '3' '0' rfl (by omega) (by omega)
    (by omega) (by omega) (by simp) (by simp) (by simp) (by simp)]
  decide

theorem recAddr_5 : recAddr 5 = go!"127.0.0.1:7631" := by
  unfold recAddr portAddr
  rw [decStr_four _ 7 6 3 1 '7' '6' '3' '1' rfl (by omega) (by omega)
    (by omega) (by omega) (by simp) (by simp) (by simp) (by simp)]
  decide

/-- Recorder `r`'s address names recorder `r` (`1 ≤ r ≤ 5`). -/
theorem recOfAddr_recAddr (r : Nat) (hr : 1 ≤ r ∧ r ≤ 5) : recOfAddr (recAddr r) = some r := by
  have h : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by omega
  unfold recOfAddr
  rcases h with rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.find?, recAddr_1, recAddr_2, recAddr_3, recAddr_4, recAddr_5] <;> try decide

end Perennial.raxos.prop
