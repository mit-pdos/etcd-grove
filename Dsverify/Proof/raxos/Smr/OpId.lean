/-
The request ids (`opId c j`, `"21.c.j"`): ASCII, and injective (package `kit`).
-/
module

public import Dsverify.Proof.raxos.Ghost
public import Std.Data.String.ToNat

@[expose] public section

noncomputable section

namespace Perennial.raxos.opid

open Perennial Perennial.raxos

theorem ba_loop (bs : ByteArray) (i : Nat) (r : List UInt8) (hi : i ≤ bs.size) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  have hsz : bs.data.toList.length = bs.size := Array.length_toList
  induction h : bs.size - i generalizing i r with
  | zero =>
    have : i = bs.size := by omega
    subst this
    rw [ByteArray.toList.loop, ite_cond_eq_false _ _ (by simp)]
    rw [List.drop_eq_nil_of_le (by omega), List.append_nil]
  | succ k ih =>
    have hlt : i < bs.size := by omega
    rw [ByteArray.toList.loop, ite_cond_eq_true _ _ (by simp [hlt]), ih (i + 1) _ (by omega) (by omega)]
    have hl : i < bs.data.toList.length := by omega
    have : bs.get! i = bs.data.toList[i] := by
      rw [ByteArray.get!, getElem!_pos bs.data i (by omega), Array.getElem_toList]
    rw [List.reverse_cons, List.append_assoc, List.singleton_append, this, List.getElem_cons_drop]

theorem ba_toList (bs : ByteArray) : bs.toList = bs.data.toList := by
  rw [ByteArray.toList, ba_loop _ _ _ (Nat.zero_le _)]; simp

def bstr (s : String) : GoString := s.toUTF8.toList.map (fun b => BitVec.ofNat 8 b.toNat)

theorem map_inj_of {α β} (f : α → β) (hf : ∀ a b, f a = f b → a = b) :
    ∀ (l1 l2 : List α), l1.map f = l2.map f → l1 = l2
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l1, b :: l2, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hf a b h.1, map_inj_of f hf l1 l2 h.2]

theorem u8_inj (a b : UInt8) (h : BitVec.ofNat 8 a.toNat = BitVec.ofNat 8 b.toNat) : a = b := by
  have ha := a.toNat_lt; have hb := b.toNat_lt
  have : a.toNat = b.toNat := by
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt (by simpa using ha), Nat.mod_eq_of_lt (by simpa using hb)] at this
  exact UInt8.toNat_inj.1 this

theorem bstr_inj {s t : String} (h : bstr s = bstr t) : s = t := by
  unfold bstr at h
  rw [ba_toList, ba_toList] at h
  have h1 := map_inj_of _ u8_inj _ _ h
  have h2 : s.toUTF8.data = t.toUTF8.data := Array.toList_inj.1 h1
  have h3 : s.toUTF8 = t.toUTF8 := by cases hs : s.toUTF8; cases ht : t.toUTF8; simp_all
  rw [String.toUTF8_eq_toByteArray, String.toUTF8_eq_toByteArray] at h3
  exact String.toByteArray_inj.1 h3

theorem bstr_ofList (l : List Char) :
    bstr (String.ofList l) = (l.flatMap String.utf8EncodeChar).map (fun b => BitVec.ofNat 8 b.toNat) := by
  unfold bstr
  rw [ba_toList, String.toUTF8_eq_toByteArray, String.toByteArray_ofList, List.utf8Encode,
    List.toList_data_toByteArray]

theorem bstr_digits (n : Nat) : ∀ b ∈ bstr (toString n), 48 ≤ b.toNat ∧ b.toNat ≤ 57 := by
  rw [Nat.toString_eq_ofList_toDigits, bstr_ofList]
  intro b hb
  simp only [List.mem_map, List.mem_flatMap] at hb
  obtain ⟨u, ⟨c, hc, hu⟩, rfl⟩ := hb
  have hd := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at hd
  have hlo : 48 ≤ c.val.toNat := hd.1
  have hhi : c.val.toNat ≤ 57 := hd.2
  have h1 : c.utf8Size = 1 := Char.utf8Size_eq_one_iff.2 (by
    rw [UInt32.le_iff_toNat_le]; have : c.toNat = c.val.toNat := rfl; simp; omega)
  rw [String.utf8EncodeChar_eq_singleton h1, List.mem_singleton] at hu
  subst hu
  have : c.val.toUInt8.toNat = c.val.toNat := by
    rw [UInt32.toNat_toUInt8]; omega
  simp only [BitVec.toNat_ofNat, this]
  omega

theorem split_dot (A A' B B' : List w8) (hA : ∀ b ∈ A, b ≠ 46#8) (hA' : ∀ b ∈ A', b ≠ 46#8)
    (h : A ++ 46#8 :: B = A' ++ 46#8 :: B') : A = A' ∧ B = B' := by
  induction A generalizing A' with
  | nil =>
    cases A' with
    | nil => simpa using h
    | cons a A' =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd h.1.symm (hA' a (by simp))
  | cons a A ih =>
    cases A' with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd h.1 (hA a (by simp))
    | cons a' A' =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      have := ih A' (fun b hb => hA b (by simp [hb])) (fun b hb => hA' b (by simp [hb])) h
      exact ⟨by rw [this.1], this.2⟩

theorem digits_ne_dot (n : Nat) : ∀ b ∈ bstr (toString n), b ≠ 46#8 := by
  intro b hb h
  have := bstr_digits n b hb
  subst h
  simp at this

theorem toString_inj {m n : Nat} (h : toString m = toString n) : m = n := by
  rw [Nat.toString_eq_repr, Nat.toString_eq_repr] at h
  exact Nat.repr_injective h

theorem decStr_eq (n : Nat) : decStr n = bstr (toString n) := rfl

theorem opId_eq (c n : Nat) :
    opId c n = bstr (toString (21 + c)) ++ go!"." ++ bstr (toString n) := rfl

/-- Request ids are injective in `(c, n)` (for any `c`). -/
theorem opId_inj {c n c' n' : Nat} (h : opId c n = opId c' n') : c = c' ∧ n = n' := by
  rw [opId_eq, opId_eq] at h
  have h' : bstr (toString (21 + c)) ++ 46#8 :: bstr (toString n) =
      bstr (toString (21 + c')) ++ 46#8 :: bstr (toString n') := by simpa using h
  obtain ⟨h1, h2⟩ := split_dot _ _ _ _ (digits_ne_dot _) (digits_ne_dot _) h'
  have := toString_inj (bstr_inj h1)
  exact ⟨by omega, toString_inj (bstr_inj h2)⟩

theorem opId_ascii (c n : Nat) : msg.asciiOk (opId c n) := by
  rw [opId_eq]
  intro b hb
  simp only [List.mem_append] at hb
  rcases hb with (hb | hb) | hb
  · have := bstr_digits _ b hb; omega
  · revert b; decide
  · have := bstr_digits n b hb; omega

theorem dot_mem_opId (c n : Nat) : 46#8 ∈ opId c n := by
  rw [opId_eq]; simp

theorem opId_ne_nil (c n : Nat) : opId c n ≠ go!"nil" := by
  intro h
  have := dot_mem_opId c n
  rw [h] at this
  revert this; decide

theorem bstr_digit (d : Nat) (h : d < 10) :
    (String.utf8EncodeChar d.digitChar).map (fun b => BitVec.ofNat 8 b.toNat) = [BitVec.ofNat 8 (48 + d)] := by
  have hv : (d.digitChar).toNat = 48 + d := Nat.toNat_digitChar_of_lt_ten h
  have h1 : d.digitChar.utf8Size = 1 := Char.utf8Size_eq_one_iff.2 (by
    rw [UInt32.le_iff_toNat_le]; have : d.digitChar.toNat = d.digitChar.val.toNat := rfl; simp; omega)
  rw [String.utf8EncodeChar_eq_singleton h1]
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
  have : d.digitChar.val.toUInt8.toNat = 48 + d := by
    rw [UInt32.toNat_toUInt8]; have : d.digitChar.toNat = d.digitChar.val.toNat := rfl; omega
  rw [this]

theorem bstr_toString_rec (n : Nat) :
    bstr (toString n) = if n < 10 then [BitVec.ofNat 8 (48 + n)]
      else bstr (toString (n / 10)) ++ [BitVec.ofNat 8 (48 + n % 10)] := by
  rw [Nat.toString_eq_ofList_toDigits, Nat.toDigits_eq_ite (by decide)]
  split
  · rename_i h; rw [bstr_ofList]; simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact bstr_digit n h
  · rw [Nat.toString_eq_ofList_toDigits, bstr_ofList, bstr_ofList, List.flatMap_append, List.map_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [bstr_digit _ (Nat.mod_lt _ (by decide))]


/-- The decimal digits of `m` are nonempty, and their first byte is a digit. -/
theorem bstr_head (m : Nat) : ∃ b t, bstr (toString m) = b :: t ∧ 48 ≤ b.toNat ∧ b.toNat ≤ 57 := by
  cases h : bstr (toString m) with
  | nil =>
    exfalso
    rw [bstr_toString_rec] at h
    split at h
    · simp at h
    · simp at h
  | cons b t =>
    have := bstr_digits m b (by rw [h]; simp)
    exact ⟨b, t, rfl, this⟩

theorem opId_take1 (c n : Nat) : ∃ b, (opId c n).take 1 = [b] ∧ 48 ≤ b.toNat ∧ b.toNat ≤ 57 := by
  obtain ⟨b, t, h, hb⟩ := bstr_head (21 + c)
  exact ⟨b, by rw [opId_eq, h]; rfl, hb⟩

theorem opId_ne_summary (c n : Nat) (p : List Nat) : opId c n ≠ pure.summaryId p := by
  intro h
  obtain ⟨b, hb, h1, h2⟩ := opId_take1 c n
  have := congrArg (List.take 1) h
  rw [hb] at this
  simp [pure.summaryId] at this
  subst this
  simp at h1 h2

theorem opId_length (c n : Nat) :
    (opId c n).length = (decStr (21 + c)).length + 1 + (decStr n).length := by
  simp [opId]; omega

end Perennial.raxos.opid
