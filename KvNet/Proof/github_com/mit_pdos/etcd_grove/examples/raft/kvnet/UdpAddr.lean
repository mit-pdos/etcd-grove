/-
# kvudp's addresses, pure (2026-11-24, `notes/kvudp-proof-plan.md`)

The round trip of a valid address through its parts, which `UdpWire.lean`'s `parseAddrM_ok` (the
`ValidDest` of what `parseAddr` reads) rests on:

* `decDigits_decNat`: a canonical decimal numeral (`Net.decNat`) is what `Udp.decDigits` writes for
  its value;
* `addrOk_parts`: a valid address (`Net.addrOk`) splits at its colon and then its dots into four
  octets and a port, canonical numerals, with their bounds;
* `addrOk_join`: and it is those parts joined back (`splitBy_shape0`).
-/
module

public import GooseLang.Ext.Udp.Impl
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Addrs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove.raft_kvnet

open Net Udp

/-- `digitsVal` only grows its accumulator. -/
theorem digitsVal_ge : ∀ (r : GoString) (acc v : Nat), digitsVal r acc = some v → acc ≤ v
  | [], acc, v, h => by
    simp only [digitsVal, Option.some.injEq] at h; omega
  | c :: r, acc, v, h => by
    unfold digitsVal at h
    split at h
    · have := digitsVal_ge r _ v h; omega
    · cases h

/-- `digitsVal` of a numeral and one more digit. -/
theorem digitsVal_snoc_inv (t : GoString) (c : w8) (acc n : Nat)
    (h : digitsVal (t ++ [c]) acc = some n) :
    ∃ v, digitsVal t acc = some v ∧ isDigit c = true ∧ n = v * 10 + (c.toNat - 48) := by
  rw [digitsVal_append] at h
  cases ht : digitsVal t acc with
  | none => rw [ht] at h; cases h
  | some v =>
    rw [ht] at h
    change digitsVal [c] v = some n at h
    refine ⟨v, rfl, ?_⟩
    unfold digitsVal at h
    split at h
    · next hc =>
      simp only [digitsVal, Option.some.injEq] at h
      exact ⟨hc, h.symm⟩
    · cases h

/-- A digit's byte, from its value. -/
theorem digit_byte (c : w8) (hc : isDigit c = true) : BitVec.ofNat 8 (48 + (c.toNat - 48)) = c := by
  unfold isDigit at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  omega

/-- `decDigits` writes back a numeral with no leading zero, from its value. -/
theorem decDigits_of_digitsVal : ∀ (k : Nat) (s : GoString) (n : Nat), s.length = k → s ≠ [] →
    (2 ≤ s.length → s.head? ≠ some (48 : w8)) → digitsVal s 0 = some n → decDigits n = s := by
  intro k
  induction k with
  | zero => intro s n hl hne; exact absurd (List.eq_nil_of_length_eq_zero hl) hne
  | succ k ih =>
    intro s n hl hne hz hv
    obtain ⟨t, c, rfl⟩ : ∃ t c, s = t ++ [c] :=
      ⟨s.dropLast, s.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
    obtain ⟨v, ht, hc, rfl⟩ := digitsVal_snoc_inv t c 0 n hv
    have hcb := digit_byte c hc
    have hc' := hc
    unfold isDigit at hc'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
    by_cases htn : t = []
    · subst htn
      have hv0 : v = 0 := by simp only [digitsVal, Option.some.injEq] at ht; omega
      subst hv0
      unfold decDigits
      rw [dif_pos (by omega)]
      simp only [List.nil_append]
      rw [show 0 * 10 + (c.toNat - 48) = c.toNat - 48 by omega, hcb]
    · obtain ⟨c0, r, rfl⟩ := List.exists_cons_of_ne_nil htn
      have hc0 : c0 ≠ (48 : w8) := by
        have := hz (by simp)
        simpa using this
      have hv1 : 1 ≤ v := by
        unfold digitsVal at ht
        split at ht
        · next hd =>
          have := digitsVal_ge r _ v ht
          unfold isDigit at hd
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
          have : c0.toNat ≠ 48 := fun e => hc0 (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
          omega
        · cases ht
      have hl' : (c0 :: r).length = k := by simp at hl; simp; omega
      have hrec := ih (c0 :: r) v hl' (List.cons_ne_nil _ _)
        (fun _ => by simp only [List.head?_cons, ne_eq, Option.some.injEq]; exact hc0) ht
      unfold decDigits
      rw [dif_neg (by omega)]
      rw [show (v * 10 + (c.toNat - 48)) / 10 = v by omega,
        show (v * 10 + (c.toNat - 48)) % 10 = c.toNat - 48 by omega, hrec, hcb]

/-- **A canonical decimal numeral is what `decDigits` writes for its value.** -/
theorem decDigits_decNat {x : GoString} {n : Nat} (h : decNat x = some n) : decDigits n = x := by
  match x, h with
  | [], h => simp [decNat] at h
  | [c], h => exact decDigits_of_digitsVal 1 [c] n rfl (List.cons_ne_nil _ _) (by simp) h
  | c :: d :: s, h =>
    simp only [decNat] at h
    split at h
    · cases h
    · next hc =>
      refine decDigits_of_digitsVal _ _ n rfl (List.cons_ne_nil _ _) (fun _ => ?_) h
      simp only [List.head?_cons, ne_eq, Option.some.injEq]
      intro e; apply hc; rw [e]; rfl

/-- **A valid address's parts**: split at its colon, then its dots, four octets and a port, each a
canonical numeral, with their bounds. -/
theorem addrOk_parts {a : GoString} (hok : addrOk a = true) :
    ∃ (h p x1 x2 x3 x4 : GoString) (n1 n2 n3 n4 pt : Nat),
      splitBy 58 a [] = [h, p] ∧ splitBy 46 h [] = [x1, x2, x3, x4] ∧
      decNat x1 = some n1 ∧ decNat x2 = some n2 ∧ decNat x3 = some n3 ∧ decNat x4 = some n4 ∧
      decNat p = some pt ∧
      1 ≤ n1 ∧ n1 < 224 ∧ n2 ≤ 255 ∧ n3 ≤ 255 ∧ n4 ≤ 255 ∧ portOk pt = true := by
  unfold addrOk at hok
  cases hp : Net.parseAddr a with
  | none => rw [hp] at hok; cases hok
  | some t =>
    obtain ⟨n1, n2, n3, n4, pt⟩ := t
    rw [hp] at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hok
    unfold Net.parseAddr at hp
    rcases h58 : splitBy 58 a [] with _ | ⟨h, _ | ⟨p, _ | ⟨q, r⟩⟩⟩ <;>
      simp only [h58, reduceCtorEq] at hp
    rcases h46 : splitBy 46 h [] with _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨y, ys⟩⟩⟩⟩⟩ <;>
      simp only [h46, reduceCtorEq] at hp
    cases e1 : decNat x1 <;> cases e2 : decNat x2 <;> cases e3 : decNat x3 <;>
      cases e4 : decNat x4 <;> cases e5 : decNat p <;>
      simp only [e1, e2, e3, e4, e5, reduceCtorEq] at hp
    rename_i m1 m2 m3 m4 m5
    simp only [Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hp
    exact ⟨h, p, x1, x2, x3, x4, m1, m2, m3, m4, m5, rfl, h46, e1, e2, e3, e4, e5,
      h1, h2, h3, h4, h5, h6⟩

/-- **A valid address is its parts joined back.** -/
theorem addrOk_join {a h p x1 x2 x3 x4 : GoString} (h58 : splitBy 58 a [] = [h, p])
    (h46 : splitBy 46 h [] = [x1, x2, x3, x4]) :
    a = x1 ++ [46] ++ x2 ++ [46] ++ x3 ++ [46] ++ x4 ++ [58] ++ p := by
  have ha := (splitBy_shape0 58 a).1
  have hh := (splitBy_shape0 46 h).1
  rw [h58] at ha
  rw [h46] at hh
  rw [ha, hh]
  simp [List.intercalate]

/-! ## `parseAddr`'s loop -/

/-- `parseAddr`'s loop: `s` split at every dot and colon (`cur`: the current piece). -/
def splitAny : GoString → GoString → List GoString
  | [], cur => [cur]
  | c :: s, cur => if c = 46 ∨ c = 58 then cur :: splitAny s [] else splitAny s (cur ++ [c])

/-- `x` has no dot and no colon. -/
def SepFree (x : GoString) : Prop := ∀ c ∈ x, c ≠ 46 ∧ c ≠ 58

theorem splitAny_ne_nil : ∀ (s cur : GoString), splitAny s cur ≠ []
  | [], cur => by simp [splitAny]
  | c :: s, cur => by
    rw [splitAny.eq_2]
    split
    · simp
    · exact splitAny_ne_nil s _

theorem splitAny_free : ∀ (x y cur : GoString), SepFree x → splitAny (x ++ y) cur = splitAny y (cur ++ x)
  | [], y, cur, _ => by simp
  | c :: x, y, cur, h => by
    have hc := h c List.mem_cons_self
    rw [List.cons_append, splitAny.eq_2, if_neg (fun e => e.elim hc.1 hc.2),
      splitAny_free x y _ (fun d hd => h d (List.mem_cons_of_mem _ hd))]
    simp

theorem splitAny_sep (x y cur : GoString) (sep : w8) (hs : sep = 46 ∨ sep = 58) (hx : SepFree x) :
    splitAny (x ++ sep :: y) cur = (cur ++ x) :: splitAny y [] := by
  rw [splitAny_free x (sep :: y) cur hx, splitAny.eq_2, if_pos hs]

theorem splitAny_last (x cur : GoString) (hx : SepFree x) : splitAny x cur = [cur ++ x] := by
  have := splitAny_free x [] cur hx
  rw [List.append_nil] at this
  rw [this, splitAny.eq_1]

theorem digits_sepFree {x : GoString} (h : ∀ c ∈ x, isDigit c = true) : SepFree x := by
  intro c hc
  have hd := h c hc
  unfold isDigit at hd
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
  constructor
  · intro e
    have : c.toNat = 46 := by rw [e]; rfl
    omega
  · intro e
    have : c.toNat = 58 := by rw [e]; rfl
    omega

/-- **A valid address split at its dots and colon** is its five parts. -/
theorem addrOk_splitAny {a h p x1 x2 x3 x4 : GoString} {n1 n2 n3 n4 pt : Nat}
    (h58 : splitBy 58 a [] = [h, p]) (h46 : splitBy 46 h [] = [x1, x2, x3, x4])
    (d1 : decNat x1 = some n1) (d2 : decNat x2 = some n2) (d3 : decNat x3 = some n3)
    (d4 : decNat x4 = some n4) (dp : decNat p = some pt) :
    splitAny a [] = [x1, x2, x3, x4, p] := by
  rw [addrOk_join h58 h46]
  simp only [List.append_assoc, List.cons_append]
  rw [splitAny_sep _ _ _ 46 (Or.inl rfl) (digits_sepFree (decNat_digits d1))]
  simp only [List.nil_append]
  rw [splitAny_sep _ _ _ 46 (Or.inl rfl) (digits_sepFree (decNat_digits d2))]
  simp only [List.nil_append]
  rw [splitAny_sep _ _ _ 46 (Or.inl rfl) (digits_sepFree (decNat_digits d3))]
  simp only [List.nil_append]
  rw [splitAny_sep _ _ _ 58 (Or.inr rfl) (digits_sepFree (decNat_digits d4))]
  simp only [List.nil_append]
  rw [splitAny_last _ _ (digits_sepFree (decNat_digits dp))]
  simp

end EtcdGrove.raft_kvnet
end Perennial
