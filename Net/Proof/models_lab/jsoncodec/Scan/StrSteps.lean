/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/jsoncodec/StrSteps.lean (lab master 915f964;
namespace `VsrJson` there).
-/
/-
`strL` (scanString's loop) one step at a time, on the suffix at an index (for the Go proof).
-/
module

public import Net.Proof.models_lab.jsoncodec.Scan.Def

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JsonScan

open Perennial

/-- After `\u`: `n` more hex digits, then the string goes on. -/
def hexR : Nat → List w8 → Nat → Nat × Nat
  | 0, l, k => strL l k
  | _ + 1, [], k => (1, k)
  | n + 1, h :: r, k => if !isHexB h then (2, k) else hexR n r (k + 1)

theorem drop_cons_of (bs : List w8) (j : Nat) (x : w8) (h : bs[j]? = some x) :
    bs.drop j = x :: bs.drop (j + 1) := by
  have hj : j < bs.length := by
    rcases Nat.lt_or_ge j bs.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  rw [List.drop_eq_getElem_cons hj]
  simp [List.getElem?_eq_getElem hj] at h
  rw [h]

variable (bs : List w8) (j : Nat)

theorem strL_end (h : bs.length ≤ j) : strL (bs.drop j) j = (1, j) := by
  rw [List.drop_eq_nil_of_le h]; simp [strL]

theorem strL_q (h : bs[j]? = some 34#8) : strL (bs.drop j) j = (0, j + 1) := by
  rw [drop_cons_of bs j _ h, strL.eq_def]; simp

theorem strL_ctl (c : w8) (h : bs[j]? = some c) (hq : c ≠ 34#8) (hc : c < 32#8) :
    strL (bs.drop j) j = (2, j) := by
  rw [drop_cons_of bs j _ h, strL.eq_def]; simp [hq, hc]

theorem strL_other (c : w8) (h : bs[j]? = some c) (hq : c ≠ 34#8) (hc : ¬ c < 32#8)
    (hb : c ≠ 92#8) : strL (bs.drop j) j = strL (bs.drop (j + 1)) (j + 1) := by
  rw [drop_cons_of bs j _ h, strL.eq_def]; simp [hq, hc, hb]

theorem strL_bs_end (h : bs[j]? = some 92#8) (h1 : bs.length ≤ j + 1) :
    strL (bs.drop j) j = (1, j) := by
  rw [drop_cons_of bs j _ h, strL.eq_def, List.drop_eq_nil_of_le h1]; simp

theorem strL_u (h : bs[j]? = some 92#8) (h1 : bs[j + 1]? = some 117#8) :
    strL (bs.drop j) j = hexR 4 (bs.drop (j + 2)) (j + 2) := by
  rw [drop_cons_of bs j _ h, drop_cons_of bs (j + 1) _ h1, strL.eq_def]
  simp only [show (92#8 : w8) ≠ 34#8 by decide, show ¬ (92#8 : w8) < 32#8 by decide, if_false,
    ite_false, if_true, ite_true, show j + 1 + 1 = j + 2 by omega]
  rcases bs.drop (j + 2) with _ | ⟨h1, r1⟩
  · simp [hexR]
  · simp only [hexR]
    rcases r1 with _ | ⟨h2, r2⟩
    · split <;> simp [hexR]
    · rcases r2 with _ | ⟨h3, r3⟩
      · split <;> simp [hexR] <;> split <;> simp
      · rcases r3 with _ | ⟨h4, r4⟩
        · split <;> simp [hexR] <;> split <;> simp [hexR] <;> split <;> simp
        · split <;> simp [hexR] <;> split <;> simp [hexR] <;> split <;> simp [hexR] <;>
            split <;> simp [hexR] <;> omega

theorem strL_esc (e : w8) (h : bs[j]? = some 92#8) (h1 : bs[j + 1]? = some e)
    (hu : e ≠ 117#8) (he : escB e = true) :
    strL (bs.drop j) j = strL (bs.drop (j + 2)) (j + 2) := by
  rw [drop_cons_of bs j _ h, drop_cons_of bs (j + 1) _ h1, strL.eq_def]
  simp [hu, he]

theorem strL_badesc (e : w8) (h : bs[j]? = some 92#8) (h1 : bs[j + 1]? = some e)
    (hu : e ≠ 117#8) (he : escB e = false) :
    strL (bs.drop j) j = (2, j) := by
  rw [drop_cons_of bs j _ h, drop_cons_of bs (j + 1) _ h1, strL.eq_def]
  simp [hu, he]

theorem hexR_end (n : Nat) (h : bs.length ≤ j) : hexR (n + 1) (bs.drop j) j = (1, j) := by
  rw [List.drop_eq_nil_of_le h]; simp [hexR]

theorem hexR_bad (n : Nat) (x : w8) (h : bs[j]? = some x) (hx : isHexB x = false) :
    hexR (n + 1) (bs.drop j) j = (2, j) := by
  rw [drop_cons_of bs j _ h]; simp [hexR, hx]

theorem hexR_ok (n : Nat) (x : w8) (h : bs[j]? = some x) (hx : isHexB x = true) :
    hexR (n + 1) (bs.drop j) j = hexR n (bs.drop (j + 1)) (j + 1) := by
  rw [drop_cons_of bs j _ h]; simp [hexR, hx]

theorem litL_done (lit : List w8) (k : Nat) (h : lit.length ≤ k) :
    litL (bs.drop j) j (lit.drop k) = (0, j) := by
  rw [List.drop_eq_nil_of_le h]
  cases bs.drop j <;> simp [litL]

theorem litL_more (lit : List w8) (k : Nat) (hk : k < lit.length) (h : bs.length ≤ j) :
    litL (bs.drop j) j (lit.drop k) = (1, j) := by
  rw [List.drop_eq_nil_of_le h, List.drop_eq_getElem_cons hk]; simp [litL]

theorem litL_bad (lit : List w8) (k : Nat) (hk : k < lit.length) (c : w8) (h : bs[j]? = some c)
    (hc : c ≠ lit[k]) : litL (bs.drop j) j (lit.drop k) = (2, j) := by
  rw [drop_cons_of bs j _ h, List.drop_eq_getElem_cons hk]; simp [litL, hc]

theorem litL_ok (lit : List w8) (k : Nat) (hk : k < lit.length) (h : bs[j]? = some lit[k]) :
    litL (bs.drop j) j (lit.drop k) = litL (bs.drop (j + 1)) (j + 1) (lit.drop (k + 1)) := by
  rw [drop_cons_of bs j _ h, List.drop_eq_getElem_cons hk]; simp [litL]

end JsonScan
