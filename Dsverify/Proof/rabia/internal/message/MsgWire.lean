/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/message/MsgWire.lean`, run `rabia-r1wake-1`.)

`Msg`'s encoding as a list of segments (one per field), and the records decoded so far
(`MsgV.upto`), for `(*Msg).Unmarshal`'s loop (prover C1).
-/
module

public import Dsverify.Proof.rabia.internal.message.Varint

@[expose] public section

namespace Perennial.rabia.model

theorem encScalar_ne_nil {t : w8} {n : Nat} (h : encScalar t n ≠ []) :
    encScalar t n = t :: varint n ∧ n ≠ 0 := by
  unfold encScalar at *; by_cases hn : n = 0 <;> simp_all

theorem encScalar_eq_nil {t : w8} {n : Nat} : encScalar t n = [] ↔ n = 0 := by
  unfold encScalar; by_cases hn : n = 0 <;> simp [hn]

theorem enumNat_lt (t : w32) : enumNat t < 2 ^ 64 := by
  unfold enumNat; exact BitVec.isLt _

theorem setWidth_signExtend32 (t : w32) : (BitVec.signExtend 64 t).setWidth 32 = t := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_signExtend, hi]
  omega

theorem ofNat_enumNat (t : w32) : BitVec.ofNat 32 (enumNat t) = t := by
  unfold enumNat
  have : BitVec.ofNat 32 (BitVec.signExtend 64 t).toNat = (BitVec.signExtend 64 t).setWidth 32 := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [this, setWidth_signExtend32]

theorem enumNat_eq_zero (t : w32) : enumNat t = 0 ↔ t = 0 := by
  constructor
  · intro h
    rw [← ofNat_enumNat t, h]; rfl
  · intro h; subst h; rfl

/-- The segments of `encMsg m`, one per field. -/
def msgSegs (m : MsgV) : List (List w8) :=
  [encScalar 0x08 (enumNat m.ty), encScalar 0x10 m.phase.toNat, encScalar 0x18 m.value.toNat,
   match m.obj with | none => [] | some o => encBytes 0x22 (encObj o)]

theorem msgSegs_length (m : MsgV) : (msgSegs m).length = 4 := rfl

theorem encMsg_flatten (m : MsgV) : encMsg m = (msgSegs m).flatten := by
  unfold encMsg msgSegs; cases m.obj <;> simp

/-- The fields before `s` of `m`, the others zero. -/
def MsgV.upto (m : MsgV) (s : Nat) : MsgV :=
  { ty := if 0 < s then m.ty else 0, phase := if 1 < s then m.phase else 0,
    value := if 2 < s then m.value else 0, obj := if 3 < s then m.obj else none }

theorem MsgV.upto_four (m : MsgV) : m.upto 4 = m := by
  simp [MsgV.upto]

theorem MsgV.upto_succ (m : MsgV) (i : Nat) (hi : i < 4) (h : (msgSegs m)[i]? = some []) :
    m.upto (i + 1) = m.upto i := by
  rcases m with ⟨ty, ph, va, ob⟩
  match i, hi with
  | 0, _ =>
    simp [msgSegs, encScalar_eq_nil, enumNat_eq_zero] at h
    simp [MsgV.upto, h]
  | 1, _ =>
    simp [msgSegs, encScalar_eq_nil] at h
    simp [MsgV.upto]; apply BitVec.eq_of_toNat_eq; simpa using h
  | 2, _ =>
    simp [msgSegs, encScalar_eq_nil] at h
    simp [MsgV.upto]; apply BitVec.eq_of_toNat_eq; simpa using h
  | 3, _ =>
    cases ob with
    | none => simp [MsgV.upto]
    | some o => simp [msgSegs, encBytes] at h

theorem MsgV.upto_of_empty (m : MsgV) (s j : Nat) (hsj : s ≤ j) (hj : j ≤ 4)
    (h : ∀ i, s ≤ i → i < j → (msgSegs m)[i]? = some []) : m.upto j = m.upto s := by
  induction j with
  | zero => have : s = 0 := by omega
            subst this; rfl
  | succ j ih =>
    by_cases hs : s = j + 1
    · subst hs; rfl
    · rw [m.upto_succ j (by omega) (h j (by omega) (by omega))]
      exact ih (by omega) (by omega) (fun i h1 h2 => h i h1 (by omega))

end Perennial.rabia.model
