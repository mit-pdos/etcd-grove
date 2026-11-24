/-
The proof of `valid` (`Spec/encoding/json/Codec/valid.lean`): the codec's `Scan` (`scanOk F`) gives
where the value ends, `n`; then `skipSpace` of `data[n:]` reaches its end exactly when every byte
after the value is whitespace (`leadSpace_eq_length`).
-/
module

public import Spec.encoding.json.Codec.valid
public import Spec.encoding.json.Codec.skipSpace

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace encoding.json

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.json.Assumptions]

/-- `leadSpace l` is `l`'s length exactly when every byte of `l` is whitespace. -/
theorem leadSpace_eq_length (l : List w8) :
    leadSpace l = l.length ↔ ∀ c ∈ l, isSpaceB c = true := by
  unfold leadSpace
  induction l with
  | nil => simp
  | cons c t ih =>
    by_cases hc : isSpaceB c = true
    · simp [hc, ih]
    · simp [hc]

/-- The value's end `n` (at most the input's length, a slice's length) as a signed index. -/
theorem valid_arith (n len : w64) (k : Nat) (hn : uint.nat n ≤ k) (hlen : k = sint.nat len)
    (hlen0 : 0 ≤ sint.Z len) :
    0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z len ∧ sint.nat n = uint.nat n := by
  subst hlen
  have h1 : (uint.nat n : Int) ≤ sint.Z len :=
    Int.le_trans (Int.ofNat_le.mpr hn) (Int.le_of_eq (Int.toNat_of_nonneg hlen0))
  have hz : sint.Z n = uint.Z n := by word
  refine ⟨by rw [hz]; word, by rw [hz]; word, ?_⟩
  show (BitVec.toInt n).toNat = BitVec.toNat n
  rw [show BitVec.toInt n = (BitVec.toNat n : Int) from hz]
  simp

/-- `leadSpace` is at most the list's length. -/
theorem leadSpace_le (l : List w8) : leadSpace l ≤ l.length := by
  unfold leadSpace; exact (List.takeWhile_prefix _).length_le

/-- The comparison `valid` returns is `jsonValid`, once the scanner found a complete value. -/
theorem valid_eq (F : List w8 → Bool → w64 × w64) (bs : List w8) (len : w64)
    (hF : (F bs true).1 = W64 0) (hn : uint.nat (F bs true).2 ≤ bs.length)
    (hlen : bs.length = sint.nat len) (hlen0 : 0 ≤ sint.Z len) :
    decide (W64 (leadSpace (bs.drop (sint.nat (F bs true).2))) = len - (F bs true).2) =
      decide (models_lab.jsoncodec.jsonValid F bs) := by
  obtain ⟨-, -, hnn⟩ := valid_arith (F bs true).2 len bs.length hn hlen hlen0
  rw [hnn]
  generalize hm : (F bs true).2 = m at hn ⊢
  have hjv : models_lab.jsoncodec.jsonValid F bs ↔
      ∀ c ∈ bs.drop (uint.nat m), isSpaceB c = true := by
    unfold models_lab.jsoncodec.jsonValid
    rw [hm]
    constructor
    · rintro ⟨-, -, h3⟩; intro c hc; rw [isSpaceB_spaceB]; exact h3 c hc
    · intro h3; exact ⟨hF, hn, fun c hc => by rw [← isSpaceB_spaceB]; exact h3 c hc⟩
  have hle := leadSpace_le (bs.drop (uint.nat m))
  have hlt : bs.length < 2 ^ 63 := by
    have h3 : ((bs.length : Nat) : Int) = BitVec.toInt len := by
      rw [hlen]; exact Int.toNat_of_nonneg hlen0
    have : BitVec.toInt len < 2 ^ 63 := by word
    omega
  have hw : W64 (leadSpace (bs.drop (uint.nat m)) : Int) = len - m ↔
      leadSpace (bs.drop (uint.nat m)) = (bs.drop (uint.nat m)).length := by
    rw [List.length_drop]
    have hl : (bs.length : Int) = sint.Z len := by
      rw [hlen]; exact Int.toNat_of_nonneg hlen0
    constructor
    · intro h
      have := congrArg uint.Z h
      simp only [List.length_drop] at hle
      word
    · intro h
      rw [h]
      word
  rw [← leadSpace_eq_length] at hjv
  simp only [hw, hjv]

theorem valid.wp_proof (wp_skipSpace : skipSpace.spec (GF := GF) (hG := hG)) :
    valid.spec (GF := GF) (hG := hG) := by
  intro F c data dq bs
  wp_start as ⟨#HS, #Hscan, Hs⟩
  unfold models_lab.jsoncodec.scanOk
  icases Hscan with ⟨%HF, #Hscan⟩
  wp_auto
  wp_apply Hscan $$ Hs
  iintro Hs
  wp_auto
  have hn := HF bs true
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
  obtain ⟨hn0, hnl, hnn⟩ := valid_arith (F bs true).2 data.len bs.length hn Hlen.1 Hlen.2
  wp_if_destruct
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hn0, hnl, Hwf.2⟩)]
    ihave ⟨Hpre, Hrest⟩ := (ownSlice_split_all (F bs true).2 data dq bs ⟨hn0, hnl⟩).1 $$ Hs
    wp_apply wp_skipSpace $$ Hrest as Hrest
    rw [valid_eq F bs data.len (by simpa using Hif) hn Hlen.1 Hlen.2]
    iapply HΦ
    iapply (ownSlice_split_all (F bs true).2 data dq bs ⟨hn0, hnl⟩).2
    iframe
  · have hd : decide (models_lab.jsoncodec.jsonValid F bs) = false :=
      decide_eq_false (fun h => Hif h.1)
    rw [hd]
    iapply HΦ $$ Hs

end proof

end encoding.json
end Perennial
