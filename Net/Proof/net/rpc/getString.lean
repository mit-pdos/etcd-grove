/-
The proof of `getString` (`Net/Spec/net/rpc/getString.lean`): the length read off the first 8
bytes (`getU64`), checked against what follows, then the string converted from `p[8:8+n]` and
`p[8+n:]` returned (the payload's points-to split at `8` and `8+n`: `ownSlice_slice`).
-/
module

public import Net.Spec.net.rpc.getString
public import Net.Spec.net.rpc.getU64

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.rpc

/-- A payload that decodes as a string starts with its length. -/
theorem strEnc_head {bs : List w8} {s : GoString} {r : List w8} (h : bs = strEnc s ++ r) :
    leToU64 (bs.take 8) = W64 s.length ∧ bs.length = 8 + s.length + r.length := by
  subst h
  refine ⟨?_, by simp [strEnc_length]⟩
  simp only [strEnc, List.append_assoc]
  rw [List.take_left' (by simp [u64Le_length]), u64Le_to_word]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions]

theorem getString.wp_proof (wp_getU64 : getU64.spec (GF := GF) (hG := hG)) :
    getString.spec (GF := GF) (hG := hG) := by
  intro p dq bs
  wp_start as Hp
  ihave %Hlen := ownSlice_len _ _ _ $$ Hp
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hp
  wp_auto
  wp_if_destruct
  · -- shorter than 8 bytes
    rename_i Hif
    iapply HΦ
    simp only [Bool.false_eq_true, ite_false]
    ipureintro
    rintro ⟨s', r, rfl⟩
    have h8 : (BitVec.ofInt 64 8).toInt = 8 := by decide
    simp [strEnc_length] at Hlen
    simp only [h8] at Hif
    have : sint.nat p.len = (sint.Z p.len).toNat := rfl
    omega
  have hb8 : 8 ≤ bs.length := by word
  rw [← List.take_append_drop 8 bs]
  wp_apply wp_getU64 p dq (bs.take 8) (bs.drop 8) (by simp; omega) $$ Hp as Hp
  rw [List.take_append_drop]
  wp_if_destruct
  · -- the length goes beyond the payload
    rename_i Hif
    iapply HΦ
    simp only [Bool.false_eq_true, ite_false]
    ipureintro
    rintro ⟨s', r, h⟩
    obtain ⟨h1, h2⟩ := strEnc_head h
    rw [h1] at Hif
    have hs : s'.length < 2 ^ 63 := by word
    word
  -- the string and the rest
  generalize hn : leToU64 (List.take 8 bs) = n at *
  have hb : 0 ≤ sint.Z (W64 8) ∧ sint.Z (W64 8) ≤ sint.Z (W64 8 + n) ∧
      sint.Z (W64 8 + n) ≤ sint.Z p.len := by
    have : sint.nat p.len = (sint.Z p.len).toNat := rfl
    word
  rw [ite_eq_left ⟨hb.1, hb.2.1, Int.le_trans hb.2.2 Hwf.2⟩]
  icases (ownSlice_slice (W64 8) (W64 8 + n) p dq bs hb).1 $$ Hp with ⟨H0, Hmid, Hrest⟩
  wp_apply wp_bytes_to_string _ _ dq $$ Hmid as Hmid
  rw [ite_eq_left ⟨Int.le_trans hb.1 hb.2.1, hb.2.2, Hwf.2⟩]
  wp_auto
  iapply HΦ
  simp only [ite_true]
  iexists bs.drop (sint.nat (W64 8 + n))
  iframe Hrest
  ipureintro
  have h8 : sint.nat (W64 8) = 8 := by decide
  have hlen8 : (List.take 8 bs).length = 8 := by simp; omega
  have hsl : (subslice 8 (sint.nat (W64 8 + n)) bs).length = uint.nat n := by
    simp only [subslice, List.length_drop, List.length_take]
    have : sint.nat p.len = (sint.Z p.len).toNat := rfl
    word
  have hW : (W64 (subslice 8 (sint.nat (W64 8 + n)) bs).length : w64) = n := by
    rw [hsl]; word
  have hk : 8 ≤ sint.nat (W64 8 + n) ∧ sint.nat (W64 8 + n) ≤ bs.length := by
    have : sint.nat p.len = (sint.Z p.len).toNat := rfl
    have : sint.nat (W64 8 + n) = (sint.Z (W64 8 + n)).toNat := rfl
    have : sint.Z (W64 8) = 8 := by decide
    omega
  rw [strEnc, hW, ← hn, leToU64_le _ hlen8, List.append_assoc, subslice]
  conv => lhs; rw [← List.take_append_drop (sint.nat (W64 8 + n)) bs,
    ← List.take_append_drop 8 (List.take (sint.nat (W64 8 + n)) bs)]
  rw [List.take_take, Nat.min_eq_left hk.1, List.append_assoc, hn]

end proof

end net.rpc
end Perennial
