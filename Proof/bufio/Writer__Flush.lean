/-
`(*bufio.Writer).Flush` (see `Spec/bufio/Writer__Flush.lean`). Ported from dsverify-lab's
`Harness/Proof/bufio/Writer.lean` (`wp_Flush`).
-/
module

public import Spec.bufio.Writer__Flush

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

set_option hygiene false in
/-- The end of `Flush` after a failed write of `k` bytes (`Hst`: the unsent bytes at the front
of the buffer). -/
local macro "flush_tail" : tactic => `(tactic| (
  icases Hst with ⟨%rest', Hbuf, %Hr'⟩
  (try wp_auto)
  isimp at Hb
  iapply HΦ
  iexists k
  isplitr
  · ipureintro; exact ⟨Hk.1, by simp, by simp⟩
  iunfold bufio.ownBufWriter, bufio.writerRep
  rw [List.append_assoc sent, List.take_append_drop]
  iframe Hpkg Hwr HJ HQ
  iexists buf, _, rest'
  iframe Hb Hbuf Herr2
  ipureintro
  constructor
  · simp only [List.length_drop]; word
  · rw [Hr']; exact Hn.2))

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.bufio.Assumptions]

set_option goose.wp.extras true

theorem bufio.Writer.Flush.wp_proof : bufio.Writer.Flush.spec (GF := GF) (hG := hG) := by
  intro bw wi J Q Ew sent pend err
  wp_start as Hown
  iunfold bufio.ownBufWriter at Hown
  icases Hown with ⟨#Hpkg, #Hwr, HJ, #HQ, Hrep⟩
  iunfold bufio.writerRep at Hrep
  icases Hrep with ⟨%buf, %n, %rest, Hb, Hbuf, %Hn, #Herr⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hbuf
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hbuf
  have h63 : sint.Z buf.len < 2 ^ 63 := by word
  have hl : ((pend ++ rest).length : Int) = sint.Z buf.len := by
    rw [Hlen.1]; exact Int.toNat_of_nonneg Hlen.2
  simp only [List.length_append] at hl
  rcases err with ei | _
  · -- a sticky error: return it
    wp_auto
    iapply HΦ
    iexists 0
    simp only [List.take_zero, List.append_nil, List.drop_zero]
    isplitr
    · ipureintro; simp
    iunfold bufio.ownBufWriter, bufio.writerRep
    iframe Hpkg Hwr HJ HQ
    iexists buf, n, rest
    iframe Hb Hbuf Herr
    ipureintro; exact Hn
  wp_auto
  wp_if_destruct
  · -- nothing buffered
    have hp : pend = [] := List.eq_nil_of_length_eq_zero (by
      have : sint.Z (W64 0) = 0 := rfl
      omega)
    subst hp
    iapply HΦ
    iexists 0
    simp only [List.take_zero, List.append_nil, List.drop_nil]
    isplitr
    · ipureintro; simp
    iunfold bufio.ownBufWriter, bufio.writerRep
    simp only [List.append_nil]
    iframe Hpkg Hwr HJ HQ
    iexists buf, _, rest
    iframe Hb Hbuf Herr
    ipureintro; exact Hn
  have hW0 : sint.Z (W64 0) = 0 := rfl
  have hn0 : sint.nat (W64 0) = 0 := rfl
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega, by omega⟩)]
  ihave ⟨Hsub, Hback⟩ := bufio.ownSlice_sub_acc (V := w8) (W64 0) n buf (DFrac.own 1)
    (pend ++ rest) ⟨by omega, by omega, by omega⟩ $$ Hbuf
  have hsub : subslice (sint.nat (W64 0)) (sint.nat n) (pend ++ rest) = pend := by
    rw [subslice_def, hn0, List.drop_zero,
      show sint.nat n = pend.length by show (sint.Z n).toNat = _; omega, List.take_left]
  rw [hsub]
  wp_auto
  wp_apply io.wp_writer_Write wi J Q Ew sent _ _ pend $$ [$Hwr $HJ $HQ $Hsub]
    as %nw %err2 ⟨%k, %Hk, Hsub, HJ, #Herr2⟩
  obtain ⟨rfl, Hk⟩ := Hk
  ihave Hbuf := Hback $$ Hsub
  have hpl : pend.length < 2 ^ 63 := by omega
  have hkZ : sint.Z (W64 k) = k := bufio.sint_Z_W64_length (by omega)
  rcases err2 with ei | _
  · -- an error: keep the unsent bytes, the error sticks
    have hn : sint.nat n = pend.length := by show (sint.Z n).toNat = _; omega
    have hk' : sint.nat (W64 k) = k := by show (sint.Z (W64 k)).toNat = _; omega
    wp_if_destruct
    all_goals
      wp_if_destruct
      · wp_if_destruct
        · -- `0 < n < b.n`: move the unsent bytes to the front
          have hnkZ : sint.Z (n - W64 k) = pend.length - k := by word
          have hnk : sint.nat (n - W64 k) = pend.length - k := by
            show (sint.Z (n - W64 k)).toNat = _; omega
          rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega, by omega⟩)]
          wp_auto
          rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega, by omega⟩)]
          wp_apply wp_slice_copy_within (V := w8) buf (pend ++ rest) (W64 0) (n - W64 k) (W64 k) n
            ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩ $$ Hbuf as %m ⟨-, Hbuf⟩
          ihave Hst : (∃ rest' : List w8, buf ↦* (pend.drop k ++ rest') ∗
              ⌜(pend.drop k ++ rest').length = (pend ++ rest).length⌝ : IProp GF) $$ [Hbuf]
          · iexists (pend ++ rest).drop (pend.length - k)
            rw [hn, hk', hnk]
            (try rw [hn0])
            rw [bufio.flush_shift pend rest k Hk.1]
            iframe Hbuf
            ipureintro; simp; omega
          flush_tail
        · -- `n = b.n`: nothing left
          ihave Hst : (∃ rest' : List w8, buf ↦* (pend.drop k ++ rest') ∗
              ⌜(pend.drop k ++ rest').length = (pend ++ rest).length⌝ : IProp GF) $$ [Hbuf]
          · iexists pend ++ rest
            rw [List.drop_eq_nil_of_le (by omega), List.nil_append]
            iframe Hbuf
            ipureintro; rfl
          flush_tail
      · -- `n = 0`: nothing sent
        have hk0 : k = 0 := by omega
        ihave Hst : (∃ rest' : List w8, buf ↦* (pend.drop k ++ rest') ∗
            ⌜(pend.drop k ++ rest').length = (pend ++ rest).length⌝ : IProp GF) $$ [Hbuf]
        · iexists rest
          rw [hk0, List.drop_zero]
          iframe Hbuf
          ipureintro; rfl
        flush_tail
  -- all sent
  have hk : k = pend.length := Hk.2 rfl
  subst hk
  have hnk : ¬ sint.Z (W64 pend.length) < sint.Z n := by omega
  simp only [decide_eq_false hnk]
  wp_auto
  isimp at Hb
  iapply HΦ
  iexists pend.length
  simp only [List.take_length, List.drop_length]
  isplitr
  · ipureintro; simp
  iunfold bufio.ownBufWriter, bufio.writerRep
  simp only [List.append_nil]
  iframe Hpkg Hwr HJ HQ
  iexists buf, _, pend ++ rest
  simp only [List.nil_append]
  iframe Hb Hbuf Herr
  ipureintro; exact ⟨rfl, Hn.2⟩

end proof

end EtcdGrove
end Perennial
