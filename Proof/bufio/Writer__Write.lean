/-
`(*bufio.Writer).Write` (see `Spec/bufio/Writer__Write.lean`). Ported from dsverify-lab's
`Harness/Proof/bufio/Writer.lean` (`wp_Write`).
-/
module

public import Spec.bufio.Writer__Write
public import Spec.bufio.Writer__Flush

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

set_option hygiene false in
/-- The end of `Write` with a sticky error `ok ei`: return it. -/
local macro "write_err_tail" : tactic => `(tactic| (
  wp_auto
  ihave Hp := Hpback $$ Hpc
  ihave #HQ0 := bufio.Q_of_prefix Q (sent0 ++ pend0) (sent ++ pend ++ ps)
    (by rw [hsent]; exact (List.prefix_append_right_inj _).mpr (List.take_prefix _ _))
    $$ HQpc HQall
  iapply HΦ
  iexists j, sent0, pend0
  iframe Hp
  isplitr
  · ipureintro
    exact ⟨hnnv, hj, hsent, hpre, fun h => absurd h (by simp), herr⟩
  iunfold bufio.ownBufWriter, bufio.writerRep
  iframe Hpkg Hwr HJ HQ0
  iexists buf0, n0, rest0
  iframe Hb Hbuf Herr0
  ipureintro; exact ⟨hn0, hlen0⟩))

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.bufio.Assumptions]

set_option goose.wp.extras true

theorem bufio.Writer.Write.wp_proof
    (wp_Flush : bufio.Writer.Flush.spec (GF := GF) (hG := hG)) :
    bufio.Writer.Write.spec (GF := GF) (hG := hG) := by
  intro bw wi J Q Ew sent pend err p dq ps
  wp_start as ⟨Hown, #HQall, Hp⟩
  iunfold bufio.ownBufWriter at Hown
  icases Hown with ⟨#Hpkg, #Hwr, HJ, -, Hrep⟩
  iunfold bufio.writerRep at Hrep
  icases Hrep with ⟨%buf, %n, %rest, Hb, Hbuf, %Hn, #Herr⟩
  ihave #HQpc := io.writerOk_prefixClosed $$ Hwr
  iunfold io.prefixClosed at HQpc
  ihave %Hplen := ownSlice_len _ _ _ $$ Hp
  have hp63 : sint.Z p.len < 2 ^ 63 := by word
  have hpl : (ps.length : Int) = sint.Z p.len := by
    rw [Hplen.1]; exact Int.toNat_of_nonneg Hplen.2
  wp_auto
  ihave HL : (∃ (j : Nat) (nnv : w64) (pc : GoSlice) (sent0 pend0 rest0 : List w8)
      (buf0 : GoSlice) (n0 : w64) (err0 : GoInterface),
      "nn" ∷ nn_ptr ↦ nnv ∗ "p" ∷ p_ptr ↦ pc ∗ "Hpc" ∷ pc ↦*{dq} ps.drop j ∗
      "Hpback" ∷ (pc ↦*{dq} ps.drop j -∗ p ↦*{dq} ps) ∗ "HJ" ∷ J sent0 ∗
      "Hb" ∷ bw ↦ _root_.Perennial.bufio.Writer.mk err0 buf0 n0 (interface.ok wi) ∗
      "Hbuf" ∷ buf0 ↦* (pend0 ++ rest0) ∗ "#Herr0" ∷ io.werrAt Ew err0 ∗
      "%Hinv" ∷ ⌜sint.Z nnv = j ∧ j ≤ ps.length ∧ sint.Z n0 = pend0.length ∧
        0 < (pend0 ++ rest0).length ∧ sent0 ++ pend0 = sent ++ pend ++ ps.take j ∧
        sent <+: sent0 ∧ (err ≠ interface.nil → err0 = err ∧ j = 0)⌝ : IProp GF)
    $$ [nn p Hp HJ Hb Hbuf]
  · iexists 0, _, p, sent, pend, rest, buf, n, err
    simp only [List.drop_zero, List.take_zero, List.append_nil]
    iframe nn p Hp HJ Hb Hbuf Herr
    isplitr
    · iintro H; iexact H
    ipureintro
    exact ⟨by first | rfl | trivial, Nat.zero_le _, Hn.1, Hn.2, by first | rfl | trivial,
      List.prefix_refl _, fun _ => ⟨by first | rfl | trivial, by first | rfl | trivial⟩⟩
  clear Hn
  wp_for HL
  obtain ⟨hnn, hj, hn0, hlen0, hsent, hpre, herr⟩ := Hinv
  ihave %Hpcl := ownSlice_len _ _ _ $$ Hpc
  ihave %Hl0 := ownSlice_len _ _ _ $$ Hbuf
  have hpcl : ((ps.drop j).length : Int) = sint.Z pc.len := by
    rw [Hpcl.1]; exact Int.toNat_of_nonneg Hpcl.2
  have hl0 : ((pend0 ++ rest0).length : Int) = sint.Z buf0.len := by
    rw [Hl0.1]; exact Int.toNat_of_nonneg Hl0.2
  simp only [List.length_append, List.length_drop] at hl0 hpcl
  have hb63 : sint.Z buf0.len < 2 ^ 63 := by word
  wp_apply bufio.wp_Writer_Available $$ Hb as Hb
  have hav : sint.Z (buf0.len - n0) = rest0.length := by word
  have hnnv : nnv = W64 j := by
    apply BitVec.eq_of_toInt_eq
    show sint.Z nnv = sint.Z (W64 j)
    rw [hnn, bufio.sint_Z_W64_length (by omega)]
  wp_if_destruct
  · -- more than fits
    have hmore : rest0.length < ps.length - j := by omega
    rcases err0 with ei | _
    · -- a sticky error: done
      wp_auto
      simp only [goose_wp_simp_extra, Bool.false_eq_true, ↓reduceIte]
      write_err_tail
    wp_auto
    simp only [goose_wp_simp_extra, ↓reduceIte]
    wp_auto
    ihave %Hpwf := ownSlice_wf _ _ _ $$ Hpc
    wp_apply bufio.wp_Writer_Buffered $$ Hb as Hb
    wp_if_destruct
    · -- nothing buffered: write `p` directly
      have hp0 : pend0 = [] := List.eq_nil_of_length_eq_zero (by
        have : sint.Z (W64 0) = 0 := rfl
        omega)
      subst hp0
      simp only [List.append_nil] at hsent
      ihave #HQw := bufio.Q_of_prefix Q (sent0 ++ ps.drop j) (sent ++ pend ++ ps)
        (by rw [hsent, List.append_assoc (sent ++ pend), List.take_append_drop]
            exact List.prefix_refl _) $$ HQpc HQall
      wp_apply io.wp_writer_Write wi J Q Ew sent0 pc dq (ps.drop j) $$ [$Hwr $HJ $HQw $Hpc]
        as %nw %err2 ⟨%k, %Hk, Hpc, HJ, #Herr2⟩
      obtain ⟨rfl, Hk⟩ := Hk
      have hdl : (ps.drop j).length = ps.length - j := List.length_drop
      have hkZ : sint.Z (W64 k) = k := bufio.sint_Z_W64_length (by omega)
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega, by omega⟩)]
      ihave ⟨-, Hpc, Hpback⟩ := bufio.slice_advance pc dq ps j k Hk.1 _ $$ [$Hpc $Hpback]
      wp_auto
      wp_for_post
      isimp at Hb
      iframe
      iexists j + k, _, _, sent0 ++ (ps.drop j).take k, [], rest0, buf0, _, err2
      simp only [List.append_nil, List.nil_append]
      iframe Hpc Hpback HJ Hb Hbuf Herr2 nn p
      ipureintro
      refine ⟨by word, by omega, hn0, hlen0, ?_, hpre.trans (List.prefix_append _ _),
        fun h => absurd (herr h).1.symm h⟩
      rw [hsent, List.take_add, List.append_assoc]
    -- something buffered: fill the buffer, flush it
    have hp0 : 0 < pend0.length := by
      rcases Nat.eq_zero_or_pos pend0.length with h | h
      · exfalso; apply Hif; apply BitVec.eq_of_toInt_eq
        show sint.Z n0 = sint.Z (W64 0)
        rw [hn0, h]; rfl
      · exact h
    have hdl : (ps.drop j).length = ps.length - j := List.length_drop
    ihave %Hbwf := ownSlice_wf _ _ _ $$ Hbuf
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega, Hbwf.2⟩)]
    ihave ⟨%Hsz, Hsuf, Hbback⟩ := bufio.suffix_acc buf0 n0 pend0 rest0 hn0 $$ Hbuf
    wp_auto
    wp_apply wp_slice_copy_int (V := w8) (slice.slice buf0 w8 n0 buf0.len) rest0 pc (ps.drop j) dq
      $$ [$Hsuf $Hpc] as %m ⟨%Hm, Hsuf, Hpc⟩
    have hdrop : rest0.drop (ps.drop j).length = [] := List.drop_eq_nil_of_le (by omega)
    rw [hdrop, List.append_nil]
    have hmr : sint.Z m = rest0.length := by rw [Hm, Nat.min_eq_left (by omega)]
    ihave Hbuf := Hbback $$ %_ %(by simp; omega) Hsuf
    isimp at Hb
    have hXl : ((ps.drop j).take rest0.length).length = rest0.length := by simp; omega
    have hX : sent0 ++ (pend0 ++ (ps.drop j).take rest0.length) =
        sent ++ pend ++ ps.take (j + rest0.length) := by
      rw [← List.append_assoc, hsent, List.take_add, List.append_assoc]
    ihave #HQ1 := bufio.Q_of_prefix Q (sent0 ++ (pend0 ++ (ps.drop j).take rest0.length))
      (sent ++ pend ++ ps)
      (by rw [hX]; exact (List.prefix_append_right_inj _).mpr (List.take_prefix _ _))
      $$ HQpc HQall
    wp_apply wp_Flush bw wi J Q Ew sent0 (pend0 ++ (ps.drop j).take rest0.length)
      interface.nil $$ [HJ Hb Hbuf] as %e1 ⟨%k1, %Hk1, Hown⟩
    · iunfold bufio.ownBufWriter, bufio.writerRep
      iframe Hpkg Hwr HJ HQ1
      iexists buf0, _, []
      rw [List.append_nil]
      iframe Hb Hbuf Herr0
      ipureintro
      constructor
      · simp only [List.length_append, hXl]; word
      · simp; omega
    have hmW : m = W64 rest0.length := by
      apply BitVec.eq_of_toInt_eq
      show sint.Z m = sint.Z (W64 rest0.length)
      rw [hmr, bufio.sint_Z_W64_length (by omega)]
    subst hmW
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega, by omega⟩)]
    ihave ⟨-, Hpc, Hpback⟩ := bufio.slice_advance pc dq ps j rest0.length (by omega) _
      $$ [$Hpc $Hpback]
    wp_auto
    wp_for_post
    iunfold bufio.ownBufWriter, bufio.writerRep at Hown
    icases Hown with ⟨-, -, HJ, -, %buf', %n', %rest', Hb, Hbuf, %Hn', #Herr'⟩
    iframe
    iexists j + rest0.length, _, _, sent0 ++ (pend0 ++ (ps.drop j).take rest0.length).take k1,
      (pend0 ++ (ps.drop j).take rest0.length).drop k1, rest', buf', n', e1
    iframe Hpc Hpback HJ Hb Hbuf Herr' nn p
    ipureintro
    refine ⟨by word, by omega, Hn'.1, Hn'.2, ?_, hpre.trans (List.prefix_append _ _),
      fun h => absurd (herr h).1.symm h⟩
    rw [List.append_assoc, List.take_append_drop, hX]
  -- it fits
  (try simp only [goose_wp_simp_extra, Bool.false_eq_true, ↓reduceIte])
  (try wp_for_post)
  rcases err0 with ei | _
  · write_err_tail
  have hfits : ps.length - j ≤ rest0.length := by omega
  have hdl : (ps.drop j).length = ps.length - j := List.length_drop
  wp_auto
  ihave %Hbwf := ownSlice_wf _ _ _ $$ Hbuf
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega, Hbwf.2⟩)]
  ihave ⟨%Hsz, Hsuf, Hbback⟩ := bufio.suffix_acc buf0 n0 pend0 rest0 hn0 $$ Hbuf
  wp_auto
  wp_apply wp_slice_copy_int (V := w8) (slice.slice buf0 w8 n0 buf0.len) rest0 pc (ps.drop j) dq
    $$ [$Hsuf $Hpc] as %m ⟨%Hm, Hsuf, Hpc⟩
  have hmr : sint.Z m = ps.length - j := by
    rw [Hm, Nat.min_eq_right (by omega), hdl]; omega
  have htk : (ps.drop j).take rest0.length = ps.drop j := List.take_of_length_le (by omega)
  rw [htk]
  ihave Hbuf := Hbback $$ %_ %(by simp; omega) Hsuf
  (try wp_auto)
  isimp at Hb
  ihave Hp := Hpback $$ Hpc
  have hfin : sent0 ++ (pend0 ++ ps.drop j) = sent ++ pend ++ ps := by
    rw [← List.append_assoc, hsent, List.append_assoc (sent ++ pend), List.take_append_drop]
  ihave #HQf := bufio.Q_of_prefix Q (sent0 ++ (pend0 ++ ps.drop j)) (sent ++ pend ++ ps)
    (by rw [hfin]; exact List.prefix_refl _) $$ HQpc HQall
  iapply HΦ
  iexists ps.length, sent0, pend0 ++ ps.drop j
  iframe Hp
  isplitr
  · ipureintro
    refine ⟨?_, Nat.le_refl _, by rw [List.take_length, ← hfin], hpre,
      fun _ => rfl, fun h => absurd (herr h).1.symm h⟩
    apply BitVec.eq_of_toInt_eq
    show sint.Z (nnv + m) = sint.Z (W64 ps.length)
    rw [bufio.sint_Z_W64_length (by omega)]
    word
  iunfold bufio.ownBufWriter, bufio.writerRep
  iframe Hpkg Hwr HJ HQf
  iexists buf0, _, rest0.drop (ps.drop j).length
  rw [List.append_assoc pend0]
  iframe Hb Hbuf Herr0
  ipureintro
  constructor
  · simp only [List.length_append, hdl]; word
  · simp only [List.length_append, List.length_drop] at hlen0 ⊢; omega

end proof

end EtcdGrove
end Perennial
