/-
`(*bufio.Writer).WriteByte` (see `Spec/bufio/Writer__WriteByte.lean`). Ported from dsverify-lab's
`Harness/Proof/bufio/Writer.lean` (`wp_WriteByte`).
-/
module

public import Spec.bufio.Writer__WriteByte
public import Spec.bufio.Writer__Flush

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

set_option hygiene false in
/-- The end of `WriteByte`: store `c` after the buffered bytes `pend0` (`Hn0`, `Hr0`: room
left; `Hpre`, `Heq`: `sent0 ++ pend0` is what was written). -/
local macro "writebyte_tail" sent0:term:max pend0:term:max rest0:term:max buf0:term:max
    n0:term:max : tactic => `(tactic| (
  ihave %Hl0 := ownSlice_len _ _ _ $$ Hbuf
  have hl0 : (($pend0 ++ $rest0).length : Int) = sint.Z ($buf0).len := by
    rw [Hl0.1]; exact Int.toNat_of_nonneg Hl0.2
  simp only [List.length_append] at hl0
  have hrl : 0 < ($rest0).length := List.length_pos_iff.mpr Hr0
  (try wp_auto)
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
  wp_apply wp_store_slice_index $buf0 (sint.Z $n0) ($pend0 ++ $rest0) c $$ [Hbuf] as Hbuf
  · iframe Hbuf; ipureintro; simp; omega
  rw [show (sint.Z $n0).toNat = ($pend0).length by omega, bufio.set_after $pend0 $rest0 c Hr0]
  (try isimp at Hb)
  iapply HΦ
  iexists $sent0, $pend0 ++ [c]
  isplitr
  · ipureintro
    exact ⟨Hpre, fun _ => by rw [← List.append_assoc, Heq], fun h => absurd rfl h, by simp,
      fun hf => ⟨rfl, hfitS hf.2⟩⟩
  iunfold bufio.ownBufWriter, bufio.writerRep
  rw [show $sent0 ++ ($pend0 ++ [c]) = sent ++ pend ++ [c] by rw [← List.append_assoc, Heq]]
  iframe Hpkg Hwr HJ HQc
  iexists $buf0, _, ($rest0).tail
  iframe Hb Hbuf Herr
  ipureintro
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton]; word
  · simp; omega
  · simp only [List.length_append, List.length_singleton, List.length_tail] at Hsz0 ⊢; omega))

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.bufio.Assumptions]

set_option goose.wp.extras true

theorem bufio.Writer.WriteByte.wp_proof
    (wp_Flush : bufio.Writer.Flush.spec (GF := GF) (hG := hG)) :
    bufio.Writer.WriteByte.spec (GF := GF) (hG := hG) := by
  intro bw wi J Q Ew sz sent pend err c
  wp_start as ⟨Hown, HQw⟩
  ihave #HQall := bufio.wand_pure_persistent _ _ $$ HQw
  iunfold bufio.ownBufWriter at Hown
  icases Hown with ⟨#Hpkg, #Hwr, HJ, #HQ, Hrep⟩
  iunfold bufio.writerRep at Hrep
  icases Hrep with ⟨%buf, %n, %rest, Hb, Hbuf, %Hn, #Herr⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hbuf
  have h63 : sint.Z buf.len < 2 ^ 63 := by word
  have hl : ((pend ++ rest).length : Int) = sint.Z buf.len := by
    rw [Hlen.1]; exact Int.toNat_of_nonneg Hlen.2
  simp only [List.length_append] at hl
  rcases err with ei | _
  · -- a sticky error: return it
    wp_auto
    iapply HΦ
    iexists sent, pend
    isplitr
    · ipureintro; simp
    iunfold bufio.ownBufWriter, bufio.writerRep
    iframe Hpkg Hwr HJ HQ
    iexists buf, n, rest
    iframe Hb Hbuf Herr
    ipureintro; exact Hn
  ihave #HQc := HQall $$ %rfl
  wp_auto
  wp_apply bufio.wp_Writer_Available $$ Hb as Hb
  have hW0 : sint.Z (W64 0) = 0 := rfl
  have hav : sint.Z (buf.len - n) = rest.length := by word
  wp_if_destruct
  · -- the buffer is full: flush it
    have hr : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hr
    wp_apply wp_Flush bw wi J Q Ew sz sent pend interface.nil $$ [HJ Hb Hbuf]
      as %e' ⟨%k, %Hk, Hown⟩
    · iunfold bufio.ownBufWriter, bufio.writerRep
      iframe Hpkg Hwr HJ HQ
      iexists buf, n, []
      iframe Hb Hbuf Herr
      ipureintro; exact Hn
    rcases e' with ei | _
    · -- the flush failed: return the error
      iunfold bufio.ownBufWriter, bufio.writerRep at Hown
      icases Hown with ⟨-, -, HJ, #HQ', %buf', %n', %rest', Hb, Hbuf, %Hn', #Herr'⟩
      wp_auto
      iapply HΦ
      iexists sent ++ pend.take k, pend.drop k
      isplitr
      · ipureintro
        refine ⟨⟨_, rfl⟩, by simp, fun _ => ?_, by simp, fun hf => ?_⟩
        · simp
        · simp only [List.append_nil] at Hn; omega
      iunfold bufio.ownBufWriter, bufio.writerRep
      iframe Hpkg Hwr HJ HQ'
      iexists buf', n', rest'
      iframe Hb Hbuf Herr'
      ipureintro; exact Hn'
    have hk : k = pend.length := Hk.2.1 rfl
    subst hk
    wp_auto
    iunfold bufio.ownBufWriter, bufio.writerRep at Hown
    icases Hown with ⟨-, -, HJ, #HQ', %buf', %n', %rest', Hb, Hbuf, %Hn', #Herr'⟩
    simp only [List.take_length, List.drop_length, List.nil_append, List.length_nil,
      List.append_nil] at Hn' ⊢
    ihave Hst : (∃ (sent0 pend0 rest0 : List w8) (buf : GoSlice) (n0 : w64),
        "HJ" ∷ J sent0 ∗ "#HQ" ∷ □ Q (sent0 ++ pend0) ∗
        "Hb" ∷ bw ↦ _root_.Perennial.bufio.Writer.mk interface.nil buf n0 (interface.ok wi) ∗
        "Hbuf" ∷ buf ↦* (pend0 ++ rest0) ∗
        "%Hst" ∷ ⌜sint.Z n0 = pend0.length ∧ rest0 ≠ [] ∧ sent <+: sent0 ∧
          sent0 ++ pend0 = sent ++ pend ∧ (pend0 ++ rest0).length = sz⌝ : IProp GF)
      $$ [HJ Hb Hbuf]
    · iexists sent ++ pend, [], rest', buf', n'
      simp only [List.append_nil, List.nil_append]
      iframe HJ HQ' Hb Hbuf
      ipureintro
      refine ⟨Hn'.1, ?_, ⟨_, rfl⟩, ?_, ?_⟩
      · intro h; subst h; simp at Hn'
      · simp
      · simpa using Hn'.2.2
    icases Hst with ⟨%sent0, %pend0, %rest0, %buf0, %n0, HJ, #HQ, Hb, Hbuf, %Hst⟩
    obtain ⟨Hn0, Hr0, Hpre, Heq, Hsz0⟩ := Hst
    have hfitS : pend.length + 1 ≤ sz → sent0 = sent := fun h => by
      simp only [List.append_nil] at Hn; omega
    writebyte_tail sent0 pend0 rest0 buf0 n0
  have Hr0 : rest ≠ [] := List.ne_nil_of_length_pos (by omega)
  have Hpre : sent <+: sent := List.prefix_refl _
  have Heq : sent ++ pend = sent ++ pend := rfl
  have Hn0 := Hn.1
  have Hsz0 := Hn.2.2
  have hfitS : pend.length + 1 ≤ sz → sent = sent := fun _ => rfl
  writebyte_tail sent pend rest buf n

end proof

end EtcdGrove
end Perennial
