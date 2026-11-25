/-
The proof of `jsoncodec.AppendCompact` (`Net/Spec/models_lab/jsoncodec/AppendCompact.lean`) over
`Valid`, `IsSpace` and `htmlByte`'s specs. Ported from dsverify-lab's `wp_AppendCompact_ok`
(`examples/vr/proof/VsrProof/Proof/jsoncodec/GoEnc.lean`, lab master 915f964).
-/
module

public import Net.Spec.models_lab.jsoncodec.AppendCompact
public import Net.Spec.models_lab.jsoncodec.Valid
public import Net.Spec.models_lab.jsoncodec.IsSpace
public import Net.Spec.models_lab.jsoncodec.htmlByte
public import Net.Proof.models_lab.jsoncodec.ScanString

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace models_lab.jsoncodec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : models_lab.jsoncodec.Assumptions]

set_option goose.wp.extras true

theorem AppendCompact.wp_proof (wp_Valid : Valid.spec (GF := GF) (hG := hG))
    (wp_IsSpace : IsSpace.spec (GF := GF) (hG := hG))
    (wp_htmlByte : htmlByte.spec (GF := GF) (hG := hG)) :
    AppendCompact.spec (GF := GF) (hG := hG) := by
  intro b bs raw dq rs hsc hc
  wp_start as ⟨Hb, Hcap, Hr⟩
  ihave %Hlen := ownSlice_len $$ Hr
  have hl63 := len_lt raw rs Hlen
  wp_auto
  wp_apply (wp_Valid raw dq rs hsc) $$ Hr as Hr
  try wp_auto
  ihave IH : iprop(∃ (i : w64) (st : Bool) (o : GoSlice),
      "i" ∷ i_ptr ↦ i ∗ "inStr" ∷ inStr_ptr ↦ st ∗ "out" ∷ out_ptr ↦ o ∗
      "Ho" ∷ o ↦* (bs ++ rs.take (uint.nat i)) ∗ "Hoc" ∷ ownSliceCap w8 o (DFrac.own 1) ∗
      "%Hi" ∷ ⌜uint.nat i ≤ rs.length ∧ cmpRun st (rs.drop (uint.nat i)) = some false⌝)
    $$ [i inStr out Hb Hcap]
  · iexists _, _, _
    iframe
    rw [show uint.nat (W64 0) = 0 by rfl]
    simp only [List.take_zero, List.append_nil, List.drop_zero]
    iframe
    ipureintro
    exact ⟨by word, hc⟩
  wp_for IH
  obtain ⟨hil, hrun⟩ := Hi
  ihave %Hwf := ownSlice_wf $$ Hr
  wp_if_destruct
  · have Hlt : uint.nat i < rs.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, rs[uint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have hdrop : rs.drop (uint.nat i) = x :: rs.drop (uint.nat i + 1) := by
      rw [List.drop_eq_getElem_cons Hlt]; simp only [List.getElem?_eq_getElem Hlt] at Hx; cases Hx; rfl
    have htake : rs.take (uint.nat i + 1) = rs.take (uint.nat i) ++ [x] := by
      rw [List.take_succ, Hx]; rfl
    have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z raw.len := by word
    have hnz : (sint.Z i).toNat = uint.nat i := by word
    rw [if_pos hb]
    wp_apply wp_load_slice_index raw (sint.Z i) rs dq x hb.1 $$ [Hr] as Hr
    · iframe; ipureintro; rw [hnz]; exact Hx
    rw [hdrop] at hrun
    cases st
    · simp only [cmpRun] at hrun
      split at hrun
      · cases hrun
      rename_i hsp
      have hsp' : JsonScan.spB x = false := by simpa using hsp
      wp_auto
      wp_apply (wp_IsSpace x)
      rw [spaceB_spB, hsp']
      wp_auto
      wp_if_destruct
      · try wp_auto
        wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
          (Val (LiteralValueV _)))
        iapply wp_slice_literal (V := w8) (t := go.byte) [_]
        wp_auto
        isplitl []
        · ipureintro; rfl
        iintro %lit ⟨Hlit, -⟩
        wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Ho $Hoc $Hlit] as %o' ⟨Ho', Hoc', -⟩
        wp_for_post
        iframe
        iexists _, _, _
        iframe
        rw [show uint.nat (i + W64 1) = uint.nat i + 1 by word, htake, List.append_assoc]
        iframe
        ipureintro
        refine ⟨by omega, ?_⟩
        simpa using hrun
      · try wp_auto
        wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
          (Val (LiteralValueV _)))
        iapply wp_slice_literal (V := w8) (t := go.byte) [_]
        wp_auto
        isplitl []
        · ipureintro; rfl
        iintro %lit ⟨Hlit, -⟩
        wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Ho $Hoc $Hlit] as %o' ⟨Ho', Hoc', -⟩
        wp_for_post
        iframe
        iexists _, _, _
        iframe
        rw [show uint.nat (i + W64 1) = uint.nat i + 1 by word, htake, List.append_assoc]
        iframe
        ipureintro
        refine ⟨by omega, ?_⟩
        have hq : decide (x = 34#8) = false := by
          simp only [decide_eq_false_iff_not]; intro e; apply Hif; rw [e]; rfl
        rwa [hq] at hrun
    · simp only [cmpRun] at hrun
      split at hrun
      · cases hrun
      rename_i hbad
      have hbad' : cmpBad x = false := by simpa using hbad
      simp only [cmpBad, decide_eq_false_iff_not, not_or] at hbad'
      obtain ⟨h60, h62, h38, h92, h128⟩ := hbad'
      have tn : ∀ (a : w8) (n : Nat), a ≠ BitVec.ofNat 8 n → n < 256 → a.toNat ≠ n := by
        intro a n h hn e; apply h; apply BitVec.eq_of_toNat_eq; simp [e]; omega
      wp_auto
      have hh : htmlB x = false := by
        simp only [htmlB, decide_eq_false_iff_not]
        rintro (e | e | e)
        · exact tn x 60 h60 (by omega) (by rw [e]; rfl)
        · exact tn x 62 h62 (by omega) (by rw [e]; rfl)
        · exact tn x 38 h38 (by omega) (by rw [e]; rfl)
      wp_apply (wp_htmlByte x)
      rw [hh]
      try wp_auto
      rw [decide_eq_false (show ¬ x = W8 92 from h92)]
      try wp_auto
      try rw [decide_eq_false (show ¬ uint.Z (W8 128) ≤ uint.Z x by simp [uint.Z]; omega)]
      try wp_auto
      wp_if_destruct
      · try wp_auto
        wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
          (Val (LiteralValueV _)))
        iapply wp_slice_literal (V := w8) (t := go.byte) [_]
        wp_auto
        isplitl []
        · ipureintro; rfl
        iintro %lit ⟨Hlit, -⟩
        wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Ho $Hoc $Hlit] as %o' ⟨Ho', Hoc', -⟩
        wp_for_post
        iframe
        iexists _, _, _
        iframe
        rw [show uint.nat (i + W64 1) = uint.nat i + 1 by word, htake, List.append_assoc]
        iframe
        ipureintro
        refine ⟨by omega, ?_⟩
        simpa using hrun
      · try wp_auto
        wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
          (Val (LiteralValueV _)))
        iapply wp_slice_literal (V := w8) (t := go.byte) [_]
        wp_auto
        isplitl []
        · ipureintro; rfl
        iintro %lit ⟨Hlit, -⟩
        wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Ho $Hoc $Hlit] as %o' ⟨Ho', Hoc', -⟩
        wp_for_post
        iframe
        iexists _, _, _
        iframe
        rw [show uint.nat (i + W64 1) = uint.nat i + 1 by word, htake, List.append_assoc]
        iframe
        ipureintro
        refine ⟨by omega, ?_⟩
        have hq : decide (x ≠ 34#8) = true := by
          simp only [decide_eq_true_eq]; intro e; apply Hif; rw [e]; rfl
        rwa [hq] at hrun
  · have hi : uint.nat i = rs.length := by word
    rw [hi, List.take_length]
    iapply HΦ
    iframe

end proof

end models_lab.jsoncodec
end Perennial
