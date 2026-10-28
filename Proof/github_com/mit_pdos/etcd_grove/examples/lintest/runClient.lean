/-
Lean-first (no Rocq counterpart).

The proof of `runClient`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.runClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.ClientSteps

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.Assumptions]

theorem runClient.wp_proof : runClient.spec (GF := GF) (hG := hG) :=
    fun σ S inOk libState clockVal Eapp Eclk n γ apply gen clock id ops lr HEapp HEclk Hid => by
  wp_start as ⟨#Happly, #Hgen, #Hclock, #Hinv, Htok⟩
  wp_auto
  ihave Hnil := ownSlice_nil (V := Operation) (GF := GF) (DFrac.own 1)
  ihave Hcap := ownSliceCap_nil (V := Operation) (GF := GF)
  ihave HI : (∃ (i : w64) (hsl : GoSlice) (hc : List Operation) (Lc : List (OpV × w64))
      (lr' : w64),
      "i" ∷ i_ptr ↦ i ∗ "history" ∷ history_ptr ↦ hsl ∗ "Hh" ∷ hsl ↦* hc ∗
      "Hcap" ∷ ownSliceCap Operation hsl (DFrac.own 1) ∗
      "Htok" ∷ clientTok γ (sint.nat id) (Lc, lr') ∗
      "%Hok" ∷ ⌜ClientOk id hc Lc⌝ ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ (Lc.length : Int) = sint.Z i ∧
        (sint.Z i = 0 ∨ sint.Z i ≤ sint.Z ops)⌝ ∗
      "#Hio" ∷ opsIoOk S hc : IProp GF) $$ [i history Hnil Hcap Htok]
  · iexists W64 0, slice.nil, [], [], lr
    iframe
    unfold named opsIoOk
    isplitr
    · iexact Hnil
    isplitr
    · iexact Hcap
    isplitr
    · ipureintro; exact ⟨rfl, fun j o p h => by simp at h⟩
    isplitr
    · ipureintro; simp
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro
  wp_for HI
  wp_if_destruct
  · iunfold genSpec at Hgen
    wp_apply (lc := 1) Hgen as %input #Hin
    · ipureintro; exact Hid
    wp_apply (lc := 1) wp_clock_read S.M libState clockVal Eclk n γ clock (sint.nat id) (Lc, lr')
      HEclk $$ [$Hclock $Hinv $Hlc1 $Htok] as %call ⟨Htok, %Hcall⟩
    wp_apply (lc := 1) wp_apply_commit S inOk libState clockVal Eapp n γ apply (sint.nat id)
      (Lc, call) input HEapp $$ [$Happly $Hin $Hinv $Hlc1 $Htok] as %output %τ ⟨Htok, %Hτ, #Hioo⟩
    wp_apply wp_clock_read S.M libState clockVal Eclk n γ clock (sint.nat id)
      (Lc ++ [((input, output), τ)], call) HEclk $$ [$Hclock $Hinv $Hlc1 $Htok]
      as %ret ⟨Htok, %Hret⟩
    wp_apply wp_slice_literal (V := Operation)
      [Operation.mk id input call output ret GoInterface.nil ()]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Hh $Hcap $Hsl2] as %hsl' ⟨Hh, Hcap, -⟩
    wp_for_post
    have Hlt : sint.Z i < sint.Z ops := by simpa using Hif
    iframe
    iexists (i + W64 1), hsl', _, Lc ++ [((input, output), τ)], ret
    iframe
    have Hi1 : sint.Z (i + W64 1) = sint.Z i + 1 := by word
    unfold named
    isplitr
    · ipureintro
      exact Hok.snoc input output call τ ret Hτ (Hret.1 ((input, output), τ) (by simp))
    isplitr
    · ipureintro
      simp only [List.length_append, List.length_singleton, Hi1]
      omega
    unfold opsIoOk
    iapply BigSepL.bigSepL_snoc.2
    iframe # ∗
  · have Hge : ¬ sint.Z i < sint.Z ops := by simpa using Hif
    iapply HΦ
    iexists hc, Lc, lr'
    iframe
    isplitr
    · ipureintro
      refine ⟨Hok, ?_⟩
      have hl := Hi.2.1
      have hi0 := Hi.1
      have hi2 := Hi.2.2
      word
    iframe #

end proof

end lintest
end EtcdGrove
end Perennial
