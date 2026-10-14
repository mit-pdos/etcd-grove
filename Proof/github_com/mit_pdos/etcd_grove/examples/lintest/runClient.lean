/-
Lean-first (no Rocq counterpart).

The proof of `runClient`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.runClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.InvLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.Assumptions]

theorem runClient.wp_proof : runClient.spec (GF := GF) (hG := hG) :=
    fun σ S libState clockVal Eapp Eclk n γ apply gen clock id ops lr HEapp HEclk Hid => by
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
    wp_apply (lc := 1) Hgen as %input -
    done
  · done

end proof

end lintest
end EtcdGrove
end Perennial
