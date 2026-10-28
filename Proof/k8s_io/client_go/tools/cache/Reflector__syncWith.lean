/-
Proof of `Spec/k8s_io/client_go/tools/cache/Reflector__syncWith.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.Reflector__syncWith

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem Reflector.syncWith.wp_proof (wp_Replace : RealFIFO.Replace.spec (GF := GF) (hG := hG)) :
    Reflector.syncWith.spec (GF := GF) (hG := hG) := by
  intro r f γ OK isl dq objs rv
  iintro %Φ ⟨#Hpkg, #Hst, #Hf, Hisl, #Hoks⟩ HAU
  wp_method_call
  wp_call
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hisl
  wp_apply (wp_slice_make3 (V := GoInterface) (W64 0) isl.len (by word)) as %fs0 ⟨Hfs0, Hfcap0, -⟩
  (try wp_auto)
  ihave IH : iprop(∃ (n : w64) (x : GoInterface) (fsl : GoSlice),
      "i" ∷ i_ptr ↦ n ∗ "item" ∷ item_ptr ↦ x ∗
      "found" ∷ found_ptr ↦ fsl ∗ "Hfsl" ∷ fsl ↦* objs.take (sint.nat n) ∗
      "Hfcap" ∷ ownSliceCap GoInterface fsl (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z isl.len⌝) $$ [i item found Hfs0 Hfcap0]
  · iexists W64 0, _, fs0
    iframe
    ipureintro; word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < objs.length := by word
    obtain ⟨e, He⟩ : ∃ e, objs[sint.nat n]? = some e := ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z isl.len from ⟨Hn.1, Hif⟩, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index isl (sint.Z n) objs dq e Hn.1 $$ [Hisl] as Hisl
    · iframe; ipureintro; rw [show (sint.Z n).toNat = sint.nat n by word]; exact He
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %l1 ⟨Hl1, -⟩
    simp only [go.arrayLiteralSize, List.foldl]
    (try wp_auto)
    wp_apply wp_slice_append $$ [$Hfsl $Hfcap $Hl1] as %fsl' ⟨Hfsl, Hfcap, -⟩
    (try wp_auto)
    wp_for_post
    iframe
    iexists n + W64 1, _, fsl'
    iframe
    have : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    rw [this, List.take_add_one, He]
    simp only [Option.toList_some]
    iframe
    ipureintro; word
  · have hn : sint.nat n = objs.length := by word
    rw [hn, List.take_length] at *
    (try wp_auto)
    wp_bind
    iapply (wp_Replace f γ OK fsl objs rv) $$ [$Hpkg $Hf $Hfsl $Hoks]
    inext
    imod HAU with ⟨%q, Hq, Hcl⟩
    imodintro
    iexists q
    iframe Hq
    iintro Hq
    imod Hcl $$ Hq with HK
    imodintro
    iintro -
    (try wp_auto)
    iapply HK; iexact Hisl

end proof

end cache
end EtcdGrove
end Perennial
