module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.appendHist

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg hnode state labelSel fieldSel)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem histOf.wp_proof
    (wp_appendHist : appendHist.spec (GF := GF) (hG := hG)) :
    histOf.spec (GF := GF) (hG := hG) := by
  intro ss xs gs dq
  wp_start as ⟨Hss, #Hxs⟩
  ihave %Hl := ownSlice_len $$ Hss
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hxs
  wp_auto
  ihave HI : (∃ (j : w64) (e0 : mstore) (hc : Loc),
      "i" ∷ i_ptr ↦ j ∗ "s" ∷ s_ptr ↦ e0 ∗ "h" ∷ h_ptr ↦ hc ∗ "#Hc" ∷ histOwn hc (gs.take (sint.nat j)) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z ss.len⌝ : IProp GF) $$ [i s h]
  · iexists W64 0, _, _
    iframe
    isplit
    · rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
      iapply (histOwn_nil _).2
      ipureintro; rfl
    · ipureintro; refine ⟨by word, by word⟩
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z ss.len := ⟨Hj.1, Hif⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem xs (sint.nat j) as x
    list_elem gs (sint.nat j) as g
    wp_apply wp_load_slice_index ss (sint.Z j) xs dq x Hj.1 $$ [Hss] as Hss
    · iframe; ipureintro; exact Hx_lookup
    ihave #Hx := BigSepL2.bigSepL2_lookup (Φ := fun _ x' g' => storeOwn (GF := GF) x' g')
      Hx_lookup Hg_lookup $$ Hxs
    wp_apply wp_appendHist $$ [$Hc $Hx] as %h' #Hh'
    (try wp_auto)
    wp_for_post
    iframe
    iexists j + W64 1, _, h'
    iframe
    isplit
    · rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, Hg_lookup, Option.toList_some]
      iexact Hh'
    · ipureintro; refine ⟨by word, by word⟩
  · (try wp_auto)
    have : gs.take (sint.nat j) = gs := List.take_of_length_le (by word)
    rw [this]
    iapply HΦ
    iframe
    iexact Hc

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
