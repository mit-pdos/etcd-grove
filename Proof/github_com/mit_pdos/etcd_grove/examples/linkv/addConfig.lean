/-
Lean-first (no Rocq counterpart).

The proof of `addConfig`: the loop's invariant is that no configuration before the index holds
`c`'s contents (`configEqual`); after it, the append.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.addConfig
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.configEqual

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkv

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv.Assumptions]

theorem addConfig.wp_proof (wp_configEqual : configEqual.spec (GF := GF) (hG := hG)) :
    addConfig.spec (GF := GF) (hG := hG) := by
  intro s cs gs c g
  wp_start as ⟨Hs, Hcap, #Hcs, #Hc⟩
  ihave %Hl := ownSlice_len $$ Hs
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hcs
  wp_auto
  ihave HI : (∃ (j : w64) (d0 : kvConfig),
      "i" ∷ i_ptr ↦ j ∗ "d" ∷ d_ptr ↦ d0 ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.len ∧ g ∉ gs.take (sint.nat j)⌝ : IProp GF)
    $$ [i d]
  · iexists W64 0, _
    iframe
    ipureintro; refine ⟨by word, by word, ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl]; simp
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len := ⟨Hj.1, Hif⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem cs (sint.nat j) as d
    list_elem gs (sint.nat j) as h
    wp_apply wp_load_slice_index s (sint.Z j) cs _ d Hj.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hd_lookup
    ihave #Hd := BigSepL2.bigSepL2_lookup (Φ := fun _ c' g' => cfgOwn (GF := GF) c' g')
      Hd_lookup Hh_lookup $$ Hcs
    wp_apply wp_configEqual c d g h $$ [$Hc $Hd]
    cases hgh : decide (g = h)
    · wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, Hh_lookup]
      simp only [Option.toList_some, List.mem_append, List.mem_singleton, not_or]
      exact ⟨Hj.2.2, of_decide_eq_false hgh⟩
    · wp_auto
      wp_for_post
      have hmem : g ∈ gs := by
        rw [of_decide_eq_true hgh]; exact List.mem_of_getElem? Hh_lookup
      iapply HΦ
      rw [addConfigL, if_pos hmem]
      iframe
      iexact Hcs
  · -- `c` is not in `s`: appended
    have hall : gs.take (sint.nat j) = gs := List.take_of_length_le (by word)
    have hnm : g ∉ gs := by rw [← hall]; exact Hj.2.2
    wp_apply wp_slice_literal (l := [c])
    isplitr
    · ipureintro; rfl
    iintro %lsl ⟨Hl1, _⟩
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hl1] as %s' ⟨Hs, Hcap, -⟩
    iapply HΦ
    rw [addConfigL, if_neg hnm]
    iframe
    iapply (BigSepL2.bigSepL2_snoc (Φ := fun _ c' g' => cfgOwn (GF := GF) c' g')).2
    isplit
    · iexact Hcs
    · iexact Hc

end proof

end linkv
end EtcdGrove
end Perennial
