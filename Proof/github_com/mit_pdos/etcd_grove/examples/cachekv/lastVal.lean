/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/cachekv/lastVal.lean` (2026-11-02): the
loop over the events keeps the last value of the prefix read (`lastValL_snoc`).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.cachekv.lastVal

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cachekv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.cachekv

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.cachekv.Assumptions]

theorem lastVal.wp_proof : lastVal.spec (GF := GF) (hG := hG) := by
  intro sl evs dq key r
  wp_start as Hs
  ihave %Hl := ownSlice_len $$ Hs
  wp_auto
  ihave HI : (∃ (j : w64) (e0 : cev) (v : GoString) (ok : Bool),
      "i" ∷ i_ptr ↦ j ∗ "e" ∷ e_ptr ↦ e0 ∗ "v" ∷ v_ptr ↦ v ∗ "ok" ∷ ok_ptr ↦ ok ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len ∧
        (if ok then some v else none) = lastValL (evs.take (sint.nat j)) key r⌝ : IProp GF)
      $$ [i e v ok]
  · iexists W64 0, _, _, _
    iframe
    ipureintro; refine ⟨by word, by word, ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl]; simp [lastValL]
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, Hif⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem evs (sint.nat j) as x
    wp_apply wp_load_slice_index sl (sint.Z j) evs dq x Hj.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hx_lookup
    have Htake : evs.take (sint.nat (j + W64 1)) = evs.take (sint.nat j) ++ [x] := by
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, Hx_lookup]
      rfl
    (try wp_auto)
    wp_if_destruct
    · wp_if_destruct
      · (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, _, _, _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [Htake, lastValL_snoc]; simp [*]
      · (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, _, _, _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [Htake, lastValL_snoc]; simp [*]
    · (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, _, _, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [Htake, lastValL_snoc]; simp [*]
  · (try wp_auto)
    iapply HΦ
    iframe
    ipureintro
    have : evs.take (sint.nat j) = evs := List.take_of_length_le (by word)
    rw [this] at Hj
    exact Hj.2.2

end proof

end cachekv
end EtcdGrove
end Perennial
