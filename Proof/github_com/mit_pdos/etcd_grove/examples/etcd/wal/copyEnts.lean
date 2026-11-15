/- Lean-first (no Rocq counterpart). The proof of `copyEnts`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.copyEnts

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

theorem copyEnts.wp_proof : copyEnts.spec (GF := GF) (hG := hG) := by
  intro s es dq
  wp_start as Hs
  ihave %Hlen := ownSlice_len $$ Hs
  wp_auto
  wp_apply (wp_slice_make3 (V := TEnt) (W64 0) s.len (by word)) as %out ⟨Hout, Hcap, -⟩
  ihave HI : (∃ (j : w64) (o : GoSlice),
      "i" ∷ i_ptr ↦ j ∗ "out" ∷ out_ptr ↦ o ∗
      "Hout" ∷ o ↦* es.take (sint.nat j) ∗ "Hcap" ∷ ownSliceCap TEnt o (DFrac.own 1) ∗
      "Hs" ∷ s ↦*{dq} es ∗ "es" ∷ es_ptr ↦ s ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.len⌝ : IProp GF) $$ [i out Hout Hcap Hs es]
  · iexists W64 0, out
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.replicate_zero]
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · have hjl : sint.nat j < es.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, es[sint.nat j]? = some x := ⟨_, List.getElem?_eq_getElem hjl⟩
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len := ⟨Hj.1, Hif⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index s (sint.Z j) es dq x Hj.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hx
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %osl ⟨Hosl, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Hout $Hcap $Hosl] as %o' ⟨Hout, Hcap, -⟩
    wp_for_post
    iframe
    iexists j + W64 1, o'
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    rw [hj1, List.take_add_one, Hx]
    iframe
    ipureintro; constructor <;> word
  · have hjn : sint.nat j = es.length := by word
    rw [hjn, List.take_length]
    wp_end

end proof

end etcd_wal
end EtcdGrove
end Perennial
