/- Lean-first (no Rocq counterpart). The proof of `readEnt`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.readEnt

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

theorem readEnt.wp_proof : readEnt.spec (GF := GF) (hG := hG) := by
  intro b s es e he
  wp_start as #Hs
  ihave %Hlen := ownSlice_len $$ Hs
  wp_auto
  wp_if_destruct
  · wp_apply +noauto (wp_slice_make2 (V := TEnt) (W64 0)) as %r ⟨Hr, -⟩
    · ipureintro; word
    ipersist Hr
    wp_auto
    wp_end
    have h1 : uint.nat e.index' ≤ uint.nat b := by word
    simp only [tReadEnt, h1, ↓reduceIte, entsRes, List.replicate_zero]
    isplitl []
    · itrivial
    · iexact Hr
  · have h1 : ¬ uint.nat e.index' ≤ uint.nat b := by intro h; apply Hif; word
    have hoff : uint.nat (e.index' - b - W64 1) = uint.nat e.index' - uint.nat b - 1 := by word
    wp_if_destruct
    · wp_end
      have h2 : es.length < uint.nat (e.index' - b - W64 1) := by
        have : es.length = sint.nat s.len := Hlen.1
        word
      simp only [tReadEnt, h1, h2, ↓reduceIte, entsRes]
      ipureintro; trivial
    · have h2 : uint.nat (e.index' - b - W64 1) ≤ es.length := by
        have : es.length = sint.nat s.len := Hlen.1
        word
      have hcap : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (e.index' - b - W64 1 + W64 1) := by
        constructor <;> word
      wp_apply (wp_slice_make3 (V := TEnt) (W64 0) (e.index' - b - W64 1 + W64 1) hcap)
        as %out ⟨Hout, Hcap, -⟩
      ihave HI : (∃ (j : w64) (o : GoSlice),
          "i" ∷ i_ptr ↦ j ∗ "out" ∷ out_ptr ↦ o ∗
          "Hout" ∷ o ↦* es.take (uint.nat j) ∗ "Hcap" ∷ ownSliceCap TEnt o (DFrac.own 1) ∗
          "%Hj" ∷ ⌜uint.nat j ≤ uint.nat (e.index' - b - W64 1)⌝ : IProp GF) $$ [i out Hout Hcap]
      · iexists W64 0, out
        simp only [show uint.nat (W64 0) = 0 from rfl, List.take_zero, show sint.nat (W64 0) = 0 from rfl,
          List.replicate_zero]
        iframe
        ipureintro; word
      wp_for HI
      wp_if_destruct
      · have hjl : uint.nat j < es.length := by word
        obtain ⟨x, Hx⟩ : ∃ x, es[uint.nat j]? = some x := ⟨_, List.getElem?_eq_getElem hjl⟩
        have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len := by
          have : es.length = sint.nat s.len := Hlen.1
          constructor <;> word
        simp only [hb, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index s (sint.Z j) es DFrac.discard x hb.1 as -
        · isplitl []
          · iexact Hs
          ipureintro
          rw [show (sint.Z j).toNat = uint.nat j by word]; exact Hx
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %osl ⟨Hosl, -⟩
        wp_auto
        wp_apply wp_slice_append $$ [$Hout $Hcap $Hosl] as %o' ⟨Hout, Hcap, -⟩
        wp_for_post
        iframe
        iexists j + W64 1, o'
        have hj1 : uint.nat (j + W64 1) = uint.nat j + 1 := by word
        rw [hj1, List.take_add_one, Hx]
        iframe
        ipureintro; word
      · have hjn : uint.nat j = uint.nat (e.index' - b - W64 1) := by word
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %osl ⟨Hosl, -⟩
        wp_auto
        wp_apply +noauto wp_slice_append $$ [$Hout $Hcap $Hosl] as %o' ⟨Hout, -, -⟩
        ipersist Hout
        wp_auto
        wp_end
        have h3 : ¬ es.length < uint.nat (e.index' - b - W64 1) := by omega
        simp only [tReadEnt, h1, h3, ↓reduceIte, entsRes]
        rw [← hjn]
        isplitl []
        · itrivial
        · iexact Hout

end proof

end etcd_wal
end EtcdGrove
end Perennial
