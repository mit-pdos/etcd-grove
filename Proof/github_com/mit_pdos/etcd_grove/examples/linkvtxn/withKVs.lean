/-
Lean-first (no Rocq counterpart).

The proof of `withKVs`: the count, then one field per element.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.withKVs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkvtxn

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

theorem withKVs.wp_proof : withKVs.spec (GF := GF) (hG := hG) := by
  intro o sl l dq
  wp_start as Hs
  ihave %Hl := ownSlice_len $$ Hs
  wp_auto
  wp_if_destruct
  · obtain ⟨x0, Hx0_lookup⟩ := lookup_lt_is_Some_2 (l := l) (i := 0) (by word)
    rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len by word)]
    wp_apply wp_load_slice_index sl (sint.Z (W64 0)) l dq x0 (by word) $$ [Hs] as Hs
    · iframe; ipureintro; rw [show (sint.Z (W64 0)).toNat = 0 by rw [show sint.Z (W64 0) = 0 by word]; rfl]
      exact Hx0_lookup
    wp_if_destruct
    · obtain ⟨x1, Hx1_lookup⟩ := lookup_lt_is_Some_2 (l := l) (i := 1) (by word)
      rw [if_pos (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z sl.len by word)]
      wp_apply wp_load_slice_index sl (sint.Z (W64 1)) l dq x1 (by word) $$ [Hs] as Hs
      · iframe; ipureintro; rw [show (sint.Z (W64 1)).toNat = 1 by rw [show sint.Z (W64 1) = 1 by word]; rfl]
        exact Hx1_lookup
      wp_if_destruct
      · obtain ⟨x2, Hx2_lookup⟩ := lookup_lt_is_Some_2 (l := l) (i := 2) (by word)
        rw [if_pos (show 0 ≤ sint.Z (W64 2) ∧ sint.Z (W64 2) < sint.Z sl.len by word)]
        wp_apply wp_load_slice_index sl (sint.Z (W64 2)) l dq x2 (by word) $$ [Hs] as Hs
        · iframe; ipureintro; rw [show (sint.Z (W64 2)).toNat = 2 by rw [show sint.Z (W64 2) = 2 by word]; rfl]
          exact Hx2_lookup
        iapply HΦ
        iframe
        ipureintro
        have hlen : W64 (l.length : Int) = sl.len := by word
        have e0 : l.getD 0 o.KV0' = x0 := by
          rw [List.getD_eq_getElem?_getD, Hx0_lookup]; rfl
        have e1 : l.getD 1 o.KV1' = x1 := by
          rw [List.getD_eq_getElem?_getD, Hx1_lookup]; rfl
        have e2 : l.getD 2 o.KV2' = x2 := by
          rw [List.getD_eq_getElem?_getD, Hx2_lookup]; rfl
        unfold withKVsL
        rw [hlen, e0, e1, e2]
      · iapply HΦ
        iframe
        ipureintro
        have hlen : W64 (l.length : Int) = sl.len := by word
        have e0 : l.getD 0 o.KV0' = x0 := by
          rw [List.getD_eq_getElem?_getD, Hx0_lookup]; rfl
        have e1 : l.getD 1 o.KV1' = x1 := by
          rw [List.getD_eq_getElem?_getD, Hx1_lookup]; rfl
        have e2 : l.getD 2 o.KV2' = o.KV2' := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by word)]; rfl
        unfold withKVsL
        rw [hlen, e0, e1, e2]
    · wp_if_destruct
      · exfalso; word
      · iapply HΦ
        iframe
        ipureintro
        have hlen : W64 (l.length : Int) = sl.len := by word
        have e0 : l.getD 0 o.KV0' = x0 := by
          rw [List.getD_eq_getElem?_getD, Hx0_lookup]; rfl
        have e1 : l.getD 1 o.KV1' = o.KV1' := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by word)]; rfl
        have e2 : l.getD 2 o.KV2' = o.KV2' := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by word)]; rfl
        unfold withKVsL
        rw [hlen, e0, e1, e2]
  · wp_if_destruct
    · exfalso; word
    · wp_if_destruct
      · exfalso; word
      · iapply HΦ
        iframe
        ipureintro
        have hlen : W64 (l.length : Int) = sl.len := by word
        have e0 : l.getD 0 o.KV0' = o.KV0' := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by word)]; rfl
        have e1 : l.getD 1 o.KV1' = o.KV1' := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by word)]; rfl
        have e2 : l.getD 2 o.KV2' = o.KV2' := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by word)]; rfl
        unfold withKVsL
        rw [hlen, e0, e1, e2]

end proof

end linkvtxn
end EtcdGrove
end Perennial
