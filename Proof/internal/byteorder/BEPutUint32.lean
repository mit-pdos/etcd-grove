/-
Proof of `byteorder.BEPutUint32` over its translated body (`internal/byteorder`, go1.27.3): a load of
`b[3]` and 4 stores at constant indices below `len(b)`. Lean-first (prove-authcrypto, 2026-11-21).
-/
module

public import Spec.internal.byteorder.BEPutUint32

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.internal.byteorder.Assumptions]

theorem byteorder.BEPutUint32.wp_proof : byteorder.BEPutUint32.spec (GF := GF) (hG := hG) := by
  intro b bs v hlen
  wp_start as Hb
  ihave %Hl := ownSlice_len _ _ _ $$ Hb
  have hbl : (4 : Int) ≤ sint.Z b.len := by have := Hl.1; word
  try wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
  obtain ⟨x, hx⟩ : ∃ x, bs[(sint.Z (W64 3)).toNat]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by have : (sint.Z (W64 3)).toNat = 3 := by word
                                     omega)⟩
  wp_apply wp_load_slice_index b _ bs _ x (by word) $$ [Hb] as Hb
  · iframe; ipureintro; exact hx
  try wp_auto
  repeat (
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
    wp_apply wp_store_slice_index b _ _ _ $$ [Hb] as Hb
    · iframe; ipureintro; constructor <;> (try simp only [List.length_set]) <;> word
    try wp_auto)
  iapply HΦ
  iexists _; iframe; ipureintro; simp only [List.length_set]


end proof

end EtcdGrove
end Perennial
