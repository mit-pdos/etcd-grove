/-
Proof of `byteorder.LEUint32` over its translated body (`internal/byteorder`, go1.27.3): a load of
`b[3]`, then four loads at constant indices below `len(b)`. Lean-first (crc32-hooks2, 2026-11-22).
-/
module

public import Spec.internal.byteorder.LEUint32

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

theorem byteorder.LEUint32.wp_proof : byteorder.LEUint32.spec (GF := GF) (hG := hG) := by
  intro b dq b0 b1 b2 b3 rest
  wp_start as Hb
  ihave %Hl := ownSlice_len _ _ _ $$ Hb
  have hbl : (4 : Int) ≤ sint.Z b.len := by have := Hl.1; simp at this; word
  try wp_auto
  repeat (
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
    wp_apply wp_load_slice_index b _ _ _ _ (by word) $$ [Hb] as Hb
    · iframe; ipureintro; rfl
    try wp_auto)
  have he : W32 (uint.Z b0) ||| W32 (uint.Z b1) <<< W64 8 ||| W32 (uint.Z b2) <<< W64 16 |||
      W32 (uint.Z b3) <<< W64 24 = byteorder.le32 b0 b1 b2 b3 := by
    have hz : ∀ v : w8, W32 (uint.Z v) = v.zeroExtend 32 := fun v => by
      apply BitVec.eq_of_toNat_eq; simp [uint.Z]
    simp only [hz, byteorder.le32]
    bv_decide
  rw [he]
  iapply HΦ $$ Hb

end proof

end EtcdGrove
end Perennial
