/-
`encoding/binary`'s `(*littleEndian).PutUint16` / `Uint16` on the global `LittleEndian` (Perennial
has the code but no spec; `state.Value`'s marshalers use them). Internal to the wire package.
-/
module

public import Perennial.Proof.encoding.binary.Results

@[expose] public section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace encoding.binary

/-- The two bytes `PutUint16` stores. -/
def u16Le (v : w16) : List w8 := [W8 (uint.Z v), W8 (uint.Z (v >>> W64 8))]

theorem u16Le_u32Le (x : w16) : u16Le x ++ [W8 0, W8 0] = u32Le (W32 (uint.Z x)) := by
  rw [u32Le_unseal]
  have := x.isLt
  simp [u16Le, u32LeDef, LittleEndian.split]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;> simp <;> omega

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.binary.Assumptions]

theorem wp_littleEndian_PutUint16 (le : littleEndian) (b : GoSlice) (space rem : List w8)
    (v : w16) (Hlen_space : space.length = 2) :
    {{ (b ↦* (space ++ rem) : IProp GF) }}
      (App (App (Val (le @!! littleEndian.ty @!! go!"PutUint16")) (Val #b)) (Val #v))
    {{ RET #(); b ↦* (u16Le v ++ rem) }} := by
  obtain ⟨w0, w1, rfl⟩ : ∃ w0 w1, space = [w0, w1] := by
    match space, Hlen_space with
    | [w0, w1], _ => exact ⟨w0, w1, rfl⟩
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  wp_auto
  idx_if
  wp_apply wp_load_slice_index b _ _ _ w1 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_pures
  wp_apply wp_store_slice_index b _ _ _ $$ [Hb] with Hb
  · iframe Hb; ipureintro
    simp (disch := decide) only [sint_W64_lit]
    simp only [List.length_set, List.length_append, List.length_cons, List.length_nil]
    omega
  (try wp_auto)
  idx_if
  wp_pures
  wp_apply wp_store_slice_index b _ _ _ $$ [Hb] with Hb
  · iframe Hb; ipureintro
    simp (disch := decide) only [sint_W64_lit]
    simp only [List.length_set, List.length_append, List.length_cons, List.length_nil]
    omega
  iapply HΦ
  simp only [u16Le, List.cons_append, List.nil_append, List.set_cons_succ, List.set_cons_zero]
  iexact Hb

theorem wp_littleEndian_Uint16 (le : littleEndian) (b : GoSlice) (w0 w1 : w8) (rem : List w8)
    (dq : DFrac) :
    {{ (b ↦*{dq} ([w0, w1] ++ rem) : IProp GF) }}
      (App (Val (le @!! littleEndian.ty @!! go!"Uint16")) (Val #b))
    {{ (r : w16), RET #r; ⌜uint.Z r = uint.Z w0 + 256 * uint.Z w1⌝ ∗ b ↦*{dq} ([w0, w1] ++ rem) }} := by
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  wp_auto
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w1 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w0 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w1 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  iapply HΦ
  iframe Hb
  ipureintro
  have e0 : W16 (uint.Z w0) = w0.setWidth 16 := by
    apply BitVec.eq_of_toNat_eq; simp [W16, uint.Z]
  have e1 : W16 (uint.Z w1) = w1.setWidth 16 := by
    apply BitVec.eq_of_toNat_eq; simp [W16, uint.Z]
  have e2 : (w1.setWidth 16 <<< W64 8) = w1.setWidth 16 <<< 8 := rfl
  rw [e0, e1, e2]
  have := w0.isLt
  have h := toNat_or_shl (w0.setWidth 16) w1 8 (by simp; omega) (by omega)
  simp only [uint.Z]
  rw [h]; simp; omega

/-- `(*littleEndian).PutUint16` on the global `LittleEndian`. -/
theorem wp_LittleEndian_PutUint16 (b : GoSlice) (space rem : List w8) (v : w16)
    (Hlen : space.length = 2) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗ b ↦* (space ++ rem) }}
      (App (App (Val ((globalAddr LittleEndian) @!! go.GoType.PointerType littleEndian.ty @!! go!"PutUint16"))
        (Val #b)) (Val #v))
    {{ RET #(); b ↦* (u16Le v ++ rem) }} := by
  wp_start as Hb
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  ihave #Hinit := isInit_access $$ Hpkg
  icases Hinit with ⟨#Hle, -⟩
  wp_auto
  wp_apply wp_littleEndian_PutUint16 _ b space rem v Hlen $$ [$Hb] as Hb
  iapply HΦ $$ Hb

/-- `(*littleEndian).Uint16` on the global `LittleEndian`. -/
theorem wp_LittleEndian_Uint16 (b : GoSlice) (w0 w1 : w8) (rem : List w8) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗ b ↦*{dq} ([w0, w1] ++ rem) }}
      (App (Val ((globalAddr LittleEndian) @!! go.GoType.PointerType littleEndian.ty @!! go!"Uint16"))
        (Val #b))
    {{ (r : w16), RET #r; ⌜uint.Z r = uint.Z w0 + 256 * uint.Z w1⌝ ∗ b ↦*{dq} ([w0, w1] ++ rem) }} := by
  wp_start as Hb
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  ihave #Hinit := isInit_access $$ Hpkg
  icases Hinit with ⟨#Hle, -⟩
  wp_auto
  wp_apply wp_littleEndian_Uint16 _ b w0 w1 rem dq $$ [$Hb] as %r ⟨%Hr, Hb⟩
  iapply HΦ
  iframe Hb; ipureintro; exact Hr

end wps

end encoding.binary

end Perennial
