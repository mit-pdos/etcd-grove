/-
Byte points-to lemmas for U1's proofs (`ReadInodeFromPage`, `WriteInodeToPage`): bounds, byte
slices over a byte points-to, persistence. Copied from Perennial's `unsafememory/Pages.lean`,
whose module is an example's and cannot be imported here; they are general facts about
Perennial's definitions and belong in Perennial (`notes/bbolt-proof-plan.md`, U1's report).
-/
module

public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace internal
namespace common

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

/-- A word read as a non-negative natural number is that number's word. -/
theorem w64_of_sint_nat (w : w64) (n : Nat) (h : n = sint.nat w) (h0 : 0 ≤ sint.Z w) :
    w = W64 (n : Int) := by
  have hlt : sint.Z w < 2 ^ 63 := by have := w.toInt_lt; simp only [sint.Z]; omega
  simp only [sint.nat, sint.Z] at h h0 hlt
  apply BitVec.eq_of_toInt_eq
  rw [show (W64 (n : Int)).toInt = n from sint_Z_W64_nat _ (by omega)]
  omega

theorem sint_Z_eq_of_sint_nat (w : w64) (n : Nat) (h : n = sint.nat w) (h0 : 0 ≤ sint.Z w) :
    sint.Z w = n := by
  simp only [sint.nat, sint.Z] at h h0 ⊢; omega


section bytes
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
open ProofMode

/-- The bytes of a non-empty byte points-to lie in `(0, maxAddr]`. -/
theorem bytesPointsto_in_bounds (l : Loc) (dq : DFrac) (bs : List w8) (h : bs ≠ []) :
    bytesPointsto (GF := GF) l dq bs ⊢ ⌜0 < l.addr ∧ l.addr + bs.length ≤ maxAddr⌝ := by
  induction bs generalizing l with
  | nil => exact absurd rfl h
  | cons b bs ih =>
    unfold bytesPointsto
    iintro ⟨Hb, Hbs⟩
    icases heapPointsto_pos l dq _ $$ Hb with %H1
    icases heapPointsto_lt_maxAddr l dq _ $$ Hb with %H2
    cases bs with
    | nil => ipureintro; simp; omega
    | cons b' bs' =>
      icases ih (l +ₗ 1) (by simp) $$ Hbs with %H3
      ipureintro
      simp only [Loc.add, List.length_cons] at H3 ⊢
      omega

/-- `bytesPointsto_in_bounds` for bytes that may be empty. -/
theorem bytesPointsto_in_bounds_imp (l : Loc) (dq : DFrac) (bs : List w8) :
    bytesPointsto (GF := GF) l dq bs ⊢ ⌜bs ≠ [] → 0 < l.addr ∧ l.addr + bs.length ≤ maxAddr⌝ := by
  by_cases h : bs = []
  · iintro _; ipureintro; intro h'; exact absurd h h'
  · iintro H
    icases bytesPointsto_in_bounds l dq bs h $$ H with %Hb
    ipureintro; intro _; exact Hb

instance bytesPointsto_discard_persistent (l : Loc) (bs : List w8) :
    Persistent (bytesPointsto (GF := GF) l .discard bs) := by
  induction bs generalizing l <;> unfold bytesPointsto <;> infer_instance

theorem bytesPointsto_persist (l : Loc) (dq : DFrac) (bs : List w8) :
    bytesPointsto (GF := GF) l dq bs ⊢ |==> bytesPointsto l .discard bs := by
  induction bs generalizing l with
  | nil => unfold bytesPointsto; iintro _; imodintro; itrivial
  | cons b bs ih =>
    unfold bytesPointsto
    iintro ⟨Hb, Hbs⟩
    imod heapPointsto_persist l dq _ $$ Hb with Hb
    imod ih (l +ₗ 1) $$ Hbs with Hbs
    imodintro
    iframe

/-- A typed points-to of an equal value. -/
theorem typedPointsto_of_eq {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v w : V) (dq : DFrac) :
    typedPointsto (GF := GF) l v dq ∗ ⌜v = w⌝ ⊢ typedPointsto l w dq := by
  iintro ⟨H, %h⟩
  rw [← h]
  iexact H

/-- A typed points-to of a type with a byte view can be made persistent. -/
theorem typedPointsto_persist_view {V : Type} {n : Nat} [ByteEncoding V n] [TypedPointsto (GF := GF) V]
    [BytesView (GF := GF) V] (l : Loc) (v : V) (dq : DFrac) (hl : 0 < l.addr) :
    typedPointsto (GF := GF) l v dq ⊢ |==> typedPointsto l v .discard := by
  iintro H
  icases (typedPointsto_bytes l v dq hl).1 $$ H with H
  imod bytesPointsto_persist _ _ _ $$ H with H
  imodintro
  iapply (typedPointsto_bytes l v _ hl).2 $$ H

/-- A sub-range of persistent bytes. -/
theorem bytesPointsto_sub (l : Loc) (B X : List w8) (k : Nat) (hk : k + X.length ≤ B.length)
    (h : (B.drop k).take X.length = X) :
    bytesPointsto (GF := GF) l .discard B ⊢ bytesPointsto (l +ₗ (k : Int)) .discard X := by
  have e : B = B.take k ++ ((B.drop k).take X.length ++ (B.drop k).drop X.length) := by
    rw [List.take_append_drop, List.take_append_drop]
  have hk' : (B.take k).length = k := by simp; omega
  iintro HB
  rw [e]
  icases (bytesPointsto_app l _ _ _).1 $$ HB with ⟨-, HB⟩
  icases (bytesPointsto_app _ _ _ _).1 $$ HB with ⟨HX, -⟩
  rw [hk', h]
  iexact HX

/-- A byte points-to from a positive address is a byte slice there. -/
theorem bytesPointsto_ownSlice (l : Loc) (dq : DFrac) (bs : List w8) (hl : 0 < l.addr)
    (hlen : bs.length < 2 ^ 63) :
    bytesPointsto (GF := GF) l dq bs ⊣⊢
      slice.mk l (W64 (bs.length : Int)) (W64 (bs.length : Int)) ↦*{dq} bs := by
  have hz : sint.Z (W64 (bs.length : Int)) = bs.length := sint_Z_W64_nat _ hlen
  have hnn : l ≠ null := by intro h; subst h; simp [null] at hl
  rw [ownSlice_unseal]; unfold ownSliceDef
  dsimp only
  rw [hz]
  by_cases hbs : bs = []
  · subst hbs
    constructor
    · iintro _
      iright
      isplitl
      · iapply array_empty _ _ hnn
      · ipureintro; omega
    · iintro _; unfold bytesPointsto; itrivial
  · have ha := typedPointsto_byte_array (GF := GF) l (bs.length : Int) (array.mk _ bs) dq hbs
    constructor
    · iintro H
      iright
      isplitl
      · iapply ha.2; iframe H; ipureintro; rfl
      · ipureintro; omega
    · iintro (%H | ⟨H, _⟩)
      · exfalso; apply hnn; have := congrArg GoSlice.ptr H.1; simpa [slice.nil] using this
      · icases ha.1 $$ H with ⟨_, H⟩
        iexact H

end bytes

end common
end internal
end bbolt
end EtcdGrove
end Perennial
