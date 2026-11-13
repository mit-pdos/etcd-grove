/-
The read path's (U6, `notes/bbolt-proof-plan.md`) byte points-to facts: bounds, sub-ranges, and
byte slices over bytes (ported from Perennial's `unsafememory` example, `Pages.lean`).
-/
module

public import Proof.go_etcd_io.bbolt.Model.Page

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


namespace Read

open Iris Iris.BI Iris.ProofMode

section bytes
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

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


instance bytesPointsto_discard_persistent (l : Loc) (bs : List w8) :
    Persistent (bytesPointsto (GF := GF) l .discard bs) := by
  induction bs generalizing l <;> unfold bytesPointsto <;> infer_instance

/-- `bytesPointsto_in_bounds`, keeping the points-to. -/
theorem bytesPointsto_bounds (l : Loc) (dq : DFrac) (bs : List w8) (h : bs ≠ []) :
    bytesPointsto (GF := GF) l dq bs ⊢ bytesPointsto l dq bs ∗
      ⌜0 < l.addr ∧ l.addr + bs.length ≤ maxAddr⌝ :=
  persistent_entails_left (bytesPointsto_in_bounds l dq bs h)

/-- A sub-range of a byte points-to, out and back. -/
theorem bytesPointsto_sub_acc (l : Loc) (dq : DFrac) (pg bs : List w8) (off : Nat)
    (hlen : off + bs.length ≤ pg.length) (hbs : bytesAt pg off bs.length = bs) :
    bytesPointsto (GF := GF) l dq pg ⊢ bytesPointsto (l +ₗ (off : Int)) dq bs ∗
      (bytesPointsto (l +ₗ (off : Int)) dq bs -∗ bytesPointsto l dq pg) := by
  have e : pg = pg.take off ++ (bs ++ (pg.drop off).drop bs.length) := by
    unfold bytesAt at hbs
    conv => lhs; rw [← List.take_append_drop off pg]
    conv => lhs; arg 2; rw [← List.take_append_drop bs.length (pg.drop off), hbs]
  have hk : (pg.take off).length = off := by simp; omega
  have Hs := (bytesPointsto_app (GF := GF) l dq (pg.take off) (bs ++ (pg.drop off).drop bs.length))
  have Hs2 := (bytesPointsto_app (GF := GF) (l +ₗ ((pg.take off).length : Int)) dq bs
    ((pg.drop off).drop bs.length))
  rw [← e, hk] at Hs
  rw [hk] at Hs2
  iintro Hp
  icases Hs.1 $$ Hp with ⟨H1, Hp⟩
  icases Hs2.1 $$ Hp with ⟨H2, H3⟩
  iframe H2
  iintro H2
  iapply Hs.2
  iframe H1
  iapply Hs2.2
  iframe

end bytes

end Read

end bbolt
end EtcdGrove
end Perennial
