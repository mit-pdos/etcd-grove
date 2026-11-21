/-
The calls of a sorter whose `Less` answers anything (`sorterAnySpec`, `Spec/sort/SortAnyLess.lean`),
shared by the proofs of `sort.Sort`'s helpers for any `Less` (`Proof/sort/*AnyLess.lean`): as
Perennial's `sort.wp_sorter_Len`/`wp_sorter_Less`/`wp_sorter_Swap` (`Perennial/Proof/sort/
SorterBasics.lean`), with `sorterAnySpec` kept folded in the caller's context.
-/
module

public import Spec.sort.SortAnyLess

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace sortAny

-- (the proof-script macros of `partition` and `partitionEqual`, as Perennial's
-- `Perennial/Proof/sort/PartitionBasics.lean`; they name `anyPartInv`, below)
set_option hygiene false in
/-- An inner loop of `partition`/`partitionEqual` for any `Less` (`for i <= j && <Less> { i++ }`
or `{ j-- }`): whatever `Less` answers, `i ≤ j` keeps the index in range.  -/
macro "any_part_loop" idx:ident : tactic => `(tactic| (
  wp_bind (App (App (App (Val doFor) _) _) _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ anyPartInv R l a b i_ptr j_ptr)))
    $$ [HI]
  · unfold anyPartInv
    wp_for HI
    have Hlen2 := HPerm1.length_eq
    wp_if_destruct
    · list_elem L (sint.nat $idx) as xk
      list_elem L (sint.nat a) as xa
      first
        | wp_apply wp_any_Less x R L $idx a xk xa (by word) (by word) Hxk_lookup Hxa_lookup
            $$ [Hl] as %r Hl
          · iframe; iexact Hs
        | wp_apply wp_any_Less x R L a $idx xa xk (by word) (by word) Hxa_lookup Hxk_lookup
            $$ [Hl] as %r Hl
          · iframe; iexact Hs
      cases r <;> bool_if' <;> first
        | (isplitl []
           · itrivial
           iexists L, i_val, j_val
           iframe
           ipureintro
           exact ⟨ij_bound, HPerm1⟩)
        | (wp_auto
           wp_for_post
           iframe
           iexists L, _, _
           iframe
           ipureintro
           exact ⟨by word, HPerm1⟩)
    · isplitl []
      · itrivial
      iexists L, i_val, j_val
      iframe
      ipureintro
      exact ⟨ij_bound, HPerm1⟩
  iintro %v ⟨%Hv, HI⟩
  subst Hv
  (try wp_auto)))

set_option hygiene false in
/-- `data.Swap(i, j); i++; j--` of `partition`/`partitionEqual` for any `Less`. -/
macro "any_part_swap" : tactic => `(tactic| (
  have Hle : sint.Z i_val ≤ sint.Z j_val := by word
  list_elem L (sint.nat i_val) as xi
  list_elem L (sint.nat j_val) as xj
  wp_apply wp_any_Swap x R L i_val j_val xi xj (by word) (by word) Hxi_lookup Hxj_lookup
    $$ [Hl] as %L2 ⟨Hl, %HP2⟩
  · iframe; iexact Hs
  (try wp_auto)
  ihave HI : anyPartInv R l a b i_ptr j_ptr $$ [Hl i j]
  · unfold anyPartInv
    iexists L2, (i_val + W64 1), (j_val - W64 1)
    iframe
    ipureintro
    exact ⟨by word, HPerm1.trans HP2⟩))


section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable {E : Type}

theorem wp_any_Len (x : GoInterfaceOk) (R : List E → IProp GF) (l : List E) :
    {{ sorterAnySpec x R ∗ R l }}
      (App (Val #(methods x.ty go!"Len" x.v)) (Val #()))
    {{ RET #(W64 l.length); R l }} := by
  iintro %Φ ⟨#Hs, Hl⟩ HΦ
  unfold sorterAnySpec
  icases Hs with ⟨#HLen, -, -⟩
  iapply HLen $$ Hl HΦ

theorem wp_any_Less (x : GoInterfaceOk) (R : List E → IProp GF)
    (l : List E) (i j : w64) (a b : E) (hi : 0 ≤ sint.Z i) (hj : 0 ≤ sint.Z j)
    (ha : l[sint.nat i]? = some a) (hb : l[sint.nat j]? = some b) :
    {{ sorterAnySpec x R ∗ R l }}
      (App (App (Val #(methods x.ty go!"Less" x.v)) (Val #i)) (Val #j))
    {{ (r : Bool), RET #r; R l }} := by
  iintro %Φ ⟨#Hs, Hl⟩ HΦ
  unfold sorterAnySpec
  icases Hs with ⟨-, #HLess, -⟩
  iapply HLess $$ %l %i %j %a %b [] Hl HΦ
  ipureintro; exact ⟨hi, hj, ha, hb⟩

/-- `Swap(i, j)`, with the result as `sorterAnySpec` states it. -/
theorem wp_any_Swap_raw (x : GoInterfaceOk) (R : List E → IProp GF)
    (l : List E) (i j : w64) (a b : E) (hi : 0 ≤ sint.Z i) (hj : 0 ≤ sint.Z j)
    (ha : l[sint.nat i]? = some a) (hb : l[sint.nat j]? = some b) :
    {{ sorterAnySpec x R ∗ R l }}
      (App (App (Val #(methods x.ty go!"Swap" x.v)) (Val #i)) (Val #j))
    {{ RET #(); R ((l.set (sint.nat i) b).set (sint.nat j) a) }} := by
  iintro %Φ ⟨#Hs, Hl⟩ HΦ
  unfold sorterAnySpec
  icases Hs with ⟨-, -, #HSwap⟩
  iapply HSwap $$ %l %i %j %a %b [] Hl HΦ
  ipureintro; exact ⟨hi, hj, ha, hb⟩

/-- A swap is a permutation. -/
theorem swap_raw_perm (l : List E) (i j : Nat) (a b : E) (ha : l[i]? = some a)
    (hb : l[j]? = some b) : l.Perm ((l.set i b).set j a) := by
  exact slices.swap_perm l j i b a hb ha

/-- `Swap(i, j)`: the sorter holds a permutation of its list, of the same length. -/
theorem wp_any_Swap (x : GoInterfaceOk) (R : List E → IProp GF)
    (l : List E) (i j : w64) (a b : E) (hi : 0 ≤ sint.Z i) (hj : 0 ≤ sint.Z j)
    (ha : l[sint.nat i]? = some a) (hb : l[sint.nat j]? = some b) :
    {{ sorterAnySpec x R ∗ R l }}
      (App (App (Val #(methods x.ty go!"Swap" x.v)) (Val #i)) (Val #j))
    {{ (l' : List E), RET #(); R l' ∗ ⌜l.Perm l'⌝ }} := by
  iintro %Φ ⟨#Hs, Hl⟩ HΦ
  iapply wp_any_Swap_raw x R l i j a b hi hj ha hb $$ [$Hs $Hl]
  inext
  iintro Hl
  iapply HΦ
  iframe Hl
  ipureintro
  exact swap_raw_perm l _ _ a b ha hb

/-- The loop invariant of `partition` and `partitionEqual` for any `Less` (Perennial's
`sort.partInv`/`sort.peqInv` without the order): `i` in `[a+1, b]`, `j` in `[a, b-1]`, the
sorter holding a permutation of `l`. -/
def anyPartInv (R : List E → IProp GF) (l : List E) (a b : w64) (i_ptr j_ptr : Loc) :
    IProp GF :=
  iprop(∃ (L : List E) (i_val j_val : w64),
    "Hl" ∷ R L ∗
    "i" ∷ i_ptr ↦ i_val ∗
    "j" ∷ j_ptr ↦ j_val ∗
    "%ij_bound" ∷ ⌜(sint.Z a + 1 ≤ sint.Z i_val ∧ sint.Z i_val ≤ sint.Z b) ∧
                   (sint.Z a ≤ sint.Z j_val ∧ sint.Z j_val ≤ sint.Z b - 1)⌝ ∗
    "%HPerm1" ∷ ⌜l.Perm L⌝)

/-- `sorterAnySpec` under an opaque name (as Perennial's `sort.sortHide`): for the Löb
induction hypothesis of `pdqsort`'s proof, which contains `▷`s. -/
def anyHide (P : IProp GF) : IProp GF := P

theorem anyHide_intro {P Q : IProp GF} : (□ anyHide P -∗ Q) ⊢ (□ P -∗ Q) := .rfl

theorem anyHide_elim {P Q : IProp GF} : (□ P -∗ Q) ⊢ (□ anyHide P -∗ Q) := .rfl

end defs

end sortAny

end EtcdGrove
end Perennial
