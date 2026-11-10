/-
Lean-first (no Rocq counterpart).

# A range over a function with two iteration values (`for k, v := range f`)

Perennial has no WP rule for `func.forRange` (`Perennial/Golang/Defn/Loop.lean`); this is a local
one for `n = 2`, for `store.GetList`'s `for chunk, chunkErr := range chunks` (stage 7e-2), recorded
in `notes/perennial-changes.md` as a candidate general Perennial lemma.

`wp_forRange2`: the caller proves `f`'s WP for an abstract yield function `y`, holding the token
`Tok` (the iterator may call `y`: `forRange`'s `state` cell is `0`, its `exit` cell untouched), with
`y`'s spec (a `GoFunc`, as iterators take it): called with `Tok`, `y k v` runs the body on `k v`; a body ending normally or with
`continue` gives `Tok` back and `y` returns `true`; a body ending with `break` or `return` gives
`Done bv` (the loop has ended with the outcome `bv`) and `y` returns `false`. After `f` returns
(with `Tok`: the loop ran to the end; or with `Done bv`), the loop's outcome is `executeVal` (for
the end and for a `break`) or the `return`. A body that panics is not covered (the rule asks the
body's outcome to be one of the four), nor is `f` calling `y` again after `false` or from the body
(Go panics; `Tok` is gone then).
-/
module

public import Perennial.Golang.Theory

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.ProofMode

section forRange
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The postcondition of a range-over-function body run by the yield function: `Ψ #true` with
`Tok` back on a normal end or `continue`, `Ψ #false` with `Done bv` on a `break` or `return`. -/
def forRangePost (Tok : IProp GF) (Done : val → IProp GF) (Ψ : val → IProp GF) (bv : val) :
    IProp GF :=
  iprop((⌜bv = executeVal ∨ bv = continueVal⌝ ∗ (Tok -∗ Ψ #true)) ∨
    (⌜bv = breakVal ∨ ∃ w, bv = returnVal w ∧ w.isPanic = false⌝ ∗ (Done bv -∗ Ψ #false)))

/-- A closure argument as a `GoFunc` value. -/
theorem wp_app_recV (f : val) (b x : Binder) (e : Expr) (Φ : val → IProp GF) :
    WP (App (Val f) (Val #(func.mk b x e))) {{ Φ }} ⊢ WP (App (Val f) (Val (RecV b x e))) {{ Φ }} := by
  rw [go.intoVal_unfold GoFunc]

/-- See the file header. -/
theorem wp_forRange2 (f body : val) (Φ : val → IProp GF) (hf : f.isPanic = false)
    (hb : body.isPanic = false) :
    (∀ (y : GoFunc) (Tok : IProp GF) (Done : val → IProp GF), Tok -∗
      □ (∀ (k v : val) (Ψ : val → IProp GF), ⌜k.isPanic = false ∧ v.isPanic = false⌝ -∗ Tok -∗
          WP (App (App (Val body) (Val k)) (Val v)) {{ forRangePost Tok Done Ψ }} -∗
          WP (App (App (Val #y) (Val k)) (Val v)) {{ Ψ }}) -∗
      WP (App (Val f) (Val #y)) {{ w, ⌜w.isPanic = false⌝ ∗
        ((Tok ∗ Φ executeVal) ∨ (Done breakVal ∗ Φ executeVal) ∨
          (∃ r, Done (returnVal r) ∗ Φ (returnVal r))) }}) ⊢
    WP (App (App (Val (func.forRange 2)) (Val f)) (Val body)) {{ Φ }} := by
  iintro H
  rw [func.forRange_unseal]
  unfold func.forRangeDef
  wp_call
  wp_auto
  have hex : executeVal.isPanic = false := by rw [executeVal_unseal]; rfl
  wp_bind (Primitive1 PrimOp1.AllocOp _)
  wp_apply (wp_alloc_untyped executeVal hex) as %exit_ptr Hexit
  wp_pures
  wp_bind (App (Val f) _)
  iapply wp_app_recV
  ispecialize H $$ %_ %(iprop(state_ptr ↦ W64 0 ∗ heapPointsto exit_ptr (DFrac.own 1) executeVal))
    %(fun bv => iprop(state_ptr ↦ W64 2 ∗ heapPointsto exit_ptr (DFrac.own 1) bv)) [state Hexit]
  · iframe
  iapply (wp_wand) $$ [H]
  · iapply H
    iintro !> %k %v %Ψ %hkv ⟨state, Hexit⟩ Hbody
    obtain ⟨hk, hv⟩ := hkv
    rw [go.intoVal_unfold GoFunc]
    wp_call
    wp_auto
    wp_bind (App (App (Val body) _) _)
    iapply (wp_wand) $$ [Hbody]
    · iexact Hbody
    iintro %bv Hpost
    unfold forRangePost
    icases Hpost with (⟨%Hbv, HW⟩ | ⟨%Hbv, HW⟩)
    · rcases Hbv with rfl | rfl
      · rw [executeVal_unseal]
        simp only [executeValDef]
        wp_auto
        iapply HW
        iframe
      · rw [continueVal_unseal]
        simp only [continueValDef]
        wp_auto
        iapply HW
        iframe
    · rcases Hbv with rfl | ⟨w, rfl, hw⟩
      · rw [breakVal_unseal]
        simp only [breakValDef]
        wp_auto
        wp_bind (App (App (Val Store) _) _)
        wp_apply (_internal_wp_untyped_store exit_ptr executeVal (PairV #go!"break" #()) rfl) $$ [$Hexit] as Hexit
        wp_pures
        iapply HW $$ [state Hexit]
        iframe
      · rw [returnVal_unseal]
        simp only [returnValDef]
        wp_auto
        wp_bind (App (App (Val Store) _) _)
        wp_apply (_internal_wp_untyped_store exit_ptr executeVal (PairV #go!"return" w) rfl) $$ [$Hexit] as Hexit
        wp_pures
        iapply HW $$ [state Hexit]
        iframe
  iintro %w ⟨%hw, Hres⟩
  wp_pures
  icases Hres with (⟨⟨state, Hexit⟩, HΦ⟩ | ⟨⟨state, Hexit⟩, HΦ⟩ | ⟨%r, ⟨state, Hexit⟩, HΦ⟩)
  · wp_auto
    wp_bind (App (Val Read) _)
    wp_apply (_internal_wp_untyped_read exit_ptr _ executeVal hex) $$ [$Hexit] as Hexit
    rw [executeVal_unseal]
    simp only [executeValDef]
    wp_auto
    iexact HΦ
  · wp_auto
    wp_bind (App (Val Read) _)
    wp_apply (_internal_wp_untyped_read exit_ptr _ breakVal (by rw [breakVal_unseal]; rfl))
      $$ [$Hexit] as Hexit
    rw [breakVal_unseal]
    simp only [breakValDef]
    wp_auto
    rw [executeVal_unseal]
    iexact HΦ
  · wp_auto
    wp_bind (App (Val Read) _)
    wp_apply (_internal_wp_untyped_read exit_ptr _ (returnVal r) (by rw [returnVal_unseal]; rfl))
      $$ [$Hexit] as Hexit
    rw [returnVal_unseal]
    simp only [returnValDef]
    wp_auto
    iexact HΦ

end forRange

end k8s
end EtcdGrove
end Perennial
