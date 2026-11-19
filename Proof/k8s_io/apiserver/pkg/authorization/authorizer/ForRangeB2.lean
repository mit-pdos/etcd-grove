/-
Lean-first (no Rocq counterpart).

# Ranges over iterators (`for x := range f`, `for k, v := range f`)

Perennial has no WP rule for `func.forRange` (`Perennial/Golang/Defn/Loop.lean`). This file has
local ones, after `Proof/k8s_io/apiserver/pkg/storage/etcd3/ForRange.lean`'s `wp_forRange2`, with a
later in the yield function's premise (the yield function takes a step before running the body):

- `wp_forRange1`, `wp_forRange2'`: the raw rules for one and two iteration values: the caller
  proves `f`'s WP for an abstract yield function `y` holding the token `Tok`; see `ForRange.lean`'s
  header for `Tok`, `Done` and `forRangePost`;
- `wp_forRange_seqOk`, `wp_forRange_seq2Ok`: the rules a client uses, for an iterator given by the
  authorizer vocabulary's `seqOk f xs` / `seq2Ok f xs` (`Defs.lean`): a loop invariant `P i` (before
  element `i`); the body, from `P i` on element `i`, ends normally or with `continue` in `P (i+1)`,
  or with `break`/`return` in `R bv`; the loop ends in `P xs.length` or `R bv`.

A candidate general Perennial lemma (`notes/perennial-changes.md`).
-/
module

public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.Defs
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ForRange

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Perennial
namespace EtcdGrove
namespace authorizer

open Iris Iris.BI Iris.ProgramLogic Iris.ProofMode
open EtcdGrove.k8s (forRangePost wp_app_recV)

section forRange
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `for x := range f` (see the file header). -/
theorem wp_forRange1 (f body : val) (Φ : val → IProp GF) (hf : f.isPanic = false)
    (hb : body.isPanic = false) :
    (∀ (y : GoFunc) (Tok : IProp GF) (Done : val → IProp GF), Tok -∗
      □ (∀ (k : val) (Ψ : val → IProp GF), ⌜k.isPanic = false⌝ -∗ Tok -∗
          ▷ WP (App (Val body) (Val k)) {{ forRangePost Tok Done Ψ }} -∗
          WP (App (Val #y) (Val k)) {{ Ψ }}) -∗
      WP (App (Val f) (Val #y)) {{ w, ⌜w.isPanic = false⌝ ∗
        ((Tok ∗ Φ executeVal) ∨ (Done breakVal ∗ Φ executeVal) ∨
          (∃ r, Done (returnVal r) ∗ Φ (returnVal r))) }}) ⊢
    WP (App (App (Val (func.forRange 1)) (Val f)) (Val body)) {{ Φ }} := by
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
    iintro !> %k %Ψ %hk ⟨state, Hexit⟩ Hbody
    rw [go.intoVal_unfold GoFunc]
    wp_call
    wp_auto
    wp_bind (App (Val body) _)
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

/-- `for k, v := range f` (see the file header). -/
theorem wp_forRange2' (f body : val) (Φ : val → IProp GF) (hf : f.isPanic = false)
    (hb : body.isPanic = false) :
    (∀ (y : GoFunc) (Tok : IProp GF) (Done : val → IProp GF), Tok -∗
      □ (∀ (k v : val) (Ψ : val → IProp GF), ⌜k.isPanic = false ∧ v.isPanic = false⌝ -∗ Tok -∗
          ▷ WP (App (App (Val body) (Val k)) (Val v)) {{ forRangePost Tok Done Ψ }} -∗
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

/-- The outcome of a loop body run on element `i` (see the file header): `P (i+1)` on a normal end
or `continue`, `R bv` on a `break` or `return`. -/
def iterBodyPost (P : Nat → IProp GF) (R : val → IProp GF) (i : Nat) (bv : val) : IProp GF :=
  iprop((⌜bv = executeVal ∨ bv = continueVal⌝ ∗ P (i + 1)) ∨
    (⌜bv = breakVal ∨ ∃ w, bv = returnVal w ∧ w.isPanic = false⌝ ∗ R bv))

/-- How a range loop's outcome gives `Φ`: from `P n` at the end, from `R` after a `break` or a
`return`. -/
def iterExit (P : Nat → IProp GF) (R : val → IProp GF) (n : Nat) (Φ : val → IProp GF) :
    IProp GF :=
  iprop((P n -∗ Φ executeVal) ∧ (R breakVal -∗ Φ executeVal) ∧
    (∀ w, R (returnVal w) -∗ Φ (returnVal w)))

/-- **`for x := range f`** over an iterator `seqOk f xs` (see the file header). -/
theorem wp_forRange_seqOk {V : Type} (f : GoFunc) (xs : List V) (body : val)
    (hb : body.isPanic = false) (P : Nat → IProp GF) (R : val → IProp GF) (Φ : val → IProp GF) :
    seqOk f xs -∗ P 0 -∗
    (□ ∀ (i : Nat) (x : V), ⌜xs[i]? = some x⌝ -∗ P i -∗
        WP (App (Val body) (Val #x)) {{ iterBodyPost P R i }}) -∗
    iterExit P R xs.length Φ -∗
    WP (App (App (Val (func.forRange 1)) (Val #f)) (Val body)) {{ Φ }} := by
  iintro #Hf HP #Hbody Hexit
  iapply wp_forRange1 #f body Φ (by rw [go.intoVal_unfold GoFunc]; rfl) hb
  iintro %y %Tok %Done HTok #Hy
  unfold seqOk iterRunOk yield1Ok
  ispecialize Hf $$ %y %(fun i => iprop(Tok ∗ P i))
    %(iprop(∃ bv, Done bv ∗ R bv ∗ ⌜bv = breakVal ∨ ∃ w, bv = returnVal w ∧ w.isPanic = false⌝))
  iapply Hf $$ [] [HTok HP]
  · iintro !> %i %x %hx !> %Ψ ⟨HTok, HP⟩ HΨ
    iapply Hy $$ %_ %Ψ %(isPanic_intoVal _) HTok
    inext
    iapply wp_wand $$ [HP]
    · iapply Hbody $$ %i %x %hx HP
    iintro %bv Hpost
    unfold iterBodyPost forRangePost
    icases Hpost with (⟨%Hbv, HP⟩ | ⟨%Hbv, HR⟩)
    · ileft
      isplitr
      · ipureintro; exact Hbv
      iintro HTok
      iapply HΨ $$ %true
      simp only [↓reduceIte]
      iframe
    · iright
      isplitr
      · ipureintro; exact Hbv
      iintro HDone
      iapply HΨ $$ %false
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexists bv
      iframe
      ipureintro; exact Hbv
  · isplitl [HTok]
    · iexact HTok
    · iexact HP
  iintro !> Hend
  isplitr
  · ipureintro; exact isPanic_intoVal _
  unfold iterExit
  icases Hend with (⟨HTok, HP⟩ | ⟨%bv, HDone, HR, %Hbv⟩)
  · ileft
    iframe
    icases Hexit with ⟨Hexit, -⟩
    iapply Hexit
    iexact HP
  · rcases Hbv with rfl | ⟨w, rfl, hw⟩
    · iright; ileft
      iframe
      icases Hexit with ⟨-, Hexit, -⟩
      iapply Hexit
      iexact HR
    · iright; iright
      iexists w
      iframe
      icases Hexit with ⟨-, -, Hexit⟩
      iapply Hexit
      iexact HR

/-- **`for k, v := range f`** over an iterator `seq2Ok f xs` (see the file header). -/
theorem wp_forRange_seq2Ok {K V : Type} (f : GoFunc) (xs : List (K × V)) (body : val)
    (hb : body.isPanic = false) (P : Nat → IProp GF) (R : val → IProp GF) (Φ : val → IProp GF) :
    seq2Ok f xs -∗ P 0 -∗
    (□ ∀ (i : Nat) (k : K) (v : V), ⌜xs[i]? = some (k, v)⌝ -∗ P i -∗
        WP (App (App (Val body) (Val #k)) (Val #v)) {{ iterBodyPost P R i }}) -∗
    iterExit P R xs.length Φ -∗
    WP (App (App (Val (func.forRange 2)) (Val #f)) (Val body)) {{ Φ }} := by
  iintro #Hf HP #Hbody Hexit
  iapply wp_forRange2' #f body Φ (by rw [go.intoVal_unfold GoFunc]; rfl) hb
  iintro %y %Tok %Done HTok #Hy
  unfold seq2Ok iterRunOk yield2Ok
  ispecialize Hf $$ %y %(fun i => iprop(Tok ∗ P i))
    %(iprop(∃ bv, Done bv ∗ R bv ∗ ⌜bv = breakVal ∨ ∃ w, bv = returnVal w ∧ w.isPanic = false⌝))
  iapply Hf $$ [] [HTok HP]
  · iintro !> %i %k %v %hx !> %Ψ ⟨HTok, HP⟩ HΨ
    iapply Hy $$ %(#k) %(#v) %Ψ %(And.intro (isPanic_intoVal k) (isPanic_intoVal v)) HTok
    inext
    iapply wp_wand $$ [HP]
    · iapply Hbody $$ %i %k %v %hx HP
    iintro %bv Hpost
    unfold iterBodyPost forRangePost
    icases Hpost with (⟨%Hbv, HP⟩ | ⟨%Hbv, HR⟩)
    · ileft
      isplitr
      · ipureintro; exact Hbv
      iintro HTok
      iapply HΨ $$ %true
      simp only [↓reduceIte]
      iframe
    · iright
      isplitr
      · ipureintro; exact Hbv
      iintro HDone
      iapply HΨ $$ %false
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexists bv
      iframe
      ipureintro; exact Hbv
  · isplitl [HTok]
    · iexact HTok
    · iexact HP
  iintro !> Hend
  isplitr
  · ipureintro; exact isPanic_intoVal _
  unfold iterExit
  icases Hend with (⟨HTok, HP⟩ | ⟨%bv, HDone, HR, %Hbv⟩)
  · ileft
    iframe
    icases Hexit with ⟨Hexit, -⟩
    iapply Hexit
    iexact HP
  · rcases Hbv with rfl | ⟨w, rfl, hw⟩
    · iright; ileft
      iframe
      icases Hexit with ⟨-, Hexit, -⟩
      iapply Hexit
      iexact HR
    · iright; iright
      iexists w
      iframe
      icases Hexit with ⟨-, -, Hexit⟩
      iapply Hexit
      iexact HR

end forRange

end authorizer
end EtcdGrove
end Perennial
