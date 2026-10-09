/-
`sync.Once.Do` with a frame: a variant of Perennial's `Once.wp_Do` (`Perennial/Proof/
sync_proof/once.lean`) in which the caller lends a resource `R` to the closure, which may
turn it into `R'`; the caller gets `R'` back if its closure ran, `R` if an earlier one had.
Perennial's spec takes a persistent triple `{{ P }} f #() {{ Q }}`, so a closure can use only
the `Once`'s own one-shot `P`, never the caller's resources: the watcher's `Stop`/`Compact`
close a channel whose state the caller (holding the producer's view) must pass in. Proved
from `isOnce`'s definition, like `Once.wp_Do` and `Once.wp_doSlow`, whose proofs these
follow.
-/
module

public import Perennial.Proof.sync

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode sync

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- The closure's (one-shot) triple in `Once.wp_Do_frame`: from the `Once`'s `P` and the
caller's `R`, `f()` returns with `Q` and `R'`. -/
def onceFrameSpec (f : GoFunc) (P Q R R' : IProp GF) : IProp GF :=
  iprop(∀ Ψ : val → IProp GF, P ∗ R -∗ ▷ (Q ∗ R' -∗ Ψ #()) -∗
    WP (App (Val #f) (Val #())) {{ Ψ }})

theorem Once.wp_doSlow_frame (o : Loc) (P Q R R' : IProp GF) (f : GoFunc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isOnce o P Q ∗ R ∗ onceFrameSpec f P Q R R' }}
      (App (Val (o @!! go.GoType.PointerType Once.ty @!! go!"doSlow")) (Val #f))
    {{ RET #(); Q ∗ (R' ∨ R) }} := by
  wp_start as ⟨#HO, HR, Hf⟩
  simp only [isOnce_unseal, isOnceDef]
  iNamed HO
  iapply wp_with_defer
  iintro %defer Hdefer
  wp_auto_lc 2
  wp_apply Mutex.wp_Lock $$ [$Hm] with ⟨Hlocked, Hlk⟩
  unfold OnceLockInv
  icases Hlk with ⟨%done, done2, HPQ⟩
  wp_apply_core sync.atomic.Bool.wp_Load $$ [] [-]
  · iPkgInit
  iinv Qinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  unfold OnceInv
  icases Hi with ⟨%done0, done1, #HQ⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  icombine done1 done2 gives %Heq
  subst Heq
  inext
  iexists done0
  iframe done1
  iintro done1
  imod Hmask with _
  imod Hclose $$ [done1] with _
  · inext; iexists done0; iframe done1; iframe #
  imodintro
  wp_auto
  cases done0
  · simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    unfold onceFrameSpec
    wp_apply Hf $$ [HPQ HR] with ⟨HQ', HR'⟩
    · iframe
    ihave #HQ2 := Q_persistent $$ HQ'
    wp_apply_core sync.atomic.Bool.wp_Store $$ [] [-]
    · iPkgInit
    iinv Qinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc2 Hi with Hi
    icases Hi with ⟨%d, done1, #HQ1⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    icombine done1 done2 gives %Heq
    subst Heq
    ihave Hfull := (ownBool_halves (OnceDone (GF := GF) o) false).2 $$ [done1 done2]
    · iframe
    inext
    iexists false
    iframe Hfull
    iintro Hfull
    icases (ownBool_halves (OnceDone (GF := GF) o) true).1 $$ Hfull with ⟨done1, done2⟩
    imod Hmask with _
    imod Hclose $$ [done1] with _
    · inext; iexists true; iframe done1; imodintro; iintro _; iexact HQ2
    imodintro
    wp_auto
    wp_apply Mutex.wp_Unlock (OnceM (GF := GF) o) (OnceLockInv o P Q) $$ [Hlocked done2 HQ']
    · iframe #; iframe Hlocked; inext; unfold OnceLockInv; iexists true
      simp only [↓reduceIte]; iframe
    iapply HΦ
    iframe HQ2
    ileft; iexact HR'
  · simp only [Bool.not_true, ↓reduceIte]
    ihave #HQ2 := Q_persistent $$ HPQ
    wp_auto
    wp_apply Mutex.wp_Unlock (OnceM (GF := GF) o) (OnceLockInv o P Q) $$ [Hlocked done2 HPQ]
    · iframe #; iframe Hlocked; inext; unfold OnceLockInv; iexists true
      simp only [↓reduceIte]; iframe
    iapply HΦ
    iframe HQ2
    iright; iexact HR

/-- `o.Do(f)` with a frame (see the module docstring): `f` runs at most once over all calls;
this call returns `Q` and either `R'` (its `f` ran, from `P ∗ R`) or `R` back (an earlier
call's `f` had run). -/
theorem Once.wp_Do_frame (o : Loc) (P Q R R' : IProp GF) (f : GoFunc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isOnce o P Q ∗ R ∗ onceFrameSpec f P Q R R' }}
      (App (Val (o @!! go.GoType.PointerType Once.ty @!! go!"Do")) (Val #f))
    {{ RET #(); Q ∗ (R' ∨ R) }} := by
  wp_start as ⟨#HO, HR, Hf⟩
  simp only [isOnce_unseal, isOnceDef]
  iNamed HO
  wp_auto_lc 1
  wp_apply_core sync.atomic.Bool.wp_Load $$ [] [-]
  · iPkgInit
  iinv Qinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  unfold OnceInv
  icases Hi with ⟨%done, done1, #HQ⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists done
  iframe done1
  iintro done1
  imod Hmask with _
  imod Hclose $$ [done1] with _
  · inext; iexists done; iframe done1; iframe #
  imodintro
  wp_auto
  cases done
  · (try wp_auto)
    wp_apply Once.wp_doSlow_frame o P Q R R' f $$ [$HR $Hf] with H
    · rw [isOnce_unseal]; unfold isOnceDef; iframe #
    iapply HΦ $$ H
  · (try wp_auto)
    iapply HΦ
    isplitl []
    · iapply HQ
      ipureintro; rfl
    iright; iexact HR

end wps

end EtcdGrove
end Perennial
