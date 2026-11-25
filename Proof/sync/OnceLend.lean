/-
**`sync.Once.Do` lending the closure a resource of the caller** (2026-11-24). Lean-first.

Perennial's `sync.Once.Do.spec` gives the closure only the once's `P`. Go runs the closure on the
caller's goroutine, and `Do` returns only after it has run (or at once, when the once is done), so
the caller may lend it a resource `R` of its own, which comes back with `Q`
(`wp_Once_Do_lend`: `{{ isOnce o P Q ∗ R ∗ {{ P ∗ R }} f() {{ Q ∗ R }} }} o.Do(f) {{ Q ∗ R }}`).
Used by k8s' `compactor.Stop`, whose `onClose` closure calls `Client.Endpoints()` with the caller's
`levelTok 0`. Proved over the real code (`sync.Once.Do`'s and `doSlow`'s translations), by the
argument of Perennial's `Proof/sync/Once__Do.lean` and `Once__doSlow.lean`, with `R` threaded
through; a stand-in for a Perennial addition (`notes/perennial-changes.md`).
-/
module

public import Perennial.Proof.sync.OnceDefs
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode
open sync

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- `o.doSlow(f)`, the closure lent `R`. -/
theorem wp_Once_doSlow_lend (o : Loc) (P Q R : IProp GF) (f : GoFunc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isOnce o P Q ∗ R ∗
        iprop({{ P ∗ R }} (App (Val #f) (Val #())) {{ RET #(); Q ∗ R }}) }}
      (App (Val (o @!! go.GoType.PointerType Once.ty @!! go!"doSlow")) (Val #f))
    {{ RET #(); Q ∗ R }} := by
  wp_start as ⟨#HO, HR, #Hf⟩
  simp only [isOnce_unseal, isOnceDef]
  iNamed HO
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply sync.Mutex.wp_Lock $$ [$Hm] with ⟨Hlocked, Hlk⟩
  unfold OnceLockInv
  icases Hlk with ⟨%done, done2, HPQ⟩
  wp_apply_core sync.atomic.Bool.wp_Load $$ [] [-]
  · iPkgInit
  iinv Qinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold OnceInv
  icases Hi with ⟨%done0, done1, #HQ⟩
  icombine done1 done2 gives %Heq
  subst Heq
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
    wp_apply Hf $$ [HPQ HR] with ⟨HQ', HR⟩
    · iframe
    ihave #HQ2 := Q_persistent $$ HQ'
    wp_apply_core sync.atomic.Bool.wp_Store $$ [] [-]
    · iPkgInit
    iinv Qinv with Hi Hclose
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    icases Hi with ⟨%d, done1, #HQ1⟩
    icombine done1 done2 gives %Heq
    subst Heq
    ihave Hfull := (ownBool_halves (OnceDone (GF := GF) o) false).2 $$ [done1 done2]
    · iframe
    iexists false
    iframe Hfull
    iintro Hfull
    icases (ownBool_halves (OnceDone (GF := GF) o) true).1 $$ Hfull with ⟨done1, done2⟩
    imod Hmask with _
    imod Hclose $$ [done1] with _
    · inext; iexists true; iframe done1; imodintro; iintro _; iexact HQ2
    imodintro
    wp_auto
    wp_apply sync.Mutex.wp_Unlock (OnceM (GF := GF) o) (OnceLockInv o P Q) $$ [Hlocked done2 HQ']
    · iframe #; iframe Hlocked; inext; unfold OnceLockInv; iexists true
      simp only [↓reduceIte]; iframe
    iapply HΦ
    iframe HR
    iexact HQ2
  · simp only [Bool.not_true, ↓reduceIte]
    ihave #HQ2 := Q_persistent $$ HPQ
    wp_auto
    wp_apply sync.Mutex.wp_Unlock (OnceM (GF := GF) o) (OnceLockInv o P Q) $$ [Hlocked done2 HPQ]
    · iframe #; iframe Hlocked; inext; unfold OnceLockInv; iexists true
      simp only [↓reduceIte]; iframe
    iapply HΦ
    iframe HR
    iexact HQ2

/-- `o.Do(f)`, the closure lent `R` (see the file header). -/
theorem wp_Once_Do_lend (o : Loc) (P Q R : IProp GF) (f : GoFunc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isOnce o P Q ∗ R ∗
        iprop({{ P ∗ R }} (App (Val #f) (Val #())) {{ RET #(); Q ∗ R }}) }}
      (App (Val (o @!! go.GoType.PointerType Once.ty @!! go!"Do")) (Val #f))
    {{ RET #(); Q ∗ R }} := by
  wp_start as ⟨#HO, HR, #Hf⟩
  simp only [isOnce_unseal, isOnceDef]
  iNamed HO
  wp_auto
  wp_apply_core sync.atomic.Bool.wp_Load $$ [] [-]
  · iPkgInit
  iinv Qinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold OnceInv
  icases Hi with ⟨%done, done1, #HQ⟩
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
    wp_apply wp_Once_doSlow_lend o P Q R f $$ [$HR] with HQR
    · rw [isOnce_unseal]; unfold isOnceDef; iframe #
    iapply HΦ $$ HQR
  · (try wp_auto)
    iapply HΦ
    iframe HR
    iapply HQ
    ipureintro; rfl

end proof

end EtcdGrove
end Perennial
