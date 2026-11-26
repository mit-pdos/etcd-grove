/-
`wp_for_loeb`: one unfolding of a Go `for` loop (`doFor`), the loop again under a later at the end
of an iteration that continues. With `iloeb` at the loop (after `wp_bind` to it) it proves a loop
whose state is easier to generalize than to state as an invariant (`wp_for`'s): the proofs of the
`os` models' loops, written over Lean recursion before the Go-model overlays (S5) made them Go
`for` loops. A fact about Perennial's `doFor` (a candidate for Perennial's `Loop.lean`,
`notes/perennial-changes.md`). Untrusted.
-/
module

public import Perennial.Golang.Theory.Auto

@[expose] public section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.ProofMode

section wp_for_loeb
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]
attribute [local instance] pure_test_execute pure_test_continue pure_test_break

/-- One iteration of `doFor cond body post`: the condition, then (if true) the body, whose
`forPostcondition` has the loop again, under a later, as its invariant. -/
theorem wp_for_loeb (s : Stuckness) (E : CoPset) (cond body post : val) (Φ : val → IProp GF)
    (hcond : cond.isPanic = false) (hbody : body.isPanic = false) (hpost : post.isPanic = false) :
    WP (App (Val cond) (Val #())) @ s; E {{ v,
        if decide (v = #true) then
          WP (App (Val body) (Val #())) @ s; E {{ forPostcondition s E post
            iprop(▷ WP (App (App (App (Val doFor) (Val cond)) (Val body)) (Val post)) @ s; E {{ Φ }})
            Φ }}
        else if decide (v = #false) then Φ executeVal else False }} ⊢
    WP (App (App (App (Val doFor) (Val cond)) (Val body)) (Val post)) @ s; E {{ Φ }} := by
  iintro Hloop1
  rw [doFor_unseal, forPostcondition_unseal]
  unfold forPostconditionDef
  wp_call
  wp_apply_core wp_wand $$ Hloop1
  iintro %c Hbody
  by_cases hc : c = #true
  · subst hc
    simp only [decide_true, ite_true]
    wp_pures
    wp_apply_core wp_wand $$ Hbody
    iintro %bc Hb
    icases Hb with (⟨%Hbc, HP⟩ | ⟨%Hbc, HP⟩ | ⟨%Hbc, HΦ⟩ | ⟨%v, %Hbc, HΦ⟩ | ⟨%p, %Hbc, HΦ⟩ |
      ⟨%Hbc, HΦ⟩)
    · subst Hbc
      wp_pures
      wp_apply_core wp_wand $$ HP
      iintro %_ ⟨%_, HIH⟩
      wp_pures
      wp_apply_core wp_wand $$ HIH
      iintro %v HΦ
      cases hv : v.isPanic
      · wp_pures
        iexact HΦ
      · obtain ⟨p, rfl⟩ := val.isPanic_eq_true hv
        wp_pures
        iexact HΦ
    · subst Hbc
      wp_pures
      wp_apply_core wp_wand $$ HP
      iintro %_ ⟨%_, HIH⟩
      wp_pures
      wp_apply_core wp_wand $$ HIH
      iintro %v HΦ
      cases hv : v.isPanic
      · wp_pures
        iexact HΦ
      · obtain ⟨p, rfl⟩ := val.isPanic_eq_true hv
        wp_pures
        iexact HΦ
    · subst Hbc
      wp_pures
      iexact HΦ
    · subst Hbc
      rw [returnVal_unseal]
      simp only [returnValDef]
      wp_pures
      iexact HΦ
    · subst Hbc
      wp_pures
      iexact HΦ
    · obtain ⟨l, rfl | rfl⟩ := Hbc
      · rw [breakToVal_unseal]
        simp only [breakToValDef]
        wp_pures
        iexact HΦ
      · rw [continueToVal_unseal]
        simp only [continueToValDef]
        wp_pures
        iexact HΦ
  · by_cases hc' : c = #false
    · subst hc'
      have : (#false : val) ≠ #true := fun h => absurd (GoGlobalContext.intoVal_inj_bool h) (by decide)
      simp only [_root_.decide_true, ite_true, this, decide_false, Bool.false_eq_true, ite_false]
      wp_pures
      iexact Hbody
    · simp only [hc, hc', decide_false, Bool.false_eq_true, ite_false]
      icases Hbody with %h
      exact h.elim

end wp_for_loeb

set_option hygiene false in
/-- `wp_for_bind`: bind the `doFor` loop at the head of the goal (then `iloeb as IH generalizing
...` and `wp_for_step`). -/
macro "wp_for_bind" : tactic => `(tactic| ((try wp_auto); wp_bind (App (App (App (Val doFor) _) _) _)))

set_option hygiene false in
/-- `wp_for_step`: one iteration of the `doFor` loop at the head of the goal (`wp_for_loeb`). At
the end of an iteration that continues, `wp_for_post` leaves `▷ WP (the loop)`: `inext` and
`iapply IH`. -/
macro "wp_for_step" : tactic => `(tactic| (
  iapply wp_for_loeb _ _ _ _ _ _ ?hcond ?hbody ?hpost
  case hcond => rfl
  case hbody => rfl
  case hpost => rfl
  wp_auto
  cleanup_bool_decide
  (try wp_auto)))

end EtcdGrove
end Perennial
