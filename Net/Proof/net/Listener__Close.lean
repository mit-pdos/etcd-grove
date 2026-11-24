/-
The proof of `Net/Spec/net/Listener__Close.lean`: the method resolves to
`TCPListener.Close.impl`, the extension's `LisClose` (`Net.wp_net_LisClose`), then `nil` or an
`*OpError`.
-/
module

public import Net.Spec.net.Listener__Close
public import Net.Proof.net.OpErrorMsg

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions]
variable [go.BasicIntoValInj]

theorem Listener.Close.wp_proof : Listener.Close.spec (GF := GF) (hG := hG) := by
  intro t l x a Q
  wp_start as ⟨#Hl, Hon, HAU⟩
  ihave ⟨%nw, %fd, %lc, %ra, %hnl, #Ht, #Hfd, #Hx⟩ := lisAt_elim _ _ _ $$ Hl
  ihave ⟨%v, %hv, #Hv⟩ := fdAt_elim _ _ _ _ _ $$ Hfd
  obtain ⟨-, rfl, rfl, rfl⟩ := hv
  ihave %Hfdn := typedPointsto_not_null _ _ _ $$ Hv
  iStructNamed Hv
  ihave #Ht2 := Ht
  iStructNamed Ht2
  (try wp_method_call)
  wp_auto
  wp_apply wp_TCPListener_ok t fd lc Hfdn $$ Ht
  (try wp_auto)
  wp_apply wp_TCPListener_close t l v.laddr' a Q $$ Hl Hon HAU as %res %e HQ #He
  rcases res with _ | k
  · unfold resKind; icases He with %he; subst he
    wp_auto
    iapply HΦ
    iexists none; iframe HQ
    unfold resErr; ipureintro; rfl
  · rw [show resKind (GF := GF) (some k) none (· = go!"close") e =
      kindErr k none (· = go!"close") e from rfl]
    ihave %hne := kindErr_ne_nil _ none _ e (fun _ h => by cases h) $$ He
    obtain ⟨ie, rfl⟩ : ∃ ie, e = GoInterface.ok ie := by
      cases e with | ok ie => exact ⟨ie, rfl⟩ | nil => exact absurd rfl hne
    wp_auto
    wp_alloc pe as Hpe
    ipersist Hpe
    wp_auto
    iapply HΦ
    iexists some k
    iframe HQ
    iapply resErr_intro hnl.1
      (by first | exact edTyped_none | (intro x h; cases h; exact ⟨_, rfl⟩)) $$ Hpe He
    all_goals first | iapply addrOrNil_nil | (iapply addrOrNil_addr; iassumption)

end proof

end net
end Perennial
