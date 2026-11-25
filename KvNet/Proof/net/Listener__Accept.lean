-- The copy for the part `KvNet/` of `Net/Proof/net/Listener__Accept.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The proof of `Net/Spec/net/Listener__Accept.lean`: the interface call resolves to
`TCPListener.Accept.impl`, the extension's `Accept` (`Net.wp_net_Accept`), then a new `*TCPConn`
holding the acceptor's end, as a `Conn`.
-/
module

public import KvNet.Spec.net.Listener__Accept
public import KvNet.Proof.net.OpErrorMsg

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

theorem Listener.Accept.wp_proof : Listener.Accept.spec (GF := GF) (hG := hG) := by
  intro t l x la Qfail Qok
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
  wp_apply wp_TCPListener_accept t l v.laddr' la $$ Hl Hon
  isplit
  · icases HAU with ⟨HAU, -⟩
    imod HAU with ⟨%o, Hlo, Hk⟩
    imodintro
    iexists o
    iframe Hlo
    iintro Hlo
    imod Hk $$ Hlo with HQ
    imodintro
    iintro %e #He
    ihave %hne := kindErr_ne_nil _ none _ e (fun _ h => by cases h) $$ He
    obtain ⟨ie, rfl⟩ : ∃ ie, e = GoInterface.ok ie := by
      cases e with | ok ie => exact ⟨ie, rfl⟩ | nil => exact absurd rfl hne
    wp_auto
    wp_alloc pe as Hpe
    ipersist Hpe
    wp_auto
    iapply HΦ
    iright
    iexists _
    iframe HQ
    iapply resErr_intro hnl.1
      (by first | exact edTyped_none | (intro x h; cases h; exact ⟨_, rfl⟩)) $$ Hpe He
    all_goals first | iapply addrOrNil_nil | (iapply addrOrNil_addr; iassumption)
  · icases HAU with ⟨-, HAU⟩
    iintro %a %ha
    imod HAU $$ %a %ha with ⟨%o, %S, Hlo, Hp, Hk⟩
    imodintro
    iexists o, S
    iframe Hlo Hp
    iintro %ho %c %hc Hlo Hp #Hat
    imod Hk $$ %ho %c %hc Hlo Hp Hat with HQ
    imodintro
    iintro %tc %la' %ra' #Hc
    wp_auto
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists c, a
    iframe HQ
    isplitr
    · ipureintro; exact ha
    unfold isConn
    iexists tc, la', ra'
    iframe Hc
    ipureintro; rfl

end proof

end net
end Perennial
