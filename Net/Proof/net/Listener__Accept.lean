/-
The proof of `Net/Spec/net/Listener__Accept.lean`: the interface call resolves to
`TCPListener.Accept.impl`, the extension's `Accept` (`Net.wp_net_Accept`), then a new `*TCPConn`
holding the acceptor's end, as a `Conn`.
-/
module

public import Net.Spec.net.Listener__Accept
public import Net.Proof.net.Errors

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
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

theorem Listener.Accept.wp_proof : Listener.Accept.spec (GF := GF) (hG := hG) := by
  intro t l x la Qfail Qok
  unfold lisAt
  wp_start as ⟨⟨%nw, %Hnw, #Ht, #Hx, %hl0⟩, #Hla, HQ⟩
  (try wp_method_call)
  (try unfold TCPListener.Accept.impl)
  rw [TCPListener_ty_eq]
  ihave #Ht2 := Ht
  iStructNamed Ht2
  wp_auto
  (try (rw [show decide (l = W64 0) = false by simpa using hl0]; wp_auto))
  wp_bind (ExternalOp _ _ _)
  iapply wp_net_Accept l la $$ Hla
  isplit
  · -- a failure
    icases HQ with ⟨HQ, -⟩
    imod HQ with ⟨%o, Hl, HQ⟩
    imodintro
    iexists o
    iframe Hl
    iintro Hl
    imod HQ $$ Hl with HQ
    imodintro
    rw [Conn_ty_eq]
    wp_auto
    cases o
    · wp_apply wp_pollErr (c := NetErr.closed.code) .closed none go!"accept4" (· = go!"accept4") rfl rfl $$ [] as %e #He
      (try wp_auto)
      wp_apply wp_opError $$ %Hnw as %err #Herr
      (try wp_auto)
      iapply HΦ
      iright
      iexists .closed
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe HQ
      unfold resErr
      iexists e
      iframe Herr
      icases He with (#He | %He)
      all_goals first | (ileft; iexact He) | (iright; ipureintro; simp_all)
    · wp_apply wp_pollErr (c := NetErr.sys.code) .sys none go!"accept4" (· = go!"accept4") rfl rfl $$ [] as %e #He
      (try wp_auto)
      wp_apply wp_opError $$ %Hnw as %err #Herr
      (try wp_auto)
      iapply HΦ
      iright
      iexists .sys
      simp only [↓reduceIte]
      iframe HQ
      unfold resErr
      iexists e
      iframe Herr
      icases He with (#He | %He)
      all_goals first | (ileft; iexact He) | (iright; ipureintro; simp_all)
  · -- a connection, dialed to `a`
    iintro %a %ha
    icases HQ with ⟨-, HQ⟩
    imod HQ $$ %a %ha with ⟨%o, %S, Hl, Hpend, Hk⟩
    imodintro
    iexists o, S
    iframe Hl Hpend
    iintro %ho %cn %HcS Hl Hpend #Hat
    imod Hk $$ %ho %cn %HcS Hl Hpend Hat with HQ
    imodintro
    wp_auto
    wp_apply wp_newConn cn true a nw $$ %Hnw Hat as %c #Hc
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists cn, a
    iframe HQ Hc
    ipureintro; exact ha

end proof

end net
end Perennial
