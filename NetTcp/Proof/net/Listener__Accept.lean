/-
The proof of `NetTcp/Spec/net/Listener__Accept.lean`: the interface call resolves to
`TCPListener.Accept.impl`, the extension's `Accept` (`Tcp.wp_tcp_Accept`), then a new `*TCPConn`
holding the acceptor's end, as a `Conn`.
-/
module

public import NetTcp.Spec.net.Listener__Accept
public import NetTcp.Proof.net.Errors

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp

namespace net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

theorem Listener.Accept.wp_proof : Listener.Accept.spec (GF := GF) (hG := hG) := by
  intro t l x a Qfail Qok
  unfold lisAt
  wp_start as ⟨⟨#Ht, #Hx, %hl0⟩, #Hla, HQ⟩
  (try wp_method_call)
  (try unfold TCPListener.Accept.impl)
  rw [TCPListener_ty_eq]
  ihave #Ht2 := Ht
  iStructNamed Ht2
  wp_auto
  (try (rw [show decide (l = W64 0) = false by simpa using hl0]; wp_auto))
  wp_bind (ExternalOp _ _ _)
  iapply wp_tcp_Accept l a $$ Hla
  imod HQ with ⟨%o, %S, Hl, Hpend, HQ⟩
  imodintro
  iexists o, S
  iframe Hl Hpend
  isplit
  · -- a failure
    iintro Hl Hpend
    icases HQ with ⟨HQ, -⟩
    imod HQ $$ Hl Hpend with HQ
    imodintro
    rw [Conn_ty_eq]
    wp_auto
    cases o
    · wp_apply wp_kindErr (c := TcpErr.closed.code) .closed none go!"accept4" (· = go!"accept4") rfl rfl $$ [] as %e #He
      (try wp_auto)
      wp_apply wp_opError as %err #Herr
      (try wp_auto)
      iapply HΦ
      iright
      iexists .closed
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe HQ
      unfold resErr
      iexists e
      iframe Herr He
    · wp_apply wp_kindErr (c := TcpErr.sys.code) .sys none go!"accept4" (· = go!"accept4") rfl rfl $$ [] as %e #He
      (try wp_auto)
      wp_apply wp_opError as %err #Herr
      (try wp_auto)
      iapply HΦ
      iright
      iexists .sys
      simp only [↓reduceIte]
      iframe HQ
      unfold resErr
      iexists e
      iframe Herr He
  · -- a connection
    iintro %ho %cn %HcS Hl Hpend #Hat
    icases HQ with ⟨-, Hk⟩
    imod Hk $$ %ho %cn %HcS Hl Hpend Hat with HQ
    imodintro
    wp_auto
    wp_apply wp_newConn cn true a $$ Hat as %c #Hc
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists cn
    iframe HQ Hc

end proof

end net
end Perennial
