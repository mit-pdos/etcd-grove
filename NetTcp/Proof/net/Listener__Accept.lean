/-
The proof of `NetTcp/Spec/net/Listener__Accept.lean`: the interface call resolves to
`TCPListener.Accept.impl`, the extension's `Accept` (`Tcp.wp_tcp_Accept`), then a new `*TCPConn`
holding the acceptor's end, as a `Conn`.
-/
module

public import NetTcp.Spec.net.Listener__Accept

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
  intro t l a Qfail Qok
  wp_start as ⟨#Ht, #Hla, HQ⟩
  (try wp_method_call)
  (try unfold TCPListener.Accept.impl)
  rw [TCPListener_ty_eq]
  ihave #Ht2 := Ht
  iStructNamed Ht2
  wp_auto
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
    wp_auto
    unfold model.opError
    rw [OpError_ty_eq, Conn_ty_eq]
    wp_auto
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact ⟨_, rfl⟩
    iexact HQ
  · -- a connection
    iintro %ho %cn %HcS Hl Hpend #Hat
    icases HQ with ⟨-, Hk⟩
    imod Hk $$ %ho %cn %HcS Hl Hpend Hat with HQ
    imodintro
    wp_auto
    unfold model.newConn
    rw [TCPConn_ty_eq, conn_ty_eq', Conn_ty_eq]
    iapply wp_fupd
    wp_auto
    ipersist t
    imodintro
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists cn
    iframe HQ
    unfold isConn connAt
    iexists _
    iframe t Hat
    ipureintro; rfl

end proof

end net
end Perennial
