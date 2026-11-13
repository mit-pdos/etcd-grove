/-
The proof of `NetTcp/Spec/net/Dial.lean`: `Dial.impl`'s extension `Dial` (`Tcp.wp_tcp_Dial`),
then a new `*TCPConn` holding the dialer's end, as a `Conn`.
-/
module

public import NetTcp.Spec.net.Dial

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

theorem Dial.wp_proof : Dial.spec (GF := GF) (hG := hG) := by
  intro a h Qfail Qok
  wp_start as ⟨#Hp, HQ⟩
  wp_bind (ExternalOp _ _ _)
  iapply wp_tcp_Dial a h $$ Hp
  isplit
  · -- a failure
    icases HQ with ⟨HQ, -⟩
    wp_auto
    unfold model.opError
    rw [OpError_ty_eq, Conn_ty_eq]
    wp_auto
    iapply HΦ
    iright
    iframe HQ
    ipureintro; exact ⟨_, rfl⟩
  · -- a new connection
    icases HQ with ⟨-, HAU⟩
    imod HAU with ⟨%S, Hpend, Hk⟩
    imodintro
    iexists S
    iframe Hpend
    iintro %cn %HcS Hpend #Hat Hd Ha
    imod Hk $$ %cn %HcS Hpend Hat Hd Ha with HQ
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
    iexists t_ptr
    iframe t Hat
    ipureintro; rfl

end proof

end net
end Perennial
