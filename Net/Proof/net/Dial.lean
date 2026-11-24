/-
The proof of `Net/Spec/net/Dial.lean`: `Dial.impl`'s extension `Dial` (`Net.wp_net_Dial`),
then a new `*TCPConn` holding the dialer's end, as a `Conn`.
-/
module

public import Net.Spec.net.Dial
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

theorem Dial.wp_proof : Dial.spec (GF := GF) (hG := hG) := by
  intro nw hnw a Qfail Qok
  wp_start as ⟨%Hp, HQ⟩
  wp_apply wp_netOk nw hnw
  (try wp_auto)
  wp_bind (ExternalOp _ _ _)
  iapply wp_net_Dial a $$ %Hp
  isplit
  · -- a failure
    icases HQ with ⟨HQ, -⟩
    rw [Conn_ty_eq]
    wp_auto
    wp_bind (ExternalOp _ _ _)
    iapply wp_net_AnyString
    iintro %nm
    wp_apply wp_pollErr (c := NetErr.sys.code) .sys none nm (fun _ => True) trivial rfl $$ [] as %e #He
    (try wp_auto)
    wp_apply wp_anyTCPAddr as %x #Hx
    (try wp_auto)
    wp_apply wp_opError $$ %hnw as %err #Herr
    (try wp_auto)
    iapply HΦ
    iright
    iframe HQ
    iexists x
    iframe Hx
    unfold resErr
    iexists e
    iframe Herr He
  · icases HQ with ⟨-, HAU⟩
    imod HAU with ⟨%S, Hpend, Hk⟩
    imodintro
    iexists S
    iframe Hpend
    iintro %cn %HcS Hpend #Hat Ha
    icases Hk $$ %cn %HcS Hpend Hat Ha with Hk
    isplit
    · -- a new connection
      iintro Hd
      icases Hk with ⟨Hk, -⟩
      imod Hk $$ Hd with HQ
      imodintro
      wp_auto
      wp_apply wp_newConn cn false a nw $$ %hnw Hat as %c #Hc
      iapply HΦ
      ileft
      isplitr
      · ipureintro; rfl
      iexists cn
      iframe HQ Hc
    · -- a failure, the connection abandoned
      iintro He Hd
      icases Hk with ⟨-, Hk⟩
      imod Hk $$ He Hd with HQ
      imodintro
      rw [Conn_ty_eq]
      wp_auto
      wp_bind (ExternalOp _ _ _)
      iapply wp_net_AnyString
      iintro %nm
      wp_apply wp_pollErr (c := NetErr.sys.code) .sys none nm (fun _ => True) trivial rfl $$ [] as %e #He
      (try wp_auto)
      wp_apply wp_anyTCPAddr as %x #Hx
      (try wp_auto)
      wp_apply wp_opError $$ %hnw as %err #Herr
      (try wp_auto)
      iapply HΦ
      iright
      iframe HQ
      iexists x
      iframe Hx
      unfold resErr
      iexists e
      iframe Herr He

end proof

end net
end Perennial
