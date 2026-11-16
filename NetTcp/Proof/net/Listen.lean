/-
The proof of `NetTcp/Spec/net/Listen.lean`: `Listen.impl`'s extension `Listen`
(`Tcp.wp_tcp_Listen`), then a new `*TCPListener` holding the listener's id, as a `Listener`.
-/
module

public import NetTcp.Spec.net.Listen
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

theorem Listen.wp_proof : Listen.spec (GF := GF) (hG := hG) := by
  intro a a0
  wp_start as %Hla
  wp_bind (ExternalOp _ _ _)
  iapply wp_tcp_Listen a a0 $$ %Hla
  isplit
  · -- a failure
    rw [Listener_ty_eq]
    wp_auto
    wp_bind (ExternalOp _ _ _)
    iapply wp_tcp_AnyString
    iintro %nm
    wp_apply wp_kindErr (c := TcpErr.sys.code) .sys none nm (fun _ => True) trivial rfl $$ [] as %e #He
    (try wp_auto)
    wp_apply wp_anyTCPAddr as %x #Hx
    (try wp_auto)
    wp_apply wp_opError as %err #Herr
    (try wp_auto)
    iapply HΦ
    iright
    iexists x
    iframe Hx
    unfold resErr
    iexists e
    iframe Herr He
  · -- a new listener
    iintro %lid %hl0 Hl #Hlat
    wp_auto
    rw [TCPListener_ty_eq, Listener_ty_eq, Addr_ty_eq']
    iapply wp_fupd
    wp_auto
    wp_apply wp_anyTCPAddr as %x #Hx
    (try wp_auto)
    ipersist l
    imodintro
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists lid
    iframe Hl Hlat
    unfold isListener lisAt
    iexists _, x
    dsimp only
    iframe l Hx
    ipureintro; exact ⟨rfl, hl0⟩

end proof

end net
end Perennial
