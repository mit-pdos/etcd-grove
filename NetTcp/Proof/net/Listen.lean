/-
The proof of `NetTcp/Spec/net/Listen.lean`: `Listen.impl`'s extension `Listen`
(`Tcp.wp_tcp_Listen`), then a new `*TCPListener` holding the listener's id, as a `Listener`.
-/
module

public import NetTcp.Spec.net.Listen

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
  intro a
  wp_start as #Hp
  wp_bind (ExternalOp _ _ _)
  iapply wp_tcp_Listen a $$ Hp
  isplit
  · -- a failure
    wp_auto
    unfold model.opError
    rw [OpError_ty_eq, Listener_ty_eq]
    wp_auto
    iapply HΦ
    iright
    ipureintro; exact ⟨_, rfl⟩
  · -- a new listener
    iintro %lid Hl #Hla
    wp_auto
    rw [TCPListener_ty_eq, Listener_ty_eq]
    iapply wp_fupd
    wp_auto
    ipersist l
    imodintro
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists lid
    iframe Hl Hla
    unfold isListener
    iexists _
    iframe l
    ipureintro; rfl

end proof

end net
end Perennial
