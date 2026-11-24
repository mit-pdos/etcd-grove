-- The copy for the part `KvNet/` of `Net/Proof/net/Listen.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The proof of `Net/Spec/net/Listen.lean`: `Listen.impl`'s extension `Listen`
(`Net.wp_net_Listen`), then a new `*TCPListener` holding the listener's id, as a `Listener`.
-/
module

public import KvNet.Spec.net.Listen
public import KvNet.Proof.net.Errors

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

theorem Listen.wp_proof : Listen.spec (GF := GF) (hG := hG) := by
  intro nw hnw a
  wp_start as ⟨%Hla, Htok⟩
  wp_apply wp_netOk nw hnw
  (try wp_auto)
  wp_bind (ExternalOp _ _ _)
  iapply wp_net_Listen a $$ %Hla Htok
  isplit
  · -- a failure
    rw [Listener_ty_eq]
    wp_auto
    wp_bind (ExternalOp _ _ _)
    iapply wp_net_AnyString
    iintro %nm
    wp_apply wp_kindErr (c := NetErr.sys.code) .sys none nm (fun _ => True) trivial rfl $$ [] as %e #He
    (try wp_auto)
    wp_apply wp_anyTCPAddr as %x #Hx
    (try wp_auto)
    wp_apply wp_opError $$ %hnw as %err #Herr
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
    isplitr
    · ipureintro; rfl
    iexists nw
    iframe l Hx
    ipureintro; exact ⟨hnw, hl0⟩

end proof

end net
end Perennial
