/-
The proof of `Net/Spec/net/Conn__SetWriteDeadline.lean`: the interface call resolves to
`conn.SetWriteDeadline.impl` (`*TCPConn`'s promoted `SetWriteDeadline`), the extension's
`SetDeadline`, taking the caller's update (`Net.wp_net_SetDeadline`).
-/
module

public import Net.Spec.net.Conn__SetWriteDeadline
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
variable [package_sem' : net.Assumptions]
variable [go.BasicIntoValInj]

theorem Conn.SetWriteDeadline.wp_proof : Conn.SetWriteDeadline.spec (GF := GF) (hG := hG) := by
  intro t cn s a la ra tm Q
  unfold connAt
  wp_start as ⟨⟨%nw, %Hnw, #Ht, #Hla, #Hra, #Hat⟩, HAU⟩
  wp_method_call
  (try unfold conn.SetWriteDeadline.impl)
  (try unfold model.setDeadline)
  (try unfold model.connId)
  (try rw [conn_ty_eq'])
  ihave #Ht2 := Ht
  iStructNamed Ht2
  iStructNamed conn
  ihave %Hne := netConnAt_endId_ne _ cn a s $$ Hat
  (try wp_auto)
  (try (rw [show decide (endId cn s = W64 0) = false by simpa using Hne]; wp_auto))
  wp_bind (ExternalOp _ _ _)
  iapply wp_net_SetDeadline cn s a (W64 2) tm.wall' tm.ext' $$ Hat
  imod HAU with ⟨%st, Hend, Hk⟩
  imodintro
  iexists st
  iframe Hend
  iintro %res %st' %Hsd Hend
  imod Hk $$ %res %st' %Hsd Hend with HQ
  imodintro
  rcases res with _ | k
  · wp_auto
    iapply HΦ
    iexists none
    iframe HQ
    unfold resErr
    ipureintro; rfl
  · have hk : k = .closed := by
      unfold DeadlineOutcome at Hsd; split at Hsd
      · exact Option.some.inj Hsd.1
      · cases Hsd.1
    subst hk
    wp_auto
    wp_apply wp_kindErr .closed none go!"set" (· = go!"set") rfl rfl $$ [] as %e #He
    (try wp_auto)
    (try unfold model.connNet)
    (try wp_auto)
    wp_apply wp_opError $$ %Hnw as %err #Herr
    iapply HΦ
    iexists some .closed
    iframe HQ
    unfold resErr
    iexists e
    iframe Herr He

end proof

end net
end Perennial
