/-
The proof of `NetTcp/Spec/net/Conn__SetDeadline.lean`: the interface call resolves to
`conn.SetDeadline.impl` (`*TCPConn`'s promoted `SetDeadline`), the extension's `SetDeadline`,
taking the caller's update (`Tcp.wp_tcp_SetDeadline`).
-/
module

public import NetTcp.Spec.net.Conn__SetDeadline
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

theorem Conn.SetDeadline.wp_proof : Conn.SetDeadline.spec (GF := GF) (hG := hG) := by
  intro t cn s a la ra tm Q
  unfold connAt
  wp_start as ⟨⟨#Ht, #Hla, #Hra, #Hat⟩, HAU⟩
  wp_method_call
  (try unfold conn.SetDeadline.impl)
  (try unfold model.setDeadline)
  (try unfold model.connId)
  (try rw [conn_ty_eq'])
  ihave #Ht2 := Ht
  iStructNamed Ht2
  iStructNamed conn
  (try wp_auto)
  wp_bind (ExternalOp _ _ _)
  iapply wp_tcp_SetDeadline cn s a (W64 0) tm.wall' tm.ext' $$ Hat
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
    wp_apply wp_opError as %err #Herr
    iapply HΦ
    iexists some .closed
    iframe HQ
    unfold resErr
    iexists e
    iframe Herr He

end proof

end net
end Perennial
