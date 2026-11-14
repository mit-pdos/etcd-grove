/-
The proof of `NetTcp/Spec/net/Conn__Close.lean`: the interface call resolves to
`conn.Close.impl` (`*TCPConn`'s promoted `Close`), the extension's `Close`, taking the caller's
update (`Tcp.wp_tcp_Close`).
-/
module

public import NetTcp.Spec.net.Conn__Close
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

theorem Conn.Close.wp_proof : Conn.Close.spec (GF := GF) (hG := hG) := by
  intro t cn s a la ra Q
  unfold connAt
  wp_start as ⟨⟨#Ht, #Hla, #Hra, #Hat⟩, HAU⟩
  wp_method_call
  (try unfold conn.Close.impl)
  (try unfold model.connId)
  (try unfold model.connErr)
  (try rw [conn_ty_eq'])
  ihave #Ht2 := Ht
  iStructNamed Ht2
  iStructNamed conn
  (try wp_auto)
  wp_bind (ExternalOp _ _ _)
  iapply wp_tcp_Close cn s a $$ Hat
  imod HAU with ⟨%st, %d, Hend, Hdir, Hk⟩
  imodintro
  iexists st, d
  iframe Hend Hdir
  iintro %res %st' %d' %Hcr Hend Hdir
  imod Hk $$ %res %st' %d' %Hcr Hend Hdir with HQ
  imodintro
  rcases res with _ | k
  · wp_auto
    iapply HΦ
    iexists none
    iframe HQ
    unfold resErr
    ipureintro; rfl
  · have hk : k = .closed := by
      unfold CloseOutcome at Hcr; split at Hcr
      · exact Option.some.inj Hcr.1
      · cases Hcr.1
    subst hk
    wp_auto
    wp_apply wp_kindErr .closed none go!"close" (· = go!"close") rfl rfl $$ [] as %e #He
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
