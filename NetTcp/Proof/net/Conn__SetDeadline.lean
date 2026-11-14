/-
The proof of `NetTcp/Spec/net/Conn__SetDeadline.lean`: the interface call resolves to
`conn.SetDeadline.impl` (`*TCPConn`'s promoted `SetDeadline`), the extension's `SetDeadline`,
taking the caller's update (`Tcp.wp_tcp_SetDeadline`).
-/
module

public import NetTcp.Spec.net.Conn__SetDeadline

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
  intro t cn s a tm Q
  unfold connAt
  wp_start as ⟨⟨#Ht, #Hat⟩, HAU⟩
  wp_method_call
  (try unfold conn.SetDeadline.impl)
  (try unfold model.connId)
  (try rw [conn_ty_eq'])
  ihave #Ht2 := Ht
  iStructNamed Ht2
  iStructNamed conn
  (try wp_auto)
  wp_bind (ExternalOp _ _ _)
  iapply wp_tcp_SetDeadline cn s a $$ Hat
  imod HAU with ⟨%st, %r, Hend, Hk⟩
  imodintro
  iexists st, r
  iframe Hend
  iintro %ok %st' %Hsd Hend
  imod Hk $$ %ok %st' %Hsd Hend with HQ
  imodintro
  cases ok
  · wp_auto
    unfold model.opError
    rw [OpError_ty_eq]
    wp_auto
    iapply HΦ
    iexists false
    iframe HQ
    ipureintro
    exact ⟨by simp, fun _ => ⟨_, rfl⟩⟩
  · wp_auto
    iapply HΦ
    iexists true
    iframe HQ
    ipureintro
    exact ⟨fun _ => rfl, by simp⟩

end proof

end net
end Perennial
