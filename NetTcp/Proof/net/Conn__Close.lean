/-
The proof of `NetTcp/Spec/net/Conn__Close.lean`: the interface call resolves to
`conn.Close.impl` (`*TCPConn`'s promoted `Close`), the extension's `Close`, taking the caller's
update (`Tcp.wp_tcp_Close`).
-/
module

public import NetTcp.Spec.net.Conn__Close

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
  intro t cn s a Q
  unfold connAt
  wp_start as ⟨⟨#Ht, #Hat⟩, HAU⟩
  wp_method_call
  (try unfold conn.Close.impl)
  (try unfold model.connId)
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
  iintro %ok %st' %d' %Hcr Hend Hdir
  imod Hk $$ %ok %st' %d' %Hcr Hend Hdir with HQ
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
