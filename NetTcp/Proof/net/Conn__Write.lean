/-
The proof of `NetTcp/Spec/net/Conn__Write.lean`: the interface call resolves to
`conn.Write.impl` (`*TCPConn`'s promoted `Write`), which reads the buffer's bytes and makes the
extension's `Write`, taking the caller's update (`Tcp.wp_tcp_Write`).
-/
module

public import NetTcp.Spec.net.Conn__Write

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

theorem Conn.Write.wp_proof : Conn.Write.spec (GF := GF) (hG := hG) := by
  intro c cn s a b bs dq Q
  unfold isConn
  wp_start as ⟨⟨%t, %Hc, #Ht, #Hat⟩, Hsl, HAU⟩
  subst Hc
  wp_auto
  wp_method_call
  wp_auto
  wp_method_call
  unfold conn.Write.impl model.connId
  rw [conn_ty_eq']
  ihave #Ht2 := Ht
  iStructNamed Ht2
  iStructNamed conn
  wp_auto
  wp_apply wp_bytes_to_string b bs dq $$ Hsl as Hsl
  wp_bind (ExternalOp _ _ _)
  iapply wp_tcp_Write cn s a bs $$ Hat
  imod HAU with ⟨%st, %r, %out, %f, Hend, Hout, Hk⟩
  imodintro
  iexists st, r, out, f
  iframe Hend Hout
  iintro %k %ok %st' %Hwr Hend Hout
  imod Hk $$ %k %ok %st' %Hwr Hend Hout with HQ
  imodintro
  cases ok
  · wp_auto
    unfold model.opError
    rw [OpError_ty_eq]
    wp_auto
    iapply HΦ
    iexists k, false
    iframe HQ Hsl
    ipureintro
    exact ⟨rfl, by simp, fun _ => ⟨_, rfl⟩⟩
  · wp_auto
    iapply HΦ
    iexists k, true
    iframe HQ Hsl
    ipureintro
    exact ⟨rfl, fun _ => rfl, by simp⟩

end proof

end net
end Perennial
