/-
The proof of `NetTcp/Spec/net/TCPConn__CloseWrite.lean`: the method resolves to
`TCPConn.CloseWrite.impl`, the extension's `CloseWrite` on the `*TCPConn`'s `conn`, taking the
caller's update (`Tcp.wp_tcp_CloseWrite`).
-/
module

public import NetTcp.Spec.net.TCPConn__CloseWrite
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

theorem TCPConn.CloseWrite.wp_proof : TCPConn.CloseWrite.spec (GF := GF) (hG := hG) := by
  intro t cn s a la ra Q
  unfold connAt
  wp_start as ⟨⟨#Ht, #Hla, #Hra, #Hat⟩, HAU⟩
  (try wp_method_call)
  (try unfold TCPConn.CloseWrite.impl)
  (try unfold model.connId)
  (try unfold model.connErr)
  (try rw [TCPConn_ty_eq])
  (try rw [conn_ty_eq'])
  ihave #Ht2 := Ht
  iStructNamed Ht2
  iStructNamed conn
  (try wp_auto)
  wp_bind (ExternalOp _ _ _)
  iapply wp_tcp_CloseWrite cn s a $$ Hat
  imod HAU with ⟨%st, %d, Hend, Hdir, Hk⟩
  imodintro
  iexists st, d
  iframe Hend Hdir
  iintro %res %d' %Hcr Hend Hdir
  imod Hk $$ %res %d' %Hcr Hend Hdir with HQ
  imodintro
  rcases res with _ | k
  · wp_auto
    iapply HΦ
    iexists none
    iframe HQ
    unfold resErr
    ipureintro; rfl
  · have hk : k ≠ .timeout := by
      unfold CloseWriteOutcome at Hcr; split at Hcr
      · rintro rfl; cases Hcr.1
      · rintro rfl; rcases Hcr with ⟨h, -⟩ | ⟨h, -⟩ <;> cases h
    wp_auto
    cases k
    · wp_apply wp_kindErr .closed none go!"shutdown" (· = go!"shutdown") rfl rfl $$ [] as %e #He
      (try wp_auto)
      wp_apply wp_opError as %err #Herr
      iapply HΦ
      iexists some .closed
      iframe HQ
      unfold resErr
      iexists e
      iframe Herr He
    · exact absurd rfl hk
    · wp_apply wp_kindErr .sys none go!"shutdown" (· = go!"shutdown") rfl rfl $$ [] as %e #He
      (try wp_auto)
      wp_apply wp_opError as %err #Herr
      iapply HΦ
      iexists some .sys
      iframe HQ
      unfold resErr
      iexists e
      iframe Herr He

end proof

end net
end Perennial
