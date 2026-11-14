/-
The proof of `NetTcp/Spec/net/Conn__Write.lean`: the interface call resolves to
`conn.Write.impl` (`*TCPConn`'s promoted `Write`), which reads the buffer's bytes and makes the
extension's `Write`, taking the caller's update (`Tcp.wp_tcp_Write`).
-/
module

public import NetTcp.Spec.net.Conn__Write
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

theorem Conn.Write.wp_proof : Conn.Write.spec (GF := GF) (hG := hG) := by
  intro t cn s a la ra b bs dq ed Q
  unfold connAt
  wp_start as ⟨⟨#Ht, #Hla, #Hra, #Hat⟩, Hsl, #Hed, HAU⟩
  wp_method_call
  (try unfold conn.Write.impl)
  (try unfold model.connId)
  (try unfold model.connErr)
  (try rw [conn_ty_eq'])
  ihave #Ht2 := Ht
  iStructNamed Ht2
  iStructNamed conn
  (try wp_auto)
  wp_apply wp_bytes_to_string b bs dq $$ Hsl as Hsl
  wp_bind (ExternalOp _ _ _)
  iapply wp_tcp_Write cn s a bs $$ Hat
  imod HAU with ⟨%st, %d, Hend, Hdir, Hk⟩
  imodintro
  iexists st, d
  iframe Hend Hdir
  iintro %k %res %d' %Hw Hend Hdir
  imod Hk $$ %k %res %d' %Hw Hend Hdir with HQ
  imodintro
  rcases res with _ | e
  · wp_auto
    iapply HΦ
    iexists k, none
    iframe HQ Hsl
    unfold resErr
    ipureintro; exact ⟨rfl, rfl⟩
  · wp_auto
    cases e
    · wp_apply wp_kindErr .closed (some ed) go!"write" (· = go!"write") rfl rfl $$ [] as %e #He
      (try wp_auto)
      wp_apply wp_opError as %err #Herr
      iapply HΦ
      iexists k, some .closed
      iframe HQ Hsl
      isplitr; · ipureintro; rfl
      unfold resErr
      iexists e
      iframe Herr He
    · wp_apply wp_kindErr .timeout (some ed) go!"write" (· = go!"write") rfl rfl $$ [Hed] as %e #He
      · iexact Hed
      (try wp_auto)
      wp_apply wp_opError as %err #Herr
      iapply HΦ
      iexists k, some .timeout
      iframe HQ Hsl
      isplitr; · ipureintro; rfl
      unfold resErr
      iexists e
      iframe Herr He
    · wp_apply wp_kindErr .sys (some ed) go!"write" (· = go!"write") rfl rfl $$ [] as %e #He
      (try wp_auto)
      wp_apply wp_opError as %err #Herr
      iapply HΦ
      iexists k, some .sys
      iframe HQ Hsl
      isplitr; · ipureintro; rfl
      unfold resErr
      iexists e
      iframe Herr He

end proof

end net
end Perennial
