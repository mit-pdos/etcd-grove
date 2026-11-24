/-
The proof of `Net/Spec/net/TCPConn__SetNoDelay.lean`: the method resolves to `TCPConn.SetNoDelay.impl`
(`model.sockOpt`), the extension's `SetSockopt` on the `conn`'s end, taking the caller's update
(`Net.wp_net_SetSockopt`).
-/
module

public import Net.Spec.net.TCPConn__SetNoDelay
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

theorem TCPConn.SetNoDelay.wp_proof : TCPConn.SetNoDelay.spec (GF := GF) (hG := hG) := by
  intro t cn s a la ra b Q
  unfold connAt
  wp_start as ⟨⟨%nw, %Hnw, #Ht, #Hla, #Hra, #Hat⟩, HAU⟩
  (try wp_method_call)
  (try unfold TCPConn.SetNoDelay.impl)
  (try unfold model.sockOpt)
  (try unfold model.connId)
  (try rw [TCPConn_ty_eq])
  (try rw [conn_ty_eq'])
  ihave #Ht2 := Ht
  iStructNamed Ht2
  iStructNamed conn
  ihave %Hne := netConnAt_endId_ne _ cn a s $$ Hat
  (try wp_auto)
  (try (rw [show decide (endId cn s = W64 0) = false by simpa using Hne]; wp_auto))
  wp_bind (ExternalOp _ _ _)
  iapply wp_net_SetSockopt cn s a (W64 0) (W64 0) $$ Hat
  imod HAU with ⟨%st, Hend, Hk⟩
  imodintro
  iexists st
  iframe Hend
  iintro %res %Hso Hend
  imod Hk $$ %res %(by simpa [sockOptValid] using Hso) Hend with HQ
  imodintro
  rcases res with _ | k
  · wp_auto
    iapply HΦ
    iexists none
    iframe HQ
    unfold resErr
    ipureintro; rfl
  · have hk : k ≠ .timeout := by
      rintro rfl
      unfold SockOptOutcome at Hso
      split at Hso
      · cases Hso
      · split at Hso
        · cases Hso
        · split at Hso <;> cases Hso
    wp_auto
    (try unfold model.sockOptErrTCP)
    (try unfold model.connErr)
    (try unfold model.connNet)
    (try wp_auto)
    cases k
    · -- closed
      wp_apply wp_kindErr .closed none go!"setsockopt" (· = go!"setsockopt") rfl rfl $$ [] as %e #He
      (try wp_auto)
      wp_apply wp_opError $$ %Hnw as %err #Herr
      iapply HΦ
      iexists some .closed
      iframe HQ
      unfold resErr
      iexists e
      iframe Herr He
    · exact absurd rfl hk
    · -- sys
      wp_apply wp_kindErr .sys none go!"setsockopt" (· = go!"setsockopt") rfl rfl $$ [] as %e #He
      (try wp_auto)
      wp_apply wp_opError $$ %Hnw as %err #Herr
      iapply HΦ
      iexists some .sys
      iframe HQ
      unfold resErr
      iexists e
      iframe Herr He

end proof

end net
end Perennial
