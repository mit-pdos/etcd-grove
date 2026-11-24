/-
The proof of `Net/Spec/net/Conn__LocalAddr.lean`: the stored address (`conn.LocalAddr.impl`).
-/
module

public import Net.Spec.net.Conn__LocalAddr
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

theorem Conn.LocalAddr.wp_proof : Conn.LocalAddr.spec (GF := GF) (hG := hG) := by
  intro t cn s a la ra
  unfold connAt connFd fdAt
  wp_start as ⟨%nw, %Hnw, ⟨%fd, #Ht, %v, %hv, #Hv⟩, #Hla, #Hra, #Hat⟩
  obtain ⟨-, -, rfl, rfl⟩ := hv
  ihave %Hfdn := typedPointsto_not_null _ _ _ $$ Hv
  ihave #Ht2 := Ht
  iStructNamed Ht2
  iStructNamed Hv
  (try wp_method_call)
  wp_auto
  wp_apply wp_conn_ok _ fd Hfdn $$ conn
  iStructNamed conn
  wp_auto
  iapply HΦ
  itrivial

end proof

end net
end Perennial
