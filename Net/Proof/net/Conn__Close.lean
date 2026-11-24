/-
The proof of `Net/Spec/net/Conn__Close.lean`: the interface call resolves to
`conn.Close.impl` (`*TCPConn`'s promoted `Close`), the extension's `Close`, taking the caller's
update (`Net.wp_net_Close`).
-/
module

public import Net.Spec.net.Conn__Close
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

theorem Conn.Close.wp_proof : Conn.Close.spec (GF := GF) (hG := hG) := by
  intro t cn s a la ra Q
  unfold connAt connFd
  wp_start as ⟨⟨%nw, %Hnw, ⟨%fd, #Ht, #Hfd⟩, #Hla, #Hra, #Hat⟩, HAU⟩
  ihave #Ht2 := Ht
  iStructNamed Ht2
  ihave #Hfd2 := Hfd
  unfold fdAt
  icases Hfd2 with ⟨%v, %hv, #Hv⟩
  ihave %Hfdn := typedPointsto_not_null _ _ _ $$ Hv
  wp_method_call
  wp_auto
  trace_state
  sorry

end proof

end net
end Perennial
