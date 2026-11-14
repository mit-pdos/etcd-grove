/-
The proof of `NetTcp/Spec/net/Listener__Close.lean`: the method resolves to
`TCPListener.Close.impl`, the extension's `LisClose` (`Tcp.wp_tcp_LisClose`), then `nil` or an
`*OpError`.
-/
module

public import NetTcp.Spec.net.Listener__Close
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

theorem Listener.Close.wp_proof : Listener.Close.spec (GF := GF) (hG := hG) := by
  intro t l x a Q
  unfold lisAt
  wp_start as ⟨⟨#Ht, #Hx, %hl0⟩, #Hla, HAU⟩
  (try wp_method_call)
  (try unfold TCPListener.Close.impl)
  rw [TCPListener_ty_eq]
  ihave #Ht2 := Ht
  iStructNamed Ht2
  wp_auto
  wp_bind (ExternalOp _ _ _)
  iapply wp_tcp_LisClose l a $$ Hla
  imod HAU with ⟨%o, Hl, Hk⟩
  imodintro
  iexists o
  iframe Hl
  iintro %res %Hres Hl
  imod Hk $$ %res %Hres Hl with HQ
  imodintro
  rcases res with _ | k
  · wp_auto
    iapply HΦ
    iexists none
    iframe HQ
    unfold resErr
    ipureintro; rfl
  · have hk : k = .closed := by
      unfold LisCloseOutcome at Hres; split at Hres
      · cases Hres.1
      · exact Option.some.inj Hres.1
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
