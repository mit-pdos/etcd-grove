/-
The proof of `NetTcp/Spec/net/Listener__Close.lean`: the method resolves to
`TCPListener.Close.impl`, the extension's `LisClose` (`Tcp.wp_tcp_LisClose`), then `nil` or an
`*OpError`.
-/
module

public import NetTcp.Spec.net.Listener__Close

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
  intro t l a Q
  wp_start as ⟨#Ht, #Hla, HQ⟩
  (try wp_method_call)
  (try unfold TCPListener.Close.impl)
  rw [TCPListener_ty_eq]
  ihave #Ht2 := Ht
  iStructNamed Ht2
  wp_auto
  wp_bind (ExternalOp _ _ _)
  iapply wp_tcp_LisClose l a $$ Hla
  imod HQ with ⟨%o, Hl, Hk⟩
  imodintro
  iexists o
  iframe Hl
  iintro Hl
  imod Hk $$ Hl with HQ
  imodintro
  cases o
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
