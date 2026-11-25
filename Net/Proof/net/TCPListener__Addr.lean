/-
The proof of `Net/Spec/net/TCPListener__Addr.lean`: the stored address (`TCPListener.Addr.impl`).
-/
module

public import Net.Spec.net.TCPListener__Addr
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

theorem TCPListener.Addr.wp_proof : TCPListener.Addr.spec (GF := GF) (hG := hG) := by
  intro t l x
  unfold lisAt lisFd fdAt
  wp_start as ⟨%nw, %Hnw, ⟨%fd, %lc, %ra, #Ht, %v, %hv, #Hv, -⟩, #Hx, %hl⟩
  obtain ⟨-, -, rfl, -⟩ := hv
  iStructNamed Ht
  iStructNamed Hv
  (try wp_method_call)
  wp_auto
  iapply HΦ
  itrivial

end proof

end net
end Perennial
