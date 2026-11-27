/-
The proof of `clientCodec.Close` (`Net/Spec/net/rpc/clientCodec__Close.lean`): `rwc`'s `Close`.
-/
module

public import Net.Spec.net.rpc.clientCodec__Close

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions]

theorem clientCodec.Close.wp_proof (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG)) :
    clientCodec.Close.spec (GF := GF) (hG := hG) := by
  intro c t cn s a la ra Q
  wp_start as ⟨#Hrwc, #Hc, Hau⟩
  wp_auto
  wp_apply wp_Close t cn s a la ra Q $$ [$Hc $Hau] as %err Hres
  iapply HΦ $$ Hres

end proof

end net.rpc
end Perennial
