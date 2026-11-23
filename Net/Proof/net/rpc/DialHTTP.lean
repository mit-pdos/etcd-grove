/-
The proof of `DialHTTP` (`Net/Spec/net/rpc/DialHTTP.lean`): `DialHTTPPath` at `DefaultRPCPath`.
-/
module

public import Net.Spec.net.rpc.DialHTTP

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

theorem DialHTTP.wp_proof (wp_DialHTTPPath : DialHTTPPath.spec (GF := GF) (hG := hG)) :
    DialHTTP.spec (GF := GF) (hG := hG) := by
  intro nw hnw W a
  wp_start as ⟨%Hbound, #Henv, #Hhenv, #Haddr⟩
  simp only [net.rpc.DefaultRPCPath, defaultRPCPath] at *
  wp_auto
  wp_apply wp_DialHTTPPath nw hnw W a go!"/_goRPC_" $$ [$Henv $Hhenv $Haddr] as %c %err Hres
  · ipureintro; exact Hbound
  iapply HΦ
  iexact Hres

end proof

end net.rpc
end Perennial
