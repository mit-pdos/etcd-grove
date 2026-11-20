/-
The proof of `Spec/net/Dial.lean`: the model (`net.wp_Dial_impl`).
-/
module

public import Harness.Spec.net.Dial

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions]

theorem net.DialNet.wp_proof : net.DialNet.spec (GF := GF) (hG := hG) := by
  intro nw a P Q hnw
  iintro %Φ ⟨#Hpkg, #Hpr⟩ HΦ
  rw [FuncUnfold.func_unfold (f := net.Dial) (type_args := [])]
  wp_apply net.wp_Dial_impl nw a hnw $$ [$Hpr] as %cv %err Hres
  iapply HΦ $$ Hres

theorem net.Dial.wp_proof : net.Dial.spec (GF := GF) (hG := hG) := fun a P Q =>
  net.DialNet.wp_proof go!"tcp" a P Q net.tcpNet_tcp

end proof

end Perennial
