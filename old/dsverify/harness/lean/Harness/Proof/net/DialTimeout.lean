/-
The proof of `Spec/net/DialTimeout.lean`: the model is `Dial`'s (`net.wp_Dial_impl`).
-/
module

public import Harness.Spec.net.DialTimeout

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

theorem net.DialTimeoutNet.wp_proof : net.DialTimeoutNet.spec (GF := GF) (hG := hG) := by
  intro nw a d P Q hnw
  wp_start as #Hpr
  wp_apply net.wp_Dial_impl nw a hnw $$ [$Hpr] as %cv %err Hres
  iapply HΦ $$ Hres

theorem net.DialTimeout.wp_proof : net.DialTimeout.spec (GF := GF) (hG := hG) := fun a d P Q =>
  net.DialTimeoutNet.wp_proof go!"tcp" a d P Q net.tcpNet_tcp

end proof

end Perennial
