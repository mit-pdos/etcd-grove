/-
The proof of `wire.Forever` (`NetTcp/Spec/.../wire/Forever.lean`): a blocking `select` with no
case (`chan.wp_select_blocking`, of the empty list of cases) never returns.
-/
module

public import NetTcp.Spec.github_com.mit_pdos.etcd_grove.examples.net.wire.Forever

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.net.wire

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Tcp.tcpExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : wire.Assumptions]

theorem Forever.wp_proof : Forever.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_bind (App (Val (GoInstruction SelectStmt)) _)
  iapply chan.wp_select_blocking []
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.net.wire
end Perennial
