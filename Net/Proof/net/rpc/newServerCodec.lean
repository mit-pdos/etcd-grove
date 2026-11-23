/-
The proof of `newServerCodec` (`Net/Spec/net/rpc/newServerCodec.lean`): a struct allocation.
-/
module

public import Net.Spec.net.rpc.newServerCodec

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.rpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions]

theorem newServerCodec.wp_proof : newServerCodec.spec (GF := GF) (hG := hG) := by
  intro conn
  wp_start
  wp_auto
  iStructNamed «$r0»
  iapply HΦ
  iframe rwc werr

end proof

end net.rpc
end Perennial
