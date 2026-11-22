/-
The proof of `hang` (`Net/Spec/.../lib/remote/hang.lean`): `for {}`, a loop with the invariant
`True` that never exits, so any postcondition holds, `False` included.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.hang

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

theorem hang.wp_proof : hang.spec (GF := GF) (hG := hG) := by
  wp_start
  ihave IH : iprop(True) $$ []
  · itrivial
  wp_for IH
  wp_for_post
  iframe

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
