/- Lean-first (no Rocq counterpart).

The proof of `groupOps` (see its spec).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.lintest.groupOps

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.lintest.Assumptions]

theorem groupOps.wp_proof : groupOps.spec (GF := GF) (hG := hG) := by
  intro id clients ops ops2
  wp_start
  wp_auto
  wp_if_destruct
  · rw [ite_eq_left (by simpa using Hif)]
    iapply HΦ; ipureintro; trivial
  · rw [ite_eq_right (by simpa using Hif)]
    iapply HΦ; ipureintro; trivial

end proof

end lintest
end EtcdGrove
end Perennial
