/- Lean-first (no Rocq counterpart).

`Main()` (`examples/k8s/smd/smd.go`): not proved yet (`sorry`). The proof needs specs of
structured-merge-diff's API the driver calls (`typed.AsTyped`, `value.NewValueInterface`,
`merge.UpdaterBuilder.BuildUpdater`, `merge.Updater.Apply`/`Update`, `TypedValue.AsValue`,
`value.Equals`, `fieldpath.ManagedFields.Equals`, `fieldpath.NewSet`/`NewVersionedSet`,
`merge.Conflicts.Equals`, ...), taken as callee hypotheses here once they are stated
(notes/smd-robustness.md, "What remains").
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.Main

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.smd.Assumptions]

theorem Main.wp_proof : Main.spec (GF := GF) := by
  sorry

end proof

end k8s_smd
end EtcdGrove
end Perennial
