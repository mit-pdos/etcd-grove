/- Lean-first (no Rocq counterpart).

`Main()` (`examples/k8s/smd/smd.go`): not proved yet (`sorry`): the glue over the specs of the
driver's functions and of structured-merge-diff's API it calls, taken as callee hypotheses; the
derivation of each step's result from those specs is `notes/smd-plan.md`, "Sanity checks".
Proved after the specs are frozen (the earlier proof was over the old model's specs).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.newSchema
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.identityConverter__Convert
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.identityConverter__IsMissingVersionError
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.state__typedObj
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.state__apply
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.state__check
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.field
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.mapKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.containerPaths
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.applied
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.updated
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.container
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.concat
public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.UpdaterBuilder__BuildUpdater
public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__Apply
public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__Update
public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Conflicts__Equals_ptr

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open smd

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.smd.Assumptions]

theorem Main.wp_proof
    (wp_newSchema : newSchema.spec (GF := GF))
    (wp_Convert : identityConverter.Convert.spec (GF := GF))
    (wp_IsMissing : identityConverter.IsMissingVersionError.spec (GF := GF))
    (wp_BuildUpdater : smd.merge.UpdaterBuilder.BuildUpdater.spec (GF := GF))
    (wp_typedObj : state.typedObj.spec (GF := GF))
    (wp_apply : state.apply.spec (GF := GF))
    (wp_check : state.check.spec (GF := GF))
    (wp_field : field.spec (GF := GF))
    (wp_mapKey : mapKey.spec (GF := GF))
    (wp_containerPaths : containerPaths.spec (GF := GF))
    (wp_concat : concat.spec (GF := GF))
    (wp_applied : applied.spec (GF := GF))
    (wp_updated : updated.spec (GF := GF))
    (wp_container : container.spec (GF := GF))
    (wp_Apply : smd.merge.Updater.Apply.spec (GF := GF))
    (wp_Update : smd.merge.Updater.Update.spec (GF := GF))
    (wp_ConflictsEquals : smd.merge.Conflicts.Equals_ptr.spec (GF := GF)) :
    Main.spec (GF := GF) := by
  sorry

end proof

end k8s_smd
end EtcdGrove
end Perennial
