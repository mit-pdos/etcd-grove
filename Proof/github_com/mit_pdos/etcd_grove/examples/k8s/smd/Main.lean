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
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.smd.Literals
public import Proof.sigs_k8s_io.structured_merge_diff.v7.OwnLaws

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
  wp_start as #Hpkg
  wp_apply wp_newSchema as %sc Hsc
  wp_apply (IntoValTyped.wp_alloc (t := sigs_k8s_io.structured_merge_diff.v7.merge.UpdaterBuilder.ty) (_ : sigs_k8s_io.structured_merge_diff.v7.merge.UpdaterBuilder)) as %b Hb
  wp_apply (wp_BuildUpdater b (DFrac.own 1) _) $$ [Hb] as %u ⟨Hb, Hu⟩
  · iexact Hb
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mf0 Hmf0
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %m0 Hm0
  imod (ownUMap_lit m0 [] [] rfl (by decide) (by decide)) $$ [Hm0] with #Hm0
  · iframe
    iintro !> %e %he
    simp at he
  wp_apply (wp_typedObj «$r0_ptr» sc u null mf0 m0 (mkKVs []) (by decide +kernel)) $$ [«$r0» Hsc] as %lv0 ⟨Hs, Hsc, #Hlv0⟩
  · iframe
    iexact Hm0
  -- the state `S0`
  ipersist Hu
  ihave #Hupd : ownUpdater u false $$ []
  · unfold ownUpdater isIdentityConverter
    iexists _
    iframe Hu
    iexists _, _
    isplitr
    · ipureintro; rfl
    isplitr
    · iintro !> %p %ver %Φ' HΦ'
      iapply (wp_Convert _ p ver Φ')
      iframe #
      inext
      iintro _
      iexact HΦ'
    · iintro !> %e %Φ' HΦ'
      iapply (wp_IsMissing _ e Φ')
      iframe #
      inext
      iintro _
      iexact HΦ'
  imod ownMap_persist _ _ _ $$ Hmf0 with #Hmf0
  ihave Hst : ownState «$r0_ptr» sc S0 $$ [Hs Hsc]
  · unfold ownState
    iexists u, lv0, mf0
    iframe
    isplitr
    · iexact Hupd
    isplitr
    · iexact Hlv0
    · unfold ownMF
      iexists ∅
      iframe Hmf0
      isplitr
      · ipureintro; simp [keysSorted, lookupKV, S0]
      · simp only [S0, ownMFL]; itrivial
  trace_state
  sorry

end proof

end k8s_smd
end EtcdGrove
end Perennial
