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
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.smd.Literals
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.WalkerLaws

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

/-- The root laws `Main`'s proof uses (until they are proved: `Main.wp_proof_of`'s premise). -/
structure MainLaws : Prop where
  scalar : isIface_scalar.law (GF := GF)
  ifaceList : isIface_list.law (GF := GF)
  ofMap : isIface_ofMap.law (GF := GF)
  mfIntro : isMF_intro.law (GF := GF)
  pathIntro : isPath_intro.law (GF := GF)
  pathsNil : isPaths_nil.law (GF := GF)
  pathsCons : isPaths_cons.law (GF := GF)
  pathsApp : isPaths_app.law (GF := GF)
  pathsLen : isPaths_length.law (GF := GF)
  pathsP : isPaths_persistent.law (GF := GF)
  pathP : isPath_persistent.law (GF := GF)
  vsetP : isVSet_persistent.law (GF := GF)
  ifaceP : isIface_persistent.law (GF := GF)
  schP : isSchema_persistent.law (GF := GF)
  tvP : isTV_persistent.law (GF := GF)
  mfP : isMF_persistent.law (GF := GF)
  updP : isUpdater_persistent.law (GF := GF)
  cvP : isIdentityConverter_persistent.law (GF := GF)
  cvIntro : isIdentityConverter_intro.law (GF := GF)
  conflictsIntro : isConflicts_intro.law (GF := GF)
  kwi : keysWithItemsB_iff.law
  tvv : isTV_isTVv.law (GF := GF)

theorem isUMap_persistent (hL : MainLaws (GF := GF)) (m : GoMap) (kvs : List (GoString × UVal)) :
    isUMap (GF := GF) m kvs ⊢ □ isUMap m kvs := hL.ifaceP _ _

theorem Main.wp_proof_of (hL : MainLaws (GF := GF))
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
  ihave #Hsc := hL.schP _ _ $$ Hsc
  wp_apply (IntoValTyped.wp_alloc (t := sigs_k8s_io.structured_merge_diff.v7.merge.UpdaterBuilder.ty)
    (_ : sigs_k8s_io.structured_merge_diff.v7.merge.UpdaterBuilder)) as %b Hb
  wp_apply (wp_BuildUpdater b (DFrac.own 1) _) $$ [Hb] as %u ⟨Hb, Hu⟩
  · iexact Hb
  ihave #Hu := hL.updP _ _ _ _ _ $$ Hu
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mf0 Hmf0
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %m0 Hm0
  imod ownMap_persist _ _ _ $$ Hmf0 with #Hmf0
  imod ownMap_persist _ _ _ $$ Hm0 with #Hm0
  ihave Hmf0' : isMF mf0 MF.none $$ []
  · rw [show MF.none = MF.ofList [] from rfl]
    iapply (hL.mfIntro mf0 _ [] (by simp) (fun k => by simp [lookupKV])) $$ Hmf0
    simp only [sepL, List.foldr_nil]; itrivial
  ihave #Hmf0' := hL.mfP _ _ $$ Hmf0'
  ihave Hm0' : isUMap m0 [] $$ []
  · unfold isUMap; rw [show UVal.map [] = UVal.ofMap [] from rfl]
    iapply (hL.ofMap m0 _ [] (by simp) (fun k => by simp [lookupKV])) $$ Hm0
    simp only [sepL, List.foldr_nil]; itrivial
  ihave #Hm0' := isUMap_persistent hL _ _ $$ Hm0'
  wp_apply (wp_typedObj «$r0_ptr» sc u null mf0 m0 []) $$ [«$r0»] as %lv0 ⟨Hs, Hlv0⟩
  · iframe «$r0» Hsc Hm0'
    ipureintro; exact conforms_all _ (List.Mem.head _)
  ihave #Hlv0 := hL.tvP _ _ _ _ _ $$ Hlv0
  ihave Hcv : isIdentityConverter (interface.mkOk github_com.mit_pdos.etcd_grove.examples.k8s.smd.identityConverter.ty
      #(zero_val github_com.mit_pdos.etcd_grove.examples.k8s.smd.identityConverter)) $$ []
  · iapply (hL.cvIntro _ _)
    isplitr
    · iintro !> %p %ver %Φ' HΦ'
      iapply (wp_Convert _ p ver)
      iframe Hpkg
      inext
      iintro _
      iexact HΦ'
    · iintro !> %e %Φ' HΦ'
      iapply (wp_IsMissing _ e)
      iframe Hpkg
      inext
      iintro _
      iexact HΦ'
  ihave #Hcv := hL.cvP _ $$ Hcv
  ihave Hst : ownState «$r0_ptr» sc ⟨UVal.map [], MF.none⟩ $$ [Hs]
  · unfold ownState
    iexists u, lv0, mf0, _
    iframe Hs Hsc Hcv Hlv0 Hmf0'
    iexact Hu
  sorry

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
    Main.spec (GF := GF) :=
  Main.wp_proof_of sorry wp_newSchema wp_Convert wp_IsMissing wp_BuildUpdater wp_typedObj wp_apply
    wp_check wp_field wp_mapKey wp_containerPaths wp_concat wp_applied wp_updated wp_container
    wp_Apply wp_Update wp_ConflictsEquals

end proof

end k8s_smd
end EtcdGrove
end Perennial
