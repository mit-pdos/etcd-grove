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

/-- A `[]interface{}` literal. -/
theorem isIface_lit_list (hL : MainLaws (GF := GF)) (sl : GoSlice) (xs : List GoInterface)
    (vs : List UVal) (h : xs.length = vs.length) :
    sl ↦* xs -∗ sepL (fun xv => isIface (GF := GF) xv.1 xv.2) (xs.zip vs) ==∗
      □ isIface (interface.mkOk sliceIfaceTy #sl) (.list vs) := by
  iintro Hs Hv
  imod ownSlice_persist $$ Hs with #Hs
  ihave H := (hL.ifaceList sl xs vs h) $$ Hs Hv
  ihave #H := hL.ifaceP _ _ $$ H
  imodintro
  iexact H

set_option hygiene false in
/-- The entries of a literal: each found in the map, each value's `isIface` (a scalar, or a
persistent hypothesis). -/
macro "lit_vals" : tactic =>
  `(tactic| ((simp only [sepL, List.foldr_cons, List.foldr_nil, List.zip_cons_cons, List.zip_nil_left, List.zip_nil_right, str, i64, labels, sel, container, A, B, C, aPaths1, aPaths5, bPaths5, aPaths6, bPaths7, aPaths7, bPaths8]); repeat' (first | itrivial | (iexists _; isplitr; · (ipureintro; rfl)) | (iapply hL.scalar.2.2.2) | (iapply hL.scalar.2.2.1) | iassumption | isplitr)))

/-- A `map[string]interface{}` literal, its inserts done: an `isUMap` of its sorted entries. -/
theorem isUMap_lit (hL : MainLaws (GF := GF)) (m : GoMap) (M : GMap GoString GoInterface)
    (x : UVal) (kvs : List (GoString × UVal)) (hx : x = UVal.ofMap kvs) (hnd : (kvs.map (·.1)).Nodup)
    (hk : ∀ k, (M !! k).isSome = (lookupKV k kvs).isSome) :
    m ↦$ M -∗ sepL (fun kv => iprop(∃ x, ⌜M !! kv.1 = some x⌝ ∗ isIface (GF := GF) x kv.2)) kvs ==∗
      □ isIface (interface.mkOk mapStrIfaceTy #m) x := by
  subst hx
  iintro Hm Hs
  imod ownMap_persist _ _ _ $$ Hm with #Hm
  ihave H := (hL.ofMap m M kvs hnd hk) $$ Hm Hs
  ihave #H := hL.ifaceP _ _ $$ H
  imodintro
  iexact H

/-- A `fieldpath.ManagedFields` literal, its inserts done. -/
theorem isMF_lit (hL : MainLaws (GF := GF)) (m : GoMap) (M : GMap GoString GoInterface)
    (mf : MF) (ms : List (GoString × VSet)) (hx : mf = MF.ofList ms) (hnd : (ms.map (·.1)).Nodup)
    (hk : ∀ k, (M !! k).isSome = (lookupKV k ms).isSome) :
    m ↦$ M -∗ sepL (fun me => iprop(∃ i, ⌜M !! me.1 = some i⌝ ∗ isVSet (GF := GF) i me.2)) ms ==∗
      □ isMF m mf := by
  subst hx
  iintro Hm Hs
  imod ownMap_persist _ _ _ $$ Hm with #Hm
  ihave H := (hL.mfIntro m M ms hnd hk) $$ Hm Hs
  ihave #H := hL.mfP _ _ $$ H
  imodintro
  iexact H

/-- A `[]fieldpath.Path` literal's paths. -/
theorem isPaths_lit (hL : MainLaws (GF := GF)) (ss : List GoSlice) (ps : List Path)
    (h : ss.length = ps.length) :
    sepL (fun sp => isPath (GF := GF) sp.1 sp.2) (ss.zip ps) ⊢ isPaths ss ps := by
  induction ss generalizing ps with
  | nil =>
    cases ps with
    | nil => exact hL.pathsNil
    | cons _ _ => simp at h
  | cons s ss ih =>
    cases ps with
    | nil => simp at h
    | cons p ps =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      rw [List.zip_cons_cons, show sepL (fun sp => isPath (GF := GF) sp.1 sp.2) ((s, p) :: ss.zip ps) =
        iprop(isPath s p ∗ sepL (fun sp => isPath (GF := GF) sp.1 sp.2) (ss.zip ps)) from rfl]
      iintro ⟨Hp, Hr⟩
      iapply (hL.pathsCons s ss p ps).2
      iframe Hp
      iapply (ih ps h)
      iexact Hr

/-- `concat`'s result's paths. -/
theorem isPaths_concat (hL : MainLaws (GF := GF)) (xs ys : List GoSlice) (ps qs : List Path) :
    isPaths (GF := GF) xs ps -∗ isPaths ys qs -∗ isPaths (xs ++ ys) (ps ++ qs) := by
  iintro Hx Hy
  ihave %hl := hL.pathsLen _ _ $$ Hx
  iapply (hL.pathsApp xs ys ps qs hl).2
  iframe

/-- `state.apply` when `Apply` returns an object. -/
theorem wp_apply_some (wp_apply : state.apply.spec (GF := GF)) :
    ∀ (s sc : Loc) (live : UVal) (mf : MF) (m : GoMap) (kvs : List (GoString × UVal))
      (mgr msg : GoString) (x : UVal) (mf' : MF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.smd ∗
        ownState s sc ⟨live, mf⟩ ∗ isUMap m kvs ∗ ⌜conforms sc0 rootRef (.map kvs)⌝ ∗
        ⌜∀ m e, mf.get m = some e → e.version = version ∧ keysWithItems sc0 rootRef e.set⌝ ∗
        ⌜inputsSmall [live, .map kvs] mf⌝ ∗
        ⌜applyResult sc0 rootRef false live (.map kvs) version mf mgr false = .ok (some x) mf'⌝ }}
      (App (App (App (Val (s @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.smd.state.ty @!! go!"apply")) (Val #m)) (Val #mgr))
        (Val #msg))
    {{ RET #true; ownState s sc ⟨x, mf'⟩ }} :=
  fun s sc live mf m kvs mgr msg x mf' => wp_apply s sc ⟨live, mf⟩ m kvs mgr msg (some x) mf'

/-- `state.apply` when `Apply` returns no object (a no-op). -/
theorem wp_apply_none (wp_apply : state.apply.spec (GF := GF)) :
    ∀ (s sc : Loc) (live : UVal) (mf : MF) (m : GoMap) (kvs : List (GoString × UVal))
      (mgr msg : GoString) (mf' : MF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.smd ∗
        ownState s sc ⟨live, mf⟩ ∗ isUMap m kvs ∗ ⌜conforms sc0 rootRef (.map kvs)⌝ ∗
        ⌜∀ m e, mf.get m = some e → e.version = version ∧ keysWithItems sc0 rootRef e.set⌝ ∗
        ⌜inputsSmall [live, .map kvs] mf⌝ ∗
        ⌜applyResult sc0 rootRef false live (.map kvs) version mf mgr false = .ok none mf'⌝ }}
      (App (App (App (Val (s @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.smd.state.ty @!! go!"apply")) (Val #m)) (Val #mgr))
        (Val #msg))
    {{ RET #false; ownState s sc ⟨live, mf'⟩ }} :=
  fun s sc live mf m kvs mgr msg mf' => wp_apply s sc ⟨live, mf⟩ m kvs mgr msg none mf'

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
  -- 1. A creates the object
  wp_apply (wp_container go!"a1" go!"x") as %mc1 Hmc1
  ihave #Hmc1 := isUMap_persistent hL _ _ $$ Hmc1
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %cs1 ⟨Hcs1, -⟩
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %ml1 Hml1
  wp_apply wp_mapInsert $$ Hml1 as Hml1
  imod (isUMap_lit hL ml1 _ _ [(go!"app", str go!"web")] rfl (by decide) (by lit_keys)) $$ Hml1 []
    with #Hl1
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %ms1 Hms1
  wp_apply wp_mapInsert $$ Hms1 as Hms1
  wp_apply wp_mapInsert $$ Hms1 as Hms1
  imod (isUMap_lit hL ms1 _ _ [(go!"k", str go!"v1"), (go!"m", str go!"x")] rfl (by decide)
    (by lit_keys)) $$ Hms1 [] with #Hs1
  · lit_vals
  unfold isUMap
  imod (isIface_lit_list hL _ _ [container go!"a1" go!"x"] rfl) $$ Hcs1 [] with #Hc1
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mo1 Hmo1
  wp_apply wp_mapInsert $$ Hmo1 as Hmo1
  wp_apply wp_mapInsert $$ Hmo1 as Hmo1
  wp_apply wp_mapInsert $$ Hmo1 as Hmo1
  wp_apply wp_mapInsert $$ Hmo1 as Hmo1
  wp_apply wp_mapInsert $$ Hmo1 as Hmo1
  wp_apply wp_mapInsert $$ Hmo1 as Hmo1
  imod (isUMap_lit hL mo1 _ obj1 _ rfl (by decide) (by lit_keys)) $$ Hmo1 [] with #Ho1
  · lit_vals
  wp_apply (wp_apply_some wp_apply «$r0_ptr» sc (.map []) MF.none mo1 (kvsU obj1) go!"A" _ obj1 mf1) $$ [Hst]
    as Hst
  · iframe Hst
    isplitr
    · unfold isUMap
      rw [show UVal.map (kvsU obj1) = obj1 from rfl]
      iexact Ho1
    ipureintro
    refine ⟨conforms_all obj1 (by simp), fun m e h => by simp [MF.none, MF.get, lookupKV] at h,
      small_all.1, step1⟩
  -- aPaths1
  wp_apply wp_field as %p1 Hp1
  wp_apply wp_field as %p2 Hp2
  wp_apply wp_field as %p3 Hp3
  wp_apply wp_mapKey as %p4 Hp4
  wp_apply wp_field as %p5 Hp5
  wp_apply (wp_slice_literal (l := [p1, p2, p3, p4, p5]))
  isplitr
  · ipureintro; rfl
  iintro %ap1 ⟨Hap1, -⟩
  wp_apply wp_containerPaths as %cp1 ⟨%css1, Hcp1, Hcps1⟩
  wp_apply wp_concat $$ [Hap1 Hcp1] as %aP1 ⟨-, -, HaP1⟩
  · iframe Hap1 Hcp1
  ihave HaPs1 : isPaths [p1, p2, p3, p4, p5] [field go!"name", field go!"image", field go!"replicas",
      mapKey go!"labels" go!"app", field go!"selector"] $$ [Hp1 Hp2 Hp3 Hp4 Hp5]
  · iapply isPaths_lit hL _ _ rfl
    simp only [List.zip_cons_cons, List.zip_nil_right, sepL, List.foldr_cons, List.foldr_nil]
    iframe
  ihave HaPs1 := isPaths_concat hL _ _ _ _ $$ HaPs1 Hcps1
  ihave #HaPs1 := hL.pathsP _ _ $$ HaPs1
  imod ownSlice_persist $$ HaP1 with #HaP1
  -- check 1: the object
  wp_apply (wp_container go!"a1" go!"x") as %mc1b Hmc1b
  ihave #Hmc1b := isUMap_persistent hL _ _ $$ Hmc1b
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %cs1b ⟨Hcs1b, -⟩
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %ml1b Hml1b
  wp_apply wp_mapInsert $$ Hml1b as Hml1b
  imod (isUMap_lit hL ml1b _ (UVal.ofMap [(go!"app", str go!"web")]) _ rfl (by decide) (by lit_keys))
    $$ Hml1b [] with #Hl1b
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %ms1b Hms1b
  wp_apply wp_mapInsert $$ Hms1b as Hms1b
  wp_apply wp_mapInsert $$ Hms1b as Hms1b
  imod (isUMap_lit hL ms1b _ (UVal.ofMap [(go!"k", str go!"v1"), (go!"m", str go!"x")]) _ rfl
    (by decide) (by lit_keys)) $$ Hms1b [] with #Hs1b
  · lit_vals
  unfold isUMap
  imod (isIface_lit_list hL _ _ [container go!"a1" go!"x"] rfl) $$ Hcs1b [] with #Hc1b
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mo1b Hmo1b
  wp_apply wp_mapInsert $$ Hmo1b as Hmo1b
  wp_apply wp_mapInsert $$ Hmo1b as Hmo1b
  wp_apply wp_mapInsert $$ Hmo1b as Hmo1b
  wp_apply wp_mapInsert $$ Hmo1b as Hmo1b
  wp_apply wp_mapInsert $$ Hmo1b as Hmo1b
  wp_apply wp_mapInsert $$ Hmo1b as Hmo1b
  imod (isUMap_lit hL mo1b _ obj1 _ rfl (by decide) (by lit_keys)) $$ Hmo1b [] with #Ho1b
  · lit_vals
  -- check 1: the managers
  wp_apply (wp_applied _ _ _ _) $$ [HaP1 HaPs1] as %v1 ⟨-, Hv1⟩
  · iframe HaP1 HaPs1
  ihave #Hv1 := hL.vsetP _ _ $$ Hv1
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm1 Hmm1
  wp_apply wp_mapInsert $$ Hmm1 as Hmm1
  imod (isMF_lit hL mm1 _ mf1 _ rfl (by decide) (by lit_keys)) $$ Hmm1 [] with #Hm1
  · lit_vals
  wp_apply (wp_check «$r0_ptr» sc ⟨obj1, mf1⟩ mo1b (kvsU obj1) mm1 mf1 _) $$ [Hst] as Hst
  · iframe Hst Hm1
    unfold isUMap
    rw [show UVal.map (kvsU obj1) = obj1 from rfl]
    iframe Ho1b
    ipureintro; exact ⟨rfl, rfl⟩
  trace_state
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
