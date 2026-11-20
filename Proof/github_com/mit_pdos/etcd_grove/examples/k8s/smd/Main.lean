/- Lean-first (no Rocq counterpart).

`Main()` (`examples/k8s/smd/smd.go`): the glue over the specs of the
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
public import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA

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

/-- `Updater.Apply` with a conflict outcome. -/
theorem wp_Apply_conflicts (wp_Apply : smd.merge.Updater.Apply.spec (GF := GF))
    (u : Loc) (cv : sigs_k8s_io.structured_merge_diff.v7.merge.Converter) (rion : Bool) (sc : Loc)
    (S : Schema) (t : TypeRef) (lp cp : Loc) (live config : UVal) (ver : GoString) (mfm : GoMap)
    (mf : MF) (mgr : GoString) (force : Bool) (cs : FSet (GoString × Path))
    (h : applyResult S t rion live config ver mf mgr force = .conflicts cs) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.merge ∗
      isUpdater u cv (zero_val GoMap) (zero_val GoMap) rion ∗ isIdentityConverter cv ∗
      isTV lp sc S t live ∗ isTV cp sc S t config ∗ isMF mfm mf ∗
      ⌜∀ m e, mf.get m = some e → e.version = ver ∧ keysWithItems S t e.set⌝ ∗
      ⌜inputsSmall [live, config] mf⌝ }}
    (App (App (App (App (App (App (Val (u @!! go.GoType.PointerType sigs_k8s_io.structured_merge_diff.v7.merge.Updater.ty @!! go!"Apply"))
      (Val #lp)) (Val #cp)) (Val #ver)) (Val #mfm)) (Val #mgr)) (Val #force))
  {{ (op : Loc) (mfm' : GoMap) (err : GoInterface), RET (PairV (PairV #op #mfm') #err);
      ⌜op = null⌝ ∗ isMF mfm' MF.none ∗
          ∃ (s : sigs_k8s_io.structured_merge_diff.v7.merge.Conflicts) (l : List (GoString × Path)),
            ⌜err = interface.mkOk sigs_k8s_io.structured_merge_diff.v7.merge.Conflicts.ty #s ∧ l.Nodup ∧
              FSet.ofList l = cs⌝ ∗ isConflicts s l }} := by
  have H := wp_Apply u cv rion sc S t lp cp live config ver mfm mf mgr force
  rw [h] at H
  exact H

/-- `Updater.Apply` returning an object. -/
theorem wp_Apply_some (wp_Apply : smd.merge.Updater.Apply.spec (GF := GF))
    (u : Loc) (cv : sigs_k8s_io.structured_merge_diff.v7.merge.Converter) (rion : Bool) (sc : Loc)
    (S : Schema) (t : TypeRef) (lp cp : Loc) (live config : UVal) (ver : GoString) (mfm : GoMap)
    (mf : MF) (mgr : GoString) (force : Bool) (x : UVal) (mf' : MF)
    (h : applyResult S t rion live config ver mf mgr force = .ok (some x) mf') :
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.merge ∗
      isUpdater u cv (zero_val GoMap) (zero_val GoMap) rion ∗ isIdentityConverter cv ∗
      isTV lp sc S t live ∗ isTV cp sc S t config ∗ isMF mfm mf ∗
      ⌜∀ m e, mf.get m = some e → e.version = ver ∧ keysWithItems S t e.set⌝ ∗
      ⌜inputsSmall [live, config] mf⌝ }}
    (App (App (App (App (App (App (Val (u @!! go.GoType.PointerType sigs_k8s_io.structured_merge_diff.v7.merge.Updater.ty @!! go!"Apply"))
      (Val #lp)) (Val #cp)) (Val #ver)) (Val #mfm)) (Val #mgr)) (Val #force))
  {{ (op : Loc) (mfm' : GoMap) (err : GoInterface), RET (PairV (PairV #op #mfm') #err);
      ⌜err = interface.nil⌝ ∗ isMF mfm' mf' ∗ isTV op sc S t x }} := by
  have H := wp_Apply u cv rion sc S t lp cp live config ver mfm mf mgr force
  rw [h] at H
  exact H

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
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
  -- 2. B applies a disjoint field
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm1 Hmm1
  wp_apply wp_mapInsert $$ Hmm1 as Hmm1
  imod (isUMap_lit hL mm1 _ (UVal.ofMap [(go!"team", str go!"t")]) _ rfl (by decide) (by lit_keys)) $$ Hmm1 [] with #Hmp2
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm3 Hmm3
  wp_apply wp_mapInsert $$ Hmm3 as Hmm3
  imod (isUMap_lit hL mm3 _ cfg2 _ rfl (by decide) (by lit_keys)) $$ Hmm3 [] with #Hmp4
  · lit_vals
  wp_apply (wp_apply_some wp_apply «$r0_ptr» sc obj1 mf1 mm3 (kvsU cfg2) go!"B" _ obj2 mf2) $$ [Hst] as Hst
  · iframe Hst
    isplitr
    · unfold isUMap
      rw [show UVal.map (kvsU cfg2) = cfg2 from rfl]
      iexact Hmp4
    ipureintro
    exact ⟨conforms_all cfg2 (by simp), mf_premise hL.kwi mf1 (version_all _ (by simp)) (kwi_all _ (by simp)), small_all.2.1, step2⟩
  wp_apply (wp_container go!"a1" go!"x") as %mc5 Hmc5
  ihave #Hmc5 := isUMap_persistent hL _ _ $$ Hmc5
  unfold isUMap
  wp_apply (wp_slice_literal (l := [interface.mkOk mapStrIfaceTy #mc5]))
  isplitr
  · ipureintro; rfl
  iintro %sl6 ⟨Hsl6, -⟩
  try wp_auto
  imod (isIface_lit_list hL _ _ [container go!"a1" go!"x"] rfl) $$ Hsl6 [] with #Hli7
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm8 Hmm8
  wp_apply wp_mapInsert $$ Hmm8 as Hmm8
  wp_apply wp_mapInsert $$ Hmm8 as Hmm8
  imod (isUMap_lit hL mm8 _ (UVal.ofMap [(go!"app", str go!"web"), (go!"team", str go!"t")]) _ rfl (by decide) (by lit_keys)) $$ Hmm8 [] with #Hmp9
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm10 Hmm10
  wp_apply wp_mapInsert $$ Hmm10 as Hmm10
  wp_apply wp_mapInsert $$ Hmm10 as Hmm10
  imod (isUMap_lit hL mm10 _ (UVal.ofMap [(go!"k", str go!"v1"), (go!"m", str go!"x")]) _ rfl (by decide) (by lit_keys)) $$ Hmm10 [] with #Hmp11
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm12 Hmm12
  wp_apply wp_mapInsert $$ Hmm12 as Hmm12
  wp_apply wp_mapInsert $$ Hmm12 as Hmm12
  wp_apply wp_mapInsert $$ Hmm12 as Hmm12
  wp_apply wp_mapInsert $$ Hmm12 as Hmm12
  wp_apply wp_mapInsert $$ Hmm12 as Hmm12
  wp_apply wp_mapInsert $$ Hmm12 as Hmm12
  imod (isUMap_lit hL mm12 _ obj2 _ rfl (by decide) (by lit_keys)) $$ Hmm12 [] with #Hmp13
  · lit_vals
  try wp_auto
  wp_apply (wp_applied _ _ _ _) $$ [HaP1 HaPs1] as %vs14 ⟨-, Hvs14⟩
  · iframe HaP1 HaPs1
  ihave #Hvs14 := hL.vsetP _ _ $$ Hvs14
  wp_apply wp_mapKey as %p15 Hp15
  wp_apply (wp_slice_literal (l := [p15]))
  isplitr
  · ipureintro; rfl
  iintro %ps16 ⟨Hps16, -⟩
  ihave Hpaths17 : isPaths [p15] [mapKey go!"labels" go!"team"] $$ [Hp15]
  · iapply isPaths_lit hL _ _ rfl
    simp only [List.zip_cons_cons, List.zip_nil_right, sepL, List.foldr_cons, List.foldr_nil]
    iframe
  try wp_auto
  wp_apply (wp_applied _ _ _ _) $$ [Hps16 Hpaths17] as %vs18 ⟨-, Hvs18⟩
  · iframe Hps16 Hpaths17
  ihave #Hvs18 := hL.vsetP _ _ $$ Hvs18
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mf19 Hmf19
  wp_apply wp_mapInsert $$ Hmf19 as Hmf19
  wp_apply wp_mapInsert $$ Hmf19 as Hmf19
  imod (isMF_lit hL mf19 _ mf2 _ rfl (by decide) (by lit_keys)) $$ Hmf19 [] with #Hmf20
  · lit_vals
  wp_apply (wp_check «$r0_ptr» sc ⟨obj2, mf2⟩ mm12 (kvsU obj2) mf19 mf2 _) $$ [Hst] as Hst
  · iframe Hst Hmf20
    unfold isUMap
    rw [show UVal.map (kvsU obj2) = obj2 from rfl]
    iframe Hmp13
    ipureintro; exact ⟨rfl, rfl⟩
  -- 3. B applies the value A has for image: no change
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm21 Hmm21
  wp_apply wp_mapInsert $$ Hmm21 as Hmm21
  imod (isUMap_lit hL mm21 _ (UVal.ofMap [(go!"team", str go!"t")]) _ rfl (by decide) (by lit_keys)) $$ Hmm21 [] with #Hmp22
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm23 Hmm23
  wp_apply wp_mapInsert $$ Hmm23 as Hmm23
  wp_apply wp_mapInsert $$ Hmm23 as Hmm23
  imod (isUMap_lit hL mm23 _ cfg3 _ rfl (by decide) (by lit_keys)) $$ Hmm23 [] with #Hmp24
  · lit_vals
  wp_apply (wp_apply_none wp_apply «$r0_ptr» sc obj2 mf2 mm23 (kvsU cfg3) go!"B" _ mf3) $$ [Hst] as Hst
  · iframe Hst
    isplitr
    · unfold isUMap
      rw [show UVal.map (kvsU cfg3) = cfg3 from rfl]
      iexact Hmp24
    ipureintro
    exact ⟨conforms_all cfg3 (by simp), mf_premise hL.kwi mf2 (version_all _ (by simp)) (kwi_all _ (by simp)), small_all.2.2.1, step3⟩
  wp_apply (wp_container go!"a1" go!"x") as %mc25 Hmc25
  ihave #Hmc25 := isUMap_persistent hL _ _ $$ Hmc25
  unfold isUMap
  wp_apply (wp_slice_literal (l := [interface.mkOk mapStrIfaceTy #mc25]))
  isplitr
  · ipureintro; rfl
  iintro %sl26 ⟨Hsl26, -⟩
  try wp_auto
  imod (isIface_lit_list hL _ _ [container go!"a1" go!"x"] rfl) $$ Hsl26 [] with #Hli27
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm28 Hmm28
  wp_apply wp_mapInsert $$ Hmm28 as Hmm28
  wp_apply wp_mapInsert $$ Hmm28 as Hmm28
  imod (isUMap_lit hL mm28 _ (UVal.ofMap [(go!"app", str go!"web"), (go!"team", str go!"t")]) _ rfl (by decide) (by lit_keys)) $$ Hmm28 [] with #Hmp29
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm30 Hmm30
  wp_apply wp_mapInsert $$ Hmm30 as Hmm30
  wp_apply wp_mapInsert $$ Hmm30 as Hmm30
  imod (isUMap_lit hL mm30 _ (UVal.ofMap [(go!"k", str go!"v1"), (go!"m", str go!"x")]) _ rfl (by decide) (by lit_keys)) $$ Hmm30 [] with #Hmp31
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm32 Hmm32
  wp_apply wp_mapInsert $$ Hmm32 as Hmm32
  wp_apply wp_mapInsert $$ Hmm32 as Hmm32
  wp_apply wp_mapInsert $$ Hmm32 as Hmm32
  wp_apply wp_mapInsert $$ Hmm32 as Hmm32
  wp_apply wp_mapInsert $$ Hmm32 as Hmm32
  wp_apply wp_mapInsert $$ Hmm32 as Hmm32
  imod (isUMap_lit hL mm32 _ obj2 _ rfl (by decide) (by lit_keys)) $$ Hmm32 [] with #Hmp33
  · lit_vals
  try wp_auto
  wp_apply (wp_applied _ _ _ _) $$ [HaP1 HaPs1] as %vs34 ⟨-, Hvs34⟩
  · iframe HaP1 HaPs1
  ihave #Hvs34 := hL.vsetP _ _ $$ Hvs34
  wp_apply wp_field as %p35 Hp35
  wp_apply wp_mapKey as %p36 Hp36
  wp_apply (wp_slice_literal (l := [p35, p36]))
  isplitr
  · ipureintro; rfl
  iintro %ps37 ⟨Hps37, -⟩
  ihave Hpaths38 : isPaths [p35, p36] [field go!"image", mapKey go!"labels" go!"team"] $$ [Hp35 Hp36]
  · iapply isPaths_lit hL _ _ rfl
    simp only [List.zip_cons_cons, List.zip_nil_right, sepL, List.foldr_cons, List.foldr_nil]
    iframe
  try wp_auto
  wp_apply (wp_applied _ _ _ _) $$ [Hps37 Hpaths38] as %vs39 ⟨-, Hvs39⟩
  · iframe Hps37 Hpaths38
  ihave #Hvs39 := hL.vsetP _ _ $$ Hvs39
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mf40 Hmf40
  wp_apply wp_mapInsert $$ Hmf40 as Hmf40
  wp_apply wp_mapInsert $$ Hmf40 as Hmf40
  imod (isMF_lit hL mf40 _ mf3 _ rfl (by decide) (by lit_keys)) $$ Hmf40 [] with #Hmf41
  · lit_vals
  wp_apply (wp_check «$r0_ptr» sc ⟨obj2, mf3⟩ mm32 (kvsU obj2) mf40 mf3 _) $$ [Hst] as Hst
  · iframe Hst Hmf41
    unfold isUMap
    rw [show UVal.map (kvsU obj2) = obj2 from rfl]
    iframe Hmp33
    ipureintro; exact ⟨rfl, rfl⟩
  -- 4. B applies replicas 2, not forced: a conflict with A
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm42 Hmm42
  wp_apply wp_mapInsert $$ Hmm42 as Hmm42
  imod (isUMap_lit hL mm42 _ (UVal.ofMap [(go!"team", str go!"t")]) _ rfl (by decide) (by lit_keys)) $$ Hmm42 [] with #Hmp43
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm44 Hmm44
  wp_apply wp_mapInsert $$ Hmm44 as Hmm44
  wp_apply wp_mapInsert $$ Hmm44 as Hmm44
  wp_apply wp_mapInsert $$ Hmm44 as Hmm44
  imod (isUMap_lit hL mm44 _ cfg4 _ rfl (by decide) (by lit_keys)) $$ Hmm44 [] with #Hmp45
  · lit_vals
  try wp_auto
  unfold ownState
  icases Hst with ⟨%u4, %lv4, %mfm4, %cv4, Hs4, Hsc4, Hu4, Hcv4, Hlv4, Hmfm4⟩
  ihave #Hsc4 := hL.schP _ _ $$ Hsc4
  ihave #Hu4 := hL.updP _ _ _ _ _ $$ Hu4
  ihave #Hcv4 := hL.cvP _ $$ Hcv4
  ihave #Hlv4 := hL.tvP _ _ _ _ _ $$ Hlv4
  ihave #Hmfm4 := hL.mfP _ _ $$ Hmfm4
  try wp_auto
  wp_apply (wp_typedObj «$r0_ptr» sc u4 lv4 mfm4 mm44 (kvsU cfg4)) $$ [Hs4] as %cp4 ⟨Hs4, Hcp4⟩
  · iframe Hs4 Hsc4
    isplitr
    · unfold isUMap
      rw [show UVal.map (kvsU cfg4) = cfg4 from rfl]
      iexact Hmp45
    ipureintro; exact conforms_all cfg4 (by simp)
  ihave #Hcp4 := hL.tvP _ _ _ _ _ $$ Hcp4
  rw [show UVal.map (kvsU cfg4) = cfg4 from rfl]
  wp_apply (wp_Apply_conflicts wp_Apply u4 cv4 false sc sc0 rootRef lv4 cp4 obj2 cfg4 version mfm4 mf3 go!"B" false conflicts4 step4) as %op4 %mfm4' %err4 ⟨%hop4, -, %cs4, %l4, ⟨%herr4, %hnd4, %hl4⟩, Hcs4⟩
  · iframe Hu4 Hcv4 Hlv4 Hcp4 Hmfm4
    ipureintro; exact ⟨mf_premise hL.kwi mf3 (version_all _ (by simp)) (kwi_all _ (by simp)), small_all.2.2.2.1⟩
  have hl4' := nodup_ofList_singleton l4 _ hnd4 hl4
  subst herr4 hl4'
  wp_auto
  wp_apply wp_field as %pr4 Hpr4
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %ccl4 ⟨Hccl4, -⟩
  imod ownSlice_persist $$ Hccl4 with #Hccl4
  ihave Hcl4 := (hL.conflictsIntro _ _ [(A, field go!"replicas")] rfl) $$ Hccl4 [Hpr4]
  · simp only [List.zip_cons_cons, List.zip_nil_right, sepL, List.foldr_cons, List.foldr_nil]
    iframe Hpr4
    ipureintro; rfl
  wp_apply (wp_ConflictsEquals conflicts_ptr _ cs4 _ _ _) $$ [conflicts Hcs4 Hcl4] as %r4 ⟨%hr4, conflicts⟩
  · iframe conflicts Hcs4 Hcl4
  have hr4' : r4 = true := hr4.2 rfl
  subst hr4'
  wp_auto
  ihave Hst : ownState «$r0_ptr» sc ⟨obj2, mf3⟩ $$ [Hs4]
  · unfold ownState
    iexists u4, lv4, mfm4, cv4
    iframe Hs4 Hsc4 Hu4 Hcv4 Hlv4 Hmfm4
  wp_apply (wp_container go!"a1" go!"x") as %mc46 Hmc46
  ihave #Hmc46 := isUMap_persistent hL _ _ $$ Hmc46
  unfold isUMap
  wp_apply (wp_slice_literal (l := [interface.mkOk mapStrIfaceTy #mc46]))
  isplitr
  · ipureintro; rfl
  iintro %sl47 ⟨Hsl47, -⟩
  try wp_auto
  imod (isIface_lit_list hL _ _ [container go!"a1" go!"x"] rfl) $$ Hsl47 [] with #Hli48
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm49 Hmm49
  wp_apply wp_mapInsert $$ Hmm49 as Hmm49
  wp_apply wp_mapInsert $$ Hmm49 as Hmm49
  imod (isUMap_lit hL mm49 _ (UVal.ofMap [(go!"app", str go!"web"), (go!"team", str go!"t")]) _ rfl (by decide) (by lit_keys)) $$ Hmm49 [] with #Hmp50
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm51 Hmm51
  wp_apply wp_mapInsert $$ Hmm51 as Hmm51
  wp_apply wp_mapInsert $$ Hmm51 as Hmm51
  imod (isUMap_lit hL mm51 _ (UVal.ofMap [(go!"k", str go!"v1"), (go!"m", str go!"x")]) _ rfl (by decide) (by lit_keys)) $$ Hmm51 [] with #Hmp52
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm53 Hmm53
  wp_apply wp_mapInsert $$ Hmm53 as Hmm53
  wp_apply wp_mapInsert $$ Hmm53 as Hmm53
  wp_apply wp_mapInsert $$ Hmm53 as Hmm53
  wp_apply wp_mapInsert $$ Hmm53 as Hmm53
  wp_apply wp_mapInsert $$ Hmm53 as Hmm53
  wp_apply wp_mapInsert $$ Hmm53 as Hmm53
  imod (isUMap_lit hL mm53 _ obj2 _ rfl (by decide) (by lit_keys)) $$ Hmm53 [] with #Hmp54
  · lit_vals
  try wp_auto
  wp_apply (wp_applied _ _ _ _) $$ [HaP1 HaPs1] as %vs55 ⟨-, Hvs55⟩
  · iframe HaP1 HaPs1
  ihave #Hvs55 := hL.vsetP _ _ $$ Hvs55
  wp_apply wp_field as %p56 Hp56
  wp_apply wp_mapKey as %p57 Hp57
  wp_apply (wp_slice_literal (l := [p56, p57]))
  isplitr
  · ipureintro; rfl
  iintro %ps58 ⟨Hps58, -⟩
  ihave Hpaths59 : isPaths [p56, p57] [field go!"image", mapKey go!"labels" go!"team"] $$ [Hp56 Hp57]
  · iapply isPaths_lit hL _ _ rfl
    simp only [List.zip_cons_cons, List.zip_nil_right, sepL, List.foldr_cons, List.foldr_nil]
    iframe
  try wp_auto
  wp_apply (wp_applied _ _ _ _) $$ [Hps58 Hpaths59] as %vs60 ⟨-, Hvs60⟩
  · iframe Hps58 Hpaths59
  ihave #Hvs60 := hL.vsetP _ _ $$ Hvs60
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mf61 Hmf61
  wp_apply wp_mapInsert $$ Hmf61 as Hmf61
  wp_apply wp_mapInsert $$ Hmf61 as Hmf61
  imod (isMF_lit hL mf61 _ mf3 _ rfl (by decide) (by lit_keys)) $$ Hmf61 [] with #Hmf62
  · lit_vals
  wp_apply (wp_check «$r0_ptr» sc ⟨obj2, mf3⟩ mm53 (kvsU obj2) mf61 mf3 _) $$ [Hst] as Hst
  · iframe Hst Hmf62
    unfold isUMap
    rw [show UVal.map (kvsU obj2) = obj2 from rfl]
    iframe Hmp54
    ipureintro; exact ⟨rfl, rfl⟩
  -- 5. The same, forced
  unfold ownState
  icases Hst with ⟨%u5, %lv5, %mfm5, %cv5, Hs5, Hsc5, Hu5, Hcv5, Hlv5, Hmfm5⟩
  ihave #Hsc5 := hL.schP _ _ $$ Hsc5
  ihave #Hu5 := hL.updP _ _ _ _ _ $$ Hu5
  ihave #Hcv5 := hL.cvP _ $$ Hcv5
  ihave #Hlv5 := hL.tvP _ _ _ _ _ $$ Hlv5
  ihave #Hmfm5 := hL.mfP _ _ $$ Hmfm5
  try wp_auto
  wp_apply (wp_typedObj «$r0_ptr» sc u5 lv5 mfm5 mm44 (kvsU cfg4)) $$ [Hs5] as %cp5 ⟨Hs5, Hcp5⟩
  · iframe Hs5 Hsc5
    isplitr
    · unfold isUMap
      rw [show UVal.map (kvsU cfg4) = cfg4 from rfl]
      iexact Hmp45
    ipureintro; exact conforms_all cfg4 (by simp)
  ihave #Hcp5 := hL.tvP _ _ _ _ _ $$ Hcp5
  rw [show UVal.map (kvsU cfg4) = cfg4 from rfl]
  wp_apply (wp_Apply_some wp_Apply u5 cv5 false sc sc0 rootRef lv5 cp5 obj2 cfg4 version mfm5 mf3 go!"B" true obj5 mf5 step5) as %op5 %mfm5' %err5 ⟨%herr5, Hmf5', Hop5⟩
  · iframe Hu5 Hcv5 Hlv5 Hcp5 Hmfm5
    ipureintro; exact ⟨mf_premise hL.kwi mf3 (version_all _ (by simp)) (kwi_all _ (by simp)), small_all.2.2.2.1⟩
  subst herr5
  ihave #Hop5 := hL.tvP _ _ _ _ _ $$ Hop5
  ihave #Hmf5' := hL.mfP _ _ $$ Hmf5'
  wp_auto
  ihave Hst : ownState «$r0_ptr» sc ⟨obj5, mf5⟩ $$ [Hs5]
  · unfold ownState
    iexists u5, op5, mfm5', cv5
    iframe Hs5 Hsc5 Hu5 Hcv5
    iframe Hop5 Hmf5'
  wp_apply wp_field as %p63 Hp63
  wp_apply wp_field as %p64 Hp64
  wp_apply wp_mapKey as %p65 Hp65
  wp_apply wp_field as %p66 Hp66
  wp_apply (wp_slice_literal (l := [p63, p64, p65, p66]))
  isplitr
  · ipureintro; rfl
  iintro %ps67 ⟨Hps67, -⟩
  ihave Hpaths68 : isPaths [p63, p64, p65, p66] [field go!"name", field go!"image", mapKey go!"labels" go!"app", field go!"selector"] $$ [Hp63 Hp64 Hp65 Hp66]
  · iapply isPaths_lit hL _ _ rfl
    simp only [List.zip_cons_cons, List.zip_nil_right, sepL, List.foldr_cons, List.foldr_nil]
    iframe
  wp_apply wp_containerPaths as %cp69 ⟨%csscp69, Hcp69, Hscp69⟩
  wp_apply wp_concat $$ [Hps67 Hcp69] as %cc70 ⟨-, -, Hcc70⟩
  · iframe Hps67 Hcp69
  ihave Hpaths71 := isPaths_concat hL _ _ _ _ $$ Hpaths68 Hscp69
  imod ownSlice_persist $$ Hcc70 with #Hcc70
  ihave #Hpaths71 := hL.pathsP _ _ $$ Hpaths71
  try wp_auto
  wp_apply wp_field as %p72 Hp72
  wp_apply wp_field as %p73 Hp73
  wp_apply wp_mapKey as %p74 Hp74
  wp_apply (wp_slice_literal (l := [p72, p73, p74]))
  isplitr
  · ipureintro; rfl
  iintro %ps75 ⟨Hps75, -⟩
  ihave Hpaths76 : isPaths [p72, p73, p74] [field go!"image", field go!"replicas", mapKey go!"labels" go!"team"] $$ [Hp72 Hp73 Hp74]
  · iapply isPaths_lit hL _ _ rfl
    simp only [List.zip_cons_cons, List.zip_nil_right, sepL, List.foldr_cons, List.foldr_nil]
    iframe
  imod ownSlice_persist $$ Hps75 with #Hps75
  ihave #Hpaths76 := hL.pathsP _ _ $$ Hpaths76
  try wp_auto
  wp_apply (wp_container go!"a1" go!"x") as %mc77 Hmc77
  ihave #Hmc77 := isUMap_persistent hL _ _ $$ Hmc77
  unfold isUMap
  wp_apply (wp_slice_literal (l := [interface.mkOk mapStrIfaceTy #mc77]))
  isplitr
  · ipureintro; rfl
  iintro %sl78 ⟨Hsl78, -⟩
  try wp_auto
  imod (isIface_lit_list hL _ _ [container go!"a1" go!"x"] rfl) $$ Hsl78 [] with #Hli79
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm80 Hmm80
  wp_apply wp_mapInsert $$ Hmm80 as Hmm80
  wp_apply wp_mapInsert $$ Hmm80 as Hmm80
  imod (isUMap_lit hL mm80 _ (UVal.ofMap [(go!"app", str go!"web"), (go!"team", str go!"t")]) _ rfl (by decide) (by lit_keys)) $$ Hmm80 [] with #Hmp81
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm82 Hmm82
  wp_apply wp_mapInsert $$ Hmm82 as Hmm82
  wp_apply wp_mapInsert $$ Hmm82 as Hmm82
  imod (isUMap_lit hL mm82 _ (UVal.ofMap [(go!"k", str go!"v1"), (go!"m", str go!"x")]) _ rfl (by decide) (by lit_keys)) $$ Hmm82 [] with #Hmp83
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm84 Hmm84
  wp_apply wp_mapInsert $$ Hmm84 as Hmm84
  wp_apply wp_mapInsert $$ Hmm84 as Hmm84
  wp_apply wp_mapInsert $$ Hmm84 as Hmm84
  wp_apply wp_mapInsert $$ Hmm84 as Hmm84
  wp_apply wp_mapInsert $$ Hmm84 as Hmm84
  wp_apply wp_mapInsert $$ Hmm84 as Hmm84
  imod (isUMap_lit hL mm84 _ obj5 _ rfl (by decide) (by lit_keys)) $$ Hmm84 [] with #Hmp85
  · lit_vals
  try wp_auto
  wp_apply (wp_applied _ _ _ _) $$ [Hcc70 Hpaths71] as %vs86 ⟨-, Hvs86⟩
  · iframe Hcc70 Hpaths71
  ihave #Hvs86 := hL.vsetP _ _ $$ Hvs86
  try wp_auto
  wp_apply (wp_applied _ _ _ _) $$ [Hps75 Hpaths76] as %vs87 ⟨-, Hvs87⟩
  · iframe Hps75 Hpaths76
  ihave #Hvs87 := hL.vsetP _ _ $$ Hvs87
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mf88 Hmf88
  wp_apply wp_mapInsert $$ Hmf88 as Hmf88
  wp_apply wp_mapInsert $$ Hmf88 as Hmf88
  imod (isMF_lit hL mf88 _ mf5 _ rfl (by decide) (by lit_keys)) $$ Hmf88 [] with #Hmf89
  · lit_vals
  wp_apply (wp_check «$r0_ptr» sc ⟨obj5, mf5⟩ mm84 (kvsU obj5) mf88 mf5 _) $$ [Hst] as Hst
  · iframe Hst Hmf89
    unfold isUMap
    rw [show UVal.map (kvsU obj5) = obj5 from rfl]
    iframe Hmp85
    ipureintro; exact ⟨rfl, rfl⟩
  -- 6. A applies again without labels.app and image
  wp_apply (wp_container go!"a1" go!"x") as %mc90 Hmc90
  ihave #Hmc90 := isUMap_persistent hL _ _ $$ Hmc90
  unfold isUMap
  wp_apply (wp_slice_literal (l := [interface.mkOk mapStrIfaceTy #mc90]))
  isplitr
  · ipureintro; rfl
  iintro %sl91 ⟨Hsl91, -⟩
  try wp_auto
  imod (isIface_lit_list hL _ _ [container go!"a1" go!"x"] rfl) $$ Hsl91 [] with #Hli92
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm93 Hmm93
  wp_apply wp_mapInsert $$ Hmm93 as Hmm93
  wp_apply wp_mapInsert $$ Hmm93 as Hmm93
  imod (isUMap_lit hL mm93 _ (UVal.ofMap [(go!"k", str go!"v1"), (go!"m", str go!"x")]) _ rfl (by decide) (by lit_keys)) $$ Hmm93 [] with #Hmp94
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm95 Hmm95
  wp_apply wp_mapInsert $$ Hmm95 as Hmm95
  wp_apply wp_mapInsert $$ Hmm95 as Hmm95
  wp_apply wp_mapInsert $$ Hmm95 as Hmm95
  imod (isUMap_lit hL mm95 _ cfg6 _ rfl (by decide) (by lit_keys)) $$ Hmm95 [] with #Hmp96
  · lit_vals
  wp_apply (wp_apply_some wp_apply «$r0_ptr» sc obj5 mf5 mm95 (kvsU cfg6) go!"A" _ obj6 mf6) $$ [Hst] as Hst
  · iframe Hst
    isplitr
    · unfold isUMap
      rw [show UVal.map (kvsU cfg6) = cfg6 from rfl]
      iexact Hmp96
    ipureintro
    exact ⟨conforms_all cfg6 (by simp), mf_premise hL.kwi mf5 (version_all _ (by simp)) (kwi_all _ (by simp)), small_all.2.2.2.2.1, step6⟩
  wp_apply wp_field as %p97 Hp97
  wp_apply wp_field as %p98 Hp98
  wp_apply (wp_slice_literal (l := [p97, p98]))
  isplitr
  · ipureintro; rfl
  iintro %ps99 ⟨Hps99, -⟩
  ihave Hpaths100 : isPaths [p97, p98] [field go!"name", field go!"selector"] $$ [Hp97 Hp98]
  · iapply isPaths_lit hL _ _ rfl
    simp only [List.zip_cons_cons, List.zip_nil_right, sepL, List.foldr_cons, List.foldr_nil]
    iframe
  wp_apply wp_containerPaths as %cp101 ⟨%csscp101, Hcp101, Hscp101⟩
  wp_apply wp_concat $$ [Hps99 Hcp101] as %cc102 ⟨-, -, Hcc102⟩
  · iframe Hps99 Hcp101
  ihave Hpaths103 := isPaths_concat hL _ _ _ _ $$ Hpaths100 Hscp101
  imod ownSlice_persist $$ Hcc102 with #Hcc102
  ihave #Hpaths103 := hL.pathsP _ _ $$ Hpaths103
  try wp_auto
  wp_apply (wp_container go!"a1" go!"x") as %mc104 Hmc104
  ihave #Hmc104 := isUMap_persistent hL _ _ $$ Hmc104
  unfold isUMap
  wp_apply (wp_slice_literal (l := [interface.mkOk mapStrIfaceTy #mc104]))
  isplitr
  · ipureintro; rfl
  iintro %sl105 ⟨Hsl105, -⟩
  try wp_auto
  imod (isIface_lit_list hL _ _ [container go!"a1" go!"x"] rfl) $$ Hsl105 [] with #Hli106
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm107 Hmm107
  wp_apply wp_mapInsert $$ Hmm107 as Hmm107
  imod (isUMap_lit hL mm107 _ (UVal.ofMap [(go!"team", str go!"t")]) _ rfl (by decide) (by lit_keys)) $$ Hmm107 [] with #Hmp108
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm109 Hmm109
  wp_apply wp_mapInsert $$ Hmm109 as Hmm109
  wp_apply wp_mapInsert $$ Hmm109 as Hmm109
  imod (isUMap_lit hL mm109 _ (UVal.ofMap [(go!"k", str go!"v1"), (go!"m", str go!"x")]) _ rfl (by decide) (by lit_keys)) $$ Hmm109 [] with #Hmp110
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm111 Hmm111
  wp_apply wp_mapInsert $$ Hmm111 as Hmm111
  wp_apply wp_mapInsert $$ Hmm111 as Hmm111
  wp_apply wp_mapInsert $$ Hmm111 as Hmm111
  wp_apply wp_mapInsert $$ Hmm111 as Hmm111
  wp_apply wp_mapInsert $$ Hmm111 as Hmm111
  wp_apply wp_mapInsert $$ Hmm111 as Hmm111
  imod (isUMap_lit hL mm111 _ obj6 _ rfl (by decide) (by lit_keys)) $$ Hmm111 [] with #Hmp112
  · lit_vals
  try wp_auto
  wp_apply (wp_applied _ _ _ _) $$ [Hcc102 Hpaths103] as %vs113 ⟨-, Hvs113⟩
  · iframe Hcc102 Hpaths103
  ihave #Hvs113 := hL.vsetP _ _ $$ Hvs113
  try wp_auto
  wp_apply (wp_applied _ _ _ _) $$ [Hps75 Hpaths76] as %vs114 ⟨-, Hvs114⟩
  · iframe Hps75 Hpaths76
  ihave #Hvs114 := hL.vsetP _ _ $$ Hvs114
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mf115 Hmf115
  wp_apply wp_mapInsert $$ Hmf115 as Hmf115
  wp_apply wp_mapInsert $$ Hmf115 as Hmf115
  imod (isMF_lit hL mf115 _ mf6 _ rfl (by decide) (by lit_keys)) $$ Hmf115 [] with #Hmf116
  · lit_vals
  wp_apply (wp_check «$r0_ptr» sc ⟨obj6, mf6⟩ mm111 (kvsU obj6) mf115 mf6 _) $$ [Hst] as Hst
  · iframe Hst Hmf116
    unfold isUMap
    rw [show UVal.map (kvsU obj6) = obj6 from rfl]
    iframe Hmp112
    ipureintro; exact ⟨rfl, rfl⟩
  -- 7. B adds a list item
  wp_apply (wp_container go!"b1" go!"y") as %mc117 Hmc117
  ihave #Hmc117 := isUMap_persistent hL _ _ $$ Hmc117
  unfold isUMap
  wp_apply (wp_slice_literal (l := [interface.mkOk mapStrIfaceTy #mc117]))
  isplitr
  · ipureintro; rfl
  iintro %sl118 ⟨Hsl118, -⟩
  try wp_auto
  imod (isIface_lit_list hL _ _ [container go!"b1" go!"y"] rfl) $$ Hsl118 [] with #Hli119
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm120 Hmm120
  wp_apply wp_mapInsert $$ Hmm120 as Hmm120
  imod (isUMap_lit hL mm120 _ (UVal.ofMap [(go!"team", str go!"t")]) _ rfl (by decide) (by lit_keys)) $$ Hmm120 [] with #Hmp121
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm122 Hmm122
  wp_apply wp_mapInsert $$ Hmm122 as Hmm122
  wp_apply wp_mapInsert $$ Hmm122 as Hmm122
  wp_apply wp_mapInsert $$ Hmm122 as Hmm122
  wp_apply wp_mapInsert $$ Hmm122 as Hmm122
  imod (isUMap_lit hL mm122 _ cfg7a _ rfl (by decide) (by lit_keys)) $$ Hmm122 [] with #Hmp123
  · lit_vals
  wp_apply (wp_apply_some wp_apply «$r0_ptr» sc obj6 mf6 mm122 (kvsU cfg7a) go!"B" _ obj7a mf7a) $$ [Hst] as Hst
  · iframe Hst
    isplitr
    · unfold isUMap
      rw [show UVal.map (kvsU cfg7a) = cfg7a from rfl]
      iexact Hmp123
    ipureintro
    exact ⟨conforms_all cfg7a (by simp), mf_premise hL.kwi mf6 (version_all _ (by simp)) (kwi_all _ (by simp)), small_all.2.2.2.2.2.1, step7a⟩
  wp_apply wp_containerPaths as %cp124 ⟨%csscp124, Hcp124, Hscp124⟩
  wp_apply wp_concat $$ [Hps75 Hcp124] as %cc125 ⟨-, -, Hcc125⟩
  · iframe Hps75 Hcp124
  ihave Hpaths126 := isPaths_concat hL _ _ _ _ $$ Hpaths76 Hscp124
  imod ownSlice_persist $$ Hcc125 with #Hcc125
  ihave #Hpaths126 := hL.pathsP _ _ $$ Hpaths126
  try wp_auto
  wp_apply (wp_container go!"a1" go!"x") as %mc127 Hmc127
  ihave #Hmc127 := isUMap_persistent hL _ _ $$ Hmc127
  unfold isUMap
  wp_apply (wp_container go!"b1" go!"y") as %mc128 Hmc128
  ihave #Hmc128 := isUMap_persistent hL _ _ $$ Hmc128
  unfold isUMap
  wp_apply (wp_slice_literal (l := [interface.mkOk mapStrIfaceTy #mc127, interface.mkOk mapStrIfaceTy #mc128]))
  isplitr
  · ipureintro; rfl
  iintro %sl129 ⟨Hsl129, -⟩
  try wp_auto
  imod (isIface_lit_list hL _ _ [container go!"a1" go!"x", container go!"b1" go!"y"] rfl) $$ Hsl129 [] with #Hli130
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm131 Hmm131
  wp_apply wp_mapInsert $$ Hmm131 as Hmm131
  imod (isUMap_lit hL mm131 _ (UVal.ofMap [(go!"team", str go!"t")]) _ rfl (by decide) (by lit_keys)) $$ Hmm131 [] with #Hmp132
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm133 Hmm133
  wp_apply wp_mapInsert $$ Hmm133 as Hmm133
  wp_apply wp_mapInsert $$ Hmm133 as Hmm133
  imod (isUMap_lit hL mm133 _ (UVal.ofMap [(go!"k", str go!"v1"), (go!"m", str go!"x")]) _ rfl (by decide) (by lit_keys)) $$ Hmm133 [] with #Hmp134
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm135 Hmm135
  wp_apply wp_mapInsert $$ Hmm135 as Hmm135
  wp_apply wp_mapInsert $$ Hmm135 as Hmm135
  wp_apply wp_mapInsert $$ Hmm135 as Hmm135
  wp_apply wp_mapInsert $$ Hmm135 as Hmm135
  wp_apply wp_mapInsert $$ Hmm135 as Hmm135
  wp_apply wp_mapInsert $$ Hmm135 as Hmm135
  imod (isUMap_lit hL mm135 _ obj7a _ rfl (by decide) (by lit_keys)) $$ Hmm135 [] with #Hmp136
  · lit_vals
  try wp_auto
  wp_apply (wp_applied _ _ _ _) $$ [Hcc102 Hpaths103] as %vs137 ⟨-, Hvs137⟩
  · iframe Hcc102 Hpaths103
  ihave #Hvs137 := hL.vsetP _ _ $$ Hvs137
  try wp_auto
  wp_apply (wp_applied _ _ _ _) $$ [Hcc125 Hpaths126] as %vs138 ⟨-, Hvs138⟩
  · iframe Hcc125 Hpaths126
  ihave #Hvs138 := hL.vsetP _ _ $$ Hvs138
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mf139 Hmf139
  wp_apply wp_mapInsert $$ Hmf139 as Hmf139
  wp_apply wp_mapInsert $$ Hmf139 as Hmf139
  imod (isMF_lit hL mf139 _ mf7a _ rfl (by decide) (by lit_keys)) $$ Hmf139 [] with #Hmf140
  · lit_vals
  wp_apply (wp_check «$r0_ptr» sc ⟨obj7a, mf7a⟩ mm135 (kvsU obj7a) mf139 mf7a _) $$ [Hst] as Hst
  · iframe Hst Hmf140
    unfold isUMap
    rw [show UVal.map (kvsU obj7a) = obj7a from rfl]
    iframe Hmp136
    ipureintro; exact ⟨rfl, rfl⟩
  -- 7. A replaces its item a1 by a2
  wp_apply (wp_container go!"a2" go!"z") as %mc141 Hmc141
  ihave #Hmc141 := isUMap_persistent hL _ _ $$ Hmc141
  unfold isUMap
  wp_apply (wp_slice_literal (l := [interface.mkOk mapStrIfaceTy #mc141]))
  isplitr
  · ipureintro; rfl
  iintro %sl142 ⟨Hsl142, -⟩
  try wp_auto
  imod (isIface_lit_list hL _ _ [container go!"a2" go!"z"] rfl) $$ Hsl142 [] with #Hli143
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm144 Hmm144
  wp_apply wp_mapInsert $$ Hmm144 as Hmm144
  wp_apply wp_mapInsert $$ Hmm144 as Hmm144
  imod (isUMap_lit hL mm144 _ (UVal.ofMap [(go!"k", str go!"v1"), (go!"m", str go!"x")]) _ rfl (by decide) (by lit_keys)) $$ Hmm144 [] with #Hmp145
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm146 Hmm146
  wp_apply wp_mapInsert $$ Hmm146 as Hmm146
  wp_apply wp_mapInsert $$ Hmm146 as Hmm146
  wp_apply wp_mapInsert $$ Hmm146 as Hmm146
  imod (isUMap_lit hL mm146 _ cfg7b _ rfl (by decide) (by lit_keys)) $$ Hmm146 [] with #Hmp147
  · lit_vals
  wp_apply (wp_apply_some wp_apply «$r0_ptr» sc obj7a mf7a mm146 (kvsU cfg7b) go!"A" _ obj7b mf7b) $$ [Hst] as Hst
  · iframe Hst
    isplitr
    · unfold isUMap
      rw [show UVal.map (kvsU cfg7b) = cfg7b from rfl]
      iexact Hmp147
    ipureintro
    exact ⟨conforms_all cfg7b (by simp), mf_premise hL.kwi mf7a (version_all _ (by simp)) (kwi_all _ (by simp)), small_all.2.2.2.2.2.2.1, step7b⟩
  wp_apply wp_field as %p148 Hp148
  wp_apply wp_field as %p149 Hp149
  wp_apply (wp_slice_literal (l := [p148, p149]))
  isplitr
  · ipureintro; rfl
  iintro %ps150 ⟨Hps150, -⟩
  ihave Hpaths151 : isPaths [p148, p149] [field go!"name", field go!"selector"] $$ [Hp148 Hp149]
  · iapply isPaths_lit hL _ _ rfl
    simp only [List.zip_cons_cons, List.zip_nil_right, sepL, List.foldr_cons, List.foldr_nil]
    iframe
  wp_apply wp_containerPaths as %cp152 ⟨%csscp152, Hcp152, Hscp152⟩
  wp_apply wp_concat $$ [Hps150 Hcp152] as %cc153 ⟨-, -, Hcc153⟩
  · iframe Hps150 Hcp152
  ihave Hpaths154 := isPaths_concat hL _ _ _ _ $$ Hpaths151 Hscp152
  imod ownSlice_persist $$ Hcc153 with #Hcc153
  ihave #Hpaths154 := hL.pathsP _ _ $$ Hpaths154
  try wp_auto
  wp_apply (wp_container go!"b1" go!"y") as %mc155 Hmc155
  ihave #Hmc155 := isUMap_persistent hL _ _ $$ Hmc155
  unfold isUMap
  wp_apply (wp_container go!"a2" go!"z") as %mc156 Hmc156
  ihave #Hmc156 := isUMap_persistent hL _ _ $$ Hmc156
  unfold isUMap
  wp_apply (wp_slice_literal (l := [interface.mkOk mapStrIfaceTy #mc155, interface.mkOk mapStrIfaceTy #mc156]))
  isplitr
  · ipureintro; rfl
  iintro %sl157 ⟨Hsl157, -⟩
  try wp_auto
  imod (isIface_lit_list hL _ _ [container go!"b1" go!"y", container go!"a2" go!"z"] rfl) $$ Hsl157 [] with #Hli158
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm159 Hmm159
  wp_apply wp_mapInsert $$ Hmm159 as Hmm159
  imod (isUMap_lit hL mm159 _ (UVal.ofMap [(go!"team", str go!"t")]) _ rfl (by decide) (by lit_keys)) $$ Hmm159 [] with #Hmp160
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm161 Hmm161
  wp_apply wp_mapInsert $$ Hmm161 as Hmm161
  wp_apply wp_mapInsert $$ Hmm161 as Hmm161
  imod (isUMap_lit hL mm161 _ (UVal.ofMap [(go!"k", str go!"v1"), (go!"m", str go!"x")]) _ rfl (by decide) (by lit_keys)) $$ Hmm161 [] with #Hmp162
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm163 Hmm163
  wp_apply wp_mapInsert $$ Hmm163 as Hmm163
  wp_apply wp_mapInsert $$ Hmm163 as Hmm163
  wp_apply wp_mapInsert $$ Hmm163 as Hmm163
  wp_apply wp_mapInsert $$ Hmm163 as Hmm163
  wp_apply wp_mapInsert $$ Hmm163 as Hmm163
  wp_apply wp_mapInsert $$ Hmm163 as Hmm163
  imod (isUMap_lit hL mm163 _ obj7b _ rfl (by decide) (by lit_keys)) $$ Hmm163 [] with #Hmp164
  · lit_vals
  try wp_auto
  wp_apply (wp_applied _ _ _ _) $$ [Hcc153 Hpaths154] as %vs165 ⟨-, Hvs165⟩
  · iframe Hcc153 Hpaths154
  ihave #Hvs165 := hL.vsetP _ _ $$ Hvs165
  try wp_auto
  wp_apply (wp_applied _ _ _ _) $$ [Hcc125 Hpaths126] as %vs166 ⟨-, Hvs166⟩
  · iframe Hcc125 Hpaths126
  ihave #Hvs166 := hL.vsetP _ _ $$ Hvs166
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mf167 Hmf167
  wp_apply wp_mapInsert $$ Hmf167 as Hmf167
  wp_apply wp_mapInsert $$ Hmf167 as Hmf167
  imod (isMF_lit hL mf167 _ mf7b _ rfl (by decide) (by lit_keys)) $$ Hmf167 [] with #Hmf168
  · lit_vals
  wp_apply (wp_check «$r0_ptr» sc ⟨obj7b, mf7b⟩ mm163 (kvsU obj7b) mf167 mf7b _) $$ [Hst] as Hst
  · iframe Hst Hmf168
    unfold isUMap
    rw [show UVal.map (kvsU obj7b) = obj7b from rfl]
    iframe Hmp164
    ipureintro; exact ⟨rfl, rfl⟩
  -- 8. C updates replicas and adds labels.env
  unfold ownState
  icases Hst with ⟨%u8, %lv8, %mfm8, %cv8, Hs8, Hsc8, Hu8, Hcv8, Hlv8, Hmfm8⟩
  ihave #Hsc8 := hL.schP _ _ $$ Hsc8
  ihave #Hu8 := hL.updP _ _ _ _ _ $$ Hu8
  ihave #Hcv8 := hL.cvP _ $$ Hcv8
  ihave #Hlv8 := hL.tvP _ _ _ _ _ $$ Hlv8
  ihave #Hmfm8 := hL.mfP _ _ $$ Hmfm8
  try wp_auto
  wp_apply (wp_container go!"b1" go!"y") as %mc169 Hmc169
  ihave #Hmc169 := isUMap_persistent hL _ _ $$ Hmc169
  unfold isUMap
  wp_apply (wp_container go!"a2" go!"z") as %mc170 Hmc170
  ihave #Hmc170 := isUMap_persistent hL _ _ $$ Hmc170
  unfold isUMap
  wp_apply (wp_slice_literal (l := [interface.mkOk mapStrIfaceTy #mc169, interface.mkOk mapStrIfaceTy #mc170]))
  isplitr
  · ipureintro; rfl
  iintro %sl171 ⟨Hsl171, -⟩
  try wp_auto
  imod (isIface_lit_list hL _ _ [container go!"b1" go!"y", container go!"a2" go!"z"] rfl) $$ Hsl171 [] with #Hli172
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm173 Hmm173
  wp_apply wp_mapInsert $$ Hmm173 as Hmm173
  wp_apply wp_mapInsert $$ Hmm173 as Hmm173
  imod (isUMap_lit hL mm173 _ (UVal.ofMap [(go!"team", str go!"t"), (go!"env", str go!"prod")]) _ rfl (by decide) (by lit_keys)) $$ Hmm173 [] with #Hmp174
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm175 Hmm175
  wp_apply wp_mapInsert $$ Hmm175 as Hmm175
  wp_apply wp_mapInsert $$ Hmm175 as Hmm175
  imod (isUMap_lit hL mm175 _ (UVal.ofMap [(go!"k", str go!"v1"), (go!"m", str go!"x")]) _ rfl (by decide) (by lit_keys)) $$ Hmm175 [] with #Hmp176
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm177 Hmm177
  wp_apply wp_mapInsert $$ Hmm177 as Hmm177
  wp_apply wp_mapInsert $$ Hmm177 as Hmm177
  wp_apply wp_mapInsert $$ Hmm177 as Hmm177
  wp_apply wp_mapInsert $$ Hmm177 as Hmm177
  wp_apply wp_mapInsert $$ Hmm177 as Hmm177
  wp_apply wp_mapInsert $$ Hmm177 as Hmm177
  imod (isUMap_lit hL mm177 _ obj8 _ rfl (by decide) (by lit_keys)) $$ Hmm177 [] with #Hmp178
  · lit_vals
  try wp_auto
  wp_apply (wp_typedObj «$r0_ptr» sc u8 lv8 mfm8 mm177 (kvsU obj8)) $$ [Hs8] as %cp8 ⟨Hs8, Hcp8⟩
  · iframe Hs8 Hsc8
    isplitr
    · unfold isUMap
      rw [show UVal.map (kvsU obj8) = obj8 from rfl]
      iexact Hmp178
    ipureintro; exact conforms_all obj8 (by simp)
  ihave #Hcp8 := hL.tvP _ _ _ _ _ $$ Hcp8
  rw [show UVal.map (kvsU obj8) = obj8 from rfl]
  wp_apply (wp_Update u8 cv8 false sc sc0 rootRef lv8 cp8 obj7b obj8 version mfm8 mf7b go!"C") as %op8 %mfm8' %err8 ⟨%h8, Hmf8'⟩
  · iframe Hu8 Hcv8 Hlv8 Hcp8 Hmfm8
    ipureintro; exact small_all.2.2.2.2.2.2.2.1
  obtain ⟨rfl, rfl⟩ := h8
  rw [show updateResult sc0 rootRef obj7b obj8 version mf7b go!"C" = mf8 from step8]
  ihave #Hmf8' := hL.mfP _ _ $$ Hmf8'
  wp_auto
  ihave Hst : ownState «$r0_ptr» sc ⟨obj8, mf8⟩ $$ [Hs8]
  · unfold ownState
    iexists u8, _, mfm8', cv8
    iframe Hs8 Hsc8 Hu8 Hcv8
    iframe Hcp8 Hmf8'
  wp_apply wp_field as %p179 Hp179
  wp_apply wp_mapKey as %p180 Hp180
  wp_apply (wp_slice_literal (l := [p179, p180]))
  isplitr
  · ipureintro; rfl
  iintro %ps181 ⟨Hps181, -⟩
  ihave Hpaths182 : isPaths [p179, p180] [field go!"image", mapKey go!"labels" go!"team"] $$ [Hp179 Hp180]
  · iapply isPaths_lit hL _ _ rfl
    simp only [List.zip_cons_cons, List.zip_nil_right, sepL, List.foldr_cons, List.foldr_nil]
    iframe
  wp_apply wp_containerPaths as %cp183 ⟨%csscp183, Hcp183, Hscp183⟩
  wp_apply wp_concat $$ [Hps181 Hcp183] as %cc184 ⟨-, -, Hcc184⟩
  · iframe Hps181 Hcp183
  ihave Hpaths185 := isPaths_concat hL _ _ _ _ $$ Hpaths182 Hscp183
  imod ownSlice_persist $$ Hcc184 with #Hcc184
  ihave #Hpaths185 := hL.pathsP _ _ $$ Hpaths185
  try wp_auto
  wp_apply (wp_container go!"b1" go!"y") as %mc186 Hmc186
  ihave #Hmc186 := isUMap_persistent hL _ _ $$ Hmc186
  unfold isUMap
  wp_apply (wp_container go!"a2" go!"z") as %mc187 Hmc187
  ihave #Hmc187 := isUMap_persistent hL _ _ $$ Hmc187
  unfold isUMap
  wp_apply (wp_slice_literal (l := [interface.mkOk mapStrIfaceTy #mc186, interface.mkOk mapStrIfaceTy #mc187]))
  isplitr
  · ipureintro; rfl
  iintro %sl188 ⟨Hsl188, -⟩
  try wp_auto
  imod (isIface_lit_list hL _ _ [container go!"b1" go!"y", container go!"a2" go!"z"] rfl) $$ Hsl188 [] with #Hli189
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm190 Hmm190
  wp_apply wp_mapInsert $$ Hmm190 as Hmm190
  wp_apply wp_mapInsert $$ Hmm190 as Hmm190
  imod (isUMap_lit hL mm190 _ (UVal.ofMap [(go!"team", str go!"t"), (go!"env", str go!"prod")]) _ rfl (by decide) (by lit_keys)) $$ Hmm190 [] with #Hmp191
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm192 Hmm192
  wp_apply wp_mapInsert $$ Hmm192 as Hmm192
  wp_apply wp_mapInsert $$ Hmm192 as Hmm192
  imod (isUMap_lit hL mm192 _ (UVal.ofMap [(go!"k", str go!"v1"), (go!"m", str go!"x")]) _ rfl (by decide) (by lit_keys)) $$ Hmm192 [] with #Hmp193
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm194 Hmm194
  wp_apply wp_mapInsert $$ Hmm194 as Hmm194
  wp_apply wp_mapInsert $$ Hmm194 as Hmm194
  wp_apply wp_mapInsert $$ Hmm194 as Hmm194
  wp_apply wp_mapInsert $$ Hmm194 as Hmm194
  wp_apply wp_mapInsert $$ Hmm194 as Hmm194
  wp_apply wp_mapInsert $$ Hmm194 as Hmm194
  imod (isUMap_lit hL mm194 _ obj8 _ rfl (by decide) (by lit_keys)) $$ Hmm194 [] with #Hmp195
  · lit_vals
  try wp_auto
  wp_apply (wp_applied _ _ _ _) $$ [Hcc153 Hpaths154] as %vs196 ⟨-, Hvs196⟩
  · iframe Hcc153 Hpaths154
  ihave #Hvs196 := hL.vsetP _ _ $$ Hvs196
  try wp_auto
  wp_apply (wp_applied _ _ _ _) $$ [Hcc184 Hpaths185] as %vs197 ⟨-, Hvs197⟩
  · iframe Hcc184 Hpaths185
  ihave #Hvs197 := hL.vsetP _ _ $$ Hvs197
  wp_apply wp_field as %p198 Hp198
  wp_apply wp_mapKey as %p199 Hp199
  wp_apply (wp_slice_literal (l := [p198, p199]))
  isplitr
  · ipureintro; rfl
  iintro %ps200 ⟨Hps200, -⟩
  ihave Hpaths201 : isPaths [p198, p199] [field go!"replicas", mapKey go!"labels" go!"env"] $$ [Hp198 Hp199]
  · iapply isPaths_lit hL _ _ rfl
    simp only [List.zip_cons_cons, List.zip_nil_right, sepL, List.foldr_cons, List.foldr_nil]
    iframe
  try wp_auto
  wp_apply (wp_updated _ _ _ _) $$ [Hps200 Hpaths201] as %vs202 ⟨-, Hvs202⟩
  · iframe Hps200 Hpaths201
  ihave #Hvs202 := hL.vsetP _ _ $$ Hvs202
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mf203 Hmf203
  wp_apply wp_mapInsert $$ Hmf203 as Hmf203
  wp_apply wp_mapInsert $$ Hmf203 as Hmf203
  wp_apply wp_mapInsert $$ Hmf203 as Hmf203
  imod (isMF_lit hL mf203 _ mf8 _ rfl (by decide) (by lit_keys)) $$ Hmf203 [] with #Hmf204
  · lit_vals
  wp_apply (wp_check «$r0_ptr» sc ⟨obj8, mf8⟩ mm194 (kvsU obj8) mf203 mf8 _) $$ [Hst] as Hst
  · iframe Hst Hmf204
    unfold isUMap
    rw [show UVal.map (kvsU obj8) = obj8 from rfl]
    iframe Hmp195
    ipureintro; exact ⟨rfl, rfl⟩
  -- 9. A changes the atomic selector
  wp_apply (wp_container go!"a2" go!"z") as %mc205 Hmc205
  ihave #Hmc205 := isUMap_persistent hL _ _ $$ Hmc205
  unfold isUMap
  wp_apply (wp_slice_literal (l := [interface.mkOk mapStrIfaceTy #mc205]))
  isplitr
  · ipureintro; rfl
  iintro %sl206 ⟨Hsl206, -⟩
  try wp_auto
  imod (isIface_lit_list hL _ _ [container go!"a2" go!"z"] rfl) $$ Hsl206 [] with #Hli207
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm208 Hmm208
  wp_apply wp_mapInsert $$ Hmm208 as Hmm208
  imod (isUMap_lit hL mm208 _ (UVal.ofMap [(go!"k", str go!"v2")]) _ rfl (by decide) (by lit_keys)) $$ Hmm208 [] with #Hmp209
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm210 Hmm210
  wp_apply wp_mapInsert $$ Hmm210 as Hmm210
  wp_apply wp_mapInsert $$ Hmm210 as Hmm210
  wp_apply wp_mapInsert $$ Hmm210 as Hmm210
  imod (isUMap_lit hL mm210 _ cfg9 _ rfl (by decide) (by lit_keys)) $$ Hmm210 [] with #Hmp211
  · lit_vals
  wp_apply (wp_apply_some wp_apply «$r0_ptr» sc obj8 mf8 mm210 (kvsU cfg9) go!"A" _ obj9 mf8) $$ [Hst] as Hst
  · iframe Hst
    isplitr
    · unfold isUMap
      rw [show UVal.map (kvsU cfg9) = cfg9 from rfl]
      iexact Hmp211
    ipureintro
    exact ⟨conforms_all cfg9 (by simp), mf_premise hL.kwi mf8 (version_all _ (by simp)) (kwi_all _ (by simp)), small_all.2.2.2.2.2.2.2.2, step9⟩
  wp_apply (wp_container go!"b1" go!"y") as %mc212 Hmc212
  ihave #Hmc212 := isUMap_persistent hL _ _ $$ Hmc212
  unfold isUMap
  wp_apply (wp_container go!"a2" go!"z") as %mc213 Hmc213
  ihave #Hmc213 := isUMap_persistent hL _ _ $$ Hmc213
  unfold isUMap
  wp_apply (wp_slice_literal (l := [interface.mkOk mapStrIfaceTy #mc212, interface.mkOk mapStrIfaceTy #mc213]))
  isplitr
  · ipureintro; rfl
  iintro %sl214 ⟨Hsl214, -⟩
  try wp_auto
  imod (isIface_lit_list hL _ _ [container go!"b1" go!"y", container go!"a2" go!"z"] rfl) $$ Hsl214 [] with #Hli215
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm216 Hmm216
  wp_apply wp_mapInsert $$ Hmm216 as Hmm216
  wp_apply wp_mapInsert $$ Hmm216 as Hmm216
  imod (isUMap_lit hL mm216 _ (UVal.ofMap [(go!"team", str go!"t"), (go!"env", str go!"prod")]) _ rfl (by decide) (by lit_keys)) $$ Hmm216 [] with #Hmp217
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm218 Hmm218
  wp_apply wp_mapInsert $$ Hmm218 as Hmm218
  imod (isUMap_lit hL mm218 _ (UVal.ofMap [(go!"k", str go!"v2")]) _ rfl (by decide) (by lit_keys)) $$ Hmm218 [] with #Hmp219
  · lit_vals
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mm220 Hmm220
  wp_apply wp_mapInsert $$ Hmm220 as Hmm220
  wp_apply wp_mapInsert $$ Hmm220 as Hmm220
  wp_apply wp_mapInsert $$ Hmm220 as Hmm220
  wp_apply wp_mapInsert $$ Hmm220 as Hmm220
  wp_apply wp_mapInsert $$ Hmm220 as Hmm220
  wp_apply wp_mapInsert $$ Hmm220 as Hmm220
  imod (isUMap_lit hL mm220 _ obj9 _ rfl (by decide) (by lit_keys)) $$ Hmm220 [] with #Hmp221
  · lit_vals
  try wp_auto
  wp_apply (wp_applied _ _ _ _) $$ [Hcc153 Hpaths154] as %vs222 ⟨-, Hvs222⟩
  · iframe Hcc153 Hpaths154
  ihave #Hvs222 := hL.vsetP _ _ $$ Hvs222
  try wp_auto
  wp_apply (wp_applied _ _ _ _) $$ [Hcc184 Hpaths185] as %vs223 ⟨-, Hvs223⟩
  · iframe Hcc184 Hpaths185
  ihave #Hvs223 := hL.vsetP _ _ $$ Hvs223
  wp_apply wp_field as %p224 Hp224
  wp_apply wp_mapKey as %p225 Hp225
  wp_apply (wp_slice_literal (l := [p224, p225]))
  isplitr
  · ipureintro; rfl
  iintro %ps226 ⟨Hps226, -⟩
  ihave Hpaths227 : isPaths [p224, p225] [field go!"replicas", mapKey go!"labels" go!"env"] $$ [Hp224 Hp225]
  · iapply isPaths_lit hL _ _ rfl
    simp only [List.zip_cons_cons, List.zip_nil_right, sepL, List.foldr_cons, List.foldr_nil]
    iframe
  try wp_auto
  wp_apply (wp_updated _ _ _ _) $$ [Hps226 Hpaths227] as %vs228 ⟨-, Hvs228⟩
  · iframe Hps226 Hpaths227
  ihave #Hvs228 := hL.vsetP _ _ $$ Hvs228
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mf229 Hmf229
  wp_apply wp_mapInsert $$ Hmf229 as Hmf229
  wp_apply wp_mapInsert $$ Hmf229 as Hmf229
  wp_apply wp_mapInsert $$ Hmf229 as Hmf229
  imod (isMF_lit hL mf229 _ mf8 _ rfl (by decide) (by lit_keys)) $$ Hmf229 [] with #Hmf230
  · lit_vals
  wp_apply (wp_check «$r0_ptr» sc ⟨obj9, mf8⟩ mm220 (kvsU obj9) mf229 mf8 _) $$ [Hst] as Hst
  · iframe Hst Hmf230
    unfold isUMap
    rw [show UVal.map (kvsU obj9) = obj9 from rfl]
    iframe Hmp221
    ipureintro; exact ⟨rfl, rfl⟩
  iapply HΦ
  itrivial

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
  Main.wp_proof_of ⟨isIface_scalar_law_holds, isIface_list_law_holds, isIface_ofMap_law_holds,
      isMF_intro_law_holds, isPath_intro_law_holds, isPaths_nil_law_holds, isPaths_cons_law_holds,
      isPaths_app_law_holds, isPaths_length_law_holds, isPaths_persistent_law_holds,
      isPath_persistent_law_holds, isVSet_persistent_law_holds, isIface_persistent_law_holds,
      isSchema_persistent_law_holds, isTV_persistent_law_holds, isMF_persistent_law_holds,
      isUpdater_persistent_law_holds, isIdentityConverter_persistent_law_holds,
      isIdentityConverter_intro_law_holds, isConflicts_intro_law_holds, keysWithItemsB_iff_law_holds,
      isTV_isTVv_law_holds⟩ wp_newSchema wp_Convert wp_IsMissing wp_BuildUpdater wp_typedObj wp_apply
    wp_check wp_field wp_mapKey wp_containerPaths wp_concat wp_applied wp_updated wp_container
    wp_Apply wp_Update wp_ConflictsEquals

end proof

end k8s_smd
end EtcdGrove
end Perennial
