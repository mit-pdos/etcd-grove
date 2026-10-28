/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/Server__update.lean`.
Lean-first. The linearization point is the write under the lock, or the lookup under it for
an error or a write of nothing (the namespace check before the lock, which the request alone
decides, and a flagged failure fire the caller's update at whatever state).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Server__update
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Server__chance
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.copyObject
public import Spec.k8s_io.apimachinery.pkg.api.errors.NewInternalError
public import Spec.k8s_io.apimachinery.pkg.api.errors.NewBadRequest
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Server__nextRV
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Server__record
public import Spec.k8s_io.apimachinery.pkg.api.errors.NewNotFound
public import Spec.k8s_io.apimachinery.pkg.api.errors.NewConflict
public import Perennial.Spec.errors.New
public import Spec.k8s_io.apimachinery.pkg.api.errors.NewTimeoutError
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.WriteLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.MapLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.SrvLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.HistLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.ObjLemmas
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option maxHeartbeats 1600000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8sdaemonset

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : apimodel.Assumptions]

theorem updateErr_ns {r : Res} {ns : GoString} {o : Obj} {σ : St}
    (h : r.namespaced = true ∧ o.meta.Namespace' ≠ go!"" ∧ o.meta.Namespace' ≠ ns) :
    updateErr r ns o σ = some .badRequest := by
  unfold updateErr
  rw [if_pos h]

theorem updateErr_notFound {r : Res} {ns : GoString} {o : Obj} {σ : St}
    (h1 : ¬ (r.namespaced = true ∧ o.meta.Namespace' ≠ go!"" ∧ o.meta.Namespace' ≠ ns))
    (h : (σ.tbl r).objs !! reqKey r ns o.meta.Name' = none) :
    updateErr r ns o σ = some .notFound := by
  unfold updateErr
  rw [if_neg h1, h]

theorem updateErr_conflict {r : Res} {ns : GoString} {o st : Obj} {σ : St}
    (h1 : ¬ (r.namespaced = true ∧ o.meta.Namespace' ≠ go!"" ∧ o.meta.Namespace' ≠ ns))
    (hst : (σ.tbl r).objs !! reqKey r ns o.meta.Name' = some st)
    (h : ¬ o.meta.ResourceVersion' = go!"" ∧ ¬ o.meta.ResourceVersion' = st.meta.ResourceVersion') :
    updateErr r ns o σ = some .conflict := by
  unfold updateErr
  rw [if_neg h1, hst]
  simp only []
  rw [if_pos h]

theorem updateErr_none {r : Res} {ns : GoString} {o st : Obj} {σ : St}
    (h1 : ¬ (r.namespaced = true ∧ o.meta.Namespace' ≠ go!"" ∧ o.meta.Namespace' ≠ ns))
    (hst : (σ.tbl r).objs !! reqKey r ns o.meta.Name' = some st)
    (h : ¬ (¬ o.meta.ResourceVersion' = go!"" ∧ ¬ o.meta.ResourceVersion' = st.meta.ResourceVersion')) :
    updateErr r ns o σ = none := by
  unfold updateErr
  rw [if_neg h1, hst]
  simp only []
  rw [if_neg h]

/-- The object an update stores, as the calls build it. -/
theorem updateApply_fst (r : Res) (st o' : Obj) (σ : St) :
    (((((o'.modMeta (fun m => { m with Name' := st.meta.Name' })).modMeta
        (fun m => { m with Namespace' := st.meta.Namespace' })).modMeta
        (fun m => { m with UID' := st.meta.UID' })).modMeta
        (fun m => { m with CreationTimestamp' := st.meta.CreationTimestamp' })).modMeta
        (fun m => { m with ResourceVersion' := rvStr (σ.rev + 1) })) =
      (updateApply r st o' σ).1 := by
  unfold updateApply
  cases o' <;> rfl

theorem updateApply_snd (r : Res) (st o' : Obj) (σ : St) :
    (updateApply r st o' σ).2 =
      σ.write r ⟨.modified, σ.rev + 1, (updateApply r st o' σ).1⟩ σ.uids := by
  unfold updateApply St.write
  cases r <;> rfl

/-- A resource's update mutation, called. -/
theorem wp_mutate_call (r : Res) (mutR : Obj → Obj → Option Obj → Prop) (f : GoFunc)
    (x y : GoInterface) (st req : Obj) :
    {{ mutateOk (GF := GF) r mutR f ∗ objAt x (DFrac.own 1) st ∗ objAt y (DFrac.own 1) req ∗
        ⌜st.res = r ∧ req.res = r⌝ }}
      (App (App (Val #f) (Val #x)) (Val #y))
    {{ (z : GoInterface), RET #z; (⌜z = interface.nil ∧ mutR st req none⌝) ∨
        (∃ o, ⌜mutR st req (some o) ∧ o.res = r⌝ ∗ objAt z (DFrac.own 1) o) }} := by
  wp_start as ⟨#H, Hx, Hy, %h⟩
  iunfold mutateOk at H
  ihave #Hp := H $$ %x %y %st %req %h
  wp_apply Hp $$ [$Hx $Hy] as %z Hz
  iapply HΦ
  iexact Hz

/-- An object's interface value is not `nil`. -/
theorem objAt_nonnil (x : GoInterface) (q : DFrac) (o : Obj) :
    objAt (GF := GF) x q o ⊢ objAt x q o ∗ ⌜x ≠ interface.nil⌝ := by
  cases o <;>
  · unfold objAt
    iintro ⟨%l, %h, H⟩
    isplitl
    · iexists l
      iframe
      ipureintro; exact h
    · ipureintro
      subst h
      simp [interface.mkOk]

theorem Server.update.wp_proof
    (wp_chance : Server.chance.spec (GF := GF) (hG := hG))
    (wp_copyObject : copyObject.spec (GF := GF) (hG := hG))
    (wp_nextRV : Server.nextRV.spec (GF := GF) (hG := hG))
    (wp_record : Server.record.spec (GF := GF) (hG := hG))
    (wp_GetNamespace : metav1.ObjectMeta.GetNamespace.spec (GF := GF) (hG := hG))
    (wp_SetNamespace : metav1.ObjectMeta.SetNamespace.spec (GF := GF) (hG := hG))
    (wp_GetName : metav1.ObjectMeta.GetName.spec (GF := GF) (hG := hG))
    (wp_SetName : metav1.ObjectMeta.SetName.spec (GF := GF) (hG := hG))
    (wp_GetResourceVersion : metav1.ObjectMeta.GetResourceVersion.spec (GF := GF) (hG := hG))
    (wp_SetResourceVersion : metav1.ObjectMeta.SetResourceVersion.spec (GF := GF) (hG := hG))
    (wp_GetUID : metav1.ObjectMeta.GetUID.spec (GF := GF) (hG := hG))
    (wp_SetUID : metav1.ObjectMeta.SetUID.spec (GF := GF) (hG := hG))
    (wp_GetCreationTimestamp : metav1.ObjectMeta.GetCreationTimestamp.spec (GF := GF) (hG := hG))
    (wp_SetCreationTimestamp : metav1.ObjectMeta.SetCreationTimestamp.spec (GF := GF) (hG := hG))
    (wp_NewInternalError : apierrors.NewInternalError.spec (GF := GF) (hG := hG))
    (wp_NewBadRequest : apierrors.NewBadRequest.spec (GF := GF) (hG := hG))
    (wp_NewNotFound : apierrors.NewNotFound.spec (GF := GF) (hG := hG))
    (wp_NewConflict : apierrors.NewConflict.spec (GF := GF) (hG := hG))
    (wp_NewTimeoutError : apierrors.NewTimeoutError.spec (GF := GF) (hG := hG))
    (wp_New : errors.New.spec (GF := GF) (hG := hG))
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    Server.update.spec (GF := GF) (hG := hG) := by
  intro _ s γ cfg r t ns inp dq o mutF mutR admin
  wp_start as ⟨#Hs, #Ht, #Hmut, Hinp, %Hres⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Herrs : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors $$ []
  · iPkgInit
  ihave #Hstrconv : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  ihave #Hinit : (github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.apimodelInit :
    IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨⟨%eS, #HeS⟩, ⟨%eR, #HeR⟩, ⟨%sA, #HeA⟩⟩
  ihave #Hsrv := Hs
  iunfold isServer at Hs
  icases Hs with ⟨%L, #Hs⟩
  ihave %Htl := srvFixed_tableOf s γ L cfg r t $$ [$Hs $Ht]
  subst Htl
  ihave ⟨#Hfx, -⟩ := srvFixed_tbl s γ L cfg r $$ Hs
  iunfold tableFixed at Hfx
  icases Hfx with ⟨#Hres, #Hnsd, #Hobjs, #Hemp, -⟩
  ihave #Hfixed := Hs
  iNamed Hs
  iNamed Hcfg
  wp_auto
  wp_apply wp_chance $$ [$Hsrv] as %b %Hb
  cases b
  · wp_auto
    wp_apply wp_copyObject $$ Hinp as %y ⟨Hinp, Hy⟩
    cases hnsr : r.namespaced
    · (try simp only [Bool.false_eq_true, ↓reduceIte])
      (try wp_auto)
      have hc1 : ¬ (r.namespaced = true ∧ o.meta.Namespace' ≠ go!"" ∧ o.meta.Namespace' ≠ ns) := by
        simp [hnsr]
      have hrk : reqKey r ns o.meta.Name' = mkKey go!"" o.meta.Name' := by simp [reqKey, hnsr]
      wp_apply wp_Lock $$ [$Hmu] as ⟨Hown, Hinv⟩
      iunfold lockInv at Hinv
      icases Hinv with ⟨%σ0, %H, Hlk, Hhist, %Hok, Hws⟩
      iNamed Hlk
      have hwf := histOk_last_wf Hok
      icases tablesLocked_acc L σ0 r $$ Htbls with ⟨Ht0, Hback⟩
      iunfold tableLocked at Ht0
      icases Ht0 with ⟨%M, %sl, %cs, HM, Hrel, Hlog, Hsl, Hcap, Hcs⟩
      wp_apply (objAt_GetName wp_GetName y _) $$ Hy as Hy
      (try wp_auto)
      (try dsimp only)
      wp_apply (wp_map_lookup2 k8s_io.apimachinery.pkg.types.NamespacedName.ty apimodel.object.ty
        (L.tbl r).objs M (mkKey go!"" o.meta.Name') (DFrac.own 1)) $$ HM as HM
      ihave %hd := objsRel_dom M (σ0.tbl r).objs (mkKey go!"" o.meta.Name') $$ Hrel
      cases hk : M !! mkKey go!"" o.meta.Name' with
      | none =>
        have hnone : (σ0.tbl r).objs !! reqKey r ns o.meta.Name' = none := by
          rw [hrk]
          cases h' : (σ0.tbl r).objs !! mkKey go!"" o.meta.Name' with
          | none => rfl
          | some _ => simp [h', hk] at hd
        (try simp only [Option.isSome_none, Option.getD_none])
        (try wp_auto)
        imod (au_write_noop γ H σ0 (.error .notFound : Except ApiErr (Bool × Obj))
            (UpdateOut cfg.FailWrites' admin r ns o mutR) (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗ Φ (PairV #x #err)))
            (Or.inr (Or.inl ⟨.notFound, updateErr_notFound hc1 hnone, rfl, rfl⟩))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
        (try wp_auto)
        wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback HM Hrel Hlog Hsl Hcap Hcs]
        · iunfold lockInv
          iexists σ0, H
          iframe
          iunfold srvLocked
          iframe
          ihave Htb := Hback $$ %σ0 %(fun _ _ => rfl) [HM Hrel Hlog Hsl Hcap Hcs]
          · iunfold tableLocked
            iexists M, sl, cs
            iframe
          iframe
          ipureintro; exact ⟨Huidlt, Hok⟩
        (try wp_auto)
        wp_apply (objAt_GetName wp_GetName y _) $$ Hy as Hy
        (try wp_auto)
        wp_apply +noauto wp_NewNotFound as %p ⟨%st, Hp, %Hst⟩
        ipersist Hp
        (try wp_auto)
        iapply HΦ
        iframe
        unfold writeRetI
        isplitr
        · ipureintro; rfl
        unfold errIs
        iexists p, st
        iframe #
        ipureintro
        exact ⟨rfl, Hst.2.1, Hst.2.2⟩
      | some x =>
        icases objsRel_lookup M (σ0.tbl r).objs _ x hk $$ Hrel with ⟨%st, %hst0, Hx, Hrelb⟩
        have hst : (σ0.tbl r).objs !! reqKey r ns o.meta.Name' = some st := by rw [hrk]; exact hst0
        obtain ⟨hstres, hstuid⟩ := wf_stored hwf hst0
        (try simp only [Option.isSome_some, Option.getD_some])
        (try wp_auto)
        wp_apply (objAt_GetResourceVersion wp_GetResourceVersion y _) $$ Hy as Hy
        wp_if_destruct
        · -- no version given: no conflict
          have hnc : ¬ (¬ o.meta.ResourceVersion' = go!"" ∧
              ¬ o.meta.ResourceVersion' = st.meta.ResourceVersion') := fun h => h.1 Hif
          wp_apply wp_copyObject $$ Hx as %x' ⟨Hx, Hx'⟩
          (try wp_auto)
          wp_apply (wp_mutate_call r mutR mutF x' y st o) $$ [$Hmut $Hx' $Hy] as %z Hz
          · ipureintro; exact ⟨hstres, Hres⟩
          icases Hz with (⟨%hz, %hmr⟩ | ⟨%o', ⟨%hmo, %ho'res⟩, Hz⟩)
          · -- nothing to write
            subst hz
            (try wp_auto)
            wp_apply wp_copyObject $$ Hx as %w ⟨Hx, Hw⟩
            ihave Hrel := Hrelb $$ Hx
            imod (au_write_noop γ H σ0 (.ok (false, st) : Except ApiErr (Bool × Obj))
                (UpdateOut cfg.FailWrites' admin r ns o mutR) (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗ Φ (PairV #x #err)))
                (Or.inr (Or.inr ⟨updateErr_none hc1 hst hnc, st, hst, Or.inl ⟨hmr, rfl, rfl⟩⟩))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
            (try wp_auto)
            wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback HM Hrel Hlog Hsl Hcap Hcs]
            · iunfold lockInv
              iexists σ0, H
              iframe
              iunfold srvLocked
              iframe
              ihave Htb := Hback $$ %σ0 %(fun _ _ => rfl) [HM Hrel Hlog Hsl Hcap Hcs]
              · iunfold tableLocked
                iexists M, sl, cs
                iframe
              iframe
              ipureintro; exact ⟨Huidlt, Hok⟩
            (try wp_auto)
            iapply HΦ
            iframe
            unfold writeRetI
            ileft
            iframe
            ipureintro; rfl
          · -- a write
            ihave ⟨Hz, %hznil⟩ := objAt_nonnil z _ o' $$ Hz
            cases z with
            | nil => exact absurd rfl hznil
            | ok zi =>
            (try wp_auto)
            wp_apply (objAt_GetName wp_GetName x _) $$ Hx as Hx
            wp_apply (objAt_SetName wp_SetName (GoInterface.ok zi) _ _) $$ Hz as Hz
            wp_apply (objAt_GetNamespace wp_GetNamespace x _) $$ Hx as Hx
            wp_apply (objAt_SetNamespace wp_SetNamespace (GoInterface.ok zi) _ _) $$ Hz as Hz
            wp_apply (objAt_GetUID wp_GetUID x _) $$ Hx as Hx
            wp_apply (objAt_SetUID wp_SetUID (GoInterface.ok zi) _ _) $$ Hz as Hz
            wp_apply (objAt_GetCreationTimestamp wp_GetCreationTimestamp x _) $$ Hx as Hx
            wp_apply (objAt_SetCreationTimestamp wp_SetCreationTimestamp (GoInterface.ok zi) _ _) $$ Hz as Hz
            ihave Hrel := Hrelb $$ Hx
            (try wp_auto)
            wp_apply (wp_nextRV s L.rvs σ0.rev) $$ [$Hstrconv $Hrev $Hrvs $Hrvsm $Hrc] as ⟨Hrev, Hrvsm, Hrc, %hno⟩
            · ipureintro; exact ⟨hwf.rev_pos, Hbound⟩
            (try wp_auto)
            wp_apply (objAt_SetResourceVersion wp_SetResourceVersion (GoInterface.ok zi) _ _) $$ Hz as Hz
            rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl] at hno
            rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl]
            ihave Hz := objAt_cast (updateApply_fst r st o' σ0) $$ Hz
            have hres3 : (updateApply r st o' σ0).1.res = r := by rw [← updateApply_fst]; simp [ho'res]
            have hRV3 : (updateApply r st o' σ0).1.meta.ResourceVersion' = rvStr (σ0.rev + 1) := by
              rw [← updateApply_fst]; simp
            have huid3 : (updateApply r st o' σ0).1.meta.UID' = st.meta.UID' := by
              rw [← updateApply_fst]; simp
            have hsnd := updateApply_snd r st o' σ0
            have hUE := updateErr_none hc1 hst hnc
            generalize hO3 : (updateApply r st o' σ0).1 = o3 at hres3 hRV3 huid3 hsnd ⊢
            (try wp_auto)
            rw [show k8s_io.apimachinery.pkg.watch.Modified = #(EvTy.modified.str) from rfl]
            wp_apply (wp_record s γ L cfg r (σ0.tbl r) .modified (σ0.rev + 1) (GoInterface.ok zi) o3) $$
              [$Hfixed HM Hrel Hlog Hsl Hcap Hcs $Hz] as ⟨Hz, Htb⟩
            · iunfold tableLocked
              iexists M, sl, cs
              iframe
            wp_apply wp_copyObject $$ Hz as %w ⟨Hz, Hw⟩
            ihave Htb := Htb $$ Hz
            obtain ⟨n, hn1, hn2, hn3⟩ := hstuid
            have hw := St.write_wf σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids hwf rfl hno hres3 hRV3
              (Nat.le_refl _) (by have := Huidlt; omega) ⟨n, hn1, hn2, by rw [huid3, hn3]⟩
            imod (au_write γ H σ0 (σ0.write r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids) (.ok (true, o3))
                (UpdateOut cfg.FailWrites' admin r ns o mutR)
                (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗
                  Φ (PairV #x #err))) Hok hw.2 hw.1
                (Or.inr (Or.inr ⟨hUE, st, hst, Or.inr ⟨o', hmo, hsnd, by rw [hO3]⟩⟩)))
              $$ [$Hhist $HΦ] with ⟨Hhist, %Hok', HΦ⟩
            (try wp_auto)
            wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback Htb]
            · iunfold lockInv
              inext
              iexists σ0.write r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids, H ++ [σ0]
              iframe Hhist Hws
              isplitl [Hrev Huids Hrvsm Hrc Hback Htb]
              · iunfold srvLocked
                simp only [named]
                isplitl [Hrev]
                · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids).rev = σ0.rev + 1 from rfl]
                  iexact Hrev
                isplitl [Huids]
                · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids).uids = σ0.uids from rfl]
                  iexact Huids
                isplitl [Hrvsm]
                · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno]
                  iexact Hrvsm
                isplitl [Hback Htb]
                · iapply Hback
                  · ipureintro
                    intro r' hr'
                    rw [St.write_tbl, if_neg hr']
                  rw [St.write_tbl, if_pos rfl]
                  iexact Htb
                isplitl [Hrc]
                · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno,
                    Nat.add_sub_cancel]
                  iexact Hrc
                ipureintro
                exact hw.1.uids_lt
              ipureintro; exact Hok'
            (try wp_auto)
            wp_apply wp_chance $$ [$Hsrv] as %b2 %Hb2
            cases b2
            · (try wp_auto)
              iapply HΦ
              iframe
              unfold writeRetI
              ileft
              iframe
              ipureintro; rfl
            · (try wp_auto)
              wp_apply +noauto wp_NewTimeoutError as %p ⟨%st', %dv, Hp, -, %Hst⟩
              ipersist Hp
              (try wp_auto)
              iapply HΦ
              iframe
              unfold writeRetI
              iright
              isplitr
              · ipureintro; exact ⟨rfl, Hb2 rfl, rfl⟩
              unfold errIs
              iexists p, st'
              iframe #
              ipureintro
              exact ⟨rfl, Hst.2.1, Hst.2.2⟩
        · have hrv1 := Hif
          wp_apply (objAt_GetResourceVersion wp_GetResourceVersion y _) $$ Hy as Hy
          wp_apply (objAt_GetResourceVersion wp_GetResourceVersion x _) $$ Hx as Hx
          by_cases Hrv2 : o.meta.ResourceVersion' = st.meta.ResourceVersion'
          rotate_left
          · -- a version other than the stored one
            simp only [decide_eq_false Hrv2, Bool.not_false, ↓reduceIte]
            (try wp_auto)
            ihave Hrel := Hrelb $$ Hx
            imod (au_write_noop γ H σ0 (.error .conflict : Except ApiErr (Bool × Obj))
                (UpdateOut cfg.FailWrites' admin r ns o mutR) (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗ Φ (PairV #x #err)))
                (Or.inr (Or.inl ⟨.conflict, updateErr_conflict hc1 hst ⟨hrv1, Hrv2⟩, rfl, rfl⟩))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
            (try wp_auto)
            wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback HM Hrel Hlog Hsl Hcap Hcs]
            · iunfold lockInv
              iexists σ0, H
              iframe
              iunfold srvLocked
              iframe
              ihave Htb := Hback $$ %σ0 %(fun _ _ => rfl) [HM Hrel Hlog Hsl Hcap Hcs]
              · iunfold tableLocked
                iexists M, sl, cs
                iframe
              iframe
              ipureintro; exact ⟨Huidlt, Hok⟩
            (try wp_auto)
            wp_apply (objAt_GetName wp_GetName y _) $$ Hy as Hy
            (try wp_auto)
            wp_apply wp_New as %e -
            (try wp_auto)
            wp_apply +noauto wp_NewConflict as %p ⟨%st, Hp, %Hst⟩
            ipersist Hp
            (try wp_auto)
            iapply HΦ
            iframe
            unfold writeRetI
            isplitr
            · ipureintro; rfl
            unfold errIs
            iexists p, st
            iframe #
            ipureintro
            exact ⟨rfl, Hst.2.1, Hst.2.2⟩
          · simp only [decide_eq_true Hrv2, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            (try wp_auto)
            have hnc : ¬ (¬ o.meta.ResourceVersion' = go!"" ∧
                ¬ o.meta.ResourceVersion' = st.meta.ResourceVersion') := fun h => h.2 Hrv2
            wp_apply wp_copyObject $$ Hx as %x' ⟨Hx, Hx'⟩
            (try wp_auto)
            wp_apply (wp_mutate_call r mutR mutF x' y st o) $$ [$Hmut $Hx' $Hy] as %z Hz
            · ipureintro; exact ⟨hstres, Hres⟩
            icases Hz with (⟨%hz, %hmr⟩ | ⟨%o', ⟨%hmo, %ho'res⟩, Hz⟩)
            · -- nothing to write
              subst hz
              (try wp_auto)
              wp_apply wp_copyObject $$ Hx as %w ⟨Hx, Hw⟩
              ihave Hrel := Hrelb $$ Hx
              imod (au_write_noop γ H σ0 (.ok (false, st) : Except ApiErr (Bool × Obj))
                  (UpdateOut cfg.FailWrites' admin r ns o mutR) (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗ Φ (PairV #x #err)))
                  (Or.inr (Or.inr ⟨updateErr_none hc1 hst hnc, st, hst, Or.inl ⟨hmr, rfl, rfl⟩⟩))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
              (try wp_auto)
              wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback HM Hrel Hlog Hsl Hcap Hcs]
              · iunfold lockInv
                iexists σ0, H
                iframe
                iunfold srvLocked
                iframe
                ihave Htb := Hback $$ %σ0 %(fun _ _ => rfl) [HM Hrel Hlog Hsl Hcap Hcs]
                · iunfold tableLocked
                  iexists M, sl, cs
                  iframe
                iframe
                ipureintro; exact ⟨Huidlt, Hok⟩
              (try wp_auto)
              iapply HΦ
              iframe
              unfold writeRetI
              ileft
              iframe
              ipureintro; rfl
            · -- a write
              ihave ⟨Hz, %hznil⟩ := objAt_nonnil z _ o' $$ Hz
              cases z with
              | nil => exact absurd rfl hznil
              | ok zi =>
              (try wp_auto)
              wp_apply (objAt_GetName wp_GetName x _) $$ Hx as Hx
              wp_apply (objAt_SetName wp_SetName (GoInterface.ok zi) _ _) $$ Hz as Hz
              wp_apply (objAt_GetNamespace wp_GetNamespace x _) $$ Hx as Hx
              wp_apply (objAt_SetNamespace wp_SetNamespace (GoInterface.ok zi) _ _) $$ Hz as Hz
              wp_apply (objAt_GetUID wp_GetUID x _) $$ Hx as Hx
              wp_apply (objAt_SetUID wp_SetUID (GoInterface.ok zi) _ _) $$ Hz as Hz
              wp_apply (objAt_GetCreationTimestamp wp_GetCreationTimestamp x _) $$ Hx as Hx
              wp_apply (objAt_SetCreationTimestamp wp_SetCreationTimestamp (GoInterface.ok zi) _ _) $$ Hz as Hz
              ihave Hrel := Hrelb $$ Hx
              (try wp_auto)
              wp_apply (wp_nextRV s L.rvs σ0.rev) $$ [$Hstrconv $Hrev $Hrvs $Hrvsm $Hrc] as ⟨Hrev, Hrvsm, Hrc, %hno⟩
              · ipureintro; exact ⟨hwf.rev_pos, Hbound⟩
              (try wp_auto)
              wp_apply (objAt_SetResourceVersion wp_SetResourceVersion (GoInterface.ok zi) _ _) $$ Hz as Hz
              rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl] at hno
              rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl]
              ihave Hz := objAt_cast (updateApply_fst r st o' σ0) $$ Hz
              have hres3 : (updateApply r st o' σ0).1.res = r := by rw [← updateApply_fst]; simp [ho'res]
              have hRV3 : (updateApply r st o' σ0).1.meta.ResourceVersion' = rvStr (σ0.rev + 1) := by
                rw [← updateApply_fst]; simp
              have huid3 : (updateApply r st o' σ0).1.meta.UID' = st.meta.UID' := by
                rw [← updateApply_fst]; simp
              have hsnd := updateApply_snd r st o' σ0
              have hUE := updateErr_none hc1 hst hnc
              generalize hO3 : (updateApply r st o' σ0).1 = o3 at hres3 hRV3 huid3 hsnd ⊢
              (try wp_auto)
              rw [show k8s_io.apimachinery.pkg.watch.Modified = #(EvTy.modified.str) from rfl]
              wp_apply (wp_record s γ L cfg r (σ0.tbl r) .modified (σ0.rev + 1) (GoInterface.ok zi) o3) $$
                [$Hfixed HM Hrel Hlog Hsl Hcap Hcs $Hz] as ⟨Hz, Htb⟩
              · iunfold tableLocked
                iexists M, sl, cs
                iframe
              wp_apply wp_copyObject $$ Hz as %w ⟨Hz, Hw⟩
              ihave Htb := Htb $$ Hz
              obtain ⟨n, hn1, hn2, hn3⟩ := hstuid
              have hw := St.write_wf σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids hwf rfl hno hres3 hRV3
                (Nat.le_refl _) (by have := Huidlt; omega) ⟨n, hn1, hn2, by rw [huid3, hn3]⟩
              imod (au_write γ H σ0 (σ0.write r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids) (.ok (true, o3))
                  (UpdateOut cfg.FailWrites' admin r ns o mutR)
                  (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗
                    Φ (PairV #x #err))) Hok hw.2 hw.1
                  (Or.inr (Or.inr ⟨hUE, st, hst, Or.inr ⟨o', hmo, hsnd, by rw [hO3]⟩⟩)))
                $$ [$Hhist $HΦ] with ⟨Hhist, %Hok', HΦ⟩
              (try wp_auto)
              wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback Htb]
              · iunfold lockInv
                inext
                iexists σ0.write r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids, H ++ [σ0]
                iframe Hhist Hws
                isplitl [Hrev Huids Hrvsm Hrc Hback Htb]
                · iunfold srvLocked
                  simp only [named]
                  isplitl [Hrev]
                  · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids).rev = σ0.rev + 1 from rfl]
                    iexact Hrev
                  isplitl [Huids]
                  · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids).uids = σ0.uids from rfl]
                    iexact Huids
                  isplitl [Hrvsm]
                  · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno]
                    iexact Hrvsm
                  isplitl [Hback Htb]
                  · iapply Hback
                    · ipureintro
                      intro r' hr'
                      rw [St.write_tbl, if_neg hr']
                    rw [St.write_tbl, if_pos rfl]
                    iexact Htb
                  isplitl [Hrc]
                  · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno,
                      Nat.add_sub_cancel]
                    iexact Hrc
                  ipureintro
                  exact hw.1.uids_lt
                ipureintro; exact Hok'
              (try wp_auto)
              wp_apply wp_chance $$ [$Hsrv] as %b2 %Hb2
              cases b2
              · (try wp_auto)
                iapply HΦ
                iframe
                unfold writeRetI
                ileft
                iframe
                ipureintro; rfl
              · (try wp_auto)
                wp_apply +noauto wp_NewTimeoutError as %p ⟨%st', %dv, Hp, -, %Hst⟩
                ipersist Hp
                (try wp_auto)
                iapply HΦ
                iframe
                unfold writeRetI
                iright
                isplitr
                · ipureintro; exact ⟨rfl, Hb2 rfl, rfl⟩
                unfold errIs
                iexists p, st'
                iframe #
                ipureintro
                exact ⟨rfl, Hst.2.1, Hst.2.2⟩
    · (try wp_auto)
      wp_apply (objAt_GetNamespace wp_GetNamespace y o) $$ Hy as Hy
      have hrk : reqKey r ns o.meta.Name' = mkKey ns o.meta.Name' := by simp [reqKey, hnsr]
      wp_if_destruct
      · have hc1 : ¬ (r.namespaced = true ∧ o.meta.Namespace' ≠ go!"" ∧ o.meta.Namespace' ≠ ns) := by
          simp [Hif]
        wp_apply wp_Lock $$ [$Hmu] as ⟨Hown, Hinv⟩
        iunfold lockInv at Hinv
        icases Hinv with ⟨%σ0, %H, Hlk, Hhist, %Hok, Hws⟩
        iNamed Hlk
        have hwf := histOk_last_wf Hok
        icases tablesLocked_acc L σ0 r $$ Htbls with ⟨Ht0, Hback⟩
        iunfold tableLocked at Ht0
        icases Ht0 with ⟨%M, %sl, %cs, HM, Hrel, Hlog, Hsl, Hcap, Hcs⟩
        wp_apply (objAt_GetName wp_GetName y _) $$ Hy as Hy
        (try wp_auto)
        (try dsimp only)
        wp_apply (wp_map_lookup2 k8s_io.apimachinery.pkg.types.NamespacedName.ty apimodel.object.ty
          (L.tbl r).objs M (mkKey ns o.meta.Name') (DFrac.own 1)) $$ HM as HM
        ihave %hd := objsRel_dom M (σ0.tbl r).objs (mkKey ns o.meta.Name') $$ Hrel
        cases hk : M !! mkKey ns o.meta.Name' with
        | none =>
          have hnone : (σ0.tbl r).objs !! reqKey r ns o.meta.Name' = none := by
            rw [hrk]
            cases h' : (σ0.tbl r).objs !! mkKey ns o.meta.Name' with
            | none => rfl
            | some _ => simp [h', hk] at hd
          (try simp only [Option.isSome_none, Option.getD_none])
          (try wp_auto)
          imod (au_write_noop γ H σ0 (.error .notFound : Except ApiErr (Bool × Obj))
              (UpdateOut cfg.FailWrites' admin r ns o mutR) (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗ Φ (PairV #x #err)))
              (Or.inr (Or.inl ⟨.notFound, updateErr_notFound hc1 hnone, rfl, rfl⟩))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
          (try wp_auto)
          wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback HM Hrel Hlog Hsl Hcap Hcs]
          · iunfold lockInv
            iexists σ0, H
            iframe
            iunfold srvLocked
            iframe
            ihave Htb := Hback $$ %σ0 %(fun _ _ => rfl) [HM Hrel Hlog Hsl Hcap Hcs]
            · iunfold tableLocked
              iexists M, sl, cs
              iframe
            iframe
            ipureintro; exact ⟨Huidlt, Hok⟩
          (try wp_auto)
          wp_apply (objAt_GetName wp_GetName y _) $$ Hy as Hy
          (try wp_auto)
          wp_apply +noauto wp_NewNotFound as %p ⟨%st, Hp, %Hst⟩
          ipersist Hp
          (try wp_auto)
          iapply HΦ
          iframe
          unfold writeRetI
          isplitr
          · ipureintro; rfl
          unfold errIs
          iexists p, st
          iframe #
          ipureintro
          exact ⟨rfl, Hst.2.1, Hst.2.2⟩
        | some x =>
          icases objsRel_lookup M (σ0.tbl r).objs _ x hk $$ Hrel with ⟨%st, %hst0, Hx, Hrelb⟩
          have hst : (σ0.tbl r).objs !! reqKey r ns o.meta.Name' = some st := by rw [hrk]; exact hst0
          obtain ⟨hstres, hstuid⟩ := wf_stored hwf hst0
          (try simp only [Option.isSome_some, Option.getD_some])
          (try wp_auto)
          wp_apply (objAt_GetResourceVersion wp_GetResourceVersion y _) $$ Hy as Hy
          wp_if_destruct
          · -- no version given: no conflict
            have hnc : ¬ (¬ o.meta.ResourceVersion' = go!"" ∧
                ¬ o.meta.ResourceVersion' = st.meta.ResourceVersion') := fun h => h.1 Hif
            wp_apply wp_copyObject $$ Hx as %x' ⟨Hx, Hx'⟩
            (try wp_auto)
            wp_apply (wp_mutate_call r mutR mutF x' y st o) $$ [$Hmut $Hx' $Hy] as %z Hz
            · ipureintro; exact ⟨hstres, Hres⟩
            icases Hz with (⟨%hz, %hmr⟩ | ⟨%o', ⟨%hmo, %ho'res⟩, Hz⟩)
            · -- nothing to write
              subst hz
              (try wp_auto)
              wp_apply wp_copyObject $$ Hx as %w ⟨Hx, Hw⟩
              ihave Hrel := Hrelb $$ Hx
              imod (au_write_noop γ H σ0 (.ok (false, st) : Except ApiErr (Bool × Obj))
                  (UpdateOut cfg.FailWrites' admin r ns o mutR) (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗ Φ (PairV #x #err)))
                  (Or.inr (Or.inr ⟨updateErr_none hc1 hst hnc, st, hst, Or.inl ⟨hmr, rfl, rfl⟩⟩))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
              (try wp_auto)
              wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback HM Hrel Hlog Hsl Hcap Hcs]
              · iunfold lockInv
                iexists σ0, H
                iframe
                iunfold srvLocked
                iframe
                ihave Htb := Hback $$ %σ0 %(fun _ _ => rfl) [HM Hrel Hlog Hsl Hcap Hcs]
                · iunfold tableLocked
                  iexists M, sl, cs
                  iframe
                iframe
                ipureintro; exact ⟨Huidlt, Hok⟩
              (try wp_auto)
              iapply HΦ
              iframe
              unfold writeRetI
              ileft
              iframe
              ipureintro; rfl
            · -- a write
              ihave ⟨Hz, %hznil⟩ := objAt_nonnil z _ o' $$ Hz
              cases z with
              | nil => exact absurd rfl hznil
              | ok zi =>
              (try wp_auto)
              wp_apply (objAt_GetName wp_GetName x _) $$ Hx as Hx
              wp_apply (objAt_SetName wp_SetName (GoInterface.ok zi) _ _) $$ Hz as Hz
              wp_apply (objAt_GetNamespace wp_GetNamespace x _) $$ Hx as Hx
              wp_apply (objAt_SetNamespace wp_SetNamespace (GoInterface.ok zi) _ _) $$ Hz as Hz
              wp_apply (objAt_GetUID wp_GetUID x _) $$ Hx as Hx
              wp_apply (objAt_SetUID wp_SetUID (GoInterface.ok zi) _ _) $$ Hz as Hz
              wp_apply (objAt_GetCreationTimestamp wp_GetCreationTimestamp x _) $$ Hx as Hx
              wp_apply (objAt_SetCreationTimestamp wp_SetCreationTimestamp (GoInterface.ok zi) _ _) $$ Hz as Hz
              ihave Hrel := Hrelb $$ Hx
              (try wp_auto)
              wp_apply (wp_nextRV s L.rvs σ0.rev) $$ [$Hstrconv $Hrev $Hrvs $Hrvsm $Hrc] as ⟨Hrev, Hrvsm, Hrc, %hno⟩
              · ipureintro; exact ⟨hwf.rev_pos, Hbound⟩
              (try wp_auto)
              wp_apply (objAt_SetResourceVersion wp_SetResourceVersion (GoInterface.ok zi) _ _) $$ Hz as Hz
              rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl] at hno
              rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl]
              ihave Hz := objAt_cast (updateApply_fst r st o' σ0) $$ Hz
              have hres3 : (updateApply r st o' σ0).1.res = r := by rw [← updateApply_fst]; simp [ho'res]
              have hRV3 : (updateApply r st o' σ0).1.meta.ResourceVersion' = rvStr (σ0.rev + 1) := by
                rw [← updateApply_fst]; simp
              have huid3 : (updateApply r st o' σ0).1.meta.UID' = st.meta.UID' := by
                rw [← updateApply_fst]; simp
              have hsnd := updateApply_snd r st o' σ0
              have hUE := updateErr_none hc1 hst hnc
              generalize hO3 : (updateApply r st o' σ0).1 = o3 at hres3 hRV3 huid3 hsnd ⊢
              (try wp_auto)
              rw [show k8s_io.apimachinery.pkg.watch.Modified = #(EvTy.modified.str) from rfl]
              wp_apply (wp_record s γ L cfg r (σ0.tbl r) .modified (σ0.rev + 1) (GoInterface.ok zi) o3) $$
                [$Hfixed HM Hrel Hlog Hsl Hcap Hcs $Hz] as ⟨Hz, Htb⟩
              · iunfold tableLocked
                iexists M, sl, cs
                iframe
              wp_apply wp_copyObject $$ Hz as %w ⟨Hz, Hw⟩
              ihave Htb := Htb $$ Hz
              obtain ⟨n, hn1, hn2, hn3⟩ := hstuid
              have hw := St.write_wf σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids hwf rfl hno hres3 hRV3
                (Nat.le_refl _) (by have := Huidlt; omega) ⟨n, hn1, hn2, by rw [huid3, hn3]⟩
              imod (au_write γ H σ0 (σ0.write r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids) (.ok (true, o3))
                  (UpdateOut cfg.FailWrites' admin r ns o mutR)
                  (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗
                    Φ (PairV #x #err))) Hok hw.2 hw.1
                  (Or.inr (Or.inr ⟨hUE, st, hst, Or.inr ⟨o', hmo, hsnd, by rw [hO3]⟩⟩)))
                $$ [$Hhist $HΦ] with ⟨Hhist, %Hok', HΦ⟩
              (try wp_auto)
              wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback Htb]
              · iunfold lockInv
                inext
                iexists σ0.write r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids, H ++ [σ0]
                iframe Hhist Hws
                isplitl [Hrev Huids Hrvsm Hrc Hback Htb]
                · iunfold srvLocked
                  simp only [named]
                  isplitl [Hrev]
                  · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids).rev = σ0.rev + 1 from rfl]
                    iexact Hrev
                  isplitl [Huids]
                  · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids).uids = σ0.uids from rfl]
                    iexact Huids
                  isplitl [Hrvsm]
                  · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno]
                    iexact Hrvsm
                  isplitl [Hback Htb]
                  · iapply Hback
                    · ipureintro
                      intro r' hr'
                      rw [St.write_tbl, if_neg hr']
                    rw [St.write_tbl, if_pos rfl]
                    iexact Htb
                  isplitl [Hrc]
                  · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno,
                      Nat.add_sub_cancel]
                    iexact Hrc
                  ipureintro
                  exact hw.1.uids_lt
                ipureintro; exact Hok'
              (try wp_auto)
              wp_apply wp_chance $$ [$Hsrv] as %b2 %Hb2
              cases b2
              · (try wp_auto)
                iapply HΦ
                iframe
                unfold writeRetI
                ileft
                iframe
                ipureintro; rfl
              · (try wp_auto)
                wp_apply +noauto wp_NewTimeoutError as %p ⟨%st', %dv, Hp, -, %Hst⟩
                ipersist Hp
                (try wp_auto)
                iapply HΦ
                iframe
                unfold writeRetI
                iright
                isplitr
                · ipureintro; exact ⟨rfl, Hb2 rfl, rfl⟩
                unfold errIs
                iexists p, st'
                iframe #
                ipureintro
                exact ⟨rfl, Hst.2.1, Hst.2.2⟩
          · have hrv1 := Hif
            wp_apply (objAt_GetResourceVersion wp_GetResourceVersion y _) $$ Hy as Hy
            wp_apply (objAt_GetResourceVersion wp_GetResourceVersion x _) $$ Hx as Hx
            by_cases Hrv2 : o.meta.ResourceVersion' = st.meta.ResourceVersion'
            rotate_left
            · -- a version other than the stored one
              simp only [decide_eq_false Hrv2, Bool.not_false, ↓reduceIte]
              (try wp_auto)
              ihave Hrel := Hrelb $$ Hx
              imod (au_write_noop γ H σ0 (.error .conflict : Except ApiErr (Bool × Obj))
                  (UpdateOut cfg.FailWrites' admin r ns o mutR) (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗ Φ (PairV #x #err)))
                  (Or.inr (Or.inl ⟨.conflict, updateErr_conflict hc1 hst ⟨hrv1, Hrv2⟩, rfl, rfl⟩))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
              (try wp_auto)
              wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback HM Hrel Hlog Hsl Hcap Hcs]
              · iunfold lockInv
                iexists σ0, H
                iframe
                iunfold srvLocked
                iframe
                ihave Htb := Hback $$ %σ0 %(fun _ _ => rfl) [HM Hrel Hlog Hsl Hcap Hcs]
                · iunfold tableLocked
                  iexists M, sl, cs
                  iframe
                iframe
                ipureintro; exact ⟨Huidlt, Hok⟩
              (try wp_auto)
              wp_apply (objAt_GetName wp_GetName y _) $$ Hy as Hy
              (try wp_auto)
              wp_apply wp_New as %e -
              (try wp_auto)
              wp_apply +noauto wp_NewConflict as %p ⟨%st, Hp, %Hst⟩
              ipersist Hp
              (try wp_auto)
              iapply HΦ
              iframe
              unfold writeRetI
              isplitr
              · ipureintro; rfl
              unfold errIs
              iexists p, st
              iframe #
              ipureintro
              exact ⟨rfl, Hst.2.1, Hst.2.2⟩
            · simp only [decide_eq_true Hrv2, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              (try wp_auto)
              have hnc : ¬ (¬ o.meta.ResourceVersion' = go!"" ∧
                  ¬ o.meta.ResourceVersion' = st.meta.ResourceVersion') := fun h => h.2 Hrv2
              wp_apply wp_copyObject $$ Hx as %x' ⟨Hx, Hx'⟩
              (try wp_auto)
              wp_apply (wp_mutate_call r mutR mutF x' y st o) $$ [$Hmut $Hx' $Hy] as %z Hz
              · ipureintro; exact ⟨hstres, Hres⟩
              icases Hz with (⟨%hz, %hmr⟩ | ⟨%o', ⟨%hmo, %ho'res⟩, Hz⟩)
              · -- nothing to write
                subst hz
                (try wp_auto)
                wp_apply wp_copyObject $$ Hx as %w ⟨Hx, Hw⟩
                ihave Hrel := Hrelb $$ Hx
                imod (au_write_noop γ H σ0 (.ok (false, st) : Except ApiErr (Bool × Obj))
                    (UpdateOut cfg.FailWrites' admin r ns o mutR) (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗ Φ (PairV #x #err)))
                    (Or.inr (Or.inr ⟨updateErr_none hc1 hst hnc, st, hst, Or.inl ⟨hmr, rfl, rfl⟩⟩))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
                (try wp_auto)
                wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback HM Hrel Hlog Hsl Hcap Hcs]
                · iunfold lockInv
                  iexists σ0, H
                  iframe
                  iunfold srvLocked
                  iframe
                  ihave Htb := Hback $$ %σ0 %(fun _ _ => rfl) [HM Hrel Hlog Hsl Hcap Hcs]
                  · iunfold tableLocked
                    iexists M, sl, cs
                    iframe
                  iframe
                  ipureintro; exact ⟨Huidlt, Hok⟩
                (try wp_auto)
                iapply HΦ
                iframe
                unfold writeRetI
                ileft
                iframe
                ipureintro; rfl
              · -- a write
                ihave ⟨Hz, %hznil⟩ := objAt_nonnil z _ o' $$ Hz
                cases z with
                | nil => exact absurd rfl hznil
                | ok zi =>
                (try wp_auto)
                wp_apply (objAt_GetName wp_GetName x _) $$ Hx as Hx
                wp_apply (objAt_SetName wp_SetName (GoInterface.ok zi) _ _) $$ Hz as Hz
                wp_apply (objAt_GetNamespace wp_GetNamespace x _) $$ Hx as Hx
                wp_apply (objAt_SetNamespace wp_SetNamespace (GoInterface.ok zi) _ _) $$ Hz as Hz
                wp_apply (objAt_GetUID wp_GetUID x _) $$ Hx as Hx
                wp_apply (objAt_SetUID wp_SetUID (GoInterface.ok zi) _ _) $$ Hz as Hz
                wp_apply (objAt_GetCreationTimestamp wp_GetCreationTimestamp x _) $$ Hx as Hx
                wp_apply (objAt_SetCreationTimestamp wp_SetCreationTimestamp (GoInterface.ok zi) _ _) $$ Hz as Hz
                ihave Hrel := Hrelb $$ Hx
                (try wp_auto)
                wp_apply (wp_nextRV s L.rvs σ0.rev) $$ [$Hstrconv $Hrev $Hrvs $Hrvsm $Hrc] as ⟨Hrev, Hrvsm, Hrc, %hno⟩
                · ipureintro; exact ⟨hwf.rev_pos, Hbound⟩
                (try wp_auto)
                wp_apply (objAt_SetResourceVersion wp_SetResourceVersion (GoInterface.ok zi) _ _) $$ Hz as Hz
                rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl] at hno
                rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl]
                ihave Hz := objAt_cast (updateApply_fst r st o' σ0) $$ Hz
                have hres3 : (updateApply r st o' σ0).1.res = r := by rw [← updateApply_fst]; simp [ho'res]
                have hRV3 : (updateApply r st o' σ0).1.meta.ResourceVersion' = rvStr (σ0.rev + 1) := by
                  rw [← updateApply_fst]; simp
                have huid3 : (updateApply r st o' σ0).1.meta.UID' = st.meta.UID' := by
                  rw [← updateApply_fst]; simp
                have hsnd := updateApply_snd r st o' σ0
                have hUE := updateErr_none hc1 hst hnc
                generalize hO3 : (updateApply r st o' σ0).1 = o3 at hres3 hRV3 huid3 hsnd ⊢
                (try wp_auto)
                rw [show k8s_io.apimachinery.pkg.watch.Modified = #(EvTy.modified.str) from rfl]
                wp_apply (wp_record s γ L cfg r (σ0.tbl r) .modified (σ0.rev + 1) (GoInterface.ok zi) o3) $$
                  [$Hfixed HM Hrel Hlog Hsl Hcap Hcs $Hz] as ⟨Hz, Htb⟩
                · iunfold tableLocked
                  iexists M, sl, cs
                  iframe
                wp_apply wp_copyObject $$ Hz as %w ⟨Hz, Hw⟩
                ihave Htb := Htb $$ Hz
                obtain ⟨n, hn1, hn2, hn3⟩ := hstuid
                have hw := St.write_wf σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids hwf rfl hno hres3 hRV3
                  (Nat.le_refl _) (by have := Huidlt; omega) ⟨n, hn1, hn2, by rw [huid3, hn3]⟩
                imod (au_write γ H σ0 (σ0.write r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids) (.ok (true, o3))
                    (UpdateOut cfg.FailWrites' admin r ns o mutR)
                    (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗
                      Φ (PairV #x #err))) Hok hw.2 hw.1
                    (Or.inr (Or.inr ⟨hUE, st, hst, Or.inr ⟨o', hmo, hsnd, by rw [hO3]⟩⟩)))
                  $$ [$Hhist $HΦ] with ⟨Hhist, %Hok', HΦ⟩
                (try wp_auto)
                wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback Htb]
                · iunfold lockInv
                  inext
                  iexists σ0.write r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids, H ++ [σ0]
                  iframe Hhist Hws
                  isplitl [Hrev Huids Hrvsm Hrc Hback Htb]
                  · iunfold srvLocked
                    simp only [named]
                    isplitl [Hrev]
                    · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids).rev = σ0.rev + 1 from rfl]
                      iexact Hrev
                    isplitl [Huids]
                    · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids).uids = σ0.uids from rfl]
                      iexact Huids
                    isplitl [Hrvsm]
                    · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno]
                      iexact Hrvsm
                    isplitl [Hback Htb]
                    · iapply Hback
                      · ipureintro
                        intro r' hr'
                        rw [St.write_tbl, if_neg hr']
                      rw [St.write_tbl, if_pos rfl]
                      iexact Htb
                    isplitl [Hrc]
                    · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno,
                        Nat.add_sub_cancel]
                      iexact Hrc
                    ipureintro
                    exact hw.1.uids_lt
                  ipureintro; exact Hok'
                (try wp_auto)
                wp_apply wp_chance $$ [$Hsrv] as %b2 %Hb2
                cases b2
                · (try wp_auto)
                  iapply HΦ
                  iframe
                  unfold writeRetI
                  ileft
                  iframe
                  ipureintro; rfl
                · (try wp_auto)
                  wp_apply +noauto wp_NewTimeoutError as %p ⟨%st', %dv, Hp, -, %Hst⟩
                  ipersist Hp
                  (try wp_auto)
                  iapply HΦ
                  iframe
                  unfold writeRetI
                  iright
                  isplitr
                  · ipureintro; exact ⟨rfl, Hb2 rfl, rfl⟩
                  unfold errIs
                  iexists p, st'
                  iframe #
                  ipureintro
                  exact ⟨rfl, Hst.2.1, Hst.2.2⟩
      · have hnsE := Hif
        wp_apply (objAt_GetNamespace wp_GetNamespace y o) $$ Hy as Hy
        by_cases Hns2 : o.meta.Namespace' = ns
        rotate_left
        · -- another namespace than the request's
          simp only [decide_eq_false Hns2, Bool.not_false, ↓reduceIte]
          (try wp_auto)
          imod (au_fail γ (.error .badRequest : Except ApiErr (Bool × Obj)) (UpdateOut cfg.FailWrites' admin r ns o mutR)
              (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗ Φ (PairV #x #err)))
              (fun σ => Or.inr (Or.inl ⟨.badRequest, updateErr_ns ⟨hnsr, hnsE, Hns2⟩, rfl, rfl⟩))) $$ HΦ with ⟨%σ, HΦ⟩
          (try wp_auto)
          wp_apply +noauto wp_NewBadRequest as %p ⟨%st, Hp, %Hst⟩
          ipersist Hp
          (try wp_auto)
          iapply HΦ
          iframe
          unfold writeRetI
          isplitr
          · ipureintro; rfl
          unfold errIs
          iexists p, st
          iframe #
          ipureintro
          exact ⟨rfl, Hst.2.1, Hst.2.2⟩
        · -- the request's namespace
          simp only [decide_eq_true Hns2, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          (try wp_auto)
          have hc1 : ¬ (r.namespaced = true ∧ o.meta.Namespace' ≠ go!"" ∧ o.meta.Namespace' ≠ ns) := by
            simp [Hns2]
          wp_apply wp_Lock $$ [$Hmu] as ⟨Hown, Hinv⟩
          iunfold lockInv at Hinv
          icases Hinv with ⟨%σ0, %H, Hlk, Hhist, %Hok, Hws⟩
          iNamed Hlk
          have hwf := histOk_last_wf Hok
          icases tablesLocked_acc L σ0 r $$ Htbls with ⟨Ht0, Hback⟩
          iunfold tableLocked at Ht0
          icases Ht0 with ⟨%M, %sl, %cs, HM, Hrel, Hlog, Hsl, Hcap, Hcs⟩
          wp_apply (objAt_GetName wp_GetName y _) $$ Hy as Hy
          (try wp_auto)
          (try dsimp only)
          wp_apply (wp_map_lookup2 k8s_io.apimachinery.pkg.types.NamespacedName.ty apimodel.object.ty
            (L.tbl r).objs M (mkKey ns o.meta.Name') (DFrac.own 1)) $$ HM as HM
          ihave %hd := objsRel_dom M (σ0.tbl r).objs (mkKey ns o.meta.Name') $$ Hrel
          cases hk : M !! mkKey ns o.meta.Name' with
          | none =>
            have hnone : (σ0.tbl r).objs !! reqKey r ns o.meta.Name' = none := by
              rw [hrk]
              cases h' : (σ0.tbl r).objs !! mkKey ns o.meta.Name' with
              | none => rfl
              | some _ => simp [h', hk] at hd
            (try simp only [Option.isSome_none, Option.getD_none])
            (try wp_auto)
            imod (au_write_noop γ H σ0 (.error .notFound : Except ApiErr (Bool × Obj))
                (UpdateOut cfg.FailWrites' admin r ns o mutR) (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗ Φ (PairV #x #err)))
                (Or.inr (Or.inl ⟨.notFound, updateErr_notFound hc1 hnone, rfl, rfl⟩))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
            (try wp_auto)
            wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback HM Hrel Hlog Hsl Hcap Hcs]
            · iunfold lockInv
              iexists σ0, H
              iframe
              iunfold srvLocked
              iframe
              ihave Htb := Hback $$ %σ0 %(fun _ _ => rfl) [HM Hrel Hlog Hsl Hcap Hcs]
              · iunfold tableLocked
                iexists M, sl, cs
                iframe
              iframe
              ipureintro; exact ⟨Huidlt, Hok⟩
            (try wp_auto)
            wp_apply (objAt_GetName wp_GetName y _) $$ Hy as Hy
            (try wp_auto)
            wp_apply +noauto wp_NewNotFound as %p ⟨%st, Hp, %Hst⟩
            ipersist Hp
            (try wp_auto)
            iapply HΦ
            iframe
            unfold writeRetI
            isplitr
            · ipureintro; rfl
            unfold errIs
            iexists p, st
            iframe #
            ipureintro
            exact ⟨rfl, Hst.2.1, Hst.2.2⟩
          | some x =>
            icases objsRel_lookup M (σ0.tbl r).objs _ x hk $$ Hrel with ⟨%st, %hst0, Hx, Hrelb⟩
            have hst : (σ0.tbl r).objs !! reqKey r ns o.meta.Name' = some st := by rw [hrk]; exact hst0
            obtain ⟨hstres, hstuid⟩ := wf_stored hwf hst0
            (try simp only [Option.isSome_some, Option.getD_some])
            (try wp_auto)
            wp_apply (objAt_GetResourceVersion wp_GetResourceVersion y _) $$ Hy as Hy
            wp_if_destruct
            · -- no version given: no conflict
              have hnc : ¬ (¬ o.meta.ResourceVersion' = go!"" ∧
                  ¬ o.meta.ResourceVersion' = st.meta.ResourceVersion') := fun h => h.1 Hif
              wp_apply wp_copyObject $$ Hx as %x' ⟨Hx, Hx'⟩
              (try wp_auto)
              wp_apply (wp_mutate_call r mutR mutF x' y st o) $$ [$Hmut $Hx' $Hy] as %z Hz
              · ipureintro; exact ⟨hstres, Hres⟩
              icases Hz with (⟨%hz, %hmr⟩ | ⟨%o', ⟨%hmo, %ho'res⟩, Hz⟩)
              · -- nothing to write
                subst hz
                (try wp_auto)
                wp_apply wp_copyObject $$ Hx as %w ⟨Hx, Hw⟩
                ihave Hrel := Hrelb $$ Hx
                imod (au_write_noop γ H σ0 (.ok (false, st) : Except ApiErr (Bool × Obj))
                    (UpdateOut cfg.FailWrites' admin r ns o mutR) (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗ Φ (PairV #x #err)))
                    (Or.inr (Or.inr ⟨updateErr_none hc1 hst hnc, st, hst, Or.inl ⟨hmr, rfl, rfl⟩⟩))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
                (try wp_auto)
                wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback HM Hrel Hlog Hsl Hcap Hcs]
                · iunfold lockInv
                  iexists σ0, H
                  iframe
                  iunfold srvLocked
                  iframe
                  ihave Htb := Hback $$ %σ0 %(fun _ _ => rfl) [HM Hrel Hlog Hsl Hcap Hcs]
                  · iunfold tableLocked
                    iexists M, sl, cs
                    iframe
                  iframe
                  ipureintro; exact ⟨Huidlt, Hok⟩
                (try wp_auto)
                iapply HΦ
                iframe
                unfold writeRetI
                ileft
                iframe
                ipureintro; rfl
              · -- a write
                ihave ⟨Hz, %hznil⟩ := objAt_nonnil z _ o' $$ Hz
                cases z with
                | nil => exact absurd rfl hznil
                | ok zi =>
                (try wp_auto)
                wp_apply (objAt_GetName wp_GetName x _) $$ Hx as Hx
                wp_apply (objAt_SetName wp_SetName (GoInterface.ok zi) _ _) $$ Hz as Hz
                wp_apply (objAt_GetNamespace wp_GetNamespace x _) $$ Hx as Hx
                wp_apply (objAt_SetNamespace wp_SetNamespace (GoInterface.ok zi) _ _) $$ Hz as Hz
                wp_apply (objAt_GetUID wp_GetUID x _) $$ Hx as Hx
                wp_apply (objAt_SetUID wp_SetUID (GoInterface.ok zi) _ _) $$ Hz as Hz
                wp_apply (objAt_GetCreationTimestamp wp_GetCreationTimestamp x _) $$ Hx as Hx
                wp_apply (objAt_SetCreationTimestamp wp_SetCreationTimestamp (GoInterface.ok zi) _ _) $$ Hz as Hz
                ihave Hrel := Hrelb $$ Hx
                (try wp_auto)
                wp_apply (wp_nextRV s L.rvs σ0.rev) $$ [$Hstrconv $Hrev $Hrvs $Hrvsm $Hrc] as ⟨Hrev, Hrvsm, Hrc, %hno⟩
                · ipureintro; exact ⟨hwf.rev_pos, Hbound⟩
                (try wp_auto)
                wp_apply (objAt_SetResourceVersion wp_SetResourceVersion (GoInterface.ok zi) _ _) $$ Hz as Hz
                rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl] at hno
                rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl]
                ihave Hz := objAt_cast (updateApply_fst r st o' σ0) $$ Hz
                have hres3 : (updateApply r st o' σ0).1.res = r := by rw [← updateApply_fst]; simp [ho'res]
                have hRV3 : (updateApply r st o' σ0).1.meta.ResourceVersion' = rvStr (σ0.rev + 1) := by
                  rw [← updateApply_fst]; simp
                have huid3 : (updateApply r st o' σ0).1.meta.UID' = st.meta.UID' := by
                  rw [← updateApply_fst]; simp
                have hsnd := updateApply_snd r st o' σ0
                have hUE := updateErr_none hc1 hst hnc
                generalize hO3 : (updateApply r st o' σ0).1 = o3 at hres3 hRV3 huid3 hsnd ⊢
                (try wp_auto)
                rw [show k8s_io.apimachinery.pkg.watch.Modified = #(EvTy.modified.str) from rfl]
                wp_apply (wp_record s γ L cfg r (σ0.tbl r) .modified (σ0.rev + 1) (GoInterface.ok zi) o3) $$
                  [$Hfixed HM Hrel Hlog Hsl Hcap Hcs $Hz] as ⟨Hz, Htb⟩
                · iunfold tableLocked
                  iexists M, sl, cs
                  iframe
                wp_apply wp_copyObject $$ Hz as %w ⟨Hz, Hw⟩
                ihave Htb := Htb $$ Hz
                obtain ⟨n, hn1, hn2, hn3⟩ := hstuid
                have hw := St.write_wf σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids hwf rfl hno hres3 hRV3
                  (Nat.le_refl _) (by have := Huidlt; omega) ⟨n, hn1, hn2, by rw [huid3, hn3]⟩
                imod (au_write γ H σ0 (σ0.write r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids) (.ok (true, o3))
                    (UpdateOut cfg.FailWrites' admin r ns o mutR)
                    (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗
                      Φ (PairV #x #err))) Hok hw.2 hw.1
                    (Or.inr (Or.inr ⟨hUE, st, hst, Or.inr ⟨o', hmo, hsnd, by rw [hO3]⟩⟩)))
                  $$ [$Hhist $HΦ] with ⟨Hhist, %Hok', HΦ⟩
                (try wp_auto)
                wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback Htb]
                · iunfold lockInv
                  inext
                  iexists σ0.write r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids, H ++ [σ0]
                  iframe Hhist Hws
                  isplitl [Hrev Huids Hrvsm Hrc Hback Htb]
                  · iunfold srvLocked
                    simp only [named]
                    isplitl [Hrev]
                    · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids).rev = σ0.rev + 1 from rfl]
                      iexact Hrev
                    isplitl [Huids]
                    · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids).uids = σ0.uids from rfl]
                      iexact Huids
                    isplitl [Hrvsm]
                    · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno]
                      iexact Hrvsm
                    isplitl [Hback Htb]
                    · iapply Hback
                      · ipureintro
                        intro r' hr'
                        rw [St.write_tbl, if_neg hr']
                      rw [St.write_tbl, if_pos rfl]
                      iexact Htb
                    isplitl [Hrc]
                    · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno,
                        Nat.add_sub_cancel]
                      iexact Hrc
                    ipureintro
                    exact hw.1.uids_lt
                  ipureintro; exact Hok'
                (try wp_auto)
                wp_apply wp_chance $$ [$Hsrv] as %b2 %Hb2
                cases b2
                · (try wp_auto)
                  iapply HΦ
                  iframe
                  unfold writeRetI
                  ileft
                  iframe
                  ipureintro; rfl
                · (try wp_auto)
                  wp_apply +noauto wp_NewTimeoutError as %p ⟨%st', %dv, Hp, -, %Hst⟩
                  ipersist Hp
                  (try wp_auto)
                  iapply HΦ
                  iframe
                  unfold writeRetI
                  iright
                  isplitr
                  · ipureintro; exact ⟨rfl, Hb2 rfl, rfl⟩
                  unfold errIs
                  iexists p, st'
                  iframe #
                  ipureintro
                  exact ⟨rfl, Hst.2.1, Hst.2.2⟩
            · have hrv1 := Hif
              wp_apply (objAt_GetResourceVersion wp_GetResourceVersion y _) $$ Hy as Hy
              wp_apply (objAt_GetResourceVersion wp_GetResourceVersion x _) $$ Hx as Hx
              by_cases Hrv2 : o.meta.ResourceVersion' = st.meta.ResourceVersion'
              rotate_left
              · -- a version other than the stored one
                simp only [decide_eq_false Hrv2, Bool.not_false, ↓reduceIte]
                (try wp_auto)
                ihave Hrel := Hrelb $$ Hx
                imod (au_write_noop γ H σ0 (.error .conflict : Except ApiErr (Bool × Obj))
                    (UpdateOut cfg.FailWrites' admin r ns o mutR) (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗ Φ (PairV #x #err)))
                    (Or.inr (Or.inl ⟨.conflict, updateErr_conflict hc1 hst ⟨hrv1, Hrv2⟩, rfl, rfl⟩))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
                (try wp_auto)
                wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback HM Hrel Hlog Hsl Hcap Hcs]
                · iunfold lockInv
                  iexists σ0, H
                  iframe
                  iunfold srvLocked
                  iframe
                  ihave Htb := Hback $$ %σ0 %(fun _ _ => rfl) [HM Hrel Hlog Hsl Hcap Hcs]
                  · iunfold tableLocked
                    iexists M, sl, cs
                    iframe
                  iframe
                  ipureintro; exact ⟨Huidlt, Hok⟩
                (try wp_auto)
                wp_apply (objAt_GetName wp_GetName y _) $$ Hy as Hy
                (try wp_auto)
                wp_apply wp_New as %e -
                (try wp_auto)
                wp_apply +noauto wp_NewConflict as %p ⟨%st, Hp, %Hst⟩
                ipersist Hp
                (try wp_auto)
                iapply HΦ
                iframe
                unfold writeRetI
                isplitr
                · ipureintro; rfl
                unfold errIs
                iexists p, st
                iframe #
                ipureintro
                exact ⟨rfl, Hst.2.1, Hst.2.2⟩
              · simp only [decide_eq_true Hrv2, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                (try wp_auto)
                have hnc : ¬ (¬ o.meta.ResourceVersion' = go!"" ∧
                    ¬ o.meta.ResourceVersion' = st.meta.ResourceVersion') := fun h => h.2 Hrv2
                wp_apply wp_copyObject $$ Hx as %x' ⟨Hx, Hx'⟩
                (try wp_auto)
                wp_apply (wp_mutate_call r mutR mutF x' y st o) $$ [$Hmut $Hx' $Hy] as %z Hz
                · ipureintro; exact ⟨hstres, Hres⟩
                icases Hz with (⟨%hz, %hmr⟩ | ⟨%o', ⟨%hmo, %ho'res⟩, Hz⟩)
                · -- nothing to write
                  subst hz
                  (try wp_auto)
                  wp_apply wp_copyObject $$ Hx as %w ⟨Hx, Hw⟩
                  ihave Hrel := Hrelb $$ Hx
                  imod (au_write_noop γ H σ0 (.ok (false, st) : Except ApiErr (Bool × Obj))
                      (UpdateOut cfg.FailWrites' admin r ns o mutR) (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗ Φ (PairV #x #err)))
                      (Or.inr (Or.inr ⟨updateErr_none hc1 hst hnc, st, hst, Or.inl ⟨hmr, rfl, rfl⟩⟩))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
                  (try wp_auto)
                  wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback HM Hrel Hlog Hsl Hcap Hcs]
                  · iunfold lockInv
                    iexists σ0, H
                    iframe
                    iunfold srvLocked
                    iframe
                    ihave Htb := Hback $$ %σ0 %(fun _ _ => rfl) [HM Hrel Hlog Hsl Hcap Hcs]
                    · iunfold tableLocked
                      iexists M, sl, cs
                      iframe
                    iframe
                    ipureintro; exact ⟨Huidlt, Hok⟩
                  (try wp_auto)
                  iapply HΦ
                  iframe
                  unfold writeRetI
                  ileft
                  iframe
                  ipureintro; rfl
                · -- a write
                  ihave ⟨Hz, %hznil⟩ := objAt_nonnil z _ o' $$ Hz
                  cases z with
                  | nil => exact absurd rfl hznil
                  | ok zi =>
                  (try wp_auto)
                  wp_apply (objAt_GetName wp_GetName x _) $$ Hx as Hx
                  wp_apply (objAt_SetName wp_SetName (GoInterface.ok zi) _ _) $$ Hz as Hz
                  wp_apply (objAt_GetNamespace wp_GetNamespace x _) $$ Hx as Hx
                  wp_apply (objAt_SetNamespace wp_SetNamespace (GoInterface.ok zi) _ _) $$ Hz as Hz
                  wp_apply (objAt_GetUID wp_GetUID x _) $$ Hx as Hx
                  wp_apply (objAt_SetUID wp_SetUID (GoInterface.ok zi) _ _) $$ Hz as Hz
                  wp_apply (objAt_GetCreationTimestamp wp_GetCreationTimestamp x _) $$ Hx as Hx
                  wp_apply (objAt_SetCreationTimestamp wp_SetCreationTimestamp (GoInterface.ok zi) _ _) $$ Hz as Hz
                  ihave Hrel := Hrelb $$ Hx
                  (try wp_auto)
                  wp_apply (wp_nextRV s L.rvs σ0.rev) $$ [$Hstrconv $Hrev $Hrvs $Hrvsm $Hrc] as ⟨Hrev, Hrvsm, Hrc, %hno⟩
                  · ipureintro; exact ⟨hwf.rev_pos, Hbound⟩
                  (try wp_auto)
                  wp_apply (objAt_SetResourceVersion wp_SetResourceVersion (GoInterface.ok zi) _ _) $$ Hz as Hz
                  rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl] at hno
                  rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl]
                  ihave Hz := objAt_cast (updateApply_fst r st o' σ0) $$ Hz
                  have hres3 : (updateApply r st o' σ0).1.res = r := by rw [← updateApply_fst]; simp [ho'res]
                  have hRV3 : (updateApply r st o' σ0).1.meta.ResourceVersion' = rvStr (σ0.rev + 1) := by
                    rw [← updateApply_fst]; simp
                  have huid3 : (updateApply r st o' σ0).1.meta.UID' = st.meta.UID' := by
                    rw [← updateApply_fst]; simp
                  have hsnd := updateApply_snd r st o' σ0
                  have hUE := updateErr_none hc1 hst hnc
                  generalize hO3 : (updateApply r st o' σ0).1 = o3 at hres3 hRV3 huid3 hsnd ⊢
                  (try wp_auto)
                  rw [show k8s_io.apimachinery.pkg.watch.Modified = #(EvTy.modified.str) from rfl]
                  wp_apply (wp_record s γ L cfg r (σ0.tbl r) .modified (σ0.rev + 1) (GoInterface.ok zi) o3) $$
                    [$Hfixed HM Hrel Hlog Hsl Hcap Hcs $Hz] as ⟨Hz, Htb⟩
                  · iunfold tableLocked
                    iexists M, sl, cs
                    iframe
                  wp_apply wp_copyObject $$ Hz as %w ⟨Hz, Hw⟩
                  ihave Htb := Htb $$ Hz
                  obtain ⟨n, hn1, hn2, hn3⟩ := hstuid
                  have hw := St.write_wf σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids hwf rfl hno hres3 hRV3
                    (Nat.le_refl _) (by have := Huidlt; omega) ⟨n, hn1, hn2, by rw [huid3, hn3]⟩
                  imod (au_write γ H σ0 (σ0.write r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids) (.ok (true, o3))
                      (UpdateOut cfg.FailWrites' admin r ns o mutR)
                      (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗
                        Φ (PairV #x #err))) Hok hw.2 hw.1
                      (Or.inr (Or.inr ⟨hUE, st, hst, Or.inr ⟨o', hmo, hsnd, by rw [hO3]⟩⟩)))
                    $$ [$Hhist $HΦ] with ⟨Hhist, %Hok', HΦ⟩
                  (try wp_auto)
                  wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback Htb]
                  · iunfold lockInv
                    inext
                    iexists σ0.write r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids, H ++ [σ0]
                    iframe Hhist Hws
                    isplitl [Hrev Huids Hrvsm Hrc Hback Htb]
                    · iunfold srvLocked
                      simp only [named]
                      isplitl [Hrev]
                      · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids).rev = σ0.rev + 1 from rfl]
                        iexact Hrev
                      isplitl [Huids]
                      · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids).uids = σ0.uids from rfl]
                        iexact Huids
                      isplitl [Hrvsm]
                      · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno]
                        iexact Hrvsm
                      isplitl [Hback Htb]
                      · iapply Hback
                        · ipureintro
                          intro r' hr'
                          rw [St.write_tbl, if_neg hr']
                        rw [St.write_tbl, if_pos rfl]
                        iexact Htb
                      isplitl [Hrc]
                      · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, o3⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno,
                          Nat.add_sub_cancel]
                        iexact Hrc
                      ipureintro
                      exact hw.1.uids_lt
                    ipureintro; exact Hok'
                  (try wp_auto)
                  wp_apply wp_chance $$ [$Hsrv] as %b2 %Hb2
                  cases b2
                  · (try wp_auto)
                    iapply HΦ
                    iframe
                    unfold writeRetI
                    ileft
                    iframe
                    ipureintro; rfl
                  · (try wp_auto)
                    wp_apply +noauto wp_NewTimeoutError as %p ⟨%st', %dv, Hp, -, %Hst⟩
                    ipersist Hp
                    (try wp_auto)
                    iapply HΦ
                    iframe
                    unfold writeRetI
                    iright
                    isplitr
                    · ipureintro; exact ⟨rfl, Hb2 rfl, rfl⟩
                    unfold errIs
                    iexists p, st'
                    iframe #
                    ipureintro
                    exact ⟨rfl, Hst.2.1, Hst.2.2⟩
  · -- a flagged failure
    imod (au_fail γ (.error .internal : Except ApiErr (Bool × Obj)) (UpdateOut cfg.FailWrites' admin r ns o mutR)
        (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗ Φ (PairV #x #err)))
        (fun σ => Or.inl ⟨Hb rfl, rfl, rfl⟩)) $$ HΦ with ⟨%σ, HΦ⟩
    (try wp_auto)
    wp_apply +noauto wp_NewInternalError as %p ⟨%st, Hp, %Hst⟩
    ipersist Hp
    (try wp_auto)
    iapply HΦ
    iframe
    unfold writeRetI
    isplitr
    · ipureintro; rfl
    unfold errIs
    iexists p, st
    iframe #
    ipureintro
    exact ⟨rfl, Hst.2.1, Hst.2.2⟩

end proof

end apimodel
end EtcdGrove
end Perennial
