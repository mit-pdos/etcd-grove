/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/Server__remove.lean`.
Lean-first. The linearization point is the write under the lock, or the lookup under it for
an error or an object already being deleted (a flagged failure fires the caller's update at
whatever state).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Server__remove
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Server__chance
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.copyObject
public import Spec.k8s_io.apimachinery.pkg.api.errors.NewInternalError
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Server__nextRV
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Server__record
public import Spec.k8s_io.apimachinery.pkg.api.errors.NewNotFound
public import Spec.k8s_io.apimachinery.pkg.api.errors.NewConflict
public import Perennial.Spec.errors.New
public import Spec.k8s_io.apimachinery.pkg.api.errors.NewTimeoutError
public import Spec.k8s_io.apimachinery.pkg.apis.meta.v1.Now
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : apimodel.Assumptions]

theorem deleteErr_notFound {r : Res} {ns name : GoString} {pre : Option kd.meta.Preconditions} {σ : St}
    (h : (σ.tbl r).objs !! reqKey r ns name = none) :
    deleteErr r ns name pre σ = some .notFound := by
  unfold deleteErr
  rw [h]

theorem deleteErr_nopre {r : Res} {ns name : GoString} {st : Obj} {σ : St}
    (h : (σ.tbl r).objs !! reqKey r ns name = some st) :
    deleteErr r ns name none σ = none := by
  unfold deleteErr
  rw [h]

/-- A precondition's failure, as the Go code tests it. -/
def preFails (p : kd.meta.Preconditions) (st : Obj) : Prop :=
  (∃ u, p.UID' = some u ∧ u ≠ st.meta.UID') ∨
    (∃ v, p.ResourceVersion' = some v ∧ v ≠ st.meta.ResourceVersion')

noncomputable instance (p : kd.meta.Preconditions) (st : Obj) : Decidable (preFails p st) :=
  Classical.propDecidable _

theorem deleteErr_conflict {r : Res} {ns name : GoString} {st : Obj} {σ : St}
    {p : kd.meta.Preconditions}
    (h : (σ.tbl r).objs !! reqKey r ns name = some st) (hf : preFails p st) :
    deleteErr r ns name (some p) σ = some .conflict := by
  unfold deleteErr
  rw [h]
  simp only []
  unfold preFails at hf
  rw [if_pos hf]

theorem deleteErr_pre_ok {r : Res} {ns name : GoString} {st : Obj} {σ : St}
    {p : kd.meta.Preconditions}
    (h : (σ.tbl r).objs !! reqKey r ns name = some st) (hf : ¬ preFails p st) :
    deleteErr r ns name (some p) σ = none := by
  unfold deleteErr
  rw [h]
  simp only []
  unfold preFails at hf
  rw [if_neg hf]

/-- A deep pointer of `DeleteOptions`' preconditions is `nil` exactly for none. -/
theorem delopts_pre_null [ApiDeps] (opts : k8s_io.apimachinery.pkg.apis.«meta».v1.DeleteOptions) (dq : DFrac)
    (dop : kd.meta.DeleteOptions) :
    kd.meta.DeleteOptions.own (GF := GF) opts dq dop ⊢ kd.meta.DeleteOptions.own opts dq dop ∗
      ⌜opts.Preconditions' = null ↔ dop.Preconditions' = none⌝ := by
  unfold kd.meta.DeleteOptions.own
  iintro ⟨TypeMeta, GracePeriodSeconds, Preconditions, OrphanDependents, PropagationPolicy, DryRun,
    IgnoreStoreReadErrorWithClusterBreakingPotential⟩
  icases ownPtrD_null _ _ _ _ $$ Preconditions with ⟨Preconditions, %h⟩
  isplitl
  · iframe
  · ipureintro; exact h

/-- **The preconditions, opened**: their struct in the heap, their fields' pointers. -/
theorem ownPtrD_some_eq {V E : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (inner : V → DFrac → E → IProp GF) (p : Loc) (dq : DFrac) (e : E) :
    ownPtrD inner p dq (some e) = iprop(∃ x : V, p ↦{dq} x ∗ inner x dq e) := rfl

theorem delopts_pre_open [ApiDeps] (opts : k8s_io.apimachinery.pkg.apis.«meta».v1.DeleteOptions) (dq : DFrac)
    (dop : kd.meta.DeleteOptions) (pre : kd.meta.Preconditions) (hpre : dop.Preconditions' = some pre) :
    kd.meta.DeleteOptions.own (GF := GF) opts dq dop ⊢
      ∃ pv : k8s_io.apimachinery.pkg.apis.«meta».v1.Preconditions,
        opts.Preconditions' ↦{dq} pv ∗
        (ownPtrD (V := k8s_io.apimachinery.pkg.types.UID) ownBaseD) pv.UID' dq pre.UID' ∗
        (ownPtrD (V := GoString) ownBaseD) pv.ResourceVersion' dq pre.ResourceVersion' ∗
        (opts.Preconditions' ↦{dq} pv -∗
          (ownPtrD (V := k8s_io.apimachinery.pkg.types.UID) ownBaseD) pv.UID' dq pre.UID' -∗
          (ownPtrD (V := GoString) ownBaseD) pv.ResourceVersion' dq pre.ResourceVersion' -∗
          kd.meta.DeleteOptions.own opts dq dop) := by
  unfold kd.meta.DeleteOptions.own
  iintro ⟨TypeMeta, GracePeriodSeconds, Preconditions, OrphanDependents, PropagationPolicy, DryRun,
    IgnoreStoreReadErrorWithClusterBreakingPotential⟩
  rw [hpre, ownPtrD_some_eq]
  icases Preconditions with ⟨%pv, Hp, Hpv⟩
  unfold kd.meta.Preconditions.own
  icases Hpv with ⟨HU, HR⟩
  iexists pv
  iframe
  iintro Hp HU HR
  iframe
  iexists pv
  iframe

/-- The object a delete keeps, as the calls build it. -/
theorem deleteApply_mod (r : Res) (st : Obj) (gps : Option w64) (σ : St)
    (t : k8s_io.apimachinery.pkg.apis.«meta».v1.Time)
    (h : 0 < sint.Z (graceOf r st gps) ∨ st.meta.Finalizers' ≠ []) :
    deleteApply r st gps σ t = σ.write r ⟨.modified, σ.rev + 1,
      ((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ.rev + 1) })).modMeta
        (fun m => { m with DeletionTimestamp' := some t })).modMeta
        (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st gps) })⟩ σ.uids := by
  unfold deleteApply St.write
  simp only [Obj.meta_modMeta]
  rw [if_pos h]
  cases r <;> cases st <;> rfl

theorem deleteApply_del (r : Res) (st : Obj) (gps : Option w64) (σ : St)
    (t : k8s_io.apimachinery.pkg.apis.«meta».v1.Time)
    (h : ¬ (0 < sint.Z (graceOf r st gps) ∨ st.meta.Finalizers' ≠ [])) :
    deleteApply r st gps σ t = σ.write r ⟨.deleted, σ.rev + 1,
      st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ.rev + 1) })⟩ σ.uids := by
  unfold deleteApply St.write
  simp only [Obj.meta_modMeta]
  rw [if_neg h]
  cases r <;> cases st <;> rfl

/-- A resource's grace function, called. -/
theorem wp_grace_call (r : Res) (f : GoFunc) (x : GoInterface) (st : Obj)
    (opts : k8s_io.apimachinery.pkg.apis.«meta».v1.DeleteOptions) (dq : DFrac) (dop : kd.meta.DeleteOptions) :
    {{ graceOk (GF := GF) r f ∗ objAt x (DFrac.own 1) st ∗ kd.meta.DeleteOptions.own opts dq dop ∗
        ⌜st.res = r⌝ }}
      (App (App (Val #f) (Val #x)) (Val #opts))
    {{ RET #(graceOf r st dop.GracePeriodSeconds'); objAt x (DFrac.own 1) st ∗
        kd.meta.DeleteOptions.own opts dq dop }} := by
  wp_start as ⟨#H, Hx, Ho, %h⟩
  iunfold graceOk at H
  ihave #Hp := H $$ %x %st %opts %dq %dop %h
  wp_apply Hp $$ [$Hx $Ho] as Hx
  iapply HΦ
  iexact Hx

theorem fin_ne {α : Type} {l : List α} {s : GoSlice} (h1 : l.length = sint.nat s.len)
    (h2 : sint.Z (W64 0) < sint.Z s.len) : l ≠ [] := by
  intro h
  subst h
  simp only [List.length_nil, sint.nat, sint.Z] at h1 h2 ⊢
  simp at h2
  omega

theorem fin_eq {α : Type} {l : List α} {s : GoSlice} (h1 : l.length = sint.nat s.len)
    (h0 : 0 ≤ sint.Z s.len) (h2 : ¬ sint.Z (W64 0) < sint.Z s.len) : l = [] := by
  apply List.eq_nil_of_length_eq_zero
  simp only [sint.nat, sint.Z] at h1 h0 h2 ⊢
  simp at h2 h0
  omega

theorem Server.remove.wp_proof
    (wp_chance : Server.chance.spec (GF := GF) (hG := hG))
    (wp_copyObject : copyObject.spec (GF := GF) (hG := hG))
    (wp_nextRV : Server.nextRV.spec (GF := GF) (hG := hG))
    (wp_record : Server.record.spec (GF := GF) (hG := hG))
    (wp_GetResourceVersion : metav1.ObjectMeta.GetResourceVersion.spec (GF := GF) (hG := hG))
    (wp_SetResourceVersion : metav1.ObjectMeta.SetResourceVersion.spec (GF := GF) (hG := hG))
    (wp_GetUID : metav1.ObjectMeta.GetUID.spec (GF := GF) (hG := hG))
    (wp_GetDeletionTimestamp : metav1.ObjectMeta.GetDeletionTimestamp.spec (GF := GF) (hG := hG))
    (wp_SetDeletionTimestamp : metav1.ObjectMeta.SetDeletionTimestamp.spec (GF := GF) (hG := hG))
    (wp_SetDeletionGracePeriodSeconds :
      metav1.ObjectMeta.SetDeletionGracePeriodSeconds.spec (GF := GF) (hG := hG))
    (wp_GetFinalizers : metav1.ObjectMeta.GetFinalizers.spec (GF := GF) (hG := hG))
    (wp_GetNamespace : metav1.ObjectMeta.GetNamespace.spec (GF := GF) (hG := hG))
    (wp_GetName : metav1.ObjectMeta.GetName.spec (GF := GF) (hG := hG))
    (wp_Now : metav1.Now.spec (GF := GF) (hG := hG))
    (wp_NewInternalError : apierrors.NewInternalError.spec (GF := GF) (hG := hG))
    (wp_NewNotFound : apierrors.NewNotFound.spec (GF := GF) (hG := hG))
    (wp_NewConflict : apierrors.NewConflict.spec (GF := GF) (hG := hG))
    (wp_NewTimeoutError : apierrors.NewTimeoutError.spec (GF := GF) (hG := hG))
    (wp_New : errors.New.spec (GF := GF) (hG := hG))
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    Server.remove.spec (GF := GF) (hG := hG) := by
  intro _ s γ cfg r t ns name opts dq dop grace admin
  wp_start as ⟨#Hs, #Ht, #Hgrace, Ho⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Herrs : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors $$ []
  · iPkgInit
  ihave #Hstrconv : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
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
  · (try wp_auto)
    cases hnsr : r.namespaced
    · have hrk : reqKey r ns name = mkKey go!"" name := by simp [reqKey, hnsr]
      wp_apply wp_Lock $$ [$Hmu] as ⟨Hown, Hinv⟩
      iunfold lockInv at Hinv
      icases Hinv with ⟨%σ0, %H, Hlk, Hhist, %Hok, Hws⟩
      iNamed Hlk
      have hwf := histOk_last_wf Hok
      icases tablesLocked_acc L σ0 r $$ Htbls with ⟨Ht0, Hback⟩
      iunfold tableLocked at Ht0
      icases Ht0 with ⟨%M, %sl, %cs, HM, Hrel, Hlog, Hsl, Hcap, Hcs⟩
      (try wp_auto)
      (try dsimp only)
      wp_apply (wp_map_lookup2 k8s_io.apimachinery.pkg.types.NamespacedName.ty apimodel.object.ty
        (L.tbl r).objs M (mkKey go!"" name) (DFrac.own 1)) $$ HM as HM
      ihave %hd := objsRel_dom M (σ0.tbl r).objs (mkKey go!"" name) $$ Hrel
      cases hk : M !! mkKey go!"" name with
      | none =>
        have hnone : (σ0.tbl r).objs !! reqKey r ns name = none := by
          rw [hrk]
          cases h' : (σ0.tbl r).objs !! mkKey go!"" name with
          | none => rfl
          | some _ => simp [h', hk] at hd
        (try simp only [Option.isSome_none, Option.getD_none])
        (try wp_auto)
        imod (au_write_noop γ H σ0 (.error .notFound : Except ApiErr Bool)
            (DeleteOut cfg.FailWrites' admin r ns name dop) (fun _ _ oc => iprop(∀ err, kd.meta.DeleteOptions.own opts dq dop ∗ deleteRet cfg.AmbiguousWrites' admin oc err -∗ Φ #err))
            (Or.inr (Or.inl ⟨.notFound, deleteErr_notFound hnone, rfl, rfl⟩))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
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
        wp_apply +noauto wp_NewNotFound as %p ⟨%st', Hp, %Hst⟩
        ipersist Hp
        (try wp_auto)
        iapply HΦ
        iframe
        unfold deleteRet
        unfold errIs
        iexists p, st'
        iframe #
        ipureintro
        exact ⟨rfl, Hst.2.1, Hst.2.2⟩
      | some x =>
        icases objsRel_lookup M (σ0.tbl r).objs _ x hk $$ Hrel with ⟨%st, %hst0, Hx, Hrelb⟩
        have hst : (σ0.tbl r).objs !! reqKey r ns name = some st := by rw [hrk]; exact hst0
        obtain ⟨hstres, hstuid⟩ := wf_stored hwf hst0
        (try simp only [Option.isSome_some, Option.getD_some])
        (try wp_auto)
        icases delopts_pre_null opts dq dop $$ Ho with ⟨Ho, %hpn⟩
        wp_if_destruct
        · have hpre : dop.Preconditions' = none := hpn.mp Hif
          have hDE : deleteErr r ns name dop.Preconditions' σ0 = none := by
            rw [hpre]; exact deleteErr_nopre hst
          wp_apply (objAt_GetDeletionTimestamp wp_GetDeletionTimestamp x _) $$ Hx as %dp ⟨Hx, %hdp⟩
          wp_if_destruct
          · -- not being deleted
            have hdts : st.meta.DeletionTimestamp' = none := hdp.mp rfl
            (try wp_auto)
            wp_apply (wp_grace_call r grace x st opts dq dop) $$ [$Hgrace $Hx $Ho] as ⟨Hx, Ho⟩
            · ipureintro; exact hstres
            (try wp_auto)
            wp_apply wp_copyObject $$ Hx as %y ⟨Hx, Hy⟩
            ihave Hrel := Hrelb $$ Hx
            (try wp_auto)
            wp_apply (wp_nextRV s L.rvs σ0.rev) $$ [$Hstrconv $Hrev $Hrvs $Hrvsm $Hrc] as ⟨Hrev, Hrvsm, Hrc, %hno⟩
            · ipureintro; exact ⟨hwf.rev_pos, Hbound⟩
            (try wp_auto)
            wp_apply (objAt_SetResourceVersion wp_SetResourceVersion y _ _) $$ Hy as Hy
            rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl] at hno
            rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl]
            (try wp_auto)
            wp_if_destruct
            · -- a positive grace period
              have hmod : 0 < sint.Z (graceOf r st dop.GracePeriodSeconds') ∨ st.meta.Finalizers' ≠ [] := Or.inl (by simpa using Hif)
              wp_apply wp_Now $$ [$Htime] as %tm -
              (try wp_auto)
              wp_apply (objAt_SetDeletionTimestamp wp_SetDeletionTimestamp y _ now_ptr tm) $$ [$Hy $now] as Hy
              (try wp_auto)
              wp_apply (objAt_SetDeletionGracePeriodSeconds wp_SetDeletionGracePeriodSeconds y _ period_ptr _) $$
                [$Hy $period] as Hy
              (try wp_auto)
              rw [show k8s_io.apimachinery.pkg.watch.Modified = #(EvTy.modified.str) from rfl]
              wp_apply (wp_record s γ L cfg r (σ0.tbl r) .modified (σ0.rev + 1) y ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))) $$
                [$Hfixed HM Hrel Hlog Hsl Hcap Hcs $Hy] as ⟨Hy, Htb⟩
              · iunfold tableLocked
                iexists M, sl, cs
                iframe
              ihave Htb := Htb $$ Hy
              obtain ⟨un, hn1, hn2, hn3⟩ := hstuid
              have hw := St.write_wf σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids hwf rfl hno
                (by simp [hstres]) (by simp) (Nat.le_refl _) (by have := Huidlt; omega)
                ⟨un, hn1, hn2, by simp [hn3]⟩
              imod (au_write γ H σ0 (σ0.write r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids) (.ok true) (DeleteOut cfg.FailWrites' admin r ns name dop) (fun _ _ oc => iprop(∀ err, kd.meta.DeleteOptions.own opts dq dop ∗ deleteRet cfg.AmbiguousWrites' admin oc err -∗ Φ #err)) Hok hw.2 hw.1
                  (Or.inr (Or.inr ⟨hDE, st, hst, Or.inr ⟨hdts, tm, (deleteApply_mod r st dop.GracePeriodSeconds' σ0 tm hmod), rfl⟩⟩)))
                $$ [$Hhist $HΦ] with ⟨Hhist, %Hok', HΦ⟩
              (try wp_auto)
              wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback Htb]
              · iunfold lockInv
                inext
                iexists σ0.write r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids, H ++ [σ0]
                iframe Hhist Hws
                isplitl [Hrev Huids Hrvsm Hrc Hback Htb]
                · iunfold srvLocked
                  simp only [named]
                  isplitl [Hrev]
                  · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl]
                    iexact Hrev
                  isplitl [Huids]
                  · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).uids = σ0.uids from rfl]
                    iexact Huids
                  isplitl [Hrvsm]
                  · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno]
                    iexact Hrvsm
                  isplitl [Hback Htb]
                  · iapply Hback
                    · ipureintro
                      intro r' hr'
                      rw [St.write_tbl, if_neg hr']
                    rw [St.write_tbl, if_pos rfl]
                    iexact Htb
                  isplitl [Hrc]
                  · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno,
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
                unfold deleteRet
                ileft
                ipureintro; rfl
              · (try wp_auto)
                wp_apply +noauto wp_NewTimeoutError as %p' ⟨%st', %dv, Hp', -, %Hst⟩
                ipersist Hp'
                (try wp_auto)
                iapply HΦ
                iframe
                unfold deleteRet
                iright
                isplitr
                · ipureintro; exact ⟨rfl, Hb2 rfl⟩
                unfold errIs
                iexists p', st'
                iframe #
                ipureintro
                exact ⟨rfl, Hst.2.1, Hst.2.2⟩
            · have hg := Hif
              wp_apply (objAt_GetFinalizers wp_GetFinalizers y _) $$ Hy as %fs ⟨Hy, %hfs⟩
              simp only [Obj.meta_modMeta] at hfs
              (try wp_auto)
              wp_if_destruct
              · -- finalizers
                have hmod : 0 < sint.Z (graceOf r st dop.GracePeriodSeconds') ∨ st.meta.Finalizers' ≠ [] := Or.inr (fin_ne hfs.1 Hif)
                wp_apply wp_Now $$ [$Htime] as %tm -
                (try wp_auto)
                wp_apply (objAt_SetDeletionTimestamp wp_SetDeletionTimestamp y _ now_ptr tm) $$ [$Hy $now] as Hy
                (try wp_auto)
                wp_apply (objAt_SetDeletionGracePeriodSeconds wp_SetDeletionGracePeriodSeconds y _ period_ptr _) $$
                  [$Hy $period] as Hy
                (try wp_auto)
                rw [show k8s_io.apimachinery.pkg.watch.Modified = #(EvTy.modified.str) from rfl]
                wp_apply (wp_record s γ L cfg r (σ0.tbl r) .modified (σ0.rev + 1) y ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))) $$
                  [$Hfixed HM Hrel Hlog Hsl Hcap Hcs $Hy] as ⟨Hy, Htb⟩
                · iunfold tableLocked
                  iexists M, sl, cs
                  iframe
                ihave Htb := Htb $$ Hy
                obtain ⟨un, hn1, hn2, hn3⟩ := hstuid
                have hw := St.write_wf σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids hwf rfl hno
                  (by simp [hstres]) (by simp) (Nat.le_refl _) (by have := Huidlt; omega)
                  ⟨un, hn1, hn2, by simp [hn3]⟩
                imod (au_write γ H σ0 (σ0.write r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids) (.ok true) (DeleteOut cfg.FailWrites' admin r ns name dop) (fun _ _ oc => iprop(∀ err, kd.meta.DeleteOptions.own opts dq dop ∗ deleteRet cfg.AmbiguousWrites' admin oc err -∗ Φ #err)) Hok hw.2 hw.1
                    (Or.inr (Or.inr ⟨hDE, st, hst, Or.inr ⟨hdts, tm, (deleteApply_mod r st dop.GracePeriodSeconds' σ0 tm hmod), rfl⟩⟩)))
                  $$ [$Hhist $HΦ] with ⟨Hhist, %Hok', HΦ⟩
                (try wp_auto)
                wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback Htb]
                · iunfold lockInv
                  inext
                  iexists σ0.write r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids, H ++ [σ0]
                  iframe Hhist Hws
                  isplitl [Hrev Huids Hrvsm Hrc Hback Htb]
                  · iunfold srvLocked
                    simp only [named]
                    isplitl [Hrev]
                    · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl]
                      iexact Hrev
                    isplitl [Huids]
                    · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).uids = σ0.uids from rfl]
                      iexact Huids
                    isplitl [Hrvsm]
                    · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno]
                      iexact Hrvsm
                    isplitl [Hback Htb]
                    · iapply Hback
                      · ipureintro
                        intro r' hr'
                        rw [St.write_tbl, if_neg hr']
                      rw [St.write_tbl, if_pos rfl]
                      iexact Htb
                    isplitl [Hrc]
                    · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno,
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
                  unfold deleteRet
                  ileft
                  ipureintro; rfl
                · (try wp_auto)
                  wp_apply +noauto wp_NewTimeoutError as %p' ⟨%st', %dv, Hp', -, %Hst⟩
                  ipersist Hp'
                  (try wp_auto)
                  iapply HΦ
                  iframe
                  unfold deleteRet
                  iright
                  isplitr
                  · ipureintro; exact ⟨rfl, Hb2 rfl⟩
                  unfold errIs
                  iexists p', st'
                  iframe #
                  ipureintro
                  exact ⟨rfl, Hst.2.1, Hst.2.2⟩
              · -- deleted at once
                have hdel : ¬ (0 < sint.Z (graceOf r st dop.GracePeriodSeconds') ∨ st.meta.Finalizers' ≠ []) := fun h => h.elim (fun h => hg (by simpa using h)) (fun h => h (fin_eq hfs.1 hfs.2 Hif))
                (try wp_auto)
                rw [show k8s_io.apimachinery.pkg.watch.Deleted = #(EvTy.deleted.str) from rfl]
                wp_apply (wp_record s γ L cfg r (σ0.tbl r) .deleted (σ0.rev + 1) y (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))) $$
                  [$Hfixed HM Hrel Hlog Hsl Hcap Hcs $Hy] as ⟨Hy, Htb⟩
                · iunfold tableLocked
                  iexists M, sl, cs
                  iframe
                ihave Htb := Htb $$ Hy
                obtain ⟨un, hn1, hn2, hn3⟩ := hstuid
                have hw := St.write_wf σ0 r ⟨.deleted, σ0.rev + 1, (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))⟩ σ0.uids hwf rfl hno
                  (by simp [hstres]) (by simp) (Nat.le_refl _) (by have := Huidlt; omega)
                  ⟨un, hn1, hn2, by simp [hn3]⟩
                imod (au_write γ H σ0 (σ0.write r ⟨.deleted, σ0.rev + 1, (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))⟩ σ0.uids) (.ok true) (DeleteOut cfg.FailWrites' admin r ns name dop) (fun _ _ oc => iprop(∀ err, kd.meta.DeleteOptions.own opts dq dop ∗ deleteRet cfg.AmbiguousWrites' admin oc err -∗ Φ #err)) Hok hw.2 hw.1
                    (Or.inr (Or.inr ⟨hDE, st, hst, Or.inr ⟨hdts, (zero_val k8s_io.apimachinery.pkg.apis.«meta».v1.Time), (deleteApply_del r st dop.GracePeriodSeconds' σ0 (zero_val k8s_io.apimachinery.pkg.apis.«meta».v1.Time) hdel), rfl⟩⟩)))
                  $$ [$Hhist $HΦ] with ⟨Hhist, %Hok', HΦ⟩
                (try wp_auto)
                wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback Htb]
                · iunfold lockInv
                  inext
                  iexists σ0.write r ⟨.deleted, σ0.rev + 1, (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))⟩ σ0.uids, H ++ [σ0]
                  iframe Hhist Hws
                  isplitl [Hrev Huids Hrvsm Hrc Hback Htb]
                  · iunfold srvLocked
                    simp only [named]
                    isplitl [Hrev]
                    · rw [show (St.write σ0 r ⟨.deleted, σ0.rev + 1, (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl]
                      iexact Hrev
                    isplitl [Huids]
                    · rw [show (St.write σ0 r ⟨.deleted, σ0.rev + 1, (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))⟩ σ0.uids).uids = σ0.uids from rfl]
                      iexact Huids
                    isplitl [Hrvsm]
                    · rw [show (St.write σ0 r ⟨.deleted, σ0.rev + 1, (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno]
                      iexact Hrvsm
                    isplitl [Hback Htb]
                    · iapply Hback
                      · ipureintro
                        intro r' hr'
                        rw [St.write_tbl, if_neg hr']
                      rw [St.write_tbl, if_pos rfl]
                      iexact Htb
                    isplitl [Hrc]
                    · rw [show (St.write σ0 r ⟨.deleted, σ0.rev + 1, (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno,
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
                  unfold deleteRet
                  ileft
                  ipureintro; rfl
                · (try wp_auto)
                  wp_apply +noauto wp_NewTimeoutError as %p' ⟨%st', %dv, Hp', -, %Hst⟩
                  ipersist Hp'
                  (try wp_auto)
                  iapply HΦ
                  iframe
                  unfold deleteRet
                  iright
                  isplitr
                  · ipureintro; exact ⟨rfl, Hb2 rfl⟩
                  unfold errIs
                  iexists p', st'
                  iframe #
                  ipureintro
                  exact ⟨rfl, Hst.2.1, Hst.2.2⟩
          · -- already being deleted: nothing changes
            have hdts : st.meta.DeletionTimestamp'.isSome := by
              cases h : st.meta.DeletionTimestamp' with
              | none => exact absurd (hdp.mpr h) Hif
              | some _ => rfl
            ihave Hrel := Hrelb $$ Hx
            imod (au_write_noop γ H σ0 (.ok false : Except ApiErr Bool) (DeleteOut cfg.FailWrites' admin r ns name dop) (fun _ _ oc => iprop(∀ err, kd.meta.DeleteOptions.own opts dq dop ∗ deleteRet cfg.AmbiguousWrites' admin oc err -∗ Φ #err))
                (Or.inr (Or.inr ⟨hDE, st, hst, Or.inl ⟨hdts, rfl, rfl⟩⟩))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
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
            unfold deleteRet
            ileft
            ipureintro; rfl
        · have hpnn := Hif
          cases hpre : dop.Preconditions' with
          | none => exact absurd (hpn.mpr hpre) hpnn
          | some pre =>
          icases delopts_pre_open opts dq dop pre hpre $$ Ho with ⟨%pv, Hp, HU, HR, Hoback⟩
          (try wp_auto)
          wp_bind (App (Val (GoInstruction (Convert go.untypedBool go.bool))) _)
          iapply (wp_wand_r (Φ := fun v => iprop(⌜v = #(decide (preFails pre st))⌝ ∗ iprop(p_ptr ↦ opts.Preconditions' ∗ opts.Preconditions' ↦{dq} pv ∗ (ownPtrD (V := k8s_io.apimachinery.pkg.types.UID) ownBaseD) pv.UID' dq pre.UID' ∗ (ownPtrD (V := GoString) ownBaseD) pv.ResourceVersion' dq pre.ResourceVersion' ∗ objAt x (DFrac.own 1) st ∗ stored_ptr ↦ x))))
          isplitl [p Hp HU HR Hx stored]
          · -- the preconditions' test
            iStructNamed Hp
            (try wp_auto)
            icases ownPtrD_null _ _ _ _ $$ HU with ⟨HU, %hun⟩
            wp_if_destruct
            · have hu0 : pre.UID' = none := hun.mp Hif
              icases ownPtrD_null _ _ _ _ $$ HR with ⟨HR, %hrn⟩
              wp_if_destruct
              · have hr0 : pre.ResourceVersion' = none := hrn.mp Hif
                (try wp_auto)
                isplitr
                · ipureintro
                  simp [preFails, hu0, hr0]
                iframe
                iapply typedPointsto_combine _ _ _ hpnn
                simp only [TypedPointsto.typedPointstoDef]
                iframe
              · cases hrv : pre.ResourceVersion' with
                | none => exact absurd (hrn.mpr hrv) Hif
                | some v =>
                ihave HR := (ownPtrD_base_some _ _ _).1 $$ HR
                (try wp_auto)
                wp_apply (objAt_GetResourceVersion wp_GetResourceVersion x _) $$ Hx as Hx
                ihave HR := (ownPtrD_base_some _ _ _).2 $$ HR
                by_cases Hv : v = st.meta.ResourceVersion'
                · simp only [decide_eq_true Hv, Bool.not_true]
                  (try wp_auto)
                  isplitr
                  · ipureintro
                    simp [preFails, hu0, hrv, Hv]
                  iframe
                  iapply typedPointsto_combine _ _ _ hpnn
                  simp only [TypedPointsto.typedPointstoDef]
                  iframe
                · simp only [decide_eq_false Hv, Bool.not_false]
                  (try wp_auto)
                  isplitr
                  · ipureintro
                    simp [preFails, hu0, hrv, Hv]
                  iframe
                  iapply typedPointsto_combine _ _ _ hpnn
                  simp only [TypedPointsto.typedPointstoDef]
                  iframe
            · cases hu : pre.UID' with
              | none => exact absurd (hun.mpr hu) Hif
              | some u =>
              ihave HU := (ownPtrD_base_some _ _ _).1 $$ HU
              (try wp_auto)
              wp_apply (objAt_GetUID wp_GetUID x _) $$ Hx as Hx
              ihave HU := (ownPtrD_base_some _ _ _).2 $$ HU
              by_cases Hu : u = st.meta.UID'
              · simp only [decide_eq_true Hu, Bool.not_true]
                (try wp_auto)
                icases ownPtrD_null _ _ _ _ $$ HR with ⟨HR, %hrn⟩
                wp_if_destruct
                · have hr0 : pre.ResourceVersion' = none := hrn.mp Hif
                  (try wp_auto)
                  isplitr
                  · ipureintro
                    simp [preFails, Hu, hu, hr0]
                  iframe
                  iapply typedPointsto_combine _ _ _ hpnn
                  simp only [TypedPointsto.typedPointstoDef]
                  iframe
                · cases hrv : pre.ResourceVersion' with
                  | none => exact absurd (hrn.mpr hrv) Hif
                  | some v =>
                  ihave HR := (ownPtrD_base_some _ _ _).1 $$ HR
                  (try wp_auto)
                  wp_apply (objAt_GetResourceVersion wp_GetResourceVersion x _) $$ Hx as Hx
                  ihave HR := (ownPtrD_base_some _ _ _).2 $$ HR
                  by_cases Hv : v = st.meta.ResourceVersion'
                  · simp only [decide_eq_true Hv, Bool.not_true]
                    (try wp_auto)
                    isplitr
                    · ipureintro
                      simp [preFails, Hu, hu, hrv, Hv]
                    iframe
                    iapply typedPointsto_combine _ _ _ hpnn
                    simp only [TypedPointsto.typedPointstoDef]
                    iframe
                  · simp only [decide_eq_false Hv, Bool.not_false]
                    (try wp_auto)
                    isplitr
                    · ipureintro
                      simp [preFails, Hu, hu, hrv, Hv]
                    iframe
                    iapply typedPointsto_combine _ _ _ hpnn
                    simp only [TypedPointsto.typedPointstoDef]
                    iframe
              · simp only [decide_eq_false Hu, Bool.not_false]
                (try wp_auto)
                isplitr
                · ipureintro
                  simp [preFails, Hu, hu]
                iframe
                iapply typedPointsto_combine _ _ _ hpnn
                simp only [TypedPointsto.typedPointstoDef]
                iframe
          iintro %v ⟨%hv, p, Hp, HU, HR, Hx, stored⟩
          subst hv
          wp_if_destruct
          · -- a precondition fails
            ihave Ho := Hoback $$ Hp HU HR
            ihave Hrel := Hrelb $$ Hx
            imod (au_write_noop γ H σ0 (.error .conflict : Except ApiErr Bool)
                (DeleteOut cfg.FailWrites' admin r ns name dop) (fun _ _ oc => iprop(∀ err, kd.meta.DeleteOptions.own opts dq dop ∗ deleteRet cfg.AmbiguousWrites' admin oc err -∗ Φ #err))
                (Or.inr (Or.inl ⟨.conflict, by rw [hpre]; exact deleteErr_conflict hst Hif, rfl, rfl⟩))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
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
            wp_apply wp_New as %e -
            (try wp_auto)
            wp_apply +noauto wp_NewConflict as %p' ⟨%st', Hp', %Hst⟩
            ipersist Hp'
            (try wp_auto)
            iapply HΦ
            iframe
            unfold deleteRet
            unfold errIs
            iexists p', st'
            iframe #
            ipureintro
            exact ⟨rfl, Hst.2.1, Hst.2.2⟩
          · have hDE : deleteErr r ns name dop.Preconditions' σ0 = none := by
              rw [hpre]; exact deleteErr_pre_ok hst Hif
            ihave Ho := Hoback $$ Hp HU HR
            wp_apply (objAt_GetDeletionTimestamp wp_GetDeletionTimestamp x _) $$ Hx as %dp ⟨Hx, %hdp⟩
            wp_if_destruct
            · -- not being deleted
              have hdts : st.meta.DeletionTimestamp' = none := hdp.mp rfl
              (try wp_auto)
              wp_apply (wp_grace_call r grace x st opts dq dop) $$ [$Hgrace $Hx $Ho] as ⟨Hx, Ho⟩
              · ipureintro; exact hstres
              (try wp_auto)
              wp_apply wp_copyObject $$ Hx as %y ⟨Hx, Hy⟩
              ihave Hrel := Hrelb $$ Hx
              (try wp_auto)
              wp_apply (wp_nextRV s L.rvs σ0.rev) $$ [$Hstrconv $Hrev $Hrvs $Hrvsm $Hrc] as ⟨Hrev, Hrvsm, Hrc, %hno⟩
              · ipureintro; exact ⟨hwf.rev_pos, Hbound⟩
              (try wp_auto)
              wp_apply (objAt_SetResourceVersion wp_SetResourceVersion y _ _) $$ Hy as Hy
              rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl] at hno
              rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl]
              (try wp_auto)
              wp_if_destruct
              · -- a positive grace period
                have hmod : 0 < sint.Z (graceOf r st dop.GracePeriodSeconds') ∨ st.meta.Finalizers' ≠ [] := Or.inl (by simpa using Hif)
                wp_apply wp_Now $$ [$Htime] as %tm -
                (try wp_auto)
                wp_apply (objAt_SetDeletionTimestamp wp_SetDeletionTimestamp y _ now_ptr tm) $$ [$Hy $now] as Hy
                (try wp_auto)
                wp_apply (objAt_SetDeletionGracePeriodSeconds wp_SetDeletionGracePeriodSeconds y _ period_ptr _) $$
                  [$Hy $period] as Hy
                (try wp_auto)
                rw [show k8s_io.apimachinery.pkg.watch.Modified = #(EvTy.modified.str) from rfl]
                wp_apply (wp_record s γ L cfg r (σ0.tbl r) .modified (σ0.rev + 1) y ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))) $$
                  [$Hfixed HM Hrel Hlog Hsl Hcap Hcs $Hy] as ⟨Hy, Htb⟩
                · iunfold tableLocked
                  iexists M, sl, cs
                  iframe
                ihave Htb := Htb $$ Hy
                obtain ⟨un, hn1, hn2, hn3⟩ := hstuid
                have hw := St.write_wf σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids hwf rfl hno
                  (by simp [hstres]) (by simp) (Nat.le_refl _) (by have := Huidlt; omega)
                  ⟨un, hn1, hn2, by simp [hn3]⟩
                imod (au_write γ H σ0 (σ0.write r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids) (.ok true) (DeleteOut cfg.FailWrites' admin r ns name dop) (fun _ _ oc => iprop(∀ err, kd.meta.DeleteOptions.own opts dq dop ∗ deleteRet cfg.AmbiguousWrites' admin oc err -∗ Φ #err)) Hok hw.2 hw.1
                    (Or.inr (Or.inr ⟨hDE, st, hst, Or.inr ⟨hdts, tm, (deleteApply_mod r st dop.GracePeriodSeconds' σ0 tm hmod), rfl⟩⟩)))
                  $$ [$Hhist $HΦ] with ⟨Hhist, %Hok', HΦ⟩
                (try wp_auto)
                wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback Htb]
                · iunfold lockInv
                  inext
                  iexists σ0.write r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids, H ++ [σ0]
                  iframe Hhist Hws
                  isplitl [Hrev Huids Hrvsm Hrc Hback Htb]
                  · iunfold srvLocked
                    simp only [named]
                    isplitl [Hrev]
                    · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl]
                      iexact Hrev
                    isplitl [Huids]
                    · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).uids = σ0.uids from rfl]
                      iexact Huids
                    isplitl [Hrvsm]
                    · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno]
                      iexact Hrvsm
                    isplitl [Hback Htb]
                    · iapply Hback
                      · ipureintro
                        intro r' hr'
                        rw [St.write_tbl, if_neg hr']
                      rw [St.write_tbl, if_pos rfl]
                      iexact Htb
                    isplitl [Hrc]
                    · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno,
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
                  unfold deleteRet
                  ileft
                  ipureintro; rfl
                · (try wp_auto)
                  wp_apply +noauto wp_NewTimeoutError as %p' ⟨%st', %dv, Hp', -, %Hst⟩
                  ipersist Hp'
                  (try wp_auto)
                  iapply HΦ
                  iframe
                  unfold deleteRet
                  iright
                  isplitr
                  · ipureintro; exact ⟨rfl, Hb2 rfl⟩
                  unfold errIs
                  iexists p', st'
                  iframe #
                  ipureintro
                  exact ⟨rfl, Hst.2.1, Hst.2.2⟩
              · have hg := Hif
                wp_apply (objAt_GetFinalizers wp_GetFinalizers y _) $$ Hy as %fs ⟨Hy, %hfs⟩
                simp only [Obj.meta_modMeta] at hfs
                (try wp_auto)
                wp_if_destruct
                · -- finalizers
                  have hmod : 0 < sint.Z (graceOf r st dop.GracePeriodSeconds') ∨ st.meta.Finalizers' ≠ [] := Or.inr (fin_ne hfs.1 Hif)
                  wp_apply wp_Now $$ [$Htime] as %tm -
                  (try wp_auto)
                  wp_apply (objAt_SetDeletionTimestamp wp_SetDeletionTimestamp y _ now_ptr tm) $$ [$Hy $now] as Hy
                  (try wp_auto)
                  wp_apply (objAt_SetDeletionGracePeriodSeconds wp_SetDeletionGracePeriodSeconds y _ period_ptr _) $$
                    [$Hy $period] as Hy
                  (try wp_auto)
                  rw [show k8s_io.apimachinery.pkg.watch.Modified = #(EvTy.modified.str) from rfl]
                  wp_apply (wp_record s γ L cfg r (σ0.tbl r) .modified (σ0.rev + 1) y ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))) $$
                    [$Hfixed HM Hrel Hlog Hsl Hcap Hcs $Hy] as ⟨Hy, Htb⟩
                  · iunfold tableLocked
                    iexists M, sl, cs
                    iframe
                  ihave Htb := Htb $$ Hy
                  obtain ⟨un, hn1, hn2, hn3⟩ := hstuid
                  have hw := St.write_wf σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids hwf rfl hno
                    (by simp [hstres]) (by simp) (Nat.le_refl _) (by have := Huidlt; omega)
                    ⟨un, hn1, hn2, by simp [hn3]⟩
                  imod (au_write γ H σ0 (σ0.write r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids) (.ok true) (DeleteOut cfg.FailWrites' admin r ns name dop) (fun _ _ oc => iprop(∀ err, kd.meta.DeleteOptions.own opts dq dop ∗ deleteRet cfg.AmbiguousWrites' admin oc err -∗ Φ #err)) Hok hw.2 hw.1
                      (Or.inr (Or.inr ⟨hDE, st, hst, Or.inr ⟨hdts, tm, (deleteApply_mod r st dop.GracePeriodSeconds' σ0 tm hmod), rfl⟩⟩)))
                    $$ [$Hhist $HΦ] with ⟨Hhist, %Hok', HΦ⟩
                  (try wp_auto)
                  wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback Htb]
                  · iunfold lockInv
                    inext
                    iexists σ0.write r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids, H ++ [σ0]
                    iframe Hhist Hws
                    isplitl [Hrev Huids Hrvsm Hrc Hback Htb]
                    · iunfold srvLocked
                      simp only [named]
                      isplitl [Hrev]
                      · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl]
                        iexact Hrev
                      isplitl [Huids]
                      · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).uids = σ0.uids from rfl]
                        iexact Huids
                      isplitl [Hrvsm]
                      · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno]
                        iexact Hrvsm
                      isplitl [Hback Htb]
                      · iapply Hback
                        · ipureintro
                          intro r' hr'
                          rw [St.write_tbl, if_neg hr']
                        rw [St.write_tbl, if_pos rfl]
                        iexact Htb
                      isplitl [Hrc]
                      · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno,
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
                    unfold deleteRet
                    ileft
                    ipureintro; rfl
                  · (try wp_auto)
                    wp_apply +noauto wp_NewTimeoutError as %p' ⟨%st', %dv, Hp', -, %Hst⟩
                    ipersist Hp'
                    (try wp_auto)
                    iapply HΦ
                    iframe
                    unfold deleteRet
                    iright
                    isplitr
                    · ipureintro; exact ⟨rfl, Hb2 rfl⟩
                    unfold errIs
                    iexists p', st'
                    iframe #
                    ipureintro
                    exact ⟨rfl, Hst.2.1, Hst.2.2⟩
                · -- deleted at once
                  have hdel : ¬ (0 < sint.Z (graceOf r st dop.GracePeriodSeconds') ∨ st.meta.Finalizers' ≠ []) := fun h => h.elim (fun h => hg (by simpa using h)) (fun h => h (fin_eq hfs.1 hfs.2 Hif))
                  (try wp_auto)
                  rw [show k8s_io.apimachinery.pkg.watch.Deleted = #(EvTy.deleted.str) from rfl]
                  wp_apply (wp_record s γ L cfg r (σ0.tbl r) .deleted (σ0.rev + 1) y (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))) $$
                    [$Hfixed HM Hrel Hlog Hsl Hcap Hcs $Hy] as ⟨Hy, Htb⟩
                  · iunfold tableLocked
                    iexists M, sl, cs
                    iframe
                  ihave Htb := Htb $$ Hy
                  obtain ⟨un, hn1, hn2, hn3⟩ := hstuid
                  have hw := St.write_wf σ0 r ⟨.deleted, σ0.rev + 1, (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))⟩ σ0.uids hwf rfl hno
                    (by simp [hstres]) (by simp) (Nat.le_refl _) (by have := Huidlt; omega)
                    ⟨un, hn1, hn2, by simp [hn3]⟩
                  imod (au_write γ H σ0 (σ0.write r ⟨.deleted, σ0.rev + 1, (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))⟩ σ0.uids) (.ok true) (DeleteOut cfg.FailWrites' admin r ns name dop) (fun _ _ oc => iprop(∀ err, kd.meta.DeleteOptions.own opts dq dop ∗ deleteRet cfg.AmbiguousWrites' admin oc err -∗ Φ #err)) Hok hw.2 hw.1
                      (Or.inr (Or.inr ⟨hDE, st, hst, Or.inr ⟨hdts, (zero_val k8s_io.apimachinery.pkg.apis.«meta».v1.Time), (deleteApply_del r st dop.GracePeriodSeconds' σ0 (zero_val k8s_io.apimachinery.pkg.apis.«meta».v1.Time) hdel), rfl⟩⟩)))
                    $$ [$Hhist $HΦ] with ⟨Hhist, %Hok', HΦ⟩
                  (try wp_auto)
                  wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback Htb]
                  · iunfold lockInv
                    inext
                    iexists σ0.write r ⟨.deleted, σ0.rev + 1, (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))⟩ σ0.uids, H ++ [σ0]
                    iframe Hhist Hws
                    isplitl [Hrev Huids Hrvsm Hrc Hback Htb]
                    · iunfold srvLocked
                      simp only [named]
                      isplitl [Hrev]
                      · rw [show (St.write σ0 r ⟨.deleted, σ0.rev + 1, (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl]
                        iexact Hrev
                      isplitl [Huids]
                      · rw [show (St.write σ0 r ⟨.deleted, σ0.rev + 1, (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))⟩ σ0.uids).uids = σ0.uids from rfl]
                        iexact Huids
                      isplitl [Hrvsm]
                      · rw [show (St.write σ0 r ⟨.deleted, σ0.rev + 1, (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno]
                        iexact Hrvsm
                      isplitl [Hback Htb]
                      · iapply Hback
                        · ipureintro
                          intro r' hr'
                          rw [St.write_tbl, if_neg hr']
                        rw [St.write_tbl, if_pos rfl]
                        iexact Htb
                      isplitl [Hrc]
                      · rw [show (St.write σ0 r ⟨.deleted, σ0.rev + 1, (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno,
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
                    unfold deleteRet
                    ileft
                    ipureintro; rfl
                  · (try wp_auto)
                    wp_apply +noauto wp_NewTimeoutError as %p' ⟨%st', %dv, Hp', -, %Hst⟩
                    ipersist Hp'
                    (try wp_auto)
                    iapply HΦ
                    iframe
                    unfold deleteRet
                    iright
                    isplitr
                    · ipureintro; exact ⟨rfl, Hb2 rfl⟩
                    unfold errIs
                    iexists p', st'
                    iframe #
                    ipureintro
                    exact ⟨rfl, Hst.2.1, Hst.2.2⟩
            · -- already being deleted: nothing changes
              have hdts : st.meta.DeletionTimestamp'.isSome := by
                cases h : st.meta.DeletionTimestamp' with
                | none => exact absurd (hdp.mpr h) Hif
                | some _ => rfl
              ihave Hrel := Hrelb $$ Hx
              imod (au_write_noop γ H σ0 (.ok false : Except ApiErr Bool) (DeleteOut cfg.FailWrites' admin r ns name dop) (fun _ _ oc => iprop(∀ err, kd.meta.DeleteOptions.own opts dq dop ∗ deleteRet cfg.AmbiguousWrites' admin oc err -∗ Φ #err))
                  (Or.inr (Or.inr ⟨hDE, st, hst, Or.inl ⟨hdts, rfl, rfl⟩⟩))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
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
              unfold deleteRet
              ileft
              ipureintro; rfl
    · have hrk : reqKey r ns name = mkKey ns name := by simp [reqKey, hnsr]
      wp_apply wp_Lock $$ [$Hmu] as ⟨Hown, Hinv⟩
      iunfold lockInv at Hinv
      icases Hinv with ⟨%σ0, %H, Hlk, Hhist, %Hok, Hws⟩
      iNamed Hlk
      have hwf := histOk_last_wf Hok
      icases tablesLocked_acc L σ0 r $$ Htbls with ⟨Ht0, Hback⟩
      iunfold tableLocked at Ht0
      icases Ht0 with ⟨%M, %sl, %cs, HM, Hrel, Hlog, Hsl, Hcap, Hcs⟩
      (try wp_auto)
      (try dsimp only)
      wp_apply (wp_map_lookup2 k8s_io.apimachinery.pkg.types.NamespacedName.ty apimodel.object.ty
        (L.tbl r).objs M (mkKey ns name) (DFrac.own 1)) $$ HM as HM
      ihave %hd := objsRel_dom M (σ0.tbl r).objs (mkKey ns name) $$ Hrel
      cases hk : M !! mkKey ns name with
      | none =>
        have hnone : (σ0.tbl r).objs !! reqKey r ns name = none := by
          rw [hrk]
          cases h' : (σ0.tbl r).objs !! mkKey ns name with
          | none => rfl
          | some _ => simp [h', hk] at hd
        (try simp only [Option.isSome_none, Option.getD_none])
        (try wp_auto)
        imod (au_write_noop γ H σ0 (.error .notFound : Except ApiErr Bool)
            (DeleteOut cfg.FailWrites' admin r ns name dop) (fun _ _ oc => iprop(∀ err, kd.meta.DeleteOptions.own opts dq dop ∗ deleteRet cfg.AmbiguousWrites' admin oc err -∗ Φ #err))
            (Or.inr (Or.inl ⟨.notFound, deleteErr_notFound hnone, rfl, rfl⟩))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
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
        wp_apply +noauto wp_NewNotFound as %p ⟨%st', Hp, %Hst⟩
        ipersist Hp
        (try wp_auto)
        iapply HΦ
        iframe
        unfold deleteRet
        unfold errIs
        iexists p, st'
        iframe #
        ipureintro
        exact ⟨rfl, Hst.2.1, Hst.2.2⟩
      | some x =>
        icases objsRel_lookup M (σ0.tbl r).objs _ x hk $$ Hrel with ⟨%st, %hst0, Hx, Hrelb⟩
        have hst : (σ0.tbl r).objs !! reqKey r ns name = some st := by rw [hrk]; exact hst0
        obtain ⟨hstres, hstuid⟩ := wf_stored hwf hst0
        (try simp only [Option.isSome_some, Option.getD_some])
        (try wp_auto)
        icases delopts_pre_null opts dq dop $$ Ho with ⟨Ho, %hpn⟩
        wp_if_destruct
        · have hpre : dop.Preconditions' = none := hpn.mp Hif
          have hDE : deleteErr r ns name dop.Preconditions' σ0 = none := by
            rw [hpre]; exact deleteErr_nopre hst
          wp_apply (objAt_GetDeletionTimestamp wp_GetDeletionTimestamp x _) $$ Hx as %dp ⟨Hx, %hdp⟩
          wp_if_destruct
          · -- not being deleted
            have hdts : st.meta.DeletionTimestamp' = none := hdp.mp rfl
            (try wp_auto)
            wp_apply (wp_grace_call r grace x st opts dq dop) $$ [$Hgrace $Hx $Ho] as ⟨Hx, Ho⟩
            · ipureintro; exact hstres
            (try wp_auto)
            wp_apply wp_copyObject $$ Hx as %y ⟨Hx, Hy⟩
            ihave Hrel := Hrelb $$ Hx
            (try wp_auto)
            wp_apply (wp_nextRV s L.rvs σ0.rev) $$ [$Hstrconv $Hrev $Hrvs $Hrvsm $Hrc] as ⟨Hrev, Hrvsm, Hrc, %hno⟩
            · ipureintro; exact ⟨hwf.rev_pos, Hbound⟩
            (try wp_auto)
            wp_apply (objAt_SetResourceVersion wp_SetResourceVersion y _ _) $$ Hy as Hy
            rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl] at hno
            rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl]
            (try wp_auto)
            wp_if_destruct
            · -- a positive grace period
              have hmod : 0 < sint.Z (graceOf r st dop.GracePeriodSeconds') ∨ st.meta.Finalizers' ≠ [] := Or.inl (by simpa using Hif)
              wp_apply wp_Now $$ [$Htime] as %tm -
              (try wp_auto)
              wp_apply (objAt_SetDeletionTimestamp wp_SetDeletionTimestamp y _ now_ptr tm) $$ [$Hy $now] as Hy
              (try wp_auto)
              wp_apply (objAt_SetDeletionGracePeriodSeconds wp_SetDeletionGracePeriodSeconds y _ period_ptr _) $$
                [$Hy $period] as Hy
              (try wp_auto)
              rw [show k8s_io.apimachinery.pkg.watch.Modified = #(EvTy.modified.str) from rfl]
              wp_apply (wp_record s γ L cfg r (σ0.tbl r) .modified (σ0.rev + 1) y ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))) $$
                [$Hfixed HM Hrel Hlog Hsl Hcap Hcs $Hy] as ⟨Hy, Htb⟩
              · iunfold tableLocked
                iexists M, sl, cs
                iframe
              ihave Htb := Htb $$ Hy
              obtain ⟨un, hn1, hn2, hn3⟩ := hstuid
              have hw := St.write_wf σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids hwf rfl hno
                (by simp [hstres]) (by simp) (Nat.le_refl _) (by have := Huidlt; omega)
                ⟨un, hn1, hn2, by simp [hn3]⟩
              imod (au_write γ H σ0 (σ0.write r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids) (.ok true) (DeleteOut cfg.FailWrites' admin r ns name dop) (fun _ _ oc => iprop(∀ err, kd.meta.DeleteOptions.own opts dq dop ∗ deleteRet cfg.AmbiguousWrites' admin oc err -∗ Φ #err)) Hok hw.2 hw.1
                  (Or.inr (Or.inr ⟨hDE, st, hst, Or.inr ⟨hdts, tm, (deleteApply_mod r st dop.GracePeriodSeconds' σ0 tm hmod), rfl⟩⟩)))
                $$ [$Hhist $HΦ] with ⟨Hhist, %Hok', HΦ⟩
              (try wp_auto)
              wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback Htb]
              · iunfold lockInv
                inext
                iexists σ0.write r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids, H ++ [σ0]
                iframe Hhist Hws
                isplitl [Hrev Huids Hrvsm Hrc Hback Htb]
                · iunfold srvLocked
                  simp only [named]
                  isplitl [Hrev]
                  · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl]
                    iexact Hrev
                  isplitl [Huids]
                  · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).uids = σ0.uids from rfl]
                    iexact Huids
                  isplitl [Hrvsm]
                  · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno]
                    iexact Hrvsm
                  isplitl [Hback Htb]
                  · iapply Hback
                    · ipureintro
                      intro r' hr'
                      rw [St.write_tbl, if_neg hr']
                    rw [St.write_tbl, if_pos rfl]
                    iexact Htb
                  isplitl [Hrc]
                  · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno,
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
                unfold deleteRet
                ileft
                ipureintro; rfl
              · (try wp_auto)
                wp_apply +noauto wp_NewTimeoutError as %p' ⟨%st', %dv, Hp', -, %Hst⟩
                ipersist Hp'
                (try wp_auto)
                iapply HΦ
                iframe
                unfold deleteRet
                iright
                isplitr
                · ipureintro; exact ⟨rfl, Hb2 rfl⟩
                unfold errIs
                iexists p', st'
                iframe #
                ipureintro
                exact ⟨rfl, Hst.2.1, Hst.2.2⟩
            · have hg := Hif
              wp_apply (objAt_GetFinalizers wp_GetFinalizers y _) $$ Hy as %fs ⟨Hy, %hfs⟩
              simp only [Obj.meta_modMeta] at hfs
              (try wp_auto)
              wp_if_destruct
              · -- finalizers
                have hmod : 0 < sint.Z (graceOf r st dop.GracePeriodSeconds') ∨ st.meta.Finalizers' ≠ [] := Or.inr (fin_ne hfs.1 Hif)
                wp_apply wp_Now $$ [$Htime] as %tm -
                (try wp_auto)
                wp_apply (objAt_SetDeletionTimestamp wp_SetDeletionTimestamp y _ now_ptr tm) $$ [$Hy $now] as Hy
                (try wp_auto)
                wp_apply (objAt_SetDeletionGracePeriodSeconds wp_SetDeletionGracePeriodSeconds y _ period_ptr _) $$
                  [$Hy $period] as Hy
                (try wp_auto)
                rw [show k8s_io.apimachinery.pkg.watch.Modified = #(EvTy.modified.str) from rfl]
                wp_apply (wp_record s γ L cfg r (σ0.tbl r) .modified (σ0.rev + 1) y ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))) $$
                  [$Hfixed HM Hrel Hlog Hsl Hcap Hcs $Hy] as ⟨Hy, Htb⟩
                · iunfold tableLocked
                  iexists M, sl, cs
                  iframe
                ihave Htb := Htb $$ Hy
                obtain ⟨un, hn1, hn2, hn3⟩ := hstuid
                have hw := St.write_wf σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids hwf rfl hno
                  (by simp [hstres]) (by simp) (Nat.le_refl _) (by have := Huidlt; omega)
                  ⟨un, hn1, hn2, by simp [hn3]⟩
                imod (au_write γ H σ0 (σ0.write r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids) (.ok true) (DeleteOut cfg.FailWrites' admin r ns name dop) (fun _ _ oc => iprop(∀ err, kd.meta.DeleteOptions.own opts dq dop ∗ deleteRet cfg.AmbiguousWrites' admin oc err -∗ Φ #err)) Hok hw.2 hw.1
                    (Or.inr (Or.inr ⟨hDE, st, hst, Or.inr ⟨hdts, tm, (deleteApply_mod r st dop.GracePeriodSeconds' σ0 tm hmod), rfl⟩⟩)))
                  $$ [$Hhist $HΦ] with ⟨Hhist, %Hok', HΦ⟩
                (try wp_auto)
                wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback Htb]
                · iunfold lockInv
                  inext
                  iexists σ0.write r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids, H ++ [σ0]
                  iframe Hhist Hws
                  isplitl [Hrev Huids Hrvsm Hrc Hback Htb]
                  · iunfold srvLocked
                    simp only [named]
                    isplitl [Hrev]
                    · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl]
                      iexact Hrev
                    isplitl [Huids]
                    · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).uids = σ0.uids from rfl]
                      iexact Huids
                    isplitl [Hrvsm]
                    · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno]
                      iexact Hrvsm
                    isplitl [Hback Htb]
                    · iapply Hback
                      · ipureintro
                        intro r' hr'
                        rw [St.write_tbl, if_neg hr']
                      rw [St.write_tbl, if_pos rfl]
                      iexact Htb
                    isplitl [Hrc]
                    · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno,
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
                  unfold deleteRet
                  ileft
                  ipureintro; rfl
                · (try wp_auto)
                  wp_apply +noauto wp_NewTimeoutError as %p' ⟨%st', %dv, Hp', -, %Hst⟩
                  ipersist Hp'
                  (try wp_auto)
                  iapply HΦ
                  iframe
                  unfold deleteRet
                  iright
                  isplitr
                  · ipureintro; exact ⟨rfl, Hb2 rfl⟩
                  unfold errIs
                  iexists p', st'
                  iframe #
                  ipureintro
                  exact ⟨rfl, Hst.2.1, Hst.2.2⟩
              · -- deleted at once
                have hdel : ¬ (0 < sint.Z (graceOf r st dop.GracePeriodSeconds') ∨ st.meta.Finalizers' ≠ []) := fun h => h.elim (fun h => hg (by simpa using h)) (fun h => h (fin_eq hfs.1 hfs.2 Hif))
                (try wp_auto)
                rw [show k8s_io.apimachinery.pkg.watch.Deleted = #(EvTy.deleted.str) from rfl]
                wp_apply (wp_record s γ L cfg r (σ0.tbl r) .deleted (σ0.rev + 1) y (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))) $$
                  [$Hfixed HM Hrel Hlog Hsl Hcap Hcs $Hy] as ⟨Hy, Htb⟩
                · iunfold tableLocked
                  iexists M, sl, cs
                  iframe
                ihave Htb := Htb $$ Hy
                obtain ⟨un, hn1, hn2, hn3⟩ := hstuid
                have hw := St.write_wf σ0 r ⟨.deleted, σ0.rev + 1, (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))⟩ σ0.uids hwf rfl hno
                  (by simp [hstres]) (by simp) (Nat.le_refl _) (by have := Huidlt; omega)
                  ⟨un, hn1, hn2, by simp [hn3]⟩
                imod (au_write γ H σ0 (σ0.write r ⟨.deleted, σ0.rev + 1, (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))⟩ σ0.uids) (.ok true) (DeleteOut cfg.FailWrites' admin r ns name dop) (fun _ _ oc => iprop(∀ err, kd.meta.DeleteOptions.own opts dq dop ∗ deleteRet cfg.AmbiguousWrites' admin oc err -∗ Φ #err)) Hok hw.2 hw.1
                    (Or.inr (Or.inr ⟨hDE, st, hst, Or.inr ⟨hdts, (zero_val k8s_io.apimachinery.pkg.apis.«meta».v1.Time), (deleteApply_del r st dop.GracePeriodSeconds' σ0 (zero_val k8s_io.apimachinery.pkg.apis.«meta».v1.Time) hdel), rfl⟩⟩)))
                  $$ [$Hhist $HΦ] with ⟨Hhist, %Hok', HΦ⟩
                (try wp_auto)
                wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback Htb]
                · iunfold lockInv
                  inext
                  iexists σ0.write r ⟨.deleted, σ0.rev + 1, (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))⟩ σ0.uids, H ++ [σ0]
                  iframe Hhist Hws
                  isplitl [Hrev Huids Hrvsm Hrc Hback Htb]
                  · iunfold srvLocked
                    simp only [named]
                    isplitl [Hrev]
                    · rw [show (St.write σ0 r ⟨.deleted, σ0.rev + 1, (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl]
                      iexact Hrev
                    isplitl [Huids]
                    · rw [show (St.write σ0 r ⟨.deleted, σ0.rev + 1, (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))⟩ σ0.uids).uids = σ0.uids from rfl]
                      iexact Huids
                    isplitl [Hrvsm]
                    · rw [show (St.write σ0 r ⟨.deleted, σ0.rev + 1, (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno]
                      iexact Hrvsm
                    isplitl [Hback Htb]
                    · iapply Hback
                      · ipureintro
                        intro r' hr'
                        rw [St.write_tbl, if_neg hr']
                      rw [St.write_tbl, if_pos rfl]
                      iexact Htb
                    isplitl [Hrc]
                    · rw [show (St.write σ0 r ⟨.deleted, σ0.rev + 1, (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno,
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
                  unfold deleteRet
                  ileft
                  ipureintro; rfl
                · (try wp_auto)
                  wp_apply +noauto wp_NewTimeoutError as %p' ⟨%st', %dv, Hp', -, %Hst⟩
                  ipersist Hp'
                  (try wp_auto)
                  iapply HΦ
                  iframe
                  unfold deleteRet
                  iright
                  isplitr
                  · ipureintro; exact ⟨rfl, Hb2 rfl⟩
                  unfold errIs
                  iexists p', st'
                  iframe #
                  ipureintro
                  exact ⟨rfl, Hst.2.1, Hst.2.2⟩
          · -- already being deleted: nothing changes
            have hdts : st.meta.DeletionTimestamp'.isSome := by
              cases h : st.meta.DeletionTimestamp' with
              | none => exact absurd (hdp.mpr h) Hif
              | some _ => rfl
            ihave Hrel := Hrelb $$ Hx
            imod (au_write_noop γ H σ0 (.ok false : Except ApiErr Bool) (DeleteOut cfg.FailWrites' admin r ns name dop) (fun _ _ oc => iprop(∀ err, kd.meta.DeleteOptions.own opts dq dop ∗ deleteRet cfg.AmbiguousWrites' admin oc err -∗ Φ #err))
                (Or.inr (Or.inr ⟨hDE, st, hst, Or.inl ⟨hdts, rfl, rfl⟩⟩))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
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
            unfold deleteRet
            ileft
            ipureintro; rfl
        · have hpnn := Hif
          cases hpre : dop.Preconditions' with
          | none => exact absurd (hpn.mpr hpre) hpnn
          | some pre =>
          icases delopts_pre_open opts dq dop pre hpre $$ Ho with ⟨%pv, Hp, HU, HR, Hoback⟩
          (try wp_auto)
          wp_bind (App (Val (GoInstruction (Convert go.untypedBool go.bool))) _)
          iapply (wp_wand_r (Φ := fun v => iprop(⌜v = #(decide (preFails pre st))⌝ ∗ iprop(p_ptr ↦ opts.Preconditions' ∗ opts.Preconditions' ↦{dq} pv ∗ (ownPtrD (V := k8s_io.apimachinery.pkg.types.UID) ownBaseD) pv.UID' dq pre.UID' ∗ (ownPtrD (V := GoString) ownBaseD) pv.ResourceVersion' dq pre.ResourceVersion' ∗ objAt x (DFrac.own 1) st ∗ stored_ptr ↦ x))))
          isplitl [p Hp HU HR Hx stored]
          · -- the preconditions' test
            iStructNamed Hp
            (try wp_auto)
            icases ownPtrD_null _ _ _ _ $$ HU with ⟨HU, %hun⟩
            wp_if_destruct
            · have hu0 : pre.UID' = none := hun.mp Hif
              icases ownPtrD_null _ _ _ _ $$ HR with ⟨HR, %hrn⟩
              wp_if_destruct
              · have hr0 : pre.ResourceVersion' = none := hrn.mp Hif
                (try wp_auto)
                isplitr
                · ipureintro
                  simp [preFails, hu0, hr0]
                iframe
                iapply typedPointsto_combine _ _ _ hpnn
                simp only [TypedPointsto.typedPointstoDef]
                iframe
              · cases hrv : pre.ResourceVersion' with
                | none => exact absurd (hrn.mpr hrv) Hif
                | some v =>
                ihave HR := (ownPtrD_base_some _ _ _).1 $$ HR
                (try wp_auto)
                wp_apply (objAt_GetResourceVersion wp_GetResourceVersion x _) $$ Hx as Hx
                ihave HR := (ownPtrD_base_some _ _ _).2 $$ HR
                by_cases Hv : v = st.meta.ResourceVersion'
                · simp only [decide_eq_true Hv, Bool.not_true]
                  (try wp_auto)
                  isplitr
                  · ipureintro
                    simp [preFails, hu0, hrv, Hv]
                  iframe
                  iapply typedPointsto_combine _ _ _ hpnn
                  simp only [TypedPointsto.typedPointstoDef]
                  iframe
                · simp only [decide_eq_false Hv, Bool.not_false]
                  (try wp_auto)
                  isplitr
                  · ipureintro
                    simp [preFails, hu0, hrv, Hv]
                  iframe
                  iapply typedPointsto_combine _ _ _ hpnn
                  simp only [TypedPointsto.typedPointstoDef]
                  iframe
            · cases hu : pre.UID' with
              | none => exact absurd (hun.mpr hu) Hif
              | some u =>
              ihave HU := (ownPtrD_base_some _ _ _).1 $$ HU
              (try wp_auto)
              wp_apply (objAt_GetUID wp_GetUID x _) $$ Hx as Hx
              ihave HU := (ownPtrD_base_some _ _ _).2 $$ HU
              by_cases Hu : u = st.meta.UID'
              · simp only [decide_eq_true Hu, Bool.not_true]
                (try wp_auto)
                icases ownPtrD_null _ _ _ _ $$ HR with ⟨HR, %hrn⟩
                wp_if_destruct
                · have hr0 : pre.ResourceVersion' = none := hrn.mp Hif
                  (try wp_auto)
                  isplitr
                  · ipureintro
                    simp [preFails, Hu, hu, hr0]
                  iframe
                  iapply typedPointsto_combine _ _ _ hpnn
                  simp only [TypedPointsto.typedPointstoDef]
                  iframe
                · cases hrv : pre.ResourceVersion' with
                  | none => exact absurd (hrn.mpr hrv) Hif
                  | some v =>
                  ihave HR := (ownPtrD_base_some _ _ _).1 $$ HR
                  (try wp_auto)
                  wp_apply (objAt_GetResourceVersion wp_GetResourceVersion x _) $$ Hx as Hx
                  ihave HR := (ownPtrD_base_some _ _ _).2 $$ HR
                  by_cases Hv : v = st.meta.ResourceVersion'
                  · simp only [decide_eq_true Hv, Bool.not_true]
                    (try wp_auto)
                    isplitr
                    · ipureintro
                      simp [preFails, Hu, hu, hrv, Hv]
                    iframe
                    iapply typedPointsto_combine _ _ _ hpnn
                    simp only [TypedPointsto.typedPointstoDef]
                    iframe
                  · simp only [decide_eq_false Hv, Bool.not_false]
                    (try wp_auto)
                    isplitr
                    · ipureintro
                      simp [preFails, Hu, hu, hrv, Hv]
                    iframe
                    iapply typedPointsto_combine _ _ _ hpnn
                    simp only [TypedPointsto.typedPointstoDef]
                    iframe
              · simp only [decide_eq_false Hu, Bool.not_false]
                (try wp_auto)
                isplitr
                · ipureintro
                  simp [preFails, Hu, hu]
                iframe
                iapply typedPointsto_combine _ _ _ hpnn
                simp only [TypedPointsto.typedPointstoDef]
                iframe
          iintro %v ⟨%hv, p, Hp, HU, HR, Hx, stored⟩
          subst hv
          wp_if_destruct
          · -- a precondition fails
            ihave Ho := Hoback $$ Hp HU HR
            ihave Hrel := Hrelb $$ Hx
            imod (au_write_noop γ H σ0 (.error .conflict : Except ApiErr Bool)
                (DeleteOut cfg.FailWrites' admin r ns name dop) (fun _ _ oc => iprop(∀ err, kd.meta.DeleteOptions.own opts dq dop ∗ deleteRet cfg.AmbiguousWrites' admin oc err -∗ Φ #err))
                (Or.inr (Or.inl ⟨.conflict, by rw [hpre]; exact deleteErr_conflict hst Hif, rfl, rfl⟩))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
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
            wp_apply wp_New as %e -
            (try wp_auto)
            wp_apply +noauto wp_NewConflict as %p' ⟨%st', Hp', %Hst⟩
            ipersist Hp'
            (try wp_auto)
            iapply HΦ
            iframe
            unfold deleteRet
            unfold errIs
            iexists p', st'
            iframe #
            ipureintro
            exact ⟨rfl, Hst.2.1, Hst.2.2⟩
          · have hDE : deleteErr r ns name dop.Preconditions' σ0 = none := by
              rw [hpre]; exact deleteErr_pre_ok hst Hif
            ihave Ho := Hoback $$ Hp HU HR
            wp_apply (objAt_GetDeletionTimestamp wp_GetDeletionTimestamp x _) $$ Hx as %dp ⟨Hx, %hdp⟩
            wp_if_destruct
            · -- not being deleted
              have hdts : st.meta.DeletionTimestamp' = none := hdp.mp rfl
              (try wp_auto)
              wp_apply (wp_grace_call r grace x st opts dq dop) $$ [$Hgrace $Hx $Ho] as ⟨Hx, Ho⟩
              · ipureintro; exact hstres
              (try wp_auto)
              wp_apply wp_copyObject $$ Hx as %y ⟨Hx, Hy⟩
              ihave Hrel := Hrelb $$ Hx
              (try wp_auto)
              wp_apply (wp_nextRV s L.rvs σ0.rev) $$ [$Hstrconv $Hrev $Hrvs $Hrvsm $Hrc] as ⟨Hrev, Hrvsm, Hrc, %hno⟩
              · ipureintro; exact ⟨hwf.rev_pos, Hbound⟩
              (try wp_auto)
              wp_apply (objAt_SetResourceVersion wp_SetResourceVersion y _ _) $$ Hy as Hy
              rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl] at hno
              rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl]
              (try wp_auto)
              wp_if_destruct
              · -- a positive grace period
                have hmod : 0 < sint.Z (graceOf r st dop.GracePeriodSeconds') ∨ st.meta.Finalizers' ≠ [] := Or.inl (by simpa using Hif)
                wp_apply wp_Now $$ [$Htime] as %tm -
                (try wp_auto)
                wp_apply (objAt_SetDeletionTimestamp wp_SetDeletionTimestamp y _ now_ptr tm) $$ [$Hy $now] as Hy
                (try wp_auto)
                wp_apply (objAt_SetDeletionGracePeriodSeconds wp_SetDeletionGracePeriodSeconds y _ period_ptr _) $$
                  [$Hy $period] as Hy
                (try wp_auto)
                rw [show k8s_io.apimachinery.pkg.watch.Modified = #(EvTy.modified.str) from rfl]
                wp_apply (wp_record s γ L cfg r (σ0.tbl r) .modified (σ0.rev + 1) y ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))) $$
                  [$Hfixed HM Hrel Hlog Hsl Hcap Hcs $Hy] as ⟨Hy, Htb⟩
                · iunfold tableLocked
                  iexists M, sl, cs
                  iframe
                ihave Htb := Htb $$ Hy
                obtain ⟨un, hn1, hn2, hn3⟩ := hstuid
                have hw := St.write_wf σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids hwf rfl hno
                  (by simp [hstres]) (by simp) (Nat.le_refl _) (by have := Huidlt; omega)
                  ⟨un, hn1, hn2, by simp [hn3]⟩
                imod (au_write γ H σ0 (σ0.write r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids) (.ok true) (DeleteOut cfg.FailWrites' admin r ns name dop) (fun _ _ oc => iprop(∀ err, kd.meta.DeleteOptions.own opts dq dop ∗ deleteRet cfg.AmbiguousWrites' admin oc err -∗ Φ #err)) Hok hw.2 hw.1
                    (Or.inr (Or.inr ⟨hDE, st, hst, Or.inr ⟨hdts, tm, (deleteApply_mod r st dop.GracePeriodSeconds' σ0 tm hmod), rfl⟩⟩)))
                  $$ [$Hhist $HΦ] with ⟨Hhist, %Hok', HΦ⟩
                (try wp_auto)
                wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback Htb]
                · iunfold lockInv
                  inext
                  iexists σ0.write r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids, H ++ [σ0]
                  iframe Hhist Hws
                  isplitl [Hrev Huids Hrvsm Hrc Hback Htb]
                  · iunfold srvLocked
                    simp only [named]
                    isplitl [Hrev]
                    · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl]
                      iexact Hrev
                    isplitl [Huids]
                    · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).uids = σ0.uids from rfl]
                      iexact Huids
                    isplitl [Hrvsm]
                    · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno]
                      iexact Hrvsm
                    isplitl [Hback Htb]
                    · iapply Hback
                      · ipureintro
                        intro r' hr'
                        rw [St.write_tbl, if_neg hr']
                      rw [St.write_tbl, if_pos rfl]
                      iexact Htb
                    isplitl [Hrc]
                    · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno,
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
                  unfold deleteRet
                  ileft
                  ipureintro; rfl
                · (try wp_auto)
                  wp_apply +noauto wp_NewTimeoutError as %p' ⟨%st', %dv, Hp', -, %Hst⟩
                  ipersist Hp'
                  (try wp_auto)
                  iapply HΦ
                  iframe
                  unfold deleteRet
                  iright
                  isplitr
                  · ipureintro; exact ⟨rfl, Hb2 rfl⟩
                  unfold errIs
                  iexists p', st'
                  iframe #
                  ipureintro
                  exact ⟨rfl, Hst.2.1, Hst.2.2⟩
              · have hg := Hif
                wp_apply (objAt_GetFinalizers wp_GetFinalizers y _) $$ Hy as %fs ⟨Hy, %hfs⟩
                simp only [Obj.meta_modMeta] at hfs
                (try wp_auto)
                wp_if_destruct
                · -- finalizers
                  have hmod : 0 < sint.Z (graceOf r st dop.GracePeriodSeconds') ∨ st.meta.Finalizers' ≠ [] := Or.inr (fin_ne hfs.1 Hif)
                  wp_apply wp_Now $$ [$Htime] as %tm -
                  (try wp_auto)
                  wp_apply (objAt_SetDeletionTimestamp wp_SetDeletionTimestamp y _ now_ptr tm) $$ [$Hy $now] as Hy
                  (try wp_auto)
                  wp_apply (objAt_SetDeletionGracePeriodSeconds wp_SetDeletionGracePeriodSeconds y _ period_ptr _) $$
                    [$Hy $period] as Hy
                  (try wp_auto)
                  rw [show k8s_io.apimachinery.pkg.watch.Modified = #(EvTy.modified.str) from rfl]
                  wp_apply (wp_record s γ L cfg r (σ0.tbl r) .modified (σ0.rev + 1) y ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))) $$
                    [$Hfixed HM Hrel Hlog Hsl Hcap Hcs $Hy] as ⟨Hy, Htb⟩
                  · iunfold tableLocked
                    iexists M, sl, cs
                    iframe
                  ihave Htb := Htb $$ Hy
                  obtain ⟨un, hn1, hn2, hn3⟩ := hstuid
                  have hw := St.write_wf σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids hwf rfl hno
                    (by simp [hstres]) (by simp) (Nat.le_refl _) (by have := Huidlt; omega)
                    ⟨un, hn1, hn2, by simp [hn3]⟩
                  imod (au_write γ H σ0 (σ0.write r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids) (.ok true) (DeleteOut cfg.FailWrites' admin r ns name dop) (fun _ _ oc => iprop(∀ err, kd.meta.DeleteOptions.own opts dq dop ∗ deleteRet cfg.AmbiguousWrites' admin oc err -∗ Φ #err)) Hok hw.2 hw.1
                      (Or.inr (Or.inr ⟨hDE, st, hst, Or.inr ⟨hdts, tm, (deleteApply_mod r st dop.GracePeriodSeconds' σ0 tm hmod), rfl⟩⟩)))
                    $$ [$Hhist $HΦ] with ⟨Hhist, %Hok', HΦ⟩
                  (try wp_auto)
                  wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback Htb]
                  · iunfold lockInv
                    inext
                    iexists σ0.write r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids, H ++ [σ0]
                    iframe Hhist Hws
                    isplitl [Hrev Huids Hrvsm Hrc Hback Htb]
                    · iunfold srvLocked
                      simp only [named]
                      isplitl [Hrev]
                      · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl]
                        iexact Hrev
                      isplitl [Huids]
                      · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).uids = σ0.uids from rfl]
                        iexact Huids
                      isplitl [Hrvsm]
                      · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno]
                        iexact Hrvsm
                      isplitl [Hback Htb]
                      · iapply Hback
                        · ipureintro
                          intro r' hr'
                          rw [St.write_tbl, if_neg hr']
                        rw [St.write_tbl, if_pos rfl]
                        iexact Htb
                      isplitl [Hrc]
                      · rw [show (St.write σ0 r ⟨.modified, σ0.rev + 1, ((((st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))).modMeta (fun m => { m with DeletionTimestamp' := some tm })).modMeta (fun m => { m with DeletionGracePeriodSeconds' := some (graceOf r st dop.GracePeriodSeconds') }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno,
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
                    unfold deleteRet
                    ileft
                    ipureintro; rfl
                  · (try wp_auto)
                    wp_apply +noauto wp_NewTimeoutError as %p' ⟨%st', %dv, Hp', -, %Hst⟩
                    ipersist Hp'
                    (try wp_auto)
                    iapply HΦ
                    iframe
                    unfold deleteRet
                    iright
                    isplitr
                    · ipureintro; exact ⟨rfl, Hb2 rfl⟩
                    unfold errIs
                    iexists p', st'
                    iframe #
                    ipureintro
                    exact ⟨rfl, Hst.2.1, Hst.2.2⟩
                · -- deleted at once
                  have hdel : ¬ (0 < sint.Z (graceOf r st dop.GracePeriodSeconds') ∨ st.meta.Finalizers' ≠ []) := fun h => h.elim (fun h => hg (by simpa using h)) (fun h => h (fin_eq hfs.1 hfs.2 Hif))
                  (try wp_auto)
                  rw [show k8s_io.apimachinery.pkg.watch.Deleted = #(EvTy.deleted.str) from rfl]
                  wp_apply (wp_record s γ L cfg r (σ0.tbl r) .deleted (σ0.rev + 1) y (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))) $$
                    [$Hfixed HM Hrel Hlog Hsl Hcap Hcs $Hy] as ⟨Hy, Htb⟩
                  · iunfold tableLocked
                    iexists M, sl, cs
                    iframe
                  ihave Htb := Htb $$ Hy
                  obtain ⟨un, hn1, hn2, hn3⟩ := hstuid
                  have hw := St.write_wf σ0 r ⟨.deleted, σ0.rev + 1, (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))⟩ σ0.uids hwf rfl hno
                    (by simp [hstres]) (by simp) (Nat.le_refl _) (by have := Huidlt; omega)
                    ⟨un, hn1, hn2, by simp [hn3]⟩
                  imod (au_write γ H σ0 (σ0.write r ⟨.deleted, σ0.rev + 1, (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))⟩ σ0.uids) (.ok true) (DeleteOut cfg.FailWrites' admin r ns name dop) (fun _ _ oc => iprop(∀ err, kd.meta.DeleteOptions.own opts dq dop ∗ deleteRet cfg.AmbiguousWrites' admin oc err -∗ Φ #err)) Hok hw.2 hw.1
                      (Or.inr (Or.inr ⟨hDE, st, hst, Or.inr ⟨hdts, (zero_val k8s_io.apimachinery.pkg.apis.«meta».v1.Time), (deleteApply_del r st dop.GracePeriodSeconds' σ0 (zero_val k8s_io.apimachinery.pkg.apis.«meta».v1.Time) hdel), rfl⟩⟩)))
                    $$ [$Hhist $HΦ] with ⟨Hhist, %Hok', HΦ⟩
                  (try wp_auto)
                  wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback Htb]
                  · iunfold lockInv
                    inext
                    iexists σ0.write r ⟨.deleted, σ0.rev + 1, (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))⟩ σ0.uids, H ++ [σ0]
                    iframe Hhist Hws
                    isplitl [Hrev Huids Hrvsm Hrc Hback Htb]
                    · iunfold srvLocked
                      simp only [named]
                      isplitl [Hrev]
                      · rw [show (St.write σ0 r ⟨.deleted, σ0.rev + 1, (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl]
                        iexact Hrev
                      isplitl [Huids]
                      · rw [show (St.write σ0 r ⟨.deleted, σ0.rev + 1, (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))⟩ σ0.uids).uids = σ0.uids from rfl]
                        iexact Huids
                      isplitl [Hrvsm]
                      · rw [show (St.write σ0 r ⟨.deleted, σ0.rev + 1, (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno]
                        iexact Hrvsm
                      isplitl [Hback Htb]
                      · iapply Hback
                        · ipureintro
                          intro r' hr'
                          rw [St.write_tbl, if_neg hr']
                        rw [St.write_tbl, if_pos rfl]
                        iexact Htb
                      isplitl [Hrc]
                      · rw [show (St.write σ0 r ⟨.deleted, σ0.rev + 1, (st.modMeta (fun m => { m with ResourceVersion' := rvStr (σ0.rev + 1) }))⟩ σ0.uids).rev = σ0.rev + 1 from rfl, hno,
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
                    unfold deleteRet
                    ileft
                    ipureintro; rfl
                  · (try wp_auto)
                    wp_apply +noauto wp_NewTimeoutError as %p' ⟨%st', %dv, Hp', -, %Hst⟩
                    ipersist Hp'
                    (try wp_auto)
                    iapply HΦ
                    iframe
                    unfold deleteRet
                    iright
                    isplitr
                    · ipureintro; exact ⟨rfl, Hb2 rfl⟩
                    unfold errIs
                    iexists p', st'
                    iframe #
                    ipureintro
                    exact ⟨rfl, Hst.2.1, Hst.2.2⟩
            · -- already being deleted: nothing changes
              have hdts : st.meta.DeletionTimestamp'.isSome := by
                cases h : st.meta.DeletionTimestamp' with
                | none => exact absurd (hdp.mpr h) Hif
                | some _ => rfl
              ihave Hrel := Hrelb $$ Hx
              imod (au_write_noop γ H σ0 (.ok false : Except ApiErr Bool) (DeleteOut cfg.FailWrites' admin r ns name dop) (fun _ _ oc => iprop(∀ err, kd.meta.DeleteOptions.own opts dq dop ∗ deleteRet cfg.AmbiguousWrites' admin oc err -∗ Φ #err))
                  (Or.inr (Or.inr ⟨hDE, st, hst, Or.inl ⟨hdts, rfl, rfl⟩⟩))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
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
              unfold deleteRet
              ileft
              ipureintro; rfl
  · -- a flagged failure
    imod (au_fail γ (.error .internal : Except ApiErr Bool) (DeleteOut cfg.FailWrites' admin r ns name dop)
        (fun _ _ oc => iprop(∀ err, kd.meta.DeleteOptions.own opts dq dop ∗ deleteRet cfg.AmbiguousWrites' admin oc err -∗ Φ #err))
        (fun σ => Or.inl ⟨Hb rfl, rfl, rfl⟩)) $$ HΦ with ⟨%σ, HΦ⟩
    (try wp_auto)
    wp_apply +noauto wp_NewInternalError as %p ⟨%st, Hp, %Hst⟩
    ipersist Hp
    (try wp_auto)
    iapply HΦ
    iframe
    unfold deleteRet
    unfold errIs
    iexists p, st
    iframe #
    ipureintro
    exact ⟨rfl, Hst.2.1, Hst.2.2⟩

end proof

end apimodel
end EtcdGrove
end Perennial
