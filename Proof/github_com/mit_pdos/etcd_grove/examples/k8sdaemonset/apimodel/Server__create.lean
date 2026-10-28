/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/Server__create.lean`.
Lean-first. The linearization point is the write under the lock (the checks before the lock,
which the request alone decides, and a flagged failure fire the caller's update at whatever
state; the checks under the lock, at the state the lock invariant holds).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Server__create
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Server__chance
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.copyObject
public import Spec.k8s_io.apimachinery.pkg.api.errors.NewInternalError
public import Spec.k8s_io.apimachinery.pkg.api.errors.NewBadRequest
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.rvString
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Server__nextRV
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Server__record
public import Spec.k8s_io.apimachinery.pkg.api.errors.NewAlreadyExists
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : apimodel.Assumptions]

/-- The name a create stores (the given one, or the generated one). -/
def createName (r : Res) (ns : GoString) (o : Obj) (σ : St) : GoString :=
  if (createNs r ns o).meta.Name' = go!"" then
    (createNs r ns o).meta.GenerateName' ++ rvStr (σ.rev + 1)
  else (createNs r ns o).meta.Name'

theorem createName_gen {r : Res} {ns : GoString} {o : Obj} {σ : St}
    (hnm : (createNs r ns o).meta.Name' = go!"") :
    (createNs r ns o).modMeta (fun m => { m with
        Name' := (createNs r ns o).meta.GenerateName' ++ rvStr (σ.rev + W64 1) }) =
      (createNs r ns o).modMeta (fun m => { m with Name' := createName r ns o σ }) := by
  unfold createName
  rw [if_pos hnm]
  rfl

theorem createName_named {r : Res} {ns : GoString} {o : Obj} {σ : St}
    (hnm : ¬ (createNs r ns o).meta.Name' = go!"") :
    createNs r ns o = (createNs r ns o).modMeta (fun m => { m with Name' := createName r ns o σ }) := by
  unfold createName
  rw [if_neg hnm]
  generalize createNs r ns o = o1
  cases o1 <;> rfl

theorem createErr_noname {r : Res} {ns : GoString} {o : Obj} {σ : St}
    (h1 : ¬ (r.namespaced = true ∧ o.meta.Namespace' ≠ go!"" ∧ o.meta.Namespace' ≠ ns))
    (h2 : (createNs r ns o).meta.ResourceVersion' = go!"")
    (h3 : (createNs r ns o).meta.Name' = go!"") (h4 : (createNs r ns o).meta.GenerateName' = go!"") :
    createErr r ns o σ = some .badRequest := by
  unfold createErr
  simp only []
  rw [if_neg h1, if_neg (fun h => h h2), if_pos ⟨h3, h4⟩]

theorem createErr_exists {r : Res} {ns : GoString} {o : Obj} {σ : St}
    (h1 : ¬ (r.namespaced = true ∧ o.meta.Namespace' ≠ go!"" ∧ o.meta.Namespace' ≠ ns))
    (h2 : (createNs r ns o).meta.ResourceVersion' = go!"")
    (h3 : ¬ ((createNs r ns o).meta.Name' = go!"" ∧ (createNs r ns o).meta.GenerateName' = go!""))
    (h4 : ((σ.tbl r).objs !! mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ)).isSome) :
    createErr r ns o σ = some .alreadyExists := by
  unfold createErr
  simp only []
  rw [if_neg h1, if_neg (fun h => h h2), if_neg h3]
  unfold createName at h4
  rw [if_pos h4]

theorem createErr_none {r : Res} {ns : GoString} {o : Obj} {σ : St}
    (h1 : ¬ (r.namespaced = true ∧ o.meta.Namespace' ≠ go!"" ∧ o.meta.Namespace' ≠ ns))
    (h2 : (createNs r ns o).meta.ResourceVersion' = go!"")
    (h3 : ¬ ((createNs r ns o).meta.Name' = go!"" ∧ (createNs r ns o).meta.GenerateName' = go!""))
    (h4 : (σ.tbl r).objs !! mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ) = none) :
    createErr r ns o σ = none := by
  unfold createErr
  simp only []
  rw [if_neg h1, if_neg (fun h => h h2), if_neg h3]
  unfold createName at h4
  rw [h4]
  rfl

/-- The object a create stores, as the calls build it. -/
theorem createApply_fst (r : Res) (ns : GoString) (o : Obj) (σ : St)
    (tm : k8s_io.apimachinery.pkg.apis.«meta».v1.Time) :
    (prepareD ((((createNs r ns o).modMeta (fun m => { m with Name' := createName r ns o σ })).modMeta
        (fun m => { m with UID' := go!"uid-" ++ rvStr (σ.uids + W64 1) })).modMeta
        (fun m => { m with CreationTimestamp' := tm }))).modMeta
        (fun m => { m with ResourceVersion' := rvStr (σ.rev + W64 1) }) =
      (createApply r ns o σ tm).1 := by
  unfold createApply createName
  simp only []
  generalize createNs r ns o = o1
  cases o1 <;> rfl

theorem createApply_snd (r : Res) (ns : GoString) (o : Obj) (σ : St)
    (tm : k8s_io.apimachinery.pkg.apis.«meta».v1.Time) :
    (createApply r ns o σ tm).2 =
      σ.write r ⟨.added, σ.rev + 1, (createApply r ns o σ tm).1⟩ (σ.uids + 1) := rfl

/-- A resource's create strategy, called. -/
theorem wp_prepare_call (r : Res) (f : GoFunc) (x : GoInterface) (o : Obj) :
    {{ prepareOk (GF := GF) r f ∗ objAt x (DFrac.own 1) o ∗ ⌜o.res = r⌝ }}
      (App (Val #f) (Val #x))
    {{ RET #(); objAt x (DFrac.own 1) (prepareD o) }} := by
  wp_start as ⟨#H, Hx, %h⟩
  iunfold prepareOk at H
  ihave #Hp := H $$ %x %o %h
  wp_apply Hp $$ Hx as Hx
  iapply HΦ
  iexact Hx

theorem createErr_ns {r : Res} {ns : GoString} {o : Obj} {σ : St}
    (h : r.namespaced = true ∧ o.meta.Namespace' ≠ go!"" ∧ o.meta.Namespace' ≠ ns) :
    createErr r ns o σ = some .badRequest := by
  unfold createErr
  rw [if_pos h]

theorem createErr_rv {r : Res} {ns : GoString} {o : Obj} {σ : St}
    (h1 : ¬ (r.namespaced = true ∧ o.meta.Namespace' ≠ go!"" ∧ o.meta.Namespace' ≠ ns))
    (h2 : ¬ (createNs r ns o).meta.ResourceVersion' = go!"") :
    createErr r ns o σ = some .badRequest := by
  unfold createErr
  simp only []
  rw [if_neg h1, if_pos h2]

theorem Server.create.wp_proof
    (wp_chance : Server.chance.spec (GF := GF) (hG := hG))
    (wp_copyObject : copyObject.spec (GF := GF) (hG := hG))
    (wp_rvString : rvString.spec (GF := GF) (hG := hG))
    (wp_nextRV : Server.nextRV.spec (GF := GF) (hG := hG))
    (wp_record : Server.record.spec (GF := GF) (hG := hG))
    (wp_GetNamespace : metav1.ObjectMeta.GetNamespace.spec (GF := GF) (hG := hG))
    (wp_SetNamespace : metav1.ObjectMeta.SetNamespace.spec (GF := GF) (hG := hG))
    (wp_GetName : metav1.ObjectMeta.GetName.spec (GF := GF) (hG := hG))
    (wp_SetName : metav1.ObjectMeta.SetName.spec (GF := GF) (hG := hG))
    (wp_GetGenerateName : metav1.ObjectMeta.GetGenerateName.spec (GF := GF) (hG := hG))
    (wp_GetResourceVersion : metav1.ObjectMeta.GetResourceVersion.spec (GF := GF) (hG := hG))
    (wp_SetResourceVersion : metav1.ObjectMeta.SetResourceVersion.spec (GF := GF) (hG := hG))
    (wp_SetUID : metav1.ObjectMeta.SetUID.spec (GF := GF) (hG := hG))
    (wp_SetCreationTimestamp : metav1.ObjectMeta.SetCreationTimestamp.spec (GF := GF) (hG := hG))
    (wp_Now : metav1.Now.spec (GF := GF) (hG := hG))
    (wp_NewInternalError : apierrors.NewInternalError.spec (GF := GF) (hG := hG))
    (wp_NewBadRequest : apierrors.NewBadRequest.spec (GF := GF) (hG := hG))
    (wp_NewAlreadyExists : apierrors.NewAlreadyExists.spec (GF := GF) (hG := hG))
    (wp_NewTimeoutError : apierrors.NewTimeoutError.spec (GF := GF) (hG := hG))
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    Server.create.spec (GF := GF) (hG := hG) := by
  intro _ s γ cfg r t ns inp dq o prep admin
  wp_start as ⟨#Hs, #Ht, #Hprep, Hinp, %Hres⟩
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
  · wp_auto
    wp_apply wp_copyObject $$ Hinp as %y ⟨Hinp, Hy⟩
    cases hnsr : r.namespaced
    · (try simp only [Bool.false_eq_true, ↓reduceIte])
      wp_auto
      -- not namespaced: the namespace cleared
      wp_apply (objAt_SetNamespace wp_SetNamespace y o _) $$ Hy as Hy
      have ho1 : o.modMeta (fun m => { m with Namespace' := go!"" }) = createNs r ns o := by
        unfold createNs; simp [hnsr]
      have hc1 : ¬ (r.namespaced = true ∧ o.meta.Namespace' ≠ go!"" ∧ o.meta.Namespace' ≠ ns) := by
        simp [hnsr]
      wp_apply (objAt_GetResourceVersion wp_GetResourceVersion y _) $$ Hy as Hy
      wp_if_destruct
      · -- no resource version: under the lock
        ihave Hy := objAt_cast ho1 $$ Hy
        rw [ho1] at Hif
        have hrv0 := Hif
        wp_apply wp_Lock $$ [$Hmu] as ⟨Hown, Hinv⟩
        iunfold lockInv at Hinv
        icases Hinv with ⟨%σ0, %H, Hlk, Hhist, %Hok, Hws⟩
        iNamed Hlk
        have hwf := histOk_last_wf Hok
        icases tablesLocked_acc L σ0 r $$ Htbls with ⟨Ht0, Hback⟩
        iunfold tableLocked at Ht0
        icases Ht0 with ⟨%M, %sl, %cs, HM, Hrel, Hlog, Hsl, Hcap, Hcs⟩
        wp_apply (objAt_GetName wp_GetName y _) $$ Hy as Hy
        wp_if_destruct
        · -- no name
          have hnm := Hif
          wp_apply (objAt_GetGenerateName wp_GetGenerateName y _) $$ Hy as Hy
          wp_if_destruct
          · -- neither a name nor a generated name
            imod (au_write_noop γ H σ0 (.error .badRequest : Except ApiErr (Bool × Obj))
                (CreateOut cfg.FailWrites' admin r ns o) (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗ Φ (PairV #x #err)))
                (Or.inr (Or.inl ⟨.badRequest, createErr_noname hc1 hrv0 hnm Hif, rfl, rfl⟩))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
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
          · have hgn := Hif
            wp_apply (objAt_GetGenerateName wp_GetGenerateName y _) $$ Hy as Hy
            wp_apply wp_rvString $$ [$Hstrconv]
            wp_apply (objAt_SetName wp_SetName y _) $$ Hy as Hy
            have hnmo : ¬ ((createNs r ns o).meta.Name' = go!"" ∧ (createNs r ns o).meta.GenerateName' = go!"") :=
              fun h => hgn h.2
            ihave Hy := objAt_cast (createName_gen (σ := σ0) hnm) $$ Hy
            wp_apply (objAt_GetNamespace wp_GetNamespace y _) $$ Hy as Hy
            wp_apply (objAt_GetName wp_GetName y _) $$ Hy as Hy
            (try wp_auto)
            (try simp only [Obj.meta_modMeta])
            wp_apply (wp_map_lookup2 k8s_io.apimachinery.pkg.types.NamespacedName.ty apimodel.object.ty
              (L.tbl r).objs M (mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0)) (DFrac.own 1)) $$ HM as HM
            ihave %hd := objsRel_dom M (σ0.tbl r).objs (mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0)) $$ Hrel
            cases hk : M !! mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0) with
            | some x =>
              have hex : ((σ0.tbl r).objs !! mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0)).isSome :=
                hd.mp (by simp [hk])
              simp only [Option.isSome_some]
              (try wp_auto)
              imod (au_write_noop γ H σ0 (.error .alreadyExists : Except ApiErr (Bool × Obj))
                  (CreateOut cfg.FailWrites' admin r ns o) (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗ Φ (PairV #x #err)))
                  (Or.inr (Or.inl ⟨.alreadyExists, createErr_exists hc1 hrv0 hnmo hex, rfl, rfl⟩))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
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
              wp_apply +noauto wp_NewAlreadyExists as %p ⟨%st, Hp, %Hst⟩
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
            | none =>
              have hnone : (σ0.tbl r).objs !! mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0) = none := by
                cases h' : (σ0.tbl r).objs !! mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0) with
                | none => rfl
                | some _ => simp [h', hk] at hd
              simp only [Option.isSome_none]
              (try wp_auto)
              wp_apply wp_rvString $$ [$Hstrconv]
              (try wp_auto)
              wp_apply (objAt_SetUID wp_SetUID y _ _) $$ Hy as Hy
              wp_apply wp_Now $$ [$Htime] as %tm -
              wp_apply (objAt_SetCreationTimestamp wp_SetCreationTimestamp y _ _) $$ Hy as Hy
              (try wp_auto)
              wp_apply (wp_prepare_call r prep y _) $$ [$Hprep $Hy] as Hy
              · ipureintro
                simp [Obj.modMeta, createNs_res, Hres]
              wp_apply (wp_nextRV s L.rvs σ0.rev) $$ [$Hstrconv $Hrev $Hrvs $Hrvsm $Hrc] as ⟨Hrev, Hrvsm, Hrc, %hno⟩
              · ipureintro; exact ⟨hwf.rev_pos, Hbound⟩
              (try wp_auto)
              wp_apply (objAt_SetResourceVersion wp_SetResourceVersion y _ _) $$ Hy as Hy
              ihave Hy := objAt_cast (createApply_fst r ns o σ0 tm) $$ Hy
              rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl] at hno
              rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl, show σ0.uids + W64 1 = σ0.uids + 1 from rfl]
              have hres3 : (createApply r ns o σ0 tm).1.res = r := by
                rw [← createApply_fst]; simp [prepareD_res, createNs_res, Hres]
              have hRV3 : (createApply r ns o σ0 tm).1.meta.ResourceVersion' = rvStr (σ0.rev + 1) := by
                rw [← createApply_fst]; simp
              have huid3 : (createApply r ns o σ0 tm).1.meta.UID' = go!"uid-" ++ rvStr (σ0.uids + 1) := by
                rw [← createApply_fst]; simp [prepareD_uid]
              have hsnd := createApply_snd r ns o σ0 tm
              have hCE := createErr_none hc1 hrv0 hnmo hnone
              generalize hO3 : (createApply r ns o σ0 tm).1 = o3 at hres3 hRV3 huid3 hsnd ⊢
              (try wp_auto)
              rw [show k8s_io.apimachinery.pkg.watch.Added = #(EvTy.added.str) from rfl]
              wp_apply (wp_record s γ L cfg r (σ0.tbl r) .added (σ0.rev + 1) y o3) $$
                [$Hfixed HM Hrel Hlog Hsl Hcap Hcs $Hy] as ⟨Hy, Htb⟩
              · iunfold tableLocked
                iexists M, sl, cs
                iframe
              wp_apply wp_copyObject $$ Hy as %z ⟨Hy, Hz⟩
              ihave Htb := Htb $$ Hy
              -- the write's linearization point
              have huid1 : (σ0.uids + 1).toNat = σ0.uids.toNat + 1 := by
                have h1 := Huidlt
                have h2 := σ0.rev.isLt
                word
              have hw := St.write_wf σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1) hwf rfl
                hno hres3 hRV3 (by rw [huid1]; omega) (by rw [huid1]; omega)
                ⟨σ0.uids + 1, by rw [huid1]; omega, Nat.le_refl _, huid3⟩
              imod (au_write γ H σ0 (σ0.write r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1))
                  (.ok (true, o3)) (CreateOut cfg.FailWrites' admin r ns o)
                  (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗
                    Φ (PairV #x #err))) Hok hw.2 hw.1
                  (Or.inr (Or.inr ⟨hCE, tm, hsnd, by rw [hO3]⟩)))
                $$ [$Hhist $HΦ] with ⟨Hhist, %Hok', HΦ⟩
              (try wp_auto)
              wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback Htb]
              · iunfold lockInv
                inext
                iexists σ0.write r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1), H ++ [σ0]
                iframe Hhist Hws
                isplitl [Hrev Huids Hrvsm Hrc Hback Htb]
                · iunfold srvLocked
                  simp only [named]
                  isplitl [Hrev]
                  · rw [show (St.write σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1)).rev =
                      σ0.rev + 1 from rfl]
                    iexact Hrev
                  isplitl [Huids]
                  · rw [show (St.write σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1)).uids =
                      σ0.uids + 1 from rfl]
                    iexact Huids
                  isplitl [Hrvsm]
                  · rw [show (St.write σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1)).rev =
                      σ0.rev + 1 from rfl, hno]
                    iexact Hrvsm
                  isplitl [Hback Htb]
                  · iapply Hback
                    · ipureintro
                      intro r' hr'
                      rw [St.write_tbl, if_neg hr']
                    rw [St.write_tbl, if_pos rfl]
                    iapply Htb
                  isplitl [Hrc]
                  · rw [show (St.write σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1)).rev =
                      σ0.rev + 1 from rfl, hno, Nat.add_sub_cancel]
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
                wp_apply +noauto wp_NewTimeoutError as %p ⟨%st, %dv, Hp, -, %Hst⟩
                ipersist Hp
                (try wp_auto)
                iapply HΦ
                iframe
                unfold writeRetI
                iright
                isplitr
                · ipureintro; exact ⟨rfl, Hb2 rfl, rfl⟩
                unfold errIs
                iexists p, st
                iframe #
                ipureintro
                exact ⟨rfl, Hst.2.1, Hst.2.2⟩
        · have hnm := Hif
          have hnmo : ¬ ((createNs r ns o).meta.Name' = go!"" ∧ (createNs r ns o).meta.GenerateName' = go!"") :=
            fun h => hnm h.1
          ihave Hy := objAt_cast (createName_named (σ := σ0) hnm) $$ Hy
          wp_apply (objAt_GetNamespace wp_GetNamespace y _) $$ Hy as Hy
          wp_apply (objAt_GetName wp_GetName y _) $$ Hy as Hy
          (try wp_auto)
          (try simp only [Obj.meta_modMeta])
          wp_apply (wp_map_lookup2 k8s_io.apimachinery.pkg.types.NamespacedName.ty apimodel.object.ty
            (L.tbl r).objs M (mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0)) (DFrac.own 1)) $$ HM as HM
          ihave %hd := objsRel_dom M (σ0.tbl r).objs (mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0)) $$ Hrel
          cases hk : M !! mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0) with
          | some x =>
            have hex : ((σ0.tbl r).objs !! mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0)).isSome :=
              hd.mp (by simp [hk])
            simp only [Option.isSome_some]
            (try wp_auto)
            imod (au_write_noop γ H σ0 (.error .alreadyExists : Except ApiErr (Bool × Obj))
                (CreateOut cfg.FailWrites' admin r ns o) (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗ Φ (PairV #x #err)))
                (Or.inr (Or.inl ⟨.alreadyExists, createErr_exists hc1 hrv0 hnmo hex, rfl, rfl⟩))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
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
            wp_apply +noauto wp_NewAlreadyExists as %p ⟨%st, Hp, %Hst⟩
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
          | none =>
            have hnone : (σ0.tbl r).objs !! mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0) = none := by
              cases h' : (σ0.tbl r).objs !! mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0) with
              | none => rfl
              | some _ => simp [h', hk] at hd
            simp only [Option.isSome_none]
            (try wp_auto)
            wp_apply wp_rvString $$ [$Hstrconv]
            (try wp_auto)
            wp_apply (objAt_SetUID wp_SetUID y _ _) $$ Hy as Hy
            wp_apply wp_Now $$ [$Htime] as %tm -
            wp_apply (objAt_SetCreationTimestamp wp_SetCreationTimestamp y _ _) $$ Hy as Hy
            (try wp_auto)
            wp_apply (wp_prepare_call r prep y _) $$ [$Hprep $Hy] as Hy
            · ipureintro
              simp [Obj.modMeta, createNs_res, Hres]
            wp_apply (wp_nextRV s L.rvs σ0.rev) $$ [$Hstrconv $Hrev $Hrvs $Hrvsm $Hrc] as ⟨Hrev, Hrvsm, Hrc, %hno⟩
            · ipureintro; exact ⟨hwf.rev_pos, Hbound⟩
            (try wp_auto)
            wp_apply (objAt_SetResourceVersion wp_SetResourceVersion y _ _) $$ Hy as Hy
            ihave Hy := objAt_cast (createApply_fst r ns o σ0 tm) $$ Hy
            rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl] at hno
            rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl, show σ0.uids + W64 1 = σ0.uids + 1 from rfl]
            have hres3 : (createApply r ns o σ0 tm).1.res = r := by
              rw [← createApply_fst]; simp [prepareD_res, createNs_res, Hres]
            have hRV3 : (createApply r ns o σ0 tm).1.meta.ResourceVersion' = rvStr (σ0.rev + 1) := by
              rw [← createApply_fst]; simp
            have huid3 : (createApply r ns o σ0 tm).1.meta.UID' = go!"uid-" ++ rvStr (σ0.uids + 1) := by
              rw [← createApply_fst]; simp [prepareD_uid]
            have hsnd := createApply_snd r ns o σ0 tm
            have hCE := createErr_none hc1 hrv0 hnmo hnone
            generalize hO3 : (createApply r ns o σ0 tm).1 = o3 at hres3 hRV3 huid3 hsnd ⊢
            (try wp_auto)
            rw [show k8s_io.apimachinery.pkg.watch.Added = #(EvTy.added.str) from rfl]
            wp_apply (wp_record s γ L cfg r (σ0.tbl r) .added (σ0.rev + 1) y o3) $$
              [$Hfixed HM Hrel Hlog Hsl Hcap Hcs $Hy] as ⟨Hy, Htb⟩
            · iunfold tableLocked
              iexists M, sl, cs
              iframe
            wp_apply wp_copyObject $$ Hy as %z ⟨Hy, Hz⟩
            ihave Htb := Htb $$ Hy
            -- the write's linearization point
            have huid1 : (σ0.uids + 1).toNat = σ0.uids.toNat + 1 := by
              have h1 := Huidlt
              have h2 := σ0.rev.isLt
              word
            have hw := St.write_wf σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1) hwf rfl
              hno hres3 hRV3 (by rw [huid1]; omega) (by rw [huid1]; omega)
              ⟨σ0.uids + 1, by rw [huid1]; omega, Nat.le_refl _, huid3⟩
            imod (au_write γ H σ0 (σ0.write r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1))
                (.ok (true, o3)) (CreateOut cfg.FailWrites' admin r ns o)
                (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗
                  Φ (PairV #x #err))) Hok hw.2 hw.1
                (Or.inr (Or.inr ⟨hCE, tm, hsnd, by rw [hO3]⟩)))
              $$ [$Hhist $HΦ] with ⟨Hhist, %Hok', HΦ⟩
            (try wp_auto)
            wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback Htb]
            · iunfold lockInv
              inext
              iexists σ0.write r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1), H ++ [σ0]
              iframe Hhist Hws
              isplitl [Hrev Huids Hrvsm Hrc Hback Htb]
              · iunfold srvLocked
                simp only [named]
                isplitl [Hrev]
                · rw [show (St.write σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1)).rev =
                    σ0.rev + 1 from rfl]
                  iexact Hrev
                isplitl [Huids]
                · rw [show (St.write σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1)).uids =
                    σ0.uids + 1 from rfl]
                  iexact Huids
                isplitl [Hrvsm]
                · rw [show (St.write σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1)).rev =
                    σ0.rev + 1 from rfl, hno]
                  iexact Hrvsm
                isplitl [Hback Htb]
                · iapply Hback
                  · ipureintro
                    intro r' hr'
                    rw [St.write_tbl, if_neg hr']
                  rw [St.write_tbl, if_pos rfl]
                  iapply Htb
                isplitl [Hrc]
                · rw [show (St.write σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1)).rev =
                    σ0.rev + 1 from rfl, hno, Nat.add_sub_cancel]
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
              wp_apply +noauto wp_NewTimeoutError as %p ⟨%st, %dv, Hp, -, %Hst⟩
              ipersist Hp
              (try wp_auto)
              iapply HΦ
              iframe
              unfold writeRetI
              iright
              isplitr
              · ipureintro; exact ⟨rfl, Hb2 rfl, rfl⟩
              unfold errIs
              iexists p, st
              iframe #
              ipureintro
              exact ⟨rfl, Hst.2.1, Hst.2.2⟩
      · -- a resource version set
        imod (au_fail γ (.error .badRequest : Except ApiErr (Bool × Obj)) (CreateOut cfg.FailWrites' admin r ns o)
            (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗ Φ (PairV #x #err)))
            (fun σ => Or.inr (Or.inl ⟨.badRequest, by exact createErr_rv hc1 (ho1 ▸ Hif), rfl, rfl⟩))) $$ HΦ with ⟨%σ, HΦ⟩
        (try wp_auto)
        wp_apply +noauto wp_NewBadRequest as %p ⟨%st, Hp, %Hst⟩
        ipersist Hp
        wp_auto
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
    · wp_auto
      wp_apply (objAt_GetNamespace wp_GetNamespace y o) $$ Hy as Hy
      wp_if_destruct
      · -- no namespace: the request's
        have hnsE := Hif
        wp_apply (objAt_SetNamespace wp_SetNamespace y o _) $$ Hy as Hy
        have ho1 : o.modMeta (fun m => { m with Namespace' := ns }) = createNs r ns o := by
          unfold createNs; simp [hnsr, Hif]
        have hc1 : ¬ (r.namespaced = true ∧ o.meta.Namespace' ≠ go!"" ∧ o.meta.Namespace' ≠ ns) := by
          simp [hnsE]
        wp_apply (objAt_GetResourceVersion wp_GetResourceVersion y _) $$ Hy as Hy
        wp_if_destruct
        · -- no resource version: under the lock
          ihave Hy := objAt_cast ho1 $$ Hy
          rw [ho1] at Hif
          have hrv0 := Hif
          wp_apply wp_Lock $$ [$Hmu] as ⟨Hown, Hinv⟩
          iunfold lockInv at Hinv
          icases Hinv with ⟨%σ0, %H, Hlk, Hhist, %Hok, Hws⟩
          iNamed Hlk
          have hwf := histOk_last_wf Hok
          icases tablesLocked_acc L σ0 r $$ Htbls with ⟨Ht0, Hback⟩
          iunfold tableLocked at Ht0
          icases Ht0 with ⟨%M, %sl, %cs, HM, Hrel, Hlog, Hsl, Hcap, Hcs⟩
          wp_apply (objAt_GetName wp_GetName y _) $$ Hy as Hy
          wp_if_destruct
          · -- no name
            have hnm := Hif
            wp_apply (objAt_GetGenerateName wp_GetGenerateName y _) $$ Hy as Hy
            wp_if_destruct
            · -- neither a name nor a generated name
              imod (au_write_noop γ H σ0 (.error .badRequest : Except ApiErr (Bool × Obj))
                  (CreateOut cfg.FailWrites' admin r ns o) (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗ Φ (PairV #x #err)))
                  (Or.inr (Or.inl ⟨.badRequest, createErr_noname hc1 hrv0 hnm Hif, rfl, rfl⟩))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
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
            · have hgn := Hif
              wp_apply (objAt_GetGenerateName wp_GetGenerateName y _) $$ Hy as Hy
              wp_apply wp_rvString $$ [$Hstrconv]
              wp_apply (objAt_SetName wp_SetName y _) $$ Hy as Hy
              have hnmo : ¬ ((createNs r ns o).meta.Name' = go!"" ∧ (createNs r ns o).meta.GenerateName' = go!"") :=
                fun h => hgn h.2
              ihave Hy := objAt_cast (createName_gen (σ := σ0) hnm) $$ Hy
              wp_apply (objAt_GetNamespace wp_GetNamespace y _) $$ Hy as Hy
              wp_apply (objAt_GetName wp_GetName y _) $$ Hy as Hy
              (try wp_auto)
              (try simp only [Obj.meta_modMeta])
              wp_apply (wp_map_lookup2 k8s_io.apimachinery.pkg.types.NamespacedName.ty apimodel.object.ty
                (L.tbl r).objs M (mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0)) (DFrac.own 1)) $$ HM as HM
              ihave %hd := objsRel_dom M (σ0.tbl r).objs (mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0)) $$ Hrel
              cases hk : M !! mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0) with
              | some x =>
                have hex : ((σ0.tbl r).objs !! mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0)).isSome :=
                  hd.mp (by simp [hk])
                simp only [Option.isSome_some]
                (try wp_auto)
                imod (au_write_noop γ H σ0 (.error .alreadyExists : Except ApiErr (Bool × Obj))
                    (CreateOut cfg.FailWrites' admin r ns o) (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗ Φ (PairV #x #err)))
                    (Or.inr (Or.inl ⟨.alreadyExists, createErr_exists hc1 hrv0 hnmo hex, rfl, rfl⟩))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
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
                wp_apply +noauto wp_NewAlreadyExists as %p ⟨%st, Hp, %Hst⟩
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
              | none =>
                have hnone : (σ0.tbl r).objs !! mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0) = none := by
                  cases h' : (σ0.tbl r).objs !! mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0) with
                  | none => rfl
                  | some _ => simp [h', hk] at hd
                simp only [Option.isSome_none]
                (try wp_auto)
                wp_apply wp_rvString $$ [$Hstrconv]
                (try wp_auto)
                wp_apply (objAt_SetUID wp_SetUID y _ _) $$ Hy as Hy
                wp_apply wp_Now $$ [$Htime] as %tm -
                wp_apply (objAt_SetCreationTimestamp wp_SetCreationTimestamp y _ _) $$ Hy as Hy
                (try wp_auto)
                wp_apply (wp_prepare_call r prep y _) $$ [$Hprep $Hy] as Hy
                · ipureintro
                  simp [Obj.modMeta, createNs_res, Hres]
                wp_apply (wp_nextRV s L.rvs σ0.rev) $$ [$Hstrconv $Hrev $Hrvs $Hrvsm $Hrc] as ⟨Hrev, Hrvsm, Hrc, %hno⟩
                · ipureintro; exact ⟨hwf.rev_pos, Hbound⟩
                (try wp_auto)
                wp_apply (objAt_SetResourceVersion wp_SetResourceVersion y _ _) $$ Hy as Hy
                ihave Hy := objAt_cast (createApply_fst r ns o σ0 tm) $$ Hy
                rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl] at hno
                rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl, show σ0.uids + W64 1 = σ0.uids + 1 from rfl]
                have hres3 : (createApply r ns o σ0 tm).1.res = r := by
                  rw [← createApply_fst]; simp [prepareD_res, createNs_res, Hres]
                have hRV3 : (createApply r ns o σ0 tm).1.meta.ResourceVersion' = rvStr (σ0.rev + 1) := by
                  rw [← createApply_fst]; simp
                have huid3 : (createApply r ns o σ0 tm).1.meta.UID' = go!"uid-" ++ rvStr (σ0.uids + 1) := by
                  rw [← createApply_fst]; simp [prepareD_uid]
                have hsnd := createApply_snd r ns o σ0 tm
                have hCE := createErr_none hc1 hrv0 hnmo hnone
                generalize hO3 : (createApply r ns o σ0 tm).1 = o3 at hres3 hRV3 huid3 hsnd ⊢
                (try wp_auto)
                rw [show k8s_io.apimachinery.pkg.watch.Added = #(EvTy.added.str) from rfl]
                wp_apply (wp_record s γ L cfg r (σ0.tbl r) .added (σ0.rev + 1) y o3) $$
                  [$Hfixed HM Hrel Hlog Hsl Hcap Hcs $Hy] as ⟨Hy, Htb⟩
                · iunfold tableLocked
                  iexists M, sl, cs
                  iframe
                wp_apply wp_copyObject $$ Hy as %z ⟨Hy, Hz⟩
                ihave Htb := Htb $$ Hy
                -- the write's linearization point
                have huid1 : (σ0.uids + 1).toNat = σ0.uids.toNat + 1 := by
                  have h1 := Huidlt
                  have h2 := σ0.rev.isLt
                  word
                have hw := St.write_wf σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1) hwf rfl
                  hno hres3 hRV3 (by rw [huid1]; omega) (by rw [huid1]; omega)
                  ⟨σ0.uids + 1, by rw [huid1]; omega, Nat.le_refl _, huid3⟩
                imod (au_write γ H σ0 (σ0.write r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1))
                    (.ok (true, o3)) (CreateOut cfg.FailWrites' admin r ns o)
                    (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗
                      Φ (PairV #x #err))) Hok hw.2 hw.1
                    (Or.inr (Or.inr ⟨hCE, tm, hsnd, by rw [hO3]⟩)))
                  $$ [$Hhist $HΦ] with ⟨Hhist, %Hok', HΦ⟩
                (try wp_auto)
                wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback Htb]
                · iunfold lockInv
                  inext
                  iexists σ0.write r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1), H ++ [σ0]
                  iframe Hhist Hws
                  isplitl [Hrev Huids Hrvsm Hrc Hback Htb]
                  · iunfold srvLocked
                    simp only [named]
                    isplitl [Hrev]
                    · rw [show (St.write σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1)).rev =
                        σ0.rev + 1 from rfl]
                      iexact Hrev
                    isplitl [Huids]
                    · rw [show (St.write σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1)).uids =
                        σ0.uids + 1 from rfl]
                      iexact Huids
                    isplitl [Hrvsm]
                    · rw [show (St.write σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1)).rev =
                        σ0.rev + 1 from rfl, hno]
                      iexact Hrvsm
                    isplitl [Hback Htb]
                    · iapply Hback
                      · ipureintro
                        intro r' hr'
                        rw [St.write_tbl, if_neg hr']
                      rw [St.write_tbl, if_pos rfl]
                      iapply Htb
                    isplitl [Hrc]
                    · rw [show (St.write σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1)).rev =
                        σ0.rev + 1 from rfl, hno, Nat.add_sub_cancel]
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
                  wp_apply +noauto wp_NewTimeoutError as %p ⟨%st, %dv, Hp, -, %Hst⟩
                  ipersist Hp
                  (try wp_auto)
                  iapply HΦ
                  iframe
                  unfold writeRetI
                  iright
                  isplitr
                  · ipureintro; exact ⟨rfl, Hb2 rfl, rfl⟩
                  unfold errIs
                  iexists p, st
                  iframe #
                  ipureintro
                  exact ⟨rfl, Hst.2.1, Hst.2.2⟩
          · have hnm := Hif
            have hnmo : ¬ ((createNs r ns o).meta.Name' = go!"" ∧ (createNs r ns o).meta.GenerateName' = go!"") :=
              fun h => hnm h.1
            ihave Hy := objAt_cast (createName_named (σ := σ0) hnm) $$ Hy
            wp_apply (objAt_GetNamespace wp_GetNamespace y _) $$ Hy as Hy
            wp_apply (objAt_GetName wp_GetName y _) $$ Hy as Hy
            (try wp_auto)
            (try simp only [Obj.meta_modMeta])
            wp_apply (wp_map_lookup2 k8s_io.apimachinery.pkg.types.NamespacedName.ty apimodel.object.ty
              (L.tbl r).objs M (mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0)) (DFrac.own 1)) $$ HM as HM
            ihave %hd := objsRel_dom M (σ0.tbl r).objs (mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0)) $$ Hrel
            cases hk : M !! mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0) with
            | some x =>
              have hex : ((σ0.tbl r).objs !! mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0)).isSome :=
                hd.mp (by simp [hk])
              simp only [Option.isSome_some]
              (try wp_auto)
              imod (au_write_noop γ H σ0 (.error .alreadyExists : Except ApiErr (Bool × Obj))
                  (CreateOut cfg.FailWrites' admin r ns o) (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗ Φ (PairV #x #err)))
                  (Or.inr (Or.inl ⟨.alreadyExists, createErr_exists hc1 hrv0 hnmo hex, rfl, rfl⟩))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
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
              wp_apply +noauto wp_NewAlreadyExists as %p ⟨%st, Hp, %Hst⟩
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
            | none =>
              have hnone : (σ0.tbl r).objs !! mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0) = none := by
                cases h' : (σ0.tbl r).objs !! mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0) with
                | none => rfl
                | some _ => simp [h', hk] at hd
              simp only [Option.isSome_none]
              (try wp_auto)
              wp_apply wp_rvString $$ [$Hstrconv]
              (try wp_auto)
              wp_apply (objAt_SetUID wp_SetUID y _ _) $$ Hy as Hy
              wp_apply wp_Now $$ [$Htime] as %tm -
              wp_apply (objAt_SetCreationTimestamp wp_SetCreationTimestamp y _ _) $$ Hy as Hy
              (try wp_auto)
              wp_apply (wp_prepare_call r prep y _) $$ [$Hprep $Hy] as Hy
              · ipureintro
                simp [Obj.modMeta, createNs_res, Hres]
              wp_apply (wp_nextRV s L.rvs σ0.rev) $$ [$Hstrconv $Hrev $Hrvs $Hrvsm $Hrc] as ⟨Hrev, Hrvsm, Hrc, %hno⟩
              · ipureintro; exact ⟨hwf.rev_pos, Hbound⟩
              (try wp_auto)
              wp_apply (objAt_SetResourceVersion wp_SetResourceVersion y _ _) $$ Hy as Hy
              ihave Hy := objAt_cast (createApply_fst r ns o σ0 tm) $$ Hy
              rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl] at hno
              rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl, show σ0.uids + W64 1 = σ0.uids + 1 from rfl]
              have hres3 : (createApply r ns o σ0 tm).1.res = r := by
                rw [← createApply_fst]; simp [prepareD_res, createNs_res, Hres]
              have hRV3 : (createApply r ns o σ0 tm).1.meta.ResourceVersion' = rvStr (σ0.rev + 1) := by
                rw [← createApply_fst]; simp
              have huid3 : (createApply r ns o σ0 tm).1.meta.UID' = go!"uid-" ++ rvStr (σ0.uids + 1) := by
                rw [← createApply_fst]; simp [prepareD_uid]
              have hsnd := createApply_snd r ns o σ0 tm
              have hCE := createErr_none hc1 hrv0 hnmo hnone
              generalize hO3 : (createApply r ns o σ0 tm).1 = o3 at hres3 hRV3 huid3 hsnd ⊢
              (try wp_auto)
              rw [show k8s_io.apimachinery.pkg.watch.Added = #(EvTy.added.str) from rfl]
              wp_apply (wp_record s γ L cfg r (σ0.tbl r) .added (σ0.rev + 1) y o3) $$
                [$Hfixed HM Hrel Hlog Hsl Hcap Hcs $Hy] as ⟨Hy, Htb⟩
              · iunfold tableLocked
                iexists M, sl, cs
                iframe
              wp_apply wp_copyObject $$ Hy as %z ⟨Hy, Hz⟩
              ihave Htb := Htb $$ Hy
              -- the write's linearization point
              have huid1 : (σ0.uids + 1).toNat = σ0.uids.toNat + 1 := by
                have h1 := Huidlt
                have h2 := σ0.rev.isLt
                word
              have hw := St.write_wf σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1) hwf rfl
                hno hres3 hRV3 (by rw [huid1]; omega) (by rw [huid1]; omega)
                ⟨σ0.uids + 1, by rw [huid1]; omega, Nat.le_refl _, huid3⟩
              imod (au_write γ H σ0 (σ0.write r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1))
                  (.ok (true, o3)) (CreateOut cfg.FailWrites' admin r ns o)
                  (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗
                    Φ (PairV #x #err))) Hok hw.2 hw.1
                  (Or.inr (Or.inr ⟨hCE, tm, hsnd, by rw [hO3]⟩)))
                $$ [$Hhist $HΦ] with ⟨Hhist, %Hok', HΦ⟩
              (try wp_auto)
              wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback Htb]
              · iunfold lockInv
                inext
                iexists σ0.write r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1), H ++ [σ0]
                iframe Hhist Hws
                isplitl [Hrev Huids Hrvsm Hrc Hback Htb]
                · iunfold srvLocked
                  simp only [named]
                  isplitl [Hrev]
                  · rw [show (St.write σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1)).rev =
                      σ0.rev + 1 from rfl]
                    iexact Hrev
                  isplitl [Huids]
                  · rw [show (St.write σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1)).uids =
                      σ0.uids + 1 from rfl]
                    iexact Huids
                  isplitl [Hrvsm]
                  · rw [show (St.write σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1)).rev =
                      σ0.rev + 1 from rfl, hno]
                    iexact Hrvsm
                  isplitl [Hback Htb]
                  · iapply Hback
                    · ipureintro
                      intro r' hr'
                      rw [St.write_tbl, if_neg hr']
                    rw [St.write_tbl, if_pos rfl]
                    iapply Htb
                  isplitl [Hrc]
                  · rw [show (St.write σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1)).rev =
                      σ0.rev + 1 from rfl, hno, Nat.add_sub_cancel]
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
                wp_apply +noauto wp_NewTimeoutError as %p ⟨%st, %dv, Hp, -, %Hst⟩
                ipersist Hp
                (try wp_auto)
                iapply HΦ
                iframe
                unfold writeRetI
                iright
                isplitr
                · ipureintro; exact ⟨rfl, Hb2 rfl, rfl⟩
                unfold errIs
                iexists p, st
                iframe #
                ipureintro
                exact ⟨rfl, Hst.2.1, Hst.2.2⟩
        · -- a resource version set
          imod (au_fail γ (.error .badRequest : Except ApiErr (Bool × Obj)) (CreateOut cfg.FailWrites' admin r ns o)
              (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗ Φ (PairV #x #err)))
              (fun σ => Or.inr (Or.inl ⟨.badRequest, by exact createErr_rv hc1 (ho1 ▸ Hif), rfl, rfl⟩))) $$ HΦ with ⟨%σ, HΦ⟩
          (try wp_auto)
          wp_apply +noauto wp_NewBadRequest as %p ⟨%st, Hp, %Hst⟩
          ipersist Hp
          wp_auto
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
      · wp_apply (objAt_GetNamespace wp_GetNamespace y o) $$ Hy as Hy
        by_cases Hns2 : o.meta.Namespace' = ns
        rotate_left
        · -- another namespace than the request's
          simp only [decide_eq_false Hns2, Bool.not_false, ↓reduceIte]
          (try wp_auto)
          imod (au_fail γ (.error .badRequest : Except ApiErr (Bool × Obj)) (CreateOut cfg.FailWrites' admin r ns o)
              (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗ Φ (PairV #x #err)))
              (fun σ => Or.inr (Or.inl ⟨.badRequest, by exact createErr_ns ⟨hnsr, Hif, Hns2⟩, rfl, rfl⟩))) $$ HΦ with ⟨%σ, HΦ⟩
          (try wp_auto)
          wp_apply +noauto wp_NewBadRequest as %p ⟨%st, Hp, %Hst⟩
          ipersist Hp
          wp_auto
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
          have ho1 : o = createNs r ns o := by
            unfold createNs; simp [hnsr, Hif]
          have hc1 : ¬ (r.namespaced = true ∧ o.meta.Namespace' ≠ go!"" ∧ o.meta.Namespace' ≠ ns) := by
            simp [Hns2]
          wp_apply (objAt_GetResourceVersion wp_GetResourceVersion y _) $$ Hy as Hy
          wp_if_destruct
          · -- no resource version: under the lock
            ihave Hy := objAt_cast ho1 $$ Hy
            rw [ho1] at Hif
            have hrv0 := Hif
            wp_apply wp_Lock $$ [$Hmu] as ⟨Hown, Hinv⟩
            iunfold lockInv at Hinv
            icases Hinv with ⟨%σ0, %H, Hlk, Hhist, %Hok, Hws⟩
            iNamed Hlk
            have hwf := histOk_last_wf Hok
            icases tablesLocked_acc L σ0 r $$ Htbls with ⟨Ht0, Hback⟩
            iunfold tableLocked at Ht0
            icases Ht0 with ⟨%M, %sl, %cs, HM, Hrel, Hlog, Hsl, Hcap, Hcs⟩
            wp_apply (objAt_GetName wp_GetName y _) $$ Hy as Hy
            wp_if_destruct
            · -- no name
              have hnm := Hif
              wp_apply (objAt_GetGenerateName wp_GetGenerateName y _) $$ Hy as Hy
              wp_if_destruct
              · -- neither a name nor a generated name
                imod (au_write_noop γ H σ0 (.error .badRequest : Except ApiErr (Bool × Obj))
                    (CreateOut cfg.FailWrites' admin r ns o) (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗ Φ (PairV #x #err)))
                    (Or.inr (Or.inl ⟨.badRequest, createErr_noname hc1 hrv0 hnm Hif, rfl, rfl⟩))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
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
              · have hgn := Hif
                wp_apply (objAt_GetGenerateName wp_GetGenerateName y _) $$ Hy as Hy
                wp_apply wp_rvString $$ [$Hstrconv]
                wp_apply (objAt_SetName wp_SetName y _) $$ Hy as Hy
                have hnmo : ¬ ((createNs r ns o).meta.Name' = go!"" ∧ (createNs r ns o).meta.GenerateName' = go!"") :=
                  fun h => hgn h.2
                ihave Hy := objAt_cast (createName_gen (σ := σ0) hnm) $$ Hy
                wp_apply (objAt_GetNamespace wp_GetNamespace y _) $$ Hy as Hy
                wp_apply (objAt_GetName wp_GetName y _) $$ Hy as Hy
                (try wp_auto)
                (try simp only [Obj.meta_modMeta])
                wp_apply (wp_map_lookup2 k8s_io.apimachinery.pkg.types.NamespacedName.ty apimodel.object.ty
                  (L.tbl r).objs M (mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0)) (DFrac.own 1)) $$ HM as HM
                ihave %hd := objsRel_dom M (σ0.tbl r).objs (mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0)) $$ Hrel
                cases hk : M !! mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0) with
                | some x =>
                  have hex : ((σ0.tbl r).objs !! mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0)).isSome :=
                    hd.mp (by simp [hk])
                  simp only [Option.isSome_some]
                  (try wp_auto)
                  imod (au_write_noop γ H σ0 (.error .alreadyExists : Except ApiErr (Bool × Obj))
                      (CreateOut cfg.FailWrites' admin r ns o) (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗ Φ (PairV #x #err)))
                      (Or.inr (Or.inl ⟨.alreadyExists, createErr_exists hc1 hrv0 hnmo hex, rfl, rfl⟩))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
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
                  wp_apply +noauto wp_NewAlreadyExists as %p ⟨%st, Hp, %Hst⟩
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
                | none =>
                  have hnone : (σ0.tbl r).objs !! mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0) = none := by
                    cases h' : (σ0.tbl r).objs !! mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0) with
                    | none => rfl
                    | some _ => simp [h', hk] at hd
                  simp only [Option.isSome_none]
                  (try wp_auto)
                  wp_apply wp_rvString $$ [$Hstrconv]
                  (try wp_auto)
                  wp_apply (objAt_SetUID wp_SetUID y _ _) $$ Hy as Hy
                  wp_apply wp_Now $$ [$Htime] as %tm -
                  wp_apply (objAt_SetCreationTimestamp wp_SetCreationTimestamp y _ _) $$ Hy as Hy
                  (try wp_auto)
                  wp_apply (wp_prepare_call r prep y _) $$ [$Hprep $Hy] as Hy
                  · ipureintro
                    simp [Obj.modMeta, createNs_res, Hres]
                  wp_apply (wp_nextRV s L.rvs σ0.rev) $$ [$Hstrconv $Hrev $Hrvs $Hrvsm $Hrc] as ⟨Hrev, Hrvsm, Hrc, %hno⟩
                  · ipureintro; exact ⟨hwf.rev_pos, Hbound⟩
                  (try wp_auto)
                  wp_apply (objAt_SetResourceVersion wp_SetResourceVersion y _ _) $$ Hy as Hy
                  ihave Hy := objAt_cast (createApply_fst r ns o σ0 tm) $$ Hy
                  rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl] at hno
                  rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl, show σ0.uids + W64 1 = σ0.uids + 1 from rfl]
                  have hres3 : (createApply r ns o σ0 tm).1.res = r := by
                    rw [← createApply_fst]; simp [prepareD_res, createNs_res, Hres]
                  have hRV3 : (createApply r ns o σ0 tm).1.meta.ResourceVersion' = rvStr (σ0.rev + 1) := by
                    rw [← createApply_fst]; simp
                  have huid3 : (createApply r ns o σ0 tm).1.meta.UID' = go!"uid-" ++ rvStr (σ0.uids + 1) := by
                    rw [← createApply_fst]; simp [prepareD_uid]
                  have hsnd := createApply_snd r ns o σ0 tm
                  have hCE := createErr_none hc1 hrv0 hnmo hnone
                  generalize hO3 : (createApply r ns o σ0 tm).1 = o3 at hres3 hRV3 huid3 hsnd ⊢
                  (try wp_auto)
                  rw [show k8s_io.apimachinery.pkg.watch.Added = #(EvTy.added.str) from rfl]
                  wp_apply (wp_record s γ L cfg r (σ0.tbl r) .added (σ0.rev + 1) y o3) $$
                    [$Hfixed HM Hrel Hlog Hsl Hcap Hcs $Hy] as ⟨Hy, Htb⟩
                  · iunfold tableLocked
                    iexists M, sl, cs
                    iframe
                  wp_apply wp_copyObject $$ Hy as %z ⟨Hy, Hz⟩
                  ihave Htb := Htb $$ Hy
                  -- the write's linearization point
                  have huid1 : (σ0.uids + 1).toNat = σ0.uids.toNat + 1 := by
                    have h1 := Huidlt
                    have h2 := σ0.rev.isLt
                    word
                  have hw := St.write_wf σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1) hwf rfl
                    hno hres3 hRV3 (by rw [huid1]; omega) (by rw [huid1]; omega)
                    ⟨σ0.uids + 1, by rw [huid1]; omega, Nat.le_refl _, huid3⟩
                  imod (au_write γ H σ0 (σ0.write r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1))
                      (.ok (true, o3)) (CreateOut cfg.FailWrites' admin r ns o)
                      (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗
                        Φ (PairV #x #err))) Hok hw.2 hw.1
                      (Or.inr (Or.inr ⟨hCE, tm, hsnd, by rw [hO3]⟩)))
                    $$ [$Hhist $HΦ] with ⟨Hhist, %Hok', HΦ⟩
                  (try wp_auto)
                  wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback Htb]
                  · iunfold lockInv
                    inext
                    iexists σ0.write r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1), H ++ [σ0]
                    iframe Hhist Hws
                    isplitl [Hrev Huids Hrvsm Hrc Hback Htb]
                    · iunfold srvLocked
                      simp only [named]
                      isplitl [Hrev]
                      · rw [show (St.write σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1)).rev =
                          σ0.rev + 1 from rfl]
                        iexact Hrev
                      isplitl [Huids]
                      · rw [show (St.write σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1)).uids =
                          σ0.uids + 1 from rfl]
                        iexact Huids
                      isplitl [Hrvsm]
                      · rw [show (St.write σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1)).rev =
                          σ0.rev + 1 from rfl, hno]
                        iexact Hrvsm
                      isplitl [Hback Htb]
                      · iapply Hback
                        · ipureintro
                          intro r' hr'
                          rw [St.write_tbl, if_neg hr']
                        rw [St.write_tbl, if_pos rfl]
                        iapply Htb
                      isplitl [Hrc]
                      · rw [show (St.write σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1)).rev =
                          σ0.rev + 1 from rfl, hno, Nat.add_sub_cancel]
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
                    wp_apply +noauto wp_NewTimeoutError as %p ⟨%st, %dv, Hp, -, %Hst⟩
                    ipersist Hp
                    (try wp_auto)
                    iapply HΦ
                    iframe
                    unfold writeRetI
                    iright
                    isplitr
                    · ipureintro; exact ⟨rfl, Hb2 rfl, rfl⟩
                    unfold errIs
                    iexists p, st
                    iframe #
                    ipureintro
                    exact ⟨rfl, Hst.2.1, Hst.2.2⟩
            · have hnm := Hif
              have hnmo : ¬ ((createNs r ns o).meta.Name' = go!"" ∧ (createNs r ns o).meta.GenerateName' = go!"") :=
                fun h => hnm h.1
              ihave Hy := objAt_cast (createName_named (σ := σ0) hnm) $$ Hy
              wp_apply (objAt_GetNamespace wp_GetNamespace y _) $$ Hy as Hy
              wp_apply (objAt_GetName wp_GetName y _) $$ Hy as Hy
              (try wp_auto)
              (try simp only [Obj.meta_modMeta])
              wp_apply (wp_map_lookup2 k8s_io.apimachinery.pkg.types.NamespacedName.ty apimodel.object.ty
                (L.tbl r).objs M (mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0)) (DFrac.own 1)) $$ HM as HM
              ihave %hd := objsRel_dom M (σ0.tbl r).objs (mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0)) $$ Hrel
              cases hk : M !! mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0) with
              | some x =>
                have hex : ((σ0.tbl r).objs !! mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0)).isSome :=
                  hd.mp (by simp [hk])
                simp only [Option.isSome_some]
                (try wp_auto)
                imod (au_write_noop γ H σ0 (.error .alreadyExists : Except ApiErr (Bool × Obj))
                    (CreateOut cfg.FailWrites' admin r ns o) (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗ Φ (PairV #x #err)))
                    (Or.inr (Or.inl ⟨.alreadyExists, createErr_exists hc1 hrv0 hnmo hex, rfl, rfl⟩))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
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
                wp_apply +noauto wp_NewAlreadyExists as %p ⟨%st, Hp, %Hst⟩
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
              | none =>
                have hnone : (σ0.tbl r).objs !! mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0) = none := by
                  cases h' : (σ0.tbl r).objs !! mkKey (createNs r ns o).meta.Namespace' (createName r ns o σ0) with
                  | none => rfl
                  | some _ => simp [h', hk] at hd
                simp only [Option.isSome_none]
                (try wp_auto)
                wp_apply wp_rvString $$ [$Hstrconv]
                (try wp_auto)
                wp_apply (objAt_SetUID wp_SetUID y _ _) $$ Hy as Hy
                wp_apply wp_Now $$ [$Htime] as %tm -
                wp_apply (objAt_SetCreationTimestamp wp_SetCreationTimestamp y _ _) $$ Hy as Hy
                (try wp_auto)
                wp_apply (wp_prepare_call r prep y _) $$ [$Hprep $Hy] as Hy
                · ipureintro
                  simp [Obj.modMeta, createNs_res, Hres]
                wp_apply (wp_nextRV s L.rvs σ0.rev) $$ [$Hstrconv $Hrev $Hrvs $Hrvsm $Hrc] as ⟨Hrev, Hrvsm, Hrc, %hno⟩
                · ipureintro; exact ⟨hwf.rev_pos, Hbound⟩
                (try wp_auto)
                wp_apply (objAt_SetResourceVersion wp_SetResourceVersion y _ _) $$ Hy as Hy
                ihave Hy := objAt_cast (createApply_fst r ns o σ0 tm) $$ Hy
                rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl] at hno
                rw [show σ0.rev + W64 1 = σ0.rev + 1 from rfl, show σ0.uids + W64 1 = σ0.uids + 1 from rfl]
                have hres3 : (createApply r ns o σ0 tm).1.res = r := by
                  rw [← createApply_fst]; simp [prepareD_res, createNs_res, Hres]
                have hRV3 : (createApply r ns o σ0 tm).1.meta.ResourceVersion' = rvStr (σ0.rev + 1) := by
                  rw [← createApply_fst]; simp
                have huid3 : (createApply r ns o σ0 tm).1.meta.UID' = go!"uid-" ++ rvStr (σ0.uids + 1) := by
                  rw [← createApply_fst]; simp [prepareD_uid]
                have hsnd := createApply_snd r ns o σ0 tm
                have hCE := createErr_none hc1 hrv0 hnmo hnone
                generalize hO3 : (createApply r ns o σ0 tm).1 = o3 at hres3 hRV3 huid3 hsnd ⊢
                (try wp_auto)
                rw [show k8s_io.apimachinery.pkg.watch.Added = #(EvTy.added.str) from rfl]
                wp_apply (wp_record s γ L cfg r (σ0.tbl r) .added (σ0.rev + 1) y o3) $$
                  [$Hfixed HM Hrel Hlog Hsl Hcap Hcs $Hy] as ⟨Hy, Htb⟩
                · iunfold tableLocked
                  iexists M, sl, cs
                  iframe
                wp_apply wp_copyObject $$ Hy as %z ⟨Hy, Hz⟩
                ihave Htb := Htb $$ Hy
                -- the write's linearization point
                have huid1 : (σ0.uids + 1).toNat = σ0.uids.toNat + 1 := by
                  have h1 := Huidlt
                  have h2 := σ0.rev.isLt
                  word
                have hw := St.write_wf σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1) hwf rfl
                  hno hres3 hRV3 (by rw [huid1]; omega) (by rw [huid1]; omega)
                  ⟨σ0.uids + 1, by rw [huid1]; omega, Nat.le_refl _, huid3⟩
                imod (au_write γ H σ0 (σ0.write r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1))
                    (.ok (true, o3)) (CreateOut cfg.FailWrites' admin r ns o)
                    (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗
                      Φ (PairV #x #err))) Hok hw.2 hw.1
                    (Or.inr (Or.inr ⟨hCE, tm, hsnd, by rw [hO3]⟩)))
                  $$ [$Hhist $HΦ] with ⟨Hhist, %Hok', HΦ⟩
                (try wp_auto)
                wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback Htb]
                · iunfold lockInv
                  inext
                  iexists σ0.write r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1), H ++ [σ0]
                  iframe Hhist Hws
                  isplitl [Hrev Huids Hrvsm Hrc Hback Htb]
                  · iunfold srvLocked
                    simp only [named]
                    isplitl [Hrev]
                    · rw [show (St.write σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1)).rev =
                        σ0.rev + 1 from rfl]
                      iexact Hrev
                    isplitl [Huids]
                    · rw [show (St.write σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1)).uids =
                        σ0.uids + 1 from rfl]
                      iexact Huids
                    isplitl [Hrvsm]
                    · rw [show (St.write σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1)).rev =
                        σ0.rev + 1 from rfl, hno]
                      iexact Hrvsm
                    isplitl [Hback Htb]
                    · iapply Hback
                      · ipureintro
                        intro r' hr'
                        rw [St.write_tbl, if_neg hr']
                      rw [St.write_tbl, if_pos rfl]
                      iapply Htb
                    isplitl [Hrc]
                    · rw [show (St.write σ0 r ⟨.added, σ0.rev + 1, o3⟩ (σ0.uids + 1)).rev =
                        σ0.rev + 1 from rfl, hno, Nat.add_sub_cancel]
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
                  wp_apply +noauto wp_NewTimeoutError as %p ⟨%st, %dv, Hp, -, %Hst⟩
                  ipersist Hp
                  (try wp_auto)
                  iapply HΦ
                  iframe
                  unfold writeRetI
                  iright
                  isplitr
                  · ipureintro; exact ⟨rfl, Hb2 rfl, rfl⟩
                  unfold errIs
                  iexists p, st
                  iframe #
                  ipureintro
                  exact ⟨rfl, Hst.2.1, Hst.2.2⟩
          · -- a resource version set
            imod (au_fail γ (.error .badRequest : Except ApiErr (Bool × Obj)) (CreateOut cfg.FailWrites' admin r ns o)
                (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗ Φ (PairV #x #err)))
                (fun σ => Or.inr (Or.inl ⟨.badRequest, by exact createErr_rv hc1 (ho1 ▸ Hif), rfl, rfl⟩))) $$ HΦ with ⟨%σ, HΦ⟩
            (try wp_auto)
            wp_apply +noauto wp_NewBadRequest as %p ⟨%st, Hp, %Hst⟩
            ipersist Hp
            wp_auto
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
  · -- a flagged failure
    imod (au_fail γ (.error .internal : Except ApiErr (Bool × Obj)) (CreateOut cfg.FailWrites' admin r ns o)
        (fun _ _ oc => iprop(∀ x err, objAt inp dq o ∗ writeRetI cfg.AmbiguousWrites' admin oc x err -∗ Φ (PairV #x #err)))
        (fun σ => Or.inl ⟨Hb rfl, rfl, rfl⟩)) $$ HΦ with ⟨%σ, HΦ⟩
    (try wp_auto)
    wp_apply +noauto wp_NewInternalError as %p ⟨%st, Hp, %Hst⟩
    ipersist Hp
    wp_auto
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
