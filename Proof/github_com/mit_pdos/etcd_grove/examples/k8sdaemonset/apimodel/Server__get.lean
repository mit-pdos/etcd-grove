/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/Server__get.lean`.
Lean-first. The linearization point is the map lookup under the lock (a flagged failure fires the
caller's update before, at whatever state).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Server__get
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Server__chance
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.copyObject
public import Spec.k8s_io.apimachinery.pkg.api.errors.NewInternalError
public import Spec.k8s_io.apimachinery.pkg.api.errors.NewNotFound
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.MapLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.SrvLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.HistLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.ObjLemmas
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

set_option linter.unusedSectionVars false

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

theorem Server.get.wp_proof
    (wp_chance : Server.chance.spec (GF := GF) (hG := hG))
    (wp_copyObject : copyObject.spec (GF := GF) (hG := hG))
    (wp_NewInternalError : apierrors.NewInternalError.spec (GF := GF) (hG := hG))
    (wp_NewNotFound : apierrors.NewNotFound.spec (GF := GF) (hG := hG))
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    Server.get.spec (GF := GF) (hG := hG) := by
  intro _ s γ cfg r t ns name admin
  wp_start as ⟨#Hs, #Ht⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Herrs : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors $$ []
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
  iNamed Hs
  iNamed Hcfg
  wp_apply wp_with_defer as %defer defer
  wp_apply wp_chance $$ [$Hsrv] as %b %Hb
  cases b
  · wp_auto
    wp_apply wp_Lock $$ [$Hmu] as ⟨Hown, Hinv⟩
    iunfold lockInv at Hinv
    icases Hinv with ⟨%σ0, %H, Hlk, Hhist, %Hok, Hws⟩
    iNamed Hlk
    icases tablesLocked_acc L σ0 r $$ Htbls with ⟨Ht0, Hback⟩
    iunfold tableLocked at Ht0
    icases Ht0 with ⟨%M, %sl, %cs, HM, Hrel, Hlog, Hsl, Hcap, Hcs⟩
    wp_apply (wp_map_lookup2 k8s_io.apimachinery.pkg.types.NamespacedName.ty apimodel.object.ty
      (L.tbl r).objs M (mkKey ns name) (DFrac.own 1)) $$ HM as HM
    imod (au_read γ H σ0 (fun σ => iprop(∀ x err, getRet cfg.FailReads' admin (getObj r ns name σ) x err -∗
      Φ (PairV #x #err)))) $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
    cases hk : M !! mkKey ns name with
    | none =>
      ihave %hd := objsRel_dom M (σ0.tbl r).objs (mkKey ns name) $$ Hrel
      have ho : (σ0.tbl r).objs !! mkKey ns name = none := by
        cases h' : (σ0.tbl r).objs !! mkKey ns name with
        | none => rfl
        | some _ => simp [hk, h'] at hd
      simp only [Option.isSome_none, Option.getD_none]
      wp_auto
      wp_apply +noauto wp_NewNotFound as %p ⟨%st, Hp, %Hst⟩
      ipersist Hp
      wp_auto
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
      iapply HΦ
      unfold getRet getObj
      iright
      rw [ho]
      isplitr
      · ipureintro; rfl
      unfold errIs
      iexists p, st
      iframe #
      ipureintro
      exact ⟨rfl, Hst.2.1, Hst.2.2⟩
    | some x =>
      icases objsRel_lookup M (σ0.tbl r).objs (mkKey ns name) x hk $$ Hrel with ⟨%o, %ho, Hx, Hrelb⟩
      simp only [Option.isSome_some, decide_true, Option.getD_some]
      wp_auto
      wp_apply wp_copyObject $$ Hx as %y ⟨Hx, Hy⟩
      ihave Hrel := Hrelb $$ Hx
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
      iapply HΦ
      unfold getRet getObj
      iright
      rw [ho]
      simp only
      isplitr
      · ipureintro; trivial
      iexact Hy
  · imod (au_read_any γ (fun σ => iprop(∀ x err, getRet cfg.FailReads' admin (getObj r ns name σ) x err -∗ Φ (PairV #x #err)))) $$ HΦ with ⟨%σ, HΦ⟩
    wp_auto
    wp_apply +noauto wp_NewInternalError as %p ⟨%st, Hp, %Hst⟩
    ipersist Hp
    wp_auto
    iapply HΦ
    unfold getRet
    ileft
    isplitr
    · ipureintro; exact ⟨Hb rfl, rfl⟩
    unfold errIs
    iexists p, st
    iframe #
    ipureintro
    exact ⟨rfl, Hst.2.1, Hst.2.2⟩
end proof

end apimodel
end EtcdGrove
end Perennial
