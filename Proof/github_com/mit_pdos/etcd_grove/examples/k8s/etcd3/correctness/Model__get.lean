module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__get
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.checkKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.versioner__ParseResourceVersion
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.newObj
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj__DeepCopyObject
public import Spec.k8s_io.apiserver.pkg.storage.NewTooLargeResourceVersionError
public import Spec.k8s_io.apiserver.pkg.storage.NewKeyNotFoundError
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ItemsRO

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map k8sDeep
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem Model.get.wp_proof
    (wp_checkKey : checkKey.spec (GF := GF) (hG := hG))
    (wp_Parse : k8s_etcd3.versioner.ParseResourceVersion.spec (GF := GF) (hG := hG))
    (wp_newObj : k8s_etcd3.newObj.spec (GF := GF) (hG := hG))
    (wp_DeepCopy : k8s_etcd3.Obj.DeepCopyObject.spec (GF := GF) (hG := hG))
    (wp_TooLarge : storage.NewTooLargeResourceVersionError.spec (GF := GF) (hG := hG))
    (wp_NotFound : storage.NewKeyNotFoundError.spec (GF := GF) (hG := hG)) :
    Model.get.spec (GF := GF) (hG := hG) := by
  intro mp m x opts hrv hinf
  wp_start as Hm
  unfold modelAt modelRep modelVal
  icases Hm with ⟨#Hinit, %il, %rl, %M, #Hp, #HI, #Hit, #HR⟩
  iStructNamed Hp
  wp_auto
  wp_apply (wp_checkKey (k8s_etcd3.storeKeyL x.Key') false) as %err %Herr
  by_cases hk : keyOkL (k8s_etcd3.storeKeyL x.Key') = true
  case neg =>
    have hne : err ≠ GoInterface.nil := fun h => hk (by unfold keyOkL; exact Herr.1 h)
    obtain ⟨ii, rfl⟩ : ∃ ii, err = GoInterface.ok ii := by
      cases err with
      | nil => exact absurd rfl hne
      | ok ii => exact ⟨ii, rfl⟩
    wp_auto
    iapply HΦ
    have : rgetL x m = ⟨.nil, .other⟩ := by unfold rgetL; simp [hk]
    rw [this]
    unfold respRep errRep deepRO deepRep
    simp only
    ipureintro; first | trivial | simp | exact ⟨rfl, nofun⟩ | exact nofun
  have he : err = GoInterface.nil := Herr.2 hk
  subst he
  wp_auto
  rw [hrv]
  wp_apply (wp_Parse x.MinRV') as %n %perr Hpr
  cases hp : k8s_etcd3.parseRVD x.MinRV' with
  | none =>
    icases Hpr with ⟨%hne, -⟩
    obtain ⟨ii, rfl⟩ : ∃ ii, perr = GoInterface.ok ii := by
      cases perr with
      | nil => exact absurd rfl hne
      | ok ii => exact ⟨ii, rfl⟩
    wp_auto
    iapply HΦ
    have : rgetL x m = ⟨.nil, .other⟩ := by unfold rgetL; simp [hk, hp]
    rw [this]
    unfold respRep errRep deepRO deepRep
    simp only
    ipureintro; first | trivial | simp | exact ⟨rfl, nofun⟩ | exact nofun
  | some rv =>
    icases Hpr with %Hpr
    obtain ⟨rfl, rfl⟩ := Hpr
    wp_auto
    by_cases hlt : uint.Z m.rv < uint.Z n
    case pos =>
      rw [decide_eq_true hlt]
      wp_auto
      wp_apply (wp_TooLarge n m.rv (W64 0)) as %e ⟨Htl0, %l, %st, %dv, %Hst, #Hl, #Hd⟩
      ihave #Htl := Htl0 $$ %(by trivial)
      iapply HΦ
      have : rgetL x m = ⟨.nil, tooLargeE⟩ := by
        unfold rgetL; simp [hk, hp]; intro h; exfalso; word
      rw [this]
      unfold respRep deepRO deepRep tooLargeE
      simp only
      isplitr
      · ipureintro; trivial
      iapply errRep_tooLarge_of e l st dv Hst
      iframe Htl Hl Hd
    rw [decide_eq_false hlt]
    wp_auto
    wp_apply (wp_map_lookup2 go.string k8s_io.apimachinery.pkg.runtime.Object.ty il M
      (k8s_etcd3.storeKeyL x.Key') DFrac.discard) $$ HI as -
    have hle : ¬ uint.nat m.rv < uint.nat n := by word
    cases hs : M !! k8s_etcd3.storeKeyL x.Key' with
    | none =>
      ihave %hnone := itemsRO_none M m.items (k8s_etcd3.storeKeyL x.Key') $$ Hit
      have hi : m.items !! k8s_etcd3.storeKeyL x.Key' = none := hnone.1 hs
      wp_auto
      rw [hinf]
      cases hig : x.IgnoreNotFound' with
      | true =>
        wp_auto
        wp_apply +noauto wp_newObj as %o Ho
        iunfold k8s_etcd3.objAtD at Ho
        icases Ho with ⟨%p, %n0, ⟨%ho, -, %hn0⟩, Hp⟩
        have hn : n0 = 0 := k8s_etcd3.rvStr_nil n0 hn0.symm
        subst ho hn
        ipersist Hp
        wp_auto
        iapply HΦ
        have : rgetL x m = ⟨.obj k8s_etcd3.zObj, .none⟩ := by
          unfold rgetL; simp [hk, hp, hle, hi, hig]
        rw [this]
        unfold respRep errRep deepRO deepRep
        simp only
        isplitl
        · iexists p
          isplitr
          · ipureintro; rfl
          · rw [show k8s_etcd3.zObj = k8s_etcd3.dzero.toObj 0 by
              simp [k8s_etcd3.zObj, k8s_etcd3.dzero]]
            iexact Hp
        · ipureintro; first | trivial | simp | exact ⟨rfl, nofun⟩ | exact nofun
      | false =>
        wp_auto
        wp_apply +noauto (wp_NotFound (m.pfx ++ k8s_etcd3.storeKeyL x.Key') _) as %l Hl
        ipersist Hl
        wp_auto
        iapply HΦ
        have : rgetL x m = ⟨.nil, notFoundE m (k8s_etcd3.storeKeyL x.Key')⟩ := by
          unfold rgetL; simp [hk, hp, hle, hi, hig]
        rw [this]
        unfold respRep errRep deepRO deepRep notFoundE
        simp only
        isplitr
        · ipureintro; first | rfl | trivial
        · iexists l, GoInterface.nil
          iframe Hl
          isplitr
          · ipureintro; rfl
          · iunfold deepRep
            ipureintro; rfl
    | some v =>
      icases itemsRO_lookup M m.items _ v hs $$ Hit with ⟨%p, %o, ⟨%ho, %hv⟩, #Hpo⟩
      subst hv
      simp only [Option.isSome_some, _root_.decide_true]
      wp_auto
      wp_apply +noauto (wp_DeepCopy p DFrac.discard o) $$ [Hpo] as %c ⟨-, Hc⟩
      · iexact Hpo
      ipersist Hc
      wp_auto
      iapply HΦ
      have : rgetL x m = ⟨.obj o, .none⟩ := by
        unfold rgetL; simp [hk, hp, hle, ho]
      rw [this]
      unfold respRep errRep deepRO deepRep
      simp only
      isplitl
      · iexists c
        iframe Hc
        ipureintro; rfl
      · ipureintro; first | rfl | trivial

end proof

end k8s_correctness
end EtcdGrove
end Perennial
