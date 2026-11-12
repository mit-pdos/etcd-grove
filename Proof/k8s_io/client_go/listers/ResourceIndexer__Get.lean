/-
Proof of `Spec/k8s_io/client_go/listers/ResourceIndexer__Get.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.listers.ResourceIndexer__Get
public import Spec.k8s_io.client_go.tools.cache.cache__GetByKey
public import Spec.k8s_io.apimachinery.pkg.api.errors.NewNotFound

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace listers

open Iris Iris.BI Iris.ProofMode cache k8s_io.client_go.listers

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.listers.Assumptions]

theorem ResourceIndexer.Get.wp_proof
    (wp_GetByKey : cache.GetByKey.spec (GF := GF) (hG := hG))
    (wp_NewNotFound : apierrors.NewNotFound.spec (GF := GF) (hG := hG)) :
    ResourceIndexer.Get.spec (GF := GF) (hG := hG) := by
  intro X ca ts γ OK Fam kf res ns name
  iintro %Φ ⟨#Hpkg, #Hca, Hr, #HT⟩ HAU
  ihave #Hcpkg : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache $$ []
  · iPkgInit
  wp_method_call
  wp_call
  (try wp_auto)
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ key_ptr ↦ nsKey ns name ∗
      l_ptr ↦ riVal ca res ns ∗ name_ptr ↦ name))) $$ [key l name]
  · by_cases hns : ns = []
    · rw [decide_eq_true hns]
      (try wp_auto)
      unfold nsKey; rw [ite_eq_left_of_eq_true _ _ (by simp [hns])]
      iframe
      ipureintro; rfl
    · rw [decide_eq_false hns]
      (try wp_auto)
      unfold nsKey; rw [ite_eq_right_of_eq_false _ _ (by simp [hns])]
      iframe
      ipureintro; rfl
  iintro %v ⟨%hv, key, l, name⟩
  subst hv
  (try wp_auto)
  wp_bind
  iapply (wp_GetByKey ca ts γ OK Fam kf (nsKey ns name)) $$ [$Hcpkg $Hca $Hr]
  inext
  imod HAU with ⟨%σ, ⟨Hst, %hnn⟩, Hcl⟩
  imodintro
  iexists σ
  iframe Hst
  iintro Hst
  imod Hcl $$ [Hst] with HK
  · iframe; ipureintro; exact hnn
  imodintro
  iintro %item %ok ⟨%Hitem, #Hokn, Hr⟩
  obtain ⟨rfl, rfl⟩ := Hitem
  (try wp_auto)
  cases hk : σ.items !! nsKey ns name with
  | none =>
    have hd : decide (nsKey ns name ∈ σ.items) = false := by
      simp [GMap.mem_iff, hk]
    rw [hd]
    (try wp_auto)
    wp_apply wp_alloc as %z Hz
    ihave #Hepkg : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors $$ []
    · iPkgInit
    wp_apply wp_NewNotFound as %p Hp
    (try wp_auto)
    iapply HK
    iframe
    unfold getPost
    rw [hk]
    ipureintro
    exact ⟨rfl, fun h => by cases h⟩
  | some o =>
    have hd : decide (nsKey ns name ∈ σ.items) = true := by
      simp [GMap.mem_iff, hk]
    rw [hd]
    have ho : objAt σ.items (nsKey ns name) = o := by unfold objAt; rw [hk]; rfl
    have hon := hnn _ o hk
    ihave #HOKo : □ OK o $$ [Hokn]
    · rw [← ho]
      iapply (okNil_noNil OK σ.items (nsKey ns name) hnn (by rw [GMap.mem_iff, hk]; rfl))
      rw [ho]; iexact Hokn
    iunfold typedOK at HT
    ihave %hty := HT $$ HOKo
    obtain ⟨r, rfl⟩ := hty
    rw [ho]
    unfold ptrObj
    (try wp_auto)
    simp only [interface.mkOk]
    (try wp_auto)
    iapply HK
    iframe
    unfold getPost
    rw [hk]
    dsimp only
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    unfold ptrObj; simp only [interface.mkOk]; imodintro; iexact HOKo

end proof

end listers
end EtcdGrove
end Perennial
