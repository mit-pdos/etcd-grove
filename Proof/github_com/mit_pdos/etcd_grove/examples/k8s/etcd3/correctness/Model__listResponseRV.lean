module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__listResponseRV
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList__GetResourceVersion
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.versioner__ParseResourceVersion
public import Spec.k8s_io.apimachinery.pkg.api.meta.ListAccessor
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ListAccessorObjList

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map k8sDeep k8s_etcd3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]
variable [meta_sem : k8s_io.apimachinery.pkg.api.«meta».Assumptions]
variable [metav1_sem : k8s_io.apimachinery.pkg.apis.«meta».v1.Assumptions]
variable [storage_sem : k8s_io.apiserver.pkg.storage.Assumptions]

theorem Model.listResponseRV.wp_proof
    (wp_LA : apimeta.ListAccessor.spec (GF := GF) (hG := hG))
    (wp_GRV : k8s_etcd3.ObjList.GetResourceVersion.spec (GF := GF) (hG := hG))
    (wp_PRV : k8s_etcd3.versioner.ParseResourceVersion.spec (GF := GF) (hG := hG)) :
    Model.listResponseRV.spec (GF := GF) (hG := hG) := by
  intro mp m r rr hlo
  wp_start as ⟨#Hm, #Hr⟩
  unfold respRep
  icases Hr with ⟨#Ho, #He⟩
  ihave %Hen := errRep_nil_iff _ _ $$ He
  ihave %Hon := deepRep_nil_iff _ _ _ $$ Ho
  unfold modelAt modelRep modelVal
  icases Hm with ⟨#Hinit, %il, %rl, %M, #Hp, -, -, -⟩
  iStructNamed Hp
  wp_auto
  have hnone : (none : Option w64).getD 0 = W64 0 ∧ (none : Option w64).isSome = false := ⟨rfl, rfl⟩
  cases hen : errNonNil rr.err
  case true =>
    have hne : r.Err' ≠ GoInterface.nil := fun h => by rw [Hen.1 h] at hen; cases hen
    obtain ⟨ii, hii⟩ : ∃ ii, r.Err' = GoInterface.ok ii := by
      cases h : r.Err' with
      | nil => exact absurd h hne
      | ok ii => exact ⟨ii, rfl⟩
    rw [hii]
    wp_auto
    have : listRespRVL rr = none := by unfold listRespRVL; simp [hen]
    rw [this, hnone.1, hnone.2]
    iapply HΦ
    itrivial
  have he : r.Err' = GoInterface.nil := Hen.2 hen
  rw [he]
  wp_auto
  unfold deepRO
  cases ho : rr.obj with
  | nil =>
    have hx : r.Object' = GoInterface.nil := (Hon.2 ho)
    rw [hx]
    wp_auto
    have : listRespRVL rr = none := by unfold listRespRVL; simp [hen, ho]
    rw [this, hnone.1, hnone.2]
    iapply HΦ
    itrivial
  | list items rv cont rem =>
    iunfold deepRep at Ho
    icases Ho with ⟨%lp, %sl, %rp, %hx, #Hl, -, -⟩
    rw [hx]
    wp_auto
    rw [hx]
    wp_apply (ListAccessor_objList wp_LA lp) as %acc %aerr %hacc
    obtain ⟨rfl, rfl⟩ := hacc
    wp_auto
    have hle1 : k8s_io.apimachinery.pkg.apis.«meta».v1.ListInterface.ty ≤u go.GoType.InterfaceType _ :=
      inferInstance
    have hle2 : go.UnderlyingDirectedEq k8s_io.apimachinery.pkg.api.«meta».List''.ty
      k8s_io.apimachinery.pkg.apis.«meta».v1.ListInterface.ty := inferInstance
    haveI : k8s_io.apimachinery.pkg.api.«meta».List''.ty ≤u go.GoType.InterfaceType _ :=
      ⟨hle2.underlying_unfold.trans hle1.underlying_eq⟩
    wp_auto
    wp_apply (wp_GRV lp DFrac.discard _) $$ [Hl]
    · iexact Hl
    iintro -
    simp only
    wp_auto
    wp_apply (wp_PRV (k8s_etcd3.rvStr rv)) as %n %perr Hpr
    rw [k8s_etcd3.parseRVD_rvStr]
    icases Hpr with %Hpr
    obtain ⟨rfl, rfl⟩ := Hpr
    wp_auto
    by_cases h0 : n = W64 0
    · rw [decide_eq_true h0]
      wp_auto
      have : listRespRVL rr = none := by unfold listRespRVL; simp [hen, ho, h0]
      rw [this, hnone.1, hnone.2]
      iapply HΦ
      itrivial
    · rw [decide_eq_false h0]
      wp_auto
      have : listRespRVL rr = some n := by unfold listRespRVL; simp [hen, ho]; exact h0
      rw [this, show (some n).getD 0 = n from rfl, show (some n).isSome = true from rfl]
      iapply HΦ
      itrivial
  | _ => rw [ho] at hlo; exact hlo.elim

end proof

end k8s_correctness
end EtcdGrove
end Perennial
