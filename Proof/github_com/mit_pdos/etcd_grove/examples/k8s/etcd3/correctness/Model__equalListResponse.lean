module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__equalListResponse
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__validCacherContinue
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList__GetContinue
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList__SetContinue
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList__DeepCopyObject
public import Spec.k8s_io.apimachinery.pkg.api.meta.ListAccessor
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ListAccessorObjList
public import Spec.reflect.DeepEqualK8s

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map k8sDeep k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input)

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

theorem iface_cases (x : GoInterface) : x = GoInterface.nil ∨ ∃ ii, x = GoInterface.ok ii := by
  cases x with
  | nil => left; rfl
  | ok ii => right; exact ⟨ii, rfl⟩

-- A failing check of `equalListResponse` answers `false` (the responses differ).
set_option hygiene false in
local macro "eq_false" a:term:max b:term:max : tactic => `(tactic| (
  have hF : equalListRespL x m ⟨$a, .deep d1⟩ ⟨$b, .deep d2⟩ = false := by
    unfold equalListRespL; rw [hR]; simp only [Bool.false_or]
    first
    | (cases d1 <;> simp_all [errNonNil]; done)
    | (cases d2 <;> simp_all [errNonNil]; done)
    | simp_all [errNonNil]
  rw [hF]
  iapply HΦ; itrivial))

theorem Model.equalListResponse.wp_proof
    (wp_DE : reflect.DeepEqual.spec_k8s (GF := GF) (hG := hG))
    (wp_LA : apimeta.ListAccessor.spec (GF := GF) (hG := hG))
    (wp_GC : k8s_etcd3.ObjList.GetContinue.spec (GF := GF) (hG := hG))
    (wp_SC : k8s_etcd3.ObjList.SetContinue.spec (GF := GF) (hG := hG))
    (wp_DC : k8s_etcd3.ObjList.DeepCopyObject.spec (GF := GF) (hG := hG))
    (wp_VCC : Model.validCacherContinue.spec (GF := GF) (hG := hG)) :
    Model.equalListResponse.spec (GF := GF) (hG := hG) := by
  intro mp m x re ro exp out hloe hloo hde hdo
  cases re with | mk o1 e1 =>
  cases ro with | mk o2 e2 =>
  cases exp with | mk eo ee =>
  cases out with | mk oo oe =>
  cases ee with
  | tooLarge _ => exact hde.elim
  | other => exact hde.elim
  | deep d1 =>
  cases oe with
  | other => exact hdo.elim
  | tooLarge dl =>
    simp only at hloe hloo
    wp_start as ⟨#Hm, #Hre, #Hro⟩
    iunfold respRep at Hre
    iunfold respRep at Hro
    icases Hre with ⟨#Ho1, #He1⟩
    icases Hro with ⟨#Ho2, #He2⟩
    ihave #He2' := He2
    iunfold errRep at He2'
    icases He2' with ⟨#Ht, -⟩
    ihave %Hpe := apierrors.tooLargeErrIs_ptr _ $$ Ht
    obtain ⟨l, rfl⟩ := Hpe
    unfold modelAt modelRep modelVal
    icases Hm with ⟨#Hinit, %il, %rl, %M, #Hp, -, -, -⟩
    iStructNamed Hp
    wp_auto
    wp_apply (wp_DeepEqual_resp wp_DE _ _ _ _ eo oo (.deep d1) (.tooLarge dl) trivial trivial) $$ []
    · iframe Ho1 He1 Ho2 He2
    rw [show respEqL ⟨eo, .deep d1⟩ ⟨oo, .tooLarge dl⟩ = false from rfl]
    have hF : equalListRespL x m ⟨eo, .deep d1⟩ ⟨oo, .tooLarge dl⟩ = false := by
      unfold equalListRespL respEqL; simp [errNonNil]
    rw [hF]
    wp_auto
    by_cases hl : sint.Z x.Limit' ≤ sint.Z (W64 0)
    · rw [decide_eq_true hl]
      wp_auto
      iapply HΦ; itrivial
    rw [decide_eq_false hl]
    wp_auto
    cases e1 with
    | ok ii => wp_auto; iapply HΦ; itrivial
    | nil => wp_auto; iapply HΦ; itrivial
  | deep d2 =>
  simp only at hloe hloo
  wp_start as ⟨#Hm, #Hre, #Hro⟩
  iunfold respRep at Hre
  iunfold respRep at Hro
  icases Hre with ⟨#Ho1, #He1⟩
  icases Hro with ⟨#Ho2, #He2⟩
  iunfold errRep at He1
  iunfold errRep at He2
  ihave #Hm0 := Hm
  unfold modelAt modelRep modelVal
  icases Hm with ⟨#Hinit, %il, %rl, %M, #Hp, -, -, -⟩
  iStructNamed Hp
  wp_auto
  wp_apply (wp_DE.2.1 o1 e1 o2 e2 eo d1 oo d2 DFrac.discard DFrac.discard) $$ [] as %b ⟨%hb, -⟩
  · iframe Ho1 He1 Ho2 He2
  cases b
  case true =>
    wp_auto
    have : equalListRespL x m ⟨eo, .deep d1⟩ ⟨oo, .deep d2⟩ = true := by
      unfold equalListRespL respEqL
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      left; exact hb.1 rfl
    rw [this]
    iapply HΦ; itrivial
  have hne : ¬ (eo = oo ∧ d1 = d2) := fun h => by cases hb.2 h
  have hR : respEqL ⟨eo, .deep d1⟩ ⟨oo, .deep d2⟩ = false := by
    unfold respEqL; simp only [decide_eq_false_iff_not]; exact hne
  ihave %hn1 := deepRep_nil_iff _ _ _ $$ He1
  ihave %hn2 := deepRep_nil_iff _ _ _ $$ He2
  ihave %hm1 := deepRep_nil_iff _ _ _ $$ Ho1
  ihave %hm2 := deepRep_nil_iff _ _ _ $$ Ho2
  wp_auto
  by_cases hl : sint.Z x.Limit' ≤ sint.Z (W64 0)
  · rw [decide_eq_true hl]
    wp_auto
    have : equalListRespL x m ⟨eo, .deep d1⟩ ⟨oo, .deep d2⟩ = false := by
      unfold equalListRespL; rw [hR]; simp only [Bool.false_or]
      have : ¬ (0 < sint.Z x.Limit') := by word
      simp [this]
    rw [this]
    iapply HΦ; itrivial
  rw [decide_eq_false hl]
  wp_auto
  rcases iface_cases e1 with he | ⟨ii, he⟩
  case inr =>
    have : d1 ≠ .nil := fun h => by rw [← hn1] at h; rw [h] at he; cases he
    rw [he]; wp_auto; eq_false eo oo
  rw [he]
  wp_auto
  have hd1 : d1 = .nil := hn1.1 he
  rcases iface_cases e2 with he2 | ⟨ii, he2⟩
  case inr =>
    have : d2 ≠ .nil := fun h => by rw [← hn2] at h; rw [h] at he2; cases he2
    rw [he2]; wp_auto; eq_false eo oo
  rw [he2]
  wp_auto
  have hd2 : d2 = .nil := hn2.1 he2
  cases eo with
  | nil =>
    rw [hm1.2 rfl]; wp_auto; eq_false DeepV.nil oo
  | obj _ | storageErr _ _ _ _ | errString _ => exact hloe.elim
  | list ei erv ec erem =>
  iunfold deepRep at Ho1
  icases Ho1 with ⟨%p1, %sl1, %rp1, %hx1, #Hl1, #Hi1, #Hr1⟩
  rw [hx1]
  wp_auto
  cases oo with
  | nil =>
    rw [hm2.2 rfl]; wp_auto; eq_false (DeepV.list ei erv ec erem) DeepV.nil
  | obj _ | storageErr _ _ _ _ | errString _ => exact hloo.elim
  | list oi orv oc orem =>
  iunfold deepRep at Ho2
  icases Ho2 with ⟨%p2, %sl2, %rp2, %hx2, #Hl2, #Hi2, #Hr2⟩
  rw [hx2]
  wp_auto
  have hle1 : k8s_io.apimachinery.pkg.apis.«meta».v1.ListInterface.ty ≤u go.GoType.InterfaceType _ :=
    inferInstance
  have hle2 : go.UnderlyingDirectedEq k8s_io.apimachinery.pkg.api.«meta».List''.ty
    k8s_io.apimachinery.pkg.apis.«meta».v1.ListInterface.ty := inferInstance
  haveI : k8s_io.apimachinery.pkg.api.«meta».List''.ty ≤u go.GoType.InterfaceType _ :=
    ⟨hle2.underlying_unfold.trans hle1.underlying_eq⟩
  wp_apply (ListAccessor_objList wp_LA p1) as %acc %aerr %hacc
  obtain ⟨rfl, rfl⟩ := hacc
  wp_auto
  wp_apply (wp_GC p1 DFrac.discard _) $$ [Hl1]
  · iexact Hl1
  iintro -
  simp only
  by_cases hec : ec = []
  · wp_auto
    rw [decide_eq_true hec]
    wp_auto
    eq_false (DeepV.list ei erv ec erem) (DeepV.list oi orv oc orem)
  wp_auto
  rw [decide_eq_false hec]
  wp_auto
  wp_apply (ListAccessor_objList wp_LA p2) as %acc %aerr %hacc
  obtain ⟨rfl, rfl⟩ := hacc
  wp_auto
  wp_apply (wp_GC p2 DFrac.discard _) $$ [Hl2]
  · iexact Hl2
  iintro -
  simp only
  wp_auto
  wp_apply (wp_GC p1 DFrac.discard _) $$ [Hl1]
  · iexact Hl1
  iintro -
  simp only
  wp_auto
  wp_apply (wp_VCC mp m x ec oc) $$ []
  · unfold modelAt modelRep modelVal
    iexact Hm0
  cases hv : validCacherContinueL x m oc
  · wp_auto
    eq_false (DeepV.list ei erv ec erem) (DeepV.list oi orv oc orem)
  wp_auto
  wp_apply (wp_DC p1 DFrac.discard sl1 erv ec rp1 ei erem) $$ [] as %c ⟨-, -, -, %sl', %rp', Hc, Hci, Hcr⟩
  · iframe Hl1 Hi1 Hr1
  wp_apply (ListAccessor_objList wp_LA c) as %acc %aerr %hacc
  obtain ⟨rfl, rfl⟩ := hacc
  wp_auto
  wp_apply (wp_SC c _ oc) $$ [Hc]
  · iexact Hc
  iintro Hc
  simp only
  wp_auto
  wp_apply (wp_DE.1 _ _ (.list (some (ei.getD [])) erv oc erem) (.list oi orv oc orem) (DFrac.own 1)
    DFrac.discard) $$ [Hc Hci Hcr] as %b2 ⟨%hb2, -⟩
  · iunfold deepRep
    iframe Hci Hcr
    isplitl [Hc]
    · iframe Hc
      ipureintro; rfl
    iexists p2, sl2, rp2
    iframe Hl2 Hi2 Hr2
    ipureintro; rfl
  have : equalListRespL x m ⟨.list ei erv ec erem, .deep d1⟩ ⟨.list oi orv oc orem, .deep d2⟩ = b2 := by
    unfold equalListRespL; rw [hR]; simp only [Bool.false_or]
    subst hd1 hd2
    have hlim : 0 < sint.Z x.Limit' := by word
    cases b2 <;> simp_all [errNonNil]
  rw [this]
  iapply HΦ; itrivial

end proof

end k8s_correctness
end EtcdGrove
end Perennial
