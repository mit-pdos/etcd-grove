/-
Lean-first (no Rocq counterpart).

The proof of `watchRevisionRange` when the pure function answers: the events' range
(`eventResourceVersionRange`), the request's resource version parsed, its start raised as the
match asks (`matchOptL`: the three matches the driver sends, so the `default` error is unreachable,
and `Exact` at `0` is excluded by `watchRangeL`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.watchRevisionRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.eventResourceVersionRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.versioner__ParseResourceVersion

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map k8sDeep k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input)


section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem watchRevisionRange.wp_proof
    (wp_ERR : eventResourceVersionRange.spec (GF := GF) (hG := hG))
    (wp_PRV : k8s_etcd3.versioner.ParseResourceVersion.spec (GF := GF) (hG := hG)) :
    watchRevisionRange.spec (GF := GF) (hG := hG) := by
  have hmax : (#(functions go.max [go.uint64, go.uint64]) : val) = max.impl go.uint64 2 :=
    FuncUnfold.func_unfold (f := go.max) (type_args := List.replicate 2 go.uint64)
  intro req x sl rs o hok
  wp_start as ⟨#Hreq, #Hs⟩
  unfold wreqRep
  icases Hreq with ⟨%p, %hreq, #Hsie⟩
  subst hreq
  unfold watchRangeL at hok
  cases her : evRangeR rs with
  | none => rw [her] at hok; cases hok
  | some eo =>
  rw [her] at hok
  wp_auto
  wp_apply (wp_ERR sl rs eo her) $$ [Hs] as %rp %err ⟨%herr, Hr⟩
  · iframe #
  subst herr
  cases eo with
  | none =>
    simp only [Option.some.injEq] at hok
    subst hok
    iunfold rangeRep at Hr
    icases Hr with %hrp
    subst hrp
    wp_auto
    iapply HΦ
    unfold rangeRep
    ipureintro; exact ⟨rfl, rfl⟩
  | some mm =>
  obtain ⟨mn, mx⟩ := mm
  iunfold rangeRep at Hr
  ihave Hr' : rp ↦ github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ResourceVersionRange.mk mn mx $$ Hr
  ihave %hnn := typedPointsto_not_null _ _ _ $$ Hr'
  iStructNamed Hr'
  wp_auto
  wp_if_destruct
  · exfalso; exact hnn rfl
  (try wp_auto)
  simp only at hok
  cases hp : parseRVD x.MinRV' with
  | none => rw [hp] at hok; cases hok
  | some req =>
  rw [hp] at hok
  simp only at hok
  wp_apply (wp_PRV x.MinRV') as %n %perr Hpr
  rw [hp]
  icases Hpr with %Hpr
  obtain ⟨rfl, rfl⟩ := Hpr
  wp_auto
  by_cases hm1 : x.Match' = W64 1
  · have hmo : matchOptL x = go!"NotOlderThan" := by simp [matchOptL, hm1]
    simp only [hm1, ↓reduceIte, Option.some.injEq] at hok
    subst hok
    rw [hmo]
    try simp (config := { decide := true }) only
    iterate 4
      all_goals (try simp only [hmax])
      all_goals (try wp_auto)
      all_goals (try wp_if_destruct)
    all_goals
      iapply HΦ
      isplitr
      · ipureintro; rfl
      unfold rangeRep
      iapply typedPointsto_combine _ _ _ hnn
      simp only [TypedPointsto.typedPointstoDef]
      unfold wmax
      repeat' split
      all_goals first | (exfalso; word) | iframe
  by_cases hm2 : x.Match' = W64 2
  · have hmo : matchOptL x = go!"Exact" := by simp [matchOptL, hm1, hm2]
    rw [if_neg hm1, if_pos hm2] at hok
    have hn0 : n ≠ 0 := by intro h; rw [if_pos h] at hok; cases hok
    rw [if_neg hn0, Option.some.injEq] at hok
    subst hok
    rw [hmo]
    try simp (config := { decide := true }) only
    iterate 4
      all_goals (try wp_auto)
      all_goals (try wp_if_destruct)
    all_goals
      try (exfalso; first | exact hn0 rfl | exact hn0 ‹_› | word)
    all_goals
      iapply HΦ
      isplitr
      · ipureintro; rfl
      unfold rangeRep
      iapply typedPointsto_combine _ _ _ hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
  · have hmo : matchOptL x = [] := by
      unfold matchOptL; rw [if_neg hm1, if_neg hm2]
    rw [if_neg hm1, if_neg hm2, Option.some.injEq] at hok
    subst hok
    rw [hmo]
    try simp (config := { decide := true }) only
    iterate 4
      all_goals (try wp_auto)
      all_goals (try wp_if_destruct)
    all_goals
      iapply HΦ
      isplitr
      · ipureintro; rfl
      unfold rangeRep
      iapply typedPointsto_combine _ _ _ hnn
      simp only [TypedPointsto.typedPointstoDef]
      repeat' split
      all_goals first | (exfalso; word) | iframe

end proof

end k8s_correctness
end EtcdGrove
end Perennial
